import Millipede.Top.Statement
import Millipede.Compile.LowerLawful
import Millipede.Compile.Linearize
import Millipede.Compile.AssembleProof
import Millipede.Target.X64.Budget
import Millipede.Object.Link
import Millipede.Object.Elf.Laws
import Millipede.Target.A64.Select
import Millipede.Opt.Config
import Millipede.RegAlloc.Alloc
import Millipede.RegAlloc.A64Reg
import Millipede.RegAlloc.IdOps

/-!
# The compiler, its backends and targets

`compile p t` runs one pipeline for every program:

```
Program --checks--> --lower--> Flat.Prog --linearize (data region [0, memBytes))--> Lin.Prog
        --allocate (validated)--> Lin.Prog --select--> Asm.Prog (bss mp_mem) --budget check-->
        --assemble--> Obj --link--> Image --write (ELF)--> bytes
```

Before lowering, the Core passes of `o.opt` rewrite the program, and the soundness theorem speaks
of the source program. `Flat.lower` places values in byte memory, except small values that are
never borrowed, which live in frame slots. The root lives in static storage, at Lin address 0,
and each reactor step runs on it. Every pass that can refuse returns `Except String`, and
`compile` returns the first refusal and never emits anything else.

The passes after lowering form a `Backend`, which bundles the Lin passes before selection,
instruction selection, the budget check, the assembler and the linker settings, while the ELF
writer belongs to the target. `backends o` registers one backend per target, and
`compileWith o p t` runs the backend registered under `t.name` and refuses every other target.
The Lin pass before selection is validated register allocation. An untrusted allocator renames
every frame slot to a location of a smaller frame, a checker validates the proposal, and a refused
proposal leaves the program as it was. `Options.regalloc := false` turns the pass off, and the
soundness theorem holds for both settings.

`compile` refuses, with a message, a program that the borrow checker rejects, that has a lens,
constructor or split without a certificate of its law, or that uses a construct outside the
fragment the memory lowering supports. It also refuses a program whose static memory does not
fit the address space, whose selected code needs more instructions per reactor step than the
target's cost model charges, that calls an extern the selector does not cover, or that exceeds
the size limits of the assembler and the linker. The stack bound and the frame discipline of the
lowered code are theorems, so they need no check. The linker enters at `main`'s symbol and asks
for exactly the Lin stack bound as the stack size, which the ELF writer records in
`PT_GNU_STACK`.

`x64Linux` bundles the x64 ISA model, the Linux system-call model, the static ELF64 format with its
loader model, the cost model `X64.κ` and the frame model `X64.φ`, and `arm64Linux` does the same
for arm64. The soundness theorem is proved once for every lawful backend in `Top/Sound.lean`.
-/

namespace Millipede

/-- The x64 Linux target, which bundles the x64 ISA model, the Linux system-call ABI and static
ELF64. -/
def x64Linux : Target where
  name := "x64-linux"
  isa := X64.isa
  abi := X64.linux
  fmt := Elf.x64Linux X64.linux
  κ := X64.κ
  φ := X64.φ

/-- The arm64 Linux target, which bundles the arm64 ISA model, the Linux system-call ABI and static
ELF64 with 64 KiB layout pages. -/
def arm64Linux : Target where
  name := "arm64-linux"
  isa := A64.isa
  abi := A64.linux
  fmt := Elf.a64Linux A64.linux
  κ := A64.κ
  φ := A64.φ

/-- A backend, which is what `compile` runs for one target after lowering. It holds the passes
before selection, instruction selection into an assembly program of its symbolic layer `arch`,
the budget check at the target's cost model with its refusal message, the assembler and the
linker settings, all applied to the program that `prep` made of the linearized one. The ELF
writer is the target's `fmt.write`, and `Backend.Laws` is what a backend proves. -/
structure Backend where
  target : Target
  arch : Asm.Arch
  /-- the Lin passes before selection, which perform validated register allocation -/
  prep : Lin.Prog → Lin.Prog
  select : Lin.Prog → Except String (Asm.Prog arch)
  /-- the budget check of the selected code at `target.κ` -/
  budgetOk : Lin.Prog → Bool
  budgetMsg : String
  assemble : Asm.Prog arch → Except String Obj
  linkConfig : Lin.Prog → Link.Config

namespace Compile

/-- The compiler's options. -/
structure Options where
  /-- run validated register allocation before selection; when `false`, the linearized program is
  selected as it is -/
  regalloc : Bool := true
  /-- the number of register locations, at most 14 on arm64 and 6 on x64; with 0 every location is
  a frame slot, and `none` takes each target's default, `X64.kDefault` or `A64Reg.kDefault` -/
  regs : Option Nat := none
  /-- the number of caller-saved register locations, which hold values not live across a call,
  at most 14 on arm64 and 6 on x64; `none` takes the target's default, `A64Reg.cDefault` or
  `X64.cDefault` -/
  cregs : Option Nat := none
  /-- the allocator's order of register classes: `some false` (the default, which executes fewer
  instructions on the high-pressure functions of doc/measurements.md) tries the preserved
  locations first for every value, `some true` the caller-saved ones, and `none` the caller-saved
  ones first exactly for the values live across no call -/
  callerFirst : Option Bool := some false
  /-- keep the data region's address in a base register and access it with displacement forms
  (x64: `lea r11, [rip + mp_mem]` once per access and `[r11 + off]`; arm64: `x29`, set at every
  function's entry, and `[x29, index]`); when `false`, every access computes the full address
  into a scratch register, as before -/
  memBase : Bool := true
  /-- rewrite the identity operations `op x, a, w` of Lin (`bor` by 0, `mul` by 1, …) to moves
  before the allocation (`RegAlloc.idOps`), so that `bor x, x, 0` and `mul i, i, 1` select to no
  code; when `false`, they are selected as operations, as before -/
  idOps : Bool := true
  /-- the Core passes, all of them by default -/
  opt : Opt.Config := Opt.Config.all
  /-- fall back to fewer passes when the pipeline refuses the optimised program; when `false`, the
  refusal is reported, which the test suites use -/
  fallback : Bool := true

/-- The Lin pass of the options, which is validated allocation with the register classes `cl`, or
nothing. The allocation's frames are checked in the words of `cl`'s register locations, which
are those of a selection at `(cl.k, cl.c)`, so when the selector `ok` refuses that allocation the
program is allocated again with the classes `cl0`, which have no caller-saved locations and whose
frames are checked in locations, as every selection allows. -/
def prepA (o : Options) (cl cl0 : RegAlloc.Alloc.Classes) (ok : Lin.Prog → Bool) (P : Lin.Prog) :
    Lin.Prog :=
  if o.regalloc then
    let P1 := RegAlloc.Alloc.allocOrId { cl with callerFirst := o.callerFirst } P
    if cl.c == 0 || ok P1 then P1 else RegAlloc.Alloc.allocOrId { cl0 with callerFirst := o.callerFirst } P
  else P

/-- The Lin passes of the options: the identity operations as moves (`Options.idOps`), then
`prepA`. -/
def prep (o : Options) (cl cl0 : RegAlloc.Alloc.Classes) (ok : Lin.Prog → Bool) (P : Lin.Prog) :
    Lin.Prog :=
  prepA o cl cl0 ok (if o.idOps then RegAlloc.idOps P else P)

/-- The linker settings for a selected x64 Lin program, which enter at `main`'s symbol and reserve
the static stack bound. -/
def linkConfig (P : Lin.Prog) : Link.Config :=
  Link.Config.x64Linux (X64.fnSym P.main) (P.stackBytes X64.φ)

/-- The linker settings for arm64, which enter at `main`'s symbol and reserve the static stack
bound. -/
def linkConfigA64 (P : Lin.Prog) : Link.Config :=
  Link.Config.a64Linux (Sel.fnSym P.main) (P.stackBytes A64.φ)

/-- The x64 linker settings for code selected with `k` preserved and `c` caller-saved register
locations, whose frames have no word for a caller-saved location: the stack bound under
`X64.φ.words k c`. -/
def linkConfigW (k c : Nat) (P : Lin.Prog) : Link.Config :=
  Link.Config.x64Linux (X64.fnSym P.main) (P.stackBytes (X64.φ.words k c))

/-- The arm64 linker settings for code selected with `k` preserved and `c` caller-saved register
locations: the stack bound under `A64.φ.words k c`. -/
def linkConfigA64W (k c : Nat) (P : Lin.Prog) : Link.Config :=
  Link.Config.a64Linux (Sel.fnSym P.main) (P.stackBytes (A64.φ.words k c))

/-- The checks before lowering, which are the certificates of the building blocks and the borrow
checker. -/
def checks (p : Program) : Bool :=
  p.init.certified && p.step.certified && p.wf

/-- The pipeline of backend `B` from a Flat program with `M` bytes of static memory up to the
linked image. It linearizes, runs `B.prep` and `B.select`, checks the instruction budget,
assembles and links. -/
def backendOf (B : Backend) (fp : Flat.Prog) (M : Nat) : Except String Image := do
  let P := B.prep (Lin.linearize fp M)
  let A ← B.select P
  if B.budgetOk P = false then throw B.budgetMsg
  let obj ← B.assemble A
  Link.link (B.linkConfig P) [obj]

/-- The pipeline of backend `B` up to the file contents. -/
def bytesOf (B : Backend) (p : Program) : Except String (List UInt8) := do
  if checks p = false then
    throw "compile: a term the borrow checker rejects, or a lens, constructor or split without a certificate of its law"
  let fp ← Flat.lower p
  let img ← backendOf B fp p.memBytes
  B.target.fmt.write img

end Compile

/-- The number of x64 register locations under options `o`, which is 0 with allocation off. -/
def Compile.x64K (o : Compile.Options) : Nat :=
  if o.regalloc then min (o.regs.getD X64.kDefault) X64.maxK else 0

/-- The caller-saved register locations of x64 under options `o` (none with allocation off). -/
def Compile.x64C (o : Compile.Options) : Nat :=
  if o.regalloc then min (o.cregs.getD X64.cDefault) X64.maxC else 0

/-- The Lin pass of the x64 backend: allocation at `(x64K o, x64C o)`, or at `(x64K o, 0)` when
the selector refuses that. -/
def Compile.x64Prep (o : Compile.Options) : Lin.Prog → Lin.Prog :=
  Compile.prep o (X64.cls (Compile.x64K o) (Compile.x64C o)) (X64.cls (Compile.x64K o) 0)
    (fun Q => (X64.select (Compile.x64K o) (Compile.x64C o) Q o.memBase).isOk)

/-- The x64 backend, which allocates with `x64K o` preserved and `x64C o` caller-saved register
locations, selects with `X64.selectFb`, which falls back to preserved locations only and then to
slot locations when the register selector refuses, checks its budget at `X64.κ`, and assembles
with `X64.assemble`. -/
def x64Backend (o : Compile.Options := {}) : Backend where
  target := x64Linux
  arch := X64.arch
  prep := Compile.x64Prep o
  select P := X64.selectFb (Compile.x64K o) (Compile.x64C o) P o.memBase
  budgetOk P := X64.budgetOk (Compile.x64K o) (Compile.x64C o) X64.κ P o.memBase
  budgetMsg := "compile: the selected code needs more instructions per reactor step than the cost model X64.κ charges"
  assemble := X64.assemble
  linkConfig P := Compile.linkConfigW (X64.kcUsed (Compile.x64K o) (Compile.x64C o) P o.memBase).1
    (X64.kcUsed (Compile.x64K o) (Compile.x64C o) P o.memBase).2 P

/-- The register locations of arm64 under options `o` (none with allocation off). -/
def Compile.a64K (o : Compile.Options) : Nat :=
  if o.regalloc then min (o.regs.getD RegAlloc.A64Reg.kDefault) 10 else 0

/-- The caller-saved register locations of arm64 under options `o` (none with allocation off). -/
def Compile.a64C (o : Compile.Options) : Nat :=
  if o.regalloc then min (o.cregs.getD RegAlloc.A64Reg.cDefault) 14 else 0

/-- The Lin pass of the arm64 backend: allocation at `(a64K o, a64C o)`, or at `(a64K o, 0)` when
the selector refuses that. -/
def Compile.a64Prep (o : Compile.Options) : Lin.Prog → Lin.Prog :=
  Compile.prep o (RegAlloc.A64Reg.cls (Compile.a64K o) (Compile.a64C o))
    (RegAlloc.A64Reg.cls (Compile.a64K o) 0)
    (fun Q => (RegAlloc.A64Reg.select (Compile.a64K o) (Compile.a64C o) Q o.memBase).isOk)

/-- The arm64 backend, which allocates with `a64K o` preserved and `a64C o` caller-saved register
locations, selects with `A64Reg.selectFb`, which falls back to preserved locations only and then
to slot locations when the register selector refuses, checks its budget at `A64.κ`, and assembles
with the word assembler. -/
def a64Backend (o : Compile.Options := {}) : Backend where
  target := arm64Linux
  arch := A64.arch
  prep := Compile.a64Prep o
  select P := RegAlloc.A64Reg.selectFb (Compile.a64K o) (Compile.a64C o) P o.memBase
  budgetOk P := RegAlloc.A64Reg.budgetOk (Compile.a64K o) (Compile.a64C o) P o.memBase
  budgetMsg := "compile: the selected code needs more instructions per reactor step than the cost model A64.κ charges"
  assemble := Asm.assemble A64.asm
  linkConfig P := Compile.linkConfigA64W (RegAlloc.A64Reg.kcUsed (Compile.a64K o) (Compile.a64C o) P o.memBase).1
    (RegAlloc.A64Reg.kcUsed (Compile.a64K o) (Compile.a64C o) P o.memBase).2 P

/-- The backends, one per target name. -/
def backends (o : Compile.Options := {}) : List Backend := [x64Backend o, a64Backend o]

/-- The backend of a target, which is the one registered under its name. -/
def Backend.of? (t : Target) (o : Compile.Options := {}) : Option Backend :=
  (backends o).find? (·.target.name == t.name)

/-- The known targets, which `mpc --target`, `MP_TARGET` and `#mp_compile` accept by name. -/
def targets : List Target := (backends).map (·.target)

/-- The target named `n`, or `none` for an unknown name, which every driver refuses. -/
def Target.ofName? (n : String) : Option Target := targets.find? (·.name == n)

/-- The target that a driver option or `MP_TARGET` names. When the option is absent it is
`x64Linux`, and a name that is not a known target's is refused rather than replaced by a
default. -/
def Target.ofOption (v : Option String) : Except String Target :=
  match v with
  | none => .ok x64Linux
  | some n => match Target.ofName? n with
    | some t => .ok t
    | none => .error s!"unknown target '{n}' (known: {", ".intercalate (targets.map (·.name))})"

/-- The pipeline of backend `B` on `p` optimised by the first of the configurations `cs` whose
program it accepts, together with that configuration. It returns `e` when none is accepted. -/
def Compile.firstOk (B : Backend) (κ : CostModel) (φ : FrameModel) (p : Program) :
    List Opt.Config → Except String (List UInt8 × Opt.Config) →
    Except String (List UInt8 × Opt.Config)
  | [], e => e
  | c :: cs, _ => match Compile.bytesOf B (c.optimize κ φ p) with
    | .ok bs => .ok (bs, c)
    | .error e => Compile.firstOk B κ φ p cs (.error e)

/-- The compiler with options `o`, which returns the image and the configuration of Core passes
whose program was compiled. It runs the Core passes that `o` enables and then the backend
registered for `t`, and it refuses any other target. When the pipeline refuses the optimised
program, it tries the program optimised by ever shorter prefixes of the enabled passes, down to
the source program, so a pass never makes an accepted program refused. With `o.fallback` off it
reports the refusal instead. The source must pass the checks before lowering whether or not it is
optimised, and with every pass off this is the unoptimised compiler. -/
def compileRun (o : Compile.Options) (p : Program) (t : Target) :
    Except String (ByteArray × Opt.Config) :=
  match Backend.of? t o with
  | some B =>
    if o.opt.passes.isEmpty || !Compile.checks p then
      (Compile.bytesOf B p).map fun bs => (⟨bs.toArray⟩, Opt.Config.none)
    else
    match Compile.bytesOf B (o.opt.optimize t.κ t.φ p) with
    | .ok bs => .ok (⟨bs.toArray⟩, o.opt)
    | .error e =>
      if o.fallback then
        (Compile.firstOk B t.κ t.φ p o.opt.prefixes (.error e)).map fun (bs, c) => (⟨bs.toArray⟩, c)
      else .error ("compile: the optimised program is refused: " ++ e)
  | none => .error ("compile: unsupported target " ++ t.name)

/-- The compiler with options `o`, which returns the image of `compileRun`. -/
def compileWith (o : Compile.Options) (p : Program) (t : Target) : Except String ByteArray :=
  (compileRun o p t).map (·.1)

/-- The compiler with the default options, which run every Core pass and register allocation. -/
def compile (p : Program) (t : Target) : Except String ByteArray := compileWith {} p t

end Millipede
