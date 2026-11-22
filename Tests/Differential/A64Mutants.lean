import Millipede.Top.Compile
import Millipede.RegAlloc.Compile

/-!
# arm64 selection mutants

Each mutant rewrites the arm64 Asm program that the selector of `compile` produced, before
assembly, which has the effect of a bug in instruction selection. The self-test of
`scripts/differential-a64.sh` requires the native runs of the mutant's functions to fail. The
mutants are these:
* `a64-cond` uses the inverted condition in the `cset` after a `cmp`;
* `a64-slot-scale` loads frame slots from `[sp, #16y]` instead of `[sp, #8y]`;
* `a64-no-x30` leaves the save of `x30` out of the entry sequence;
* `a64-movk-shift` puts a constant's `movk` one halfword too low;
* `a64-byte-sext` sign-extends a byte load instead of zero-extending it;
* `a64-misaligned` makes frames of `8 (F + 1) - 8` bytes without rounding them to 16, so `sp` is
  misaligned or the saved `x30` lands on the caller's slot 0.
-/

namespace Millipede.Tests.Differential

open Millipede A64

/-- A mutant with its name, which rewrites each selected instruction into a list of instructions. -/
structure A64Mutant where
  name : String
  /-- the functions whose runs must fail -/
  funcs : List String
  rewrite : Instr → List Instr

def a64Mutants : List A64Mutant := [
  ⟨"a64-cond", ["cmps", "minmax", "clamp3"], fun
    | .csel .csinc true d 31 31 c => [.csel .csinc true d 31 31 c.invert]
    | i => [i]⟩,
  ⟨"a64-slot-scale", ["addClamp", "arith", "divmod"], fun
    | .ldr .x r (.uimm 31 y) => [.ldr .x r (.uimm 31 (y + y))]
    | i => [i]⟩,
  ⟨"a64-no-x30", ["addClamp", "arith", "mop"], fun
    | .str .x 30 (.uimm 31 _) => []
    | i => [i]⟩,
  ⟨"a64-movk-shift", ["bigImm", "lcg", "addClamp"], fun
    | .mov .k true d imm hw => [.mov .k true d imm (hw - 1)]
    | i => [i]⟩,
  ⟨"a64-byte-sext", ["bTok", "bOps", "ovByte"], fun
    | .ldr .b d a => [.ldr .b d a, .bfm true true d d 0 7]
    | i => [i]⟩,
  ⟨"a64-misaligned", ["addClamp", "arith", "mop"], fun
    | .addImm true sub false d 31 imm false =>
      if d = 31 || d = 17 then [.addImm true sub false d 31 (imm - 8) false]
      else [.addImm true sub false d 31 imm false]
    | i => [i]⟩]

/-- Apply a mutation to every plain instruction of a symbolic sequence. -/
def mutSeq (m : A64Mutant) (is : List A64.SI) : List A64.SI :=
  is.flatMap fun
    | .op i => (m.rewrite i).map .op
    | si => [si]

/-- The arm64 pipeline with the options `o`, including allocation and the register selector, with
each block of the selected program rewritten by `rw`. -/
def compileA64Rw (rw : List A64.SI → List A64.SI) (p : Program) (o : Compile.Options := {}) :
    Except String ByteArray := do
  if Compile.checks p = false then throw "checks"
  let fp ← Flat.lower p
  let P := Compile.a64Prep o (Lin.linearize fp p.memBytes)
  let A ← RegAlloc.A64Reg.selectFb (Compile.a64K o) (Compile.a64C o) P o.memBase
  let A' : Asm.Prog A64.arch := { A with funs := A.funs.map fun f =>
    { f with entry := rw f.entry, blocks := f.blocks.map rw } }
  let obj ← Asm.assemble A64.asm A'
  let img ← Link.link (Compile.linkConfigA64 P) [obj]
  let bs ← arm64Linux.fmt.write img
  pure ⟨bs.toArray⟩

/-! ## Register-selector mutants

Each of these mutants rewrites the program that the register selector produced, which has the
effect of a bug in that selector. `differential genmut-areg <dir> <mutant> <function>` builds a
function with one, under the options that the environment selects. The mutants are these:
* `areg-no-save` leaves out the call sequence's saves of the caller's registers;
* `areg-restore-word` makes `ret` restore a register from the wrong frame word;
* `areg-scratch` renames `x19` and `x4`, the registers of the first preserved and caller-saved
  locations, to the scratch register `x16`;
* `areg-syscall` renames `x19` to the system-call argument register `x1`;
* `areg-wrong-reg` makes an addition read the register of location 1 instead of location 0;
* `areg-last-save` skips the last save of each call sequence, as a callee that saves one register
  too few would;
* `areg-slot-move` selects a move between two different slot locations as nothing, as a selector
  that took it for a move of a location to itself would;
* `areg-last-arg` omits the last register argument of each call sequence, as a call that took a
  location live at the callee's entry for a dead one would;
* `areg-imm` adds one to the immediate of every `add`/`sub` of an immediate that is not a frame
  set-up, as a wrong immediate encoding would;
* `areg-zero-store` stores a one to the data region where the selector stores a zero from `xzr`;
* `areg-clobber` leaves values in caller-saved registers across calls: the allocator ignores the
  clobber sets and the selector skips the clobber check;
* `areg-sys-clobber` leaves values in `x8` across system calls, into which an extern call loads
  its number: with no preserved locations, the allocator lets a value live across an extern call
  take `x8` and no other caller-saved register, and the selector skips the clobber check;
* `areg-res-clobber` leaves values in `x0` across calls, which deliver their first result there:
  with no preserved locations, the allocator lets a value live across a call take `x0` and the
  selector skips the clobber check;
* `areg-pmove` emits each run of register copies of a block in reverse order, as a parallel move
  sequentialised without regard to which move reads a register another one writes;
* `amem-disp` adds 8 to the index of every data load `[x29, xm]` (`Options.memBase`), as a wrong
  offset would;
* `amem-base-call` sets `x29` to zero after every `bl`, as a callee that did not keep the data
  region's base would;
* `amem-no-base` leaves the `adrp x29` of every entry sequence out, so that `x29` never holds the
  data region's address.
-/

/-- Rename the registers of an instruction. -/
def mapReg (f : Reg → Reg) : Instr → Instr
  | .mov op sf d imm hw => .mov op sf (f d) imm hw
  | .addImm sf sub setf d n imm sh => .addImm sf sub setf (f d) (f n) imm sh
  | .addReg sf sub setf d n m => .addReg sf sub setf (f d) (f n) (f m)
  | .logReg op sf d n m => .logReg op sf (f d) (f n) (f m)
  | .madd sf sub d n m a => .madd sf sub (f d) (f n) (f m) (f a)
  | .div sf s d n m => .div sf s (f d) (f n) (f m)
  | .shiftV op sf d n m => .shiftV op sf (f d) (f n) (f m)
  | .bfm s sf d n r i => .bfm s sf (f d) (f n) r i
  | .csel op sf d n m c => .csel op sf (f d) (f n) (f m) c
  | .ldr sz t a => .ldr sz (f t) (mapAddr a)
  | .str sz t a => .str sz (f t) (mapAddr a)
  | .cbz sf nz t imm => .cbz sf nz (f t) imm
  | i => i
where
  mapAddr : Addr → Addr
    | .uimm n imm => .uimm (f n) imm
    | .simm n imm => .simm (f n) imm
    | .reg n m => .reg (f n) (f m)

/-- Whether `r` is one of the location registers, `x19 … x28` or the caller-saved
`x4 … x7, x10 … x14, x8`. -/
def isLoc (r : Reg) : Bool :=
  (19 ≤ r.toNat && r.toNat ≤ 28) || (4 ≤ r.toNat && r.toNat ≤ 8) || (10 ≤ r.toNat && r.toNat ≤ 14)

/-- A register-selector mutant, which rewrites each block. -/
structure ARegMutant where
  name : String
  funcs : List String
  block : List A64.SI → List A64.SI

/-- Whether the mutant allocates as if nothing destroyed a caller-saved register and selects
without the clobber check, which leaves values in caller-saved registers across calls. -/
def ARegMutant.noKill (m : ARegMutant) : Bool :=
  m.name == "areg-clobber" || m.name == "areg-res-clobber" || m.name == "areg-sys-clobber"

/-- A rewrite of each plain instruction. -/
def perInstr (f : Instr → List Instr) (is : List A64.SI) : List A64.SI :=
  is.flatMap fun
    | .op i => (f i).map .op
    | si => [si]

/-- Drop the last save of a location register, `str x19…, [x17, #8j]`, from a block. -/
def dropLastSave (is : List A64.SI) : List A64.SI :=
  let isSave : A64.SI → Bool := fun
    | .op (.str .x r (.uimm 17 _)) => isLoc r
    | _ => false
  match (is.zipIdx.filter (isSave ·.1)).getLast? with
  | some (_, n) => is.eraseIdx n
  | none => is

/-- Whether an instruction writes a location register `x19 … x28`. -/
def writesLoc : Instr → Bool
  | .ldr _ t _ => isLoc t
  | .logReg _ _ d _ _ | .mov _ _ d _ _ | .addImm _ _ _ d _ _ _ => isLoc d
  | _ => false

/-- Drops the instruction right before `bl` when it writes a location register, which is the last
register argument. -/
def dropLastArg : List A64.SI → List A64.SI
  | .op i :: .fix k (.b true imm) r :: rest =>
    if writesLoc i then .fix k (.b true imm) r :: rest else .op i :: .fix k (.b true imm) r :: rest
  | i :: rest => i :: dropLastArg rest
  | [] => []

/-- Whether an instruction is a register copy `mov d, s` (`orr d, xzr, s`). -/
def isMv : A64.SI → Bool
  | .op (.logReg .orr true _ 31 _) => true
  | _ => false

/-- Reverses each run of two or more register copies. -/
def revMoves (is : List A64.SI) : List A64.SI :=
  let rec go : List A64.SI → List A64.SI → List A64.SI
    | [], run => run
    | i :: rest, run => if isMv i then go rest (i :: run) else run ++ i :: go rest []
  go is []

def aregMutants : List ARegMutant := [
  ⟨"areg-no-save", ["addClamp", "clamp3", "lcg"], perInstr fun
    | .str .x r (.uimm 17 imm) => if isLoc r then [] else [.str .x r (.uimm 17 imm)]
    | i => [i]⟩,
  ⟨"areg-restore-word", ["addClamp", "arith", "cmps"], perInstr fun
    | .ldr .x r (.uimm 31 y) => if isLoc r then [.ldr .x r (.uimm 31 (y + 1))] else [.ldr .x r (.uimm 31 y)]
    | i => [i]⟩,
  ⟨"areg-scratch", ["addClamp", "arith", "bigImm"], perInstr fun i => [mapReg (fun r => if r = 19 || r = 4 then 16 else r) i]⟩,
  ⟨"areg-syscall", ["addClamp", "arith", "cmps"], perInstr fun i => [mapReg (fun r => if r = 19 then 1 else r) i]⟩,
  ⟨"areg-wrong-reg", ["arith", "cmps", "divmod"], perInstr fun
    | .addReg sf sub setf d n m => [.addReg sf sub setf d (if n = 19 then 20 else n) m]
    | i => [i]⟩,
  ⟨"areg-last-save", ["clamp3", "mEnum", "mop"], dropLastSave⟩,
  ⟨"areg-slot-move", ["dRetMid", "ovWord", "pressure"], fun
    | [.op (.ldr .x 16 (.uimm 31 y₁)), .op (.str .x 16 (.uimm 31 y₂))] =>
      if y₁ == y₂ then [.op (.ldr .x 16 (.uimm 31 y₁)), .op (.str .x 16 (.uimm 31 y₂))] else []
    | b => b⟩,
  ⟨"areg-last-arg", ["addClamp", "arith", "cmps"], dropLastArg⟩,
  ⟨"areg-imm", ["mBorrow", "mop", "sRev"], perInstr fun
    | .addImm true sub false d n imm false =>
      if d = 31 || n = 31 || d = 17 then [.addImm true sub false d n imm false]
      else [.addImm true sub false d n (imm + 1) false]
    | i => [i]⟩,
  ⟨"areg-zero-store", ["iBubble", "iLibFill", "sRev", "iRoot", "pRoot", "svSort", "svRev"], perInstr fun
    | .str sz 31 a => [.mov .z true 17 1 0, .str sz 17 a]
    | i => [i]⟩,
  ⟨"areg-clobber", ["hpCall", "clamp3", "lcg"], id⟩,
  ⟨"areg-sys-clobber", ["addClamp", "arith", "cmps"], id⟩,
  ⟨"areg-res-clobber", ["hpCall", "clamp3", "lcg"], id⟩,
  ⟨"areg-pmove", ["hpCall", "arith", "cmps"], revMoves⟩,
  ⟨"amem-disp", ["mBump", "sRev", "bCopy"], perInstr fun
    | .ldr sz d (.reg b m) =>
      if b = 29 then [.addImm true false false 16 m 8 false, .ldr sz d (.reg 29 16)]
      else [.ldr sz d (.reg b m)]
    | i => [i]⟩,
  ⟨"amem-base-call", ["mBump", "sRev", "mEnum"], fun is => is.flatMap fun
    | .fix k (.b true imm) r => [.fix k (.b true imm) r, .op (.mov .z true 29 0 0)]
    | i => [i]⟩,
  ⟨"amem-no-base", ["mBump", "sRev", "bCopy"], fun is => is.filter fun
    | .fix _ (.adr true d _) _ => d != 29
    | _ => true⟩]

/-- The arm64 pipeline with a mutation of the selected program. -/
def compileA64Mut (m : A64Mutant) (p : Program) (o : Compile.Options := {}) :
    Except String ByteArray := compileA64Rw (mutSeq m) p o

/-- The arm64 pipeline of options `o` with a register-selector mutant. -/
def compileARegMut (o : Compile.Options) (m : ARegMutant) (p : Program) : Except String ByteArray :=
  if m.noKill then do
    -- values left in caller-saved registers across calls
    if Compile.checks p = false then throw "checks"
    let fp ← Flat.lower p
    -- the result and system-call mutants have no preserved locations and let only `x0`
    -- (caller-saved register 10) hold a value across a call, or only `x8` (register 9) one across
    -- an extern call
    let res := m.name == "areg-res-clobber"
    let sys := m.name == "areg-sys-clobber"
    let k := if res || sys then 0 else Compile.a64K o
    let c := if res then 14 else Compile.a64C o
    let cl := RegAlloc.A64Reg.cls k c
    -- caller-saved registers first, so that callees use them too
    let P := Compile.prep { o with callerFirst := some true }
      (if res then { cl with kill := fun i => match i with
          | .call .. => ((List.range c).erase 10, [])
          | i => cl.kill i }
        else if sys then { cl with kill := fun i => match i with
          | .ext .. => ((List.range c).erase 9, (cl.kill i).2)
          | i => cl.kill i }
        else { cl with kill := fun i => ([], (cl.kill i).2) })
      (RegAlloc.A64Reg.cls k 0) (fun _ => true) (Lin.linearize fp p.memBytes)
    let A ← Sel.select (RegAlloc.A64Reg.selector k c o.memBase (RegAlloc.Live.of P)) P
    let obj ← Asm.assemble A64.asm A
    let img ← Link.link (Compile.linkConfigA64 P) [obj]
    let bs ← arm64Linux.fmt.write img
    pure ⟨bs.toArray⟩
  else
    -- the slot-move mutant runs with preserved locations only, where these functions move
    -- values between slots
    compileA64Rw m.block p (if m.name == "areg-slot-move" then { o with cregs := some 0 } else o)

end Millipede.Tests.Differential
