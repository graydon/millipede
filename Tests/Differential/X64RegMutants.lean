import Millipede.Top.Compile

/-!
# x64 register-selector mutants

Each mutant rewrites the x64 assembly program that the register selector of `compile` produced,
before assembly, with the effect of a bug in the selector. The self-test of
`scripts/differential.sh` compiles the mutant's functions this way, runs them under qemu and
requires each run to fail. The mutants are these:

* `xreg-no-save` does not save the caller's location registers in a call sequence;
* `xreg-restore-word` restores a location register from the wrong frame word at `ret`;
* `xreg-rcx` puts location 0 in `rcx`, which holds the second operand and the shift count;
* `xreg-div` puts location 0 in `rdx`, which division and the length of `write` clobber;
* `xreg-syscall` puts location 0 in `rdi`, the first system-call argument;
* `xreg-wrong-reg` makes the copies, operations and stores that read location 0 read the
  register of location 1;
* `xreg-no-move` omits the copy of the first operand into the destination of a two-operand form,
  so `mov d, n; op d, m` becomes `op d, m`;
* `xreg-last-save` skips the last save of each call sequence, as a callee that saves one
  register too few would;
* `xreg-slot-move` selects a move between two different slot locations as nothing, as a
  selector that took it for a move of a location to itself would;
* `xreg-last-arg` omits the last register argument of each call sequence, as a call that took a
  location live at the callee's entry for a dead one would;
* `xreg-clobber` leaves values in caller-saved registers across calls: the allocator ignores the
  clobber sets and the selector skips the clobber check, so a callee that uses `r8 r9 r10`
  destroys its caller's values;
* `xreg-div-clobber` leaves values in `rdx rsi rdi` across a division or remainder, which
  destroys them: the allocator, with caller-saved locations only and `r8 r9 r10` kept from every
  value, ignores the clobber set of `udiv` and `umod`, and the selector skips the clobber check;
* `xreg-sys-clobber` likewise leaves values in `rdi rsi rdx` across a system call (the allocator
  ignores the extern call's clobber set and its operand restriction);
* `xreg-res-clobber` likewise leaves a value in `rdx`, result register 2, across a call, whose
  result delivery (or callee) overwrites it;
* `xreg-pmove` emits each run of register copies of a block in reverse order, as a parallel move
  sequentialised without regard to which move reads a register another one writes;
* `xmem-disp` takes 8 from the displacement of every data load `[r11 + a + off]` with `off ≥ 8`
  (`Options.memBase`), so that it reads the word before, as a selector that put the wrong offset
  into the displacement would;
* `xmem-base` drops the `lea r11, [rip + mp_mem]` of every data access, so that `r11` holds
  whatever it held before instead of the region's base;
* `xstore-imm` keeps the low 16 bits of a word store's immediate and halves a byte store's,
  as an immediate truncated wrongly;
* `xcmp-imm` compares with an immediate one too large;
* `xcmp-signed` selects signed comparisons for unsigned ones (`setl`/`setle` for `setb`/`setbe`);
* `xidop-trunc` takes `band x, a, 0xFF` for an identity operation (`RegAlloc.idOps` with a wrong
  `BinOp.rightId`), so that byte arithmetic is no longer truncated;
* `xmem-index` puts `rax` in place of the index register of every data load and word store, as
  a selector that named the wrong register for the address would.

A location in `r11`, which `syscall` clobbers on hardware, is not tested here, because
`qemu-x86_64` does not clobber it.
-/

namespace Millipede.Tests.Differential

open Millipede X64

/-- Renames the registers of an instruction, memory bases included. -/
def xMapReg (f : Reg → Reg) : Instr → Instr
  | .movRR d s => .movRR (f d) (f s)
  | .movRI d imm => .movRI (f d) imm
  | .load d m => .load (f d) (mapMem m)
  | .store m s => .store (mapMem m) (f s)
  | .load8 d m => .load8 (f d) (mapMem m)
  | .store8 m s => .store8 (mapMem m) (f s)
  | .storeI m v => .storeI (mapMem m) v
  | .store8I m v => .store8I (mapMem m) v
  | .lea d m => .lea (f d) (mapMem m)
  | .aluRR op d s => .aluRR op (f d) (f s)
  | .aluRI op d imm => .aluRI op (f d) imm
  | .imul d s => .imul (f d) (f s)
  | .div s => .div (f s)
  | .shiftCL op d => .shiftCL op (f d)
  | .setcc c d => .setcc c (f d)
  | .movzx d s => .movzx (f d) (f s)
  | i => i
where
  mapMem : X64.Mem → X64.Mem
    | .base b d => .base (f b) d
    | .sib b i d => if h : f i.1 = .rsp then .sib b i d else .sib (f b) ⟨f i.1, h⟩ d
    | m => m

/-- Whether `r` is one of the location registers. -/
def xIsLoc (r : Reg) : Bool :=
  r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .r8, .r9, .r10, .rdi, .rsi, .rdx]

/-- Whether a displacement is negative, as in `[rsp - n]`, a word of a callee frame below `rsp`. -/
def negDisp (d : UInt32) : Bool := d ≥ 0x80000000

/-- A register-selector mutant, which rewrites each block, with the functions it is run on. -/
structure XRegMutant where
  name : String
  funcs : List String
  block : List SI → List SI

/-- The clobber mutants' allocation: the numbers of preserved and caller-saved locations and the
classes with part of the clobber sets left out; the selector then skips the clobber check. -/
def XRegMutant.classes (m : XRegMutant) (k c : Nat) : Option (Nat × Nat × RegAlloc.Alloc.Classes) :=
  let cl := X64.cls 0 6
  if m.name == "xreg-clobber" then some (k, c, { X64.cls k c with kill := fun _ => ([], []) })
  else
  -- `r8 r9 r10` are kept from every value, so that values go to `rdi rsi rdx`
  let only (cross : List Nat) (i : Lin.Instr) : List Nat × List Nat := (cross, (cl.kill i).2 ++ [0, 1, 2])
  if m.name == "xreg-div-clobber" then some (0, 6, { cl with kill := fun i => match i with
    | .bin .udiv .. | .bin .umod .. => only [] i
    | i => only (cl.kill i).1 i })
  else if m.name == "xreg-sys-clobber" then some (0, 6, { cl with kill := fun i => match i with
    | .ext .. => ([], [0, 1, 2])
    | i => only (cl.kill i).1 i })
  else if m.name == "xreg-res-clobber" then some (0, 6, { cl with kill := fun i => match i with
    | .call .. => only ((List.range 6).erase 5) i
    | i => only (cl.kill i).1 i })
  else none

/-- A rewrite of each plain instruction. -/
def xPerInstr (f : Instr → List Instr) (is : List SI) : List SI :=
  is.flatMap fun
    | .op i => (f i).map .op
    | si => [si]

/-- Whether the instruction is a save `mov [rsp - n], loc`. -/
def isSave : SI → Bool
  | .op (.store (.base .rsp d) r) => xIsLoc r && negDisp d
  | _ => false

/-- Drops the last save of a block. -/
def xDropLastSave (is : List SI) : List SI :=
  match (is.zipIdx.filter (isSave ·.1)).getLast? with
  | some (_, n) => is.eraseIdx n
  | none => is

/-- Whether an instruction writes a location register. -/
def xWritesLoc : Instr → Bool
  | .movRR d _ | .movRI d _ | .load d _ => xIsLoc d
  | _ => false

/-- Drops the instruction right before a `call` when it writes a location register, which is the
last register argument. -/
def xDropLastArg : List SI → List SI
  | .op i :: .call r :: rest => if xWritesLoc i then .call r :: rest else .op i :: .call r :: rest
  | i :: rest => i :: xDropLastArg rest
  | [] => []

/-- Drops `mov d, n`, for a location register `d`, right before a two-operand form on `d`. -/
def dropMove : List SI → List SI
  | .op (.movRR d n) :: .op (.aluRR op d' m) :: rest =>
    if xIsLoc d && d == d' && op != .cmp then .op (.aluRR op d' m) :: dropMove rest
    else .op (.movRR d n) :: dropMove (.op (.aluRR op d' m) :: rest)
  | .op (.movRR d n) :: .op (.imul d' m) :: rest =>
    if xIsLoc d && d == d' then .op (.imul d' m) :: dropMove rest
    else .op (.movRR d n) :: dropMove (.op (.imul d' m) :: rest)
  | i :: rest => i :: dropMove rest
  | [] => []

/-- Reverses each run of two or more register copies `mov r, r'`. -/
def xRevMoves (is : List SI) : List SI :=
  let isMv : SI → Bool := fun
    | .op (.movRR _ _) => true
    | _ => false
  let rec go : List SI → List SI → List SI
    | [], run => run
    | i :: rest, run => if isMv i then go rest (i :: run) else run ++ i :: go rest []
  go is []

def xregMutants : List XRegMutant := [
  ⟨"xreg-no-save", ["addClamp", "clamp3", "lcg"], xPerInstr fun
    | .store (.base .rsp d) r => if xIsLoc r && negDisp d then [] else [.store (.base .rsp d) r]
    | i => [i]⟩,
  ⟨"xreg-restore-word", ["addClamp", "arith", "cmps"], xPerInstr fun
    | .load r (.base .rsp d) =>
      if xIsLoc r && !negDisp d then [.load r (.base .rsp (d + 8))] else [.load r (.base .rsp d)]
    | i => [i]⟩,
  ⟨"xreg-rcx", ["arith", "cmps", "divmod"],
    xPerInstr fun i => [xMapReg (fun r => if r = .rbx then .rcx else r) i]⟩,
  ⟨"xreg-div", ["divmod", "divc", "sRev"],
    xPerInstr fun i => [xMapReg (fun r => if r = .rbx then .rdx else r) i]⟩,
  ⟨"xreg-syscall", ["divc", "sLoop", "sRev"],
    xPerInstr fun i => [xMapReg (fun r => if r = .rbx then .rdi else r) i]⟩,
  ⟨"xreg-wrong-reg", ["addClamp", "arith", "cmps"], xPerInstr fun
    | .movRR d s => [.movRR d (if s = .rbx then .rbp else s)]
    | .aluRR op d s => [.aluRR op d (if s = .rbx then .rbp else s)]
    | .imul d s => [.imul d (if s = .rbx then .rbp else s)]
    | .store m s => [.store m (if s = .rbx then .rbp else s)]
    | i => [i]⟩,
  ⟨"xreg-no-move", ["cmps", "mop", "mEnum"], dropMove⟩,
  ⟨"xreg-last-save", ["clamp3", "mEnum", "mop"], xDropLastSave⟩,
  ⟨"xreg-slot-move", ["dRetMid", "ovWord", "pressure"], fun
    | [.op (.load .rax (.base .rsp d₁)), .op (.store (.base .rsp d₂) .rax)] =>
      if d₁ == d₂ || negDisp d₁ || negDisp d₂ then
        [.op (.load .rax (.base .rsp d₁)), .op (.store (.base .rsp d₂) .rax)]
      else []
    | b => b⟩,
  ⟨"xreg-last-arg", ["addClamp", "arith", "cmps"], xDropLastArg⟩,
  ⟨"xreg-clobber", ["hpCall", "clamp3", "lcg"], id⟩,
  ⟨"xreg-div-clobber", ["divmod", "divc", "sRev"], id⟩,
  ⟨"xreg-sys-clobber", ["addClamp", "arith", "cmps"], id⟩,
  ⟨"xreg-res-clobber", ["hpCall", "pRet", "sLoop"], id⟩,
  ⟨"xreg-pmove", ["hpCall", "arith", "cmps"], xRevMoves⟩,
  ⟨"xmem-disp", ["mBump", "sRev", "bCopy"], xPerInstr fun
    | .load d (.sib .r11 x e) => [.load d (.sib .r11 x (if e ≥ 8 then e - 8 else e))]
    | .load8 d (.sib .r11 x e) => [.load8 d (.sib .r11 x (if e ≥ 8 then e - 8 else e))]
    | i => [i]⟩,
  ⟨"xmem-base", ["mBump", "sRev", "bCopy"], fun is => is.filter fun
    | .lea .r11 _ => false
    | _ => true⟩,
  ⟨"xmem-index", ["mBump", "sRev", "bCopy"], xPerInstr fun
    | .load d (.sib .r11 _ e) => [.load d (.sib .r11 ⟨.rax, nofun⟩ e)]
    | .load8 d (.sib .r11 _ e) => [.load8 d (.sib .r11 ⟨.rax, nofun⟩ e)]
    | .store (.sib .r11 _ e) r => [.store (.sib .r11 ⟨.rax, nofun⟩ e) r]
    | i => [i]⟩,
  ⟨"xstore-imm", ["svTok", "bTok", "ovByte"], xPerInstr fun
    | .storeI m v => [.storeI m (v &&& 0xFFFF)]
    | .store8I m v => [.store8I m (v >>> 1)]
    | i => [i]⟩,
  ⟨"xidop-trunc", ["ovByte", "bOps", "bTok"], id⟩,
  ⟨"xcmp-imm", ["arith", "cmps", "lcg"], xPerInstr fun
    | .aluRI .cmp d v => [.aluRI .cmp d (v + 1)]
    | i => [i]⟩,
  ⟨"xcmp-signed", ["arith", "cmps", "lcg"], xPerInstr fun
    | .setcc .b d => [.setcc .l d]
    | .setcc .be d => [.setcc .le d]
    | i => [i]⟩]

/-- The Lin program with every `band x, a, 0xFF` taken for an identity operation (`xidop-trunc`). -/
def xIdopTrunc (P : Lin.Prog) : Lin.Prog :=
  { P with funs := P.funs.map fun fn => { fn with code := fn.code.map fun
    | .bin .band x a (.imm 0xFF) => .mov x a
    | i => i } }

/-- The x64 pipeline of options `o`, with each block of the selected program rewritten by a
register-selector mutant. -/
def compileXRegMut (o : Compile.Options) (m : XRegMutant) (p : Program) :
    Except String ByteArray := do
  -- the slot-move mutant runs with preserved locations only, where these functions move between
  -- slots
  let o := if m.name == "xreg-slot-move" then { o with cregs := some 0 } else o
  if Compile.checks p = false then throw "checks"
  let fp ← Flat.lower p
  let k := Compile.x64K o
  let c := Compile.x64C o
  -- the clobber mutants try caller-saved registers first, so that callees use them too
  let (P, A) ← match m.classes k c with
    | some (k', c', cl) =>
      let P := Compile.prep { o with callerFirst := some true } cl (X64.cls k' 0) (fun _ => true)
        (Lin.linearize fp p.memBytes)
      pure (P, ← Sel.select (X64.selector k' c' o.memBase (RegAlloc.Live.of P)) P)
    | none =>
      let P := Compile.x64Prep o (Lin.linearize fp p.memBytes)
      let P := if m.name == "xidop-trunc" then xIdopTrunc P else P
      pure (P, ← X64.selectFb k c P o.memBase)
  let A' : Asm.Prog X64.arch := { A with funs := A.funs.map fun f =>
    { f with entry := m.block f.entry, blocks := f.blocks.map m.block } }
  let obj ← X64.assemble A'
  let img ← Link.link (Compile.linkConfig P) [obj]
  let bs ← x64Linux.fmt.write img
  pure ⟨bs.toArray⟩

end Millipede.Tests.Differential
