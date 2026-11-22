import Millipede.Target.Target

/-!
# The Asm language

Asm is the instruction language of an ISA with symbolic references. An instruction may name a
local label, which is a block of the same function, or a symbol, which is another function or a
constant in read-only data, and everything else is a plain ISA instruction. An architecture's
symbolic layer `Asm.Arch` gives the instructions with symbolic references `SInstr`, their encoded
sizes, and their resolution. The size of each instruction is known before resolution, because on
x64 the rel32 and disp32 fields have a fixed width, so a layout can be computed without knowing any
address. `resolve σ a i` is the ISA instruction for `i` placed at address `a` when every reference
`r` resolves to address `σ r`, and it is `none` when a reference is unknown or out of the
encoding's reach, which the assembler refuses.

A function is an entry sequence, where its symbol points and where x64 puts the frame set-up,
followed by numbered blocks. Local label `l` is the start of block `l`, and `l = blocks.length` is
the end of the function. A program is a list of functions, constant data items with names and
bytes, the index of the entry function, and zero-initialised writable regions with names and
sizes.

The meaning of an Asm program is the machine `Asm.msem isa abi`, the same `Sem` as `Target.sem`,
started in any memory where the program is loaded under a symbol assignment `σ`. Loaded means that
each function's resolved code sits, executable, at `σ name`, and each data item sits, readable and
not writable, at `σ name`. The linker's job is to produce such a memory.

See doc/design/compiler.md.
-/

namespace Millipede.Asm

/-- A symbolic reference, to a block of the current function or to a global symbol. -/
inductive Ref where
  | label (l : Nat)
  | sym (s : String)
deriving DecidableEq, Repr, Inhabited

/-- The symbolic layer of an ISA. -/
structure Arch where
  isa : Isa
  /-- Instructions with symbolic references. -/
  SInstr : Type
  /-- The encoded size, which does not depend on what the references resolve to. -/
  size : SInstr → Nat
  /-- Resolves an instruction placed at address `a`, given the address of every reference. -/
  resolve : (Ref → Option UInt64) → UInt64 → SInstr → Option isa.Instr

/-- An Asm function, which is the entry sequence its symbol points to followed by the labelled
blocks. -/
structure Fn (A : Arch) where
  name : String
  entry : List A.SInstr
  blocks : List (List A.SInstr)

/-- An Asm program has functions, constant data items with names and bytes, the entry function,
and zero-initialised writable regions with names and sizes in bytes. A program with memory keeps
its data region in such a region. -/
structure Prog (A : Arch) where
  funs : List (Fn A)
  data : List (String × List UInt8)
  main : Nat
  bss : List (String × Nat) := []

variable {A : Arch}

/-- The total encoded size of a list of instructions. -/
def seqSize (A : Arch) : List A.SInstr → Nat
  | [] => 0
  | i :: is => A.size i + seqSize A is

/-- The offset of the start of block `l` within the blocks, which is the sum of the sizes of the
blocks before `l`. -/
def blocksOff (A : Arch) : List (List A.SInstr) → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | b :: bs, l + 1 => seqSize A b + blocksOff A bs l

/-- The offset of local label `l` in function `f`. -/
def Fn.labelOff (f : Fn A) (l : Nat) : Nat := seqSize A f.entry + blocksOff A f.blocks l

/-- How references resolve inside function `f` placed at `base`. Labels `0 … blocks.length`
resolve relative to `base`, and symbols resolve by `σ`. -/
def Fn.refAddr (f : Fn A) (σ : String → Option UInt64) (base : UInt64) : Ref → Option UInt64
  | .label l => if l ≤ f.blocks.length then some (base + UInt64.ofNat (f.labelOff l)) else none
  | .sym s => σ s

/-- Resolves a sequence of instructions placed from address `a`, by structural recursion on the
list. -/
def resolveAt (A : Arch) (ρ : Ref → Option UInt64) : UInt64 → List A.SInstr →
    Option (List A.isa.Instr)
  | _, [] => some []
  | a, i :: is =>
    match A.resolve ρ a i, resolveAt A ρ (a + UInt64.ofNat (A.size i)) is with
    | some i', some is' => some (i' :: is')
    | _, _ => none

/-- The whole function as one instruction list, the entry sequence followed by the blocks in
order. -/
def Fn.code (f : Fn A) : List A.SInstr := f.entry ++ f.blocks.flatten

/-- The resolved instructions of `f` placed at `base`. -/
def Fn.resolve (f : Fn A) (σ : String → Option UInt64) (base : UInt64) :
    Option (List A.isa.Instr) :=
  resolveAt A (f.refAddr σ base) base f.code

/-- Encodes a list of ISA instructions, or gives `none` if one cannot be encoded. -/
def encodeAll (isa : Isa) : List isa.Instr → Option (List UInt8)
  | [] => some []
  | i :: is =>
    match isa.encode i, encodeAll isa is with
    | some b, some bs => some (b ++ bs)
    | _, _ => none

/-- The machine code of `f` placed at `base`. -/
def Fn.bytes (f : Fn A) (σ : String → Option UInt64) (base : UInt64) : Option (List UInt8) :=
  (f.resolve σ base).bind (encodeAll A.isa)

/-- The program is loaded in memory `m` under symbol assignment `σ` when every function's code
sits, executable, at its symbol, and every data item sits, readable and not writable, at its
symbol. -/
def Prog.Loaded (P : Prog A) (σ : String → Option UInt64) (m : Memory) : Prop :=
  (∀ f ∈ P.funs, ∃ a bs, σ f.name = some a ∧ f.bytes σ a = some bs ∧ m.CodeAt a bs) ∧
  (∀ d ∈ P.data, ∃ a, σ d.1 = some a ∧ m.read a d.2.length = some d.2 ∧
    ∀ i, i < d.2.length → m.writable (a + UInt64.ofNat i) = false)

/-- The writable regions of `P` are in place in memory `m` under `σ` when each sits at its symbol,
readable and writable, holding zeros. A loader establishes this at the start, and the program then
writes the regions. -/
def Prog.BssAt (P : Prog A) (σ : String → Option UInt64) (m : Memory) : Prop :=
  ∀ b ∈ P.bss, ∃ a, σ b.1 = some a ∧ ∀ i, i < b.2 →
    m.readable (a + UInt64.ofNat i) = true ∧ m.writable (a + UInt64.ofNat i) = true ∧
      m.bytes (a + UInt64.ofNat i) = 0

/-- The machine of an ISA with an ABI's system calls as a `Sem`, whose state is the machine state
and the number of instructions executed. A halted machine stutters. It is definitionally
`Target.sem`. -/
def msem (isa : Isa) (abi : Abi isa) : Sem where
  State := MState isa.Regs × Nat
  step ω s :=
    if s.1.world.halted then some s
    else (isa.step (abi.trap ω) s.1).map (fun s' => (s', s.2 + 1))
  events s := s.1.world.events
  clock s := s.2

end Millipede.Asm
