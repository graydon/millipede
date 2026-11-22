import Millipede.Compile.Asm
import Millipede.Object.Obj

/-!
# The generic assembler

`assemble asm P` encodes every function of `P` into one `.text` section, in order and each at the
offset of its symbol, and every data item into one `.rodata` section. Each symbolic instruction is
assembled by the architecture's `Assembler.asmSI`, which knows the section offset of the
instruction and of every local label of its function. It returns the instruction's bytes and the
relocations for its references to symbols, which are other functions and data items, and leaves
their fields for the linker. It resolves references to local labels itself as distances inside the
section, or refuses them when they are out of reach. Every function and data item gets a symbol at
its offset. The zero-initialised regions, such as the data region `mp_mem`, go into one `.bss`
section, which has a size but no bytes, each at a multiple of 16 with a symbol at its offset.

`assemble` refuses, instead of emitting something else, when `asmSI` refuses an instruction because
a label is missing or out of reach or the encoder cannot encode it, when two symbols share a name,
and when a section reaches `2^31` bytes.

There are two instances. `X64.asm` handles variable-length instructions with rel32 fields, and
`Asm.wordAsm` handles fixed 4-byte instruction words with fixups, the shape of arm64. For every
assembler that satisfies `Assembler.Laws`, once the relocations are applied for any placement of
the sections, the `.text` bytes are exactly the resolved code of every function, so decoding the
section at a label's address yields the instruction.

See doc/design/compiler.md.
-/

namespace Millipede.Asm

/-- The section numbers of the object. -/
def textSec : Nat := 0
def rodataSec : Nat := 1
def bssSec : Nat := 2

/-- The per-architecture part of the assembler. -/
structure Assembler (A : Arch) where
  /-- Assembles one symbolic instruction placed at section offset `off`, with the local labels
  of its function at section offsets `lab l`. It gives the instruction's bytes, in which fields
  that name a symbol are left for the linker, and its relocations. -/
  asmSI : (Nat → Option Nat) → Nat → A.SInstr → Except String (List UInt8 × List Reloc)

variable {A : Arch} (asm : Assembler A)

/-- Assembles a sequence placed at section offset `off`, by structural recursion on the list. -/
def asmSeq (lab : Nat → Option Nat) : Nat → List A.SInstr → Except String (List UInt8 × List Reloc)
  | _, [] => .ok ([], [])
  | off, i :: is => do
    let (bs, rs) ← asm.asmSI lab off i
    let (bs', rs') ← asmSeq lab (off + A.size i) is
    pure (bs ++ bs', rs ++ rs')

/-- The section offsets of the labels of `f` placed at section offset `off`. -/
def fnLabels (f : Fn A) (off : Nat) (l : Nat) : Option Nat :=
  if l ≤ f.blocks.length then some (off + f.labelOff l) else none

/-- Assembles the functions from section offset `off`, giving bytes, relocations and symbols. -/
def asmFns : Nat → List (Fn A) → Except String (List UInt8 × List Reloc × List Symbol)
  | _, [] => .ok ([], [], [])
  | off, f :: fs => do
    let (bs, rs) ← asmSeq asm (fnLabels f off) off f.code
    let (bs', rs', ss') ← asmFns (off + bs.length) fs
    pure (bs ++ bs', rs ++ rs', ⟨f.name, textSec, off, true⟩ :: ss')

/-- Lays out the data items from section offset `off`, giving bytes and symbols. -/
def asmData : Nat → List (String × List UInt8) → List UInt8 × List Symbol
  | _, [] => ([], [])
  | off, d :: ds =>
    let r := asmData (off + d.2.length) ds
    (d.2 ++ r.1, ⟨d.1, rodataSec, off, false⟩ :: r.2)

/-- Lays out the zero-initialised regions from section offset `off`, each at a multiple of 16,
giving the section's size and the symbols. -/
def asmBss : Nat → List (String × Nat) → Nat × List Symbol
  | off, [] => (off, [])
  | off, b :: bs =>
    let o := (off + 15) / 16 * 16
    let r := asmBss (o + b.2) bs
    (r.1, ⟨b.1, bssSec, o, false⟩ :: r.2)

/-- The assembler. -/
def assemble (P : Prog A) : Except String Obj := do
  let (text, relocs, fsyms) ← asmFns asm 0 P.funs
  let (rodata, dsyms) := asmData 0 P.data
  let (bssSize, bsyms) := asmBss 0 P.bss
  let syms := fsyms ++ dsyms ++ bsyms
  if text.length < 2 ^ 31 ∧ rodata.length < 2 ^ 31 then
    if (syms.map (·.name)).Nodup then
      pure ⟨[⟨".text", .text, 16, text, 0⟩, ⟨".rodata", .rodata, 8, rodata, 0⟩,
        ⟨".bss", .bss, 16, [], bssSize⟩], syms, relocs⟩
    else .error "assemble: duplicate symbol"
  else .error "assemble: section too large"

end Millipede.Asm
