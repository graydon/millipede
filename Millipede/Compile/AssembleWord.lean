import Millipede.Compile.AssembleLaws

/-!
# The assembler of a fixed-width ISA

An ISA whose instructions are 32-bit little-endian words, such as arm64, describes itself to the
assembler as a `WordIsa`. It gives its `Isa`, the word of an instruction, the instruction of a word,
and which instructions may carry which fixup, as `BL` carries `branch26` and `ADRP` carries
`page21`. Nothing else of the instruction set is needed, because the fields that references fill
are described once, as `Fixup`. `Fixup.value` computes a field's value from the target and the
instruction's address, and `Fixup.insert` puts it into a word. The assembler uses these functions
for local labels and the linker uses them for symbols.

`wordArch W` has two kinds of symbolic instruction. `op i` is a plain instruction, and `fix k i r`
is instruction `i`, with its field zero, whose fixup `k` is filled from reference `r`. At address
`a` with target `t` it resolves to `ofWord (k.insert (word i) v)` where `v = k.value t a`. Every
instruction has size 4.

`wordAsm W` resolves references to local labels with a pc-relative fixup, `branch26`, `cond19` or
`adr21`, at assembly time from the section offsets, because their distance does not depend on
where the section is placed. It refuses `page21` and `lo12` references to a local label, whose
value depends on the absolute address, and distances out of reach. A reference to a symbol becomes
a `RelocKind.word k` relocation at the instruction's offset with addend `0`, and the template word
goes in the section.

`wordAsm_laws` derives the assembler laws from the laws of the instruction set, which its model
must prove:

- `isa`, the ISA laws;
- `encode_word`, that `isa.encode i = (word i).map (natBytes 4)`, so an encoding is the 4
  little-endian bytes of the word;
- `word_lt`, that words are below `2^32`;
- `word_ofWord`, that `ofWord w = some i → word i = some w`, so decoding a word gives an
  instruction that encodes back to it;
- `ofWord_fix`, that if `fixable k i` and `word i = some w`, then `ofWord (k.insert w v)` is some
  instruction for every field value `v`, because the field is an immediate.

See doc/design/targets.md.
-/

namespace Millipede.Asm

/-- What a fixed-width ISA with 32-bit little-endian instruction words provides. -/
structure WordIsa where
  isa : Isa
  /-- The instruction word of `i`, or `none` when `i` cannot be encoded. -/
  word : isa.Instr → Option Nat
  /-- The instruction a word encodes, or `none` outside the modelled subset. -/
  ofWord : Nat → Option isa.Instr
  /-- Instruction `i` may carry fixup `k`, because its field is the fixup's immediate. -/
  fixable : Fixup → isa.Instr → Bool

/-- The laws of a `WordIsa`, which the module documentation describes. -/
structure WordIsa.Laws (W : WordIsa) : Prop where
  isa : W.isa.Laws
  encode_word : ∀ i, W.isa.encode i = (W.word i).map (natBytes 4)
  word_lt : ∀ i w, W.word i = some w → w < 2 ^ 32
  word_ofWord : ∀ w i, W.ofWord w = some i → W.word i = some w
  ofWord_fix : ∀ k i w v, W.fixable k i = true → W.word i = some w →
    (W.ofWord (k.insert w v)).isSome = true

/-- Symbolic instructions of a word ISA. -/
inductive WSI (I : Type) where
  | op (i : I)
  | fix (k : Fixup) (i : I) (r : Ref)

/-- The fixups whose value depends only on the distance from the instruction to the target. -/
def _root_.Millipede.Fixup.pcrel : Fixup → Bool
  | .branch26 | .cond19 | .adr21 => true
  | .page21 | .lo12 _ => false

variable (W : WordIsa)

/-- Resolves a symbolic instruction placed at `a`. -/
def WSI.resolve (ρ : Ref → Option UInt64) (a : UInt64) : WSI W.isa.Instr → Option W.isa.Instr
  | .op i => some i
  | .fix k i r =>
    if W.fixable k i then
      (ρ r).bind fun t => (W.word i).bind fun w => (k.apply t a w).bind W.ofWord
    else none

/-- The symbolic layer of a word ISA, in which every instruction is 4 bytes. -/
def wordArch : Arch where
  isa := W.isa
  SInstr := WSI W.isa.Instr
  size _ := 4
  resolve := WSI.resolve W

/-- Assembles one instruction of a word ISA, as the module documentation describes. -/
def wordSI (lab : Nat → Option Nat) (off : Nat) :
    WSI W.isa.Instr → Except String (List UInt8 × List Reloc)
  | .op i =>
    match W.word i with
    | some w => .ok (natBytes 4 w, [])
    | none => .error "assemble: instruction not encodable"
  | .fix k i r =>
    match W.word i, W.fixable k i with
    | some w, true =>
      match r with
      | .sym s => .ok (natBytes 4 w, [⟨textSec, off, .word k, s, 0⟩])
      | .label l =>
        if k.pcrel then
          match lab l with
          | none => .error "assemble: unknown label"
          | some t =>
            match k.apply (UInt64.ofNat t) (UInt64.ofNat off) w with
            | some w' => .ok (natBytes 4 w', [])
            | none => .error "assemble: branch out of range"
        else .error "assemble: page-relative reference to a local label"
    | _, _ => .error "assemble: instruction cannot carry this fixup"

/-- The assembler of a word ISA. -/
def wordAsm : Assembler (wordArch W) where
  asmSI := wordSI W

/-! ## Laws -/

variable {W}

/-- A pc-relative fixup's value depends only on the distance. -/
theorem Fixup.value_shift {k : Fixup} (hk : k.pcrel = true) {T P T' P' : UInt64}
    (h : (T.toNat : Int) - P.toNat = (T'.toNat : Int) - P'.toNat) :
    k.value T P = k.value T' P' := by
  cases k <;> simp_all [Fixup.pcrel, Fixup.value]

theorem ofInt_toNat (S : UInt64) : UInt64.ofInt (S.toNat : Int) = S := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.ofInt, UInt64.toNat_ofNat']
  have := S.toNat_lt
  omega

theorem natOfBytes_word {w : Nat} (h : w < 2 ^ 32) : natOfBytes (natBytes 4 w) = w := by
  rw [natOfBytes_natBytes]; exact Nat.mod_eq_of_lt (by simpa using h)

/-- The resolved instruction of a fixup and its encoding. -/
theorem fix_resolved (hW : W.Laws) {k : Fixup} {i : W.isa.Instr} {w w' : Nat}
    (hf : W.fixable k i = true) (hw : W.word i = some w) {T P : UInt64}
    (ha : k.apply T P w = some w') :
    ∃ i', W.ofWord w' = some i' ∧ W.isa.encode i' = some (natBytes 4 w') := by
  simp only [Fixup.apply, Option.map_eq_some_iff] at ha
  obtain ⟨v, -, rfl⟩ := ha
  have := hW.ofWord_fix k i w v hf hw
  obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.mp this
  exact ⟨i', hi', by rw [hW.encode_word, hW.word_ofWord _ _ hi']; rfl⟩

theorem wordSI_inv {lab : Nat → Option Nat} {off : Nat} {si : WSI W.isa.Instr}
    {bs : List UInt8} {rs : List Reloc} (h : wordSI W lab off si = .ok (bs, rs)) :
    ∃ w, bs = natBytes 4 w ∧ ∀ r ∈ rs, r.sec = textSec := by
  cases si with
  | op i =>
    simp only [wordSI] at h; split at h <;> cases h; exact ⟨_, rfl, by simp⟩
  | fix k i r =>
    simp only [wordSI] at h
    split at h
    · split at h
      · cases h; exact ⟨_, rfl, by simp⟩
      · split at h
        · split at h
          · cases h
          · split at h <;> cases h; exact ⟨_, rfl, by simp⟩
        · cases h
    · cases h

/-- The assembler of a word ISA satisfies the assembler laws. -/
theorem wordAsm_laws (hW : W.Laws) : (wordAsm W).Laws where
  isa := hW.isa
  size _ _ _ _ _ h := by obtain ⟨w, rfl, -⟩ := wordSI_inv h; simp; rfl
  sec _ _ _ _ _ h := by obtain ⟨_, -, h'⟩ := wordSI_inv h; exact h'
  resolve_size _ _ _ i e _ he := by
    have h2 := hW.encode_word i
    rw [show W.isa.encode i = some e from he] at h2
    obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h2.symm
    simp; rfl
  spec := by
    intro σ base N ρ lab hA off si bs rs h pre post X hpre hN hX
    have hw64 := hA.wrap
    cases si with
    | op i =>
      simp only [wordAsm, wordSI] at h
      split at h
      · rename_i w hw
        cases h
        simp only [applyRelocs, Option.some.injEq] at hX
        exact ⟨i, _, rfl, by change W.isa.encode i = _; rw [hW.encode_word, hw]; rfl, hX.symm⟩
      · cases h
    | fix k i r =>
      cases hw : W.word i with
      | none => simp [wordAsm, wordSI, hw] at h
      | some w =>
      cases hf : W.fixable k i with
      | false => simp [wordAsm, wordSI, hw, hf] at h
      | true =>
        cases r with
        | sym s =>
          simp only [wordAsm, wordSI, hw, hf, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [applyRelocs, ite_true] at hX
          cases hs : σ s with
          | none => rw [hs] at hX; cases hX
          | some S =>
            rw [hs] at hX
            have hold : ((pre ++ natBytes 4 w ++ post).drop off).take (RelocKind.word k).width =
                natBytes 4 w := by
              simp [RelocKind.width, ← hpre, List.take_left' (natBytes_length 4 w)]
            simp only [hold, RelocKind.patch, Int.add_zero, natOfBytes_word (hW.word_lt _ _ hw),
              ofInt_toNat] at hX
            cases ha : k.apply S (base + UInt64.ofNat off) w with
            | none => rw [ha] at hX; cases hX
            | some w' =>
              rw [ha] at hX
              simp only [Option.map_some, Option.some.injEq] at hX
              obtain ⟨i', hi', he'⟩ := fix_resolved hW hf hw ha
              refine ⟨i', _, ?_, he', ?_⟩
              · simp only [wordArch, WSI.resolve, hf, ite_true, hA.sym s, hs, Option.bind_some,
                  hw, ha, hi']
              · rw [← hX, ← hpre, patchBytes_mid _ _ _ _ (by simp)]
        | label l =>
          cases hk : k.pcrel with
          | false => simp [wordAsm, wordSI, hw, hf, hk] at h
          | true =>
          cases ht : lab l with
          | none => simp [wordAsm, wordSI, hw, hf, hk, ht] at h
          | some t =>
          cases ha : k.apply (UInt64.ofNat t) (UInt64.ofNat off) w with
          | none => simp [wordAsm, wordSI, hw, hf, hk, ht, ha] at h
          | some w' =>
            simp only [wordAsm, wordSI, hw, hf, hk, ht, ha, ite_true, Except.ok.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [applyRelocs, Option.some.injEq] at hX
            obtain ⟨hρ, htN⟩ := hA.label l t ht
            have ha' : k.apply (base + UInt64.ofNat t) (base + UInt64.ofNat off) w = some w' := by
              have hsz : UInt64.size = 2 ^ 64 := rfl
              rw [← ha]
              simp only [Fixup.apply]
              rw [Fixup.value_shift hk]
              rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega),
                UInt64.toNat_ofNat_of_lt' (by omega), UInt64.toNat_ofNat_of_lt' (by omega)]
              omega
            obtain ⟨i', hi', he'⟩ := fix_resolved hW hf hw ha'
            refine ⟨i', _, ?_, he', hX.symm⟩
            simp only [wordArch, WSI.resolve, hf, ite_true, hρ, Option.bind_some, hw, ha', hi']

end Millipede.Asm
