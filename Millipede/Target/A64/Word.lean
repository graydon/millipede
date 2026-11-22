import Millipede.Compile.AssembleWord
import Millipede.Target.A64.Isa
import Std.Tactic.BVDecide

/-!
# arm64 as a word ISA

The fixed-width assembler works over any instruction set whose instructions are single words.
This module makes arm64 such an instruction set, `W`, in which `word i` is the word of an
encodable instruction, `ofWord` decodes one word, and `fixable k i` says which instructions carry
the fixup `k`. A fixable instruction has its field zero in the template, as `select` emits it.
The fixups and the instructions that carry them are the following:

| fixup | instructions |
|---|---|
| `branch26` | `b`, `bl` |
| `cond19` | `cbz`, `cbnz` |
| `adr21` | `adr` |
| `page21` | `adrp` |
| `lo12 0` | the 64-bit, unshifted `add xd, xn, #imm` |

Selection uses neither `b.cond` nor the scaled `lo12` forms of loads and stores, so they are not
fixable. The word assembler refuses a `page21` or `lo12` fixup to a local label, and selection
uses those fixups only for symbols. From `W_laws`, the proof that `W` is lawful, come the
symbolic layer `arch` and the assembler `asm` with its laws.

A resolved fixup is the instruction with its field set so that it reaches its target `t`. A
branch satisfies `pc + (sext imm <<< 2) = t` and an `adr` satisfies `pc + sext imm = t`. An `adrp`
computes the page of `t`, within 4 GiB of the page of `pc`, and the `add :lo12:` adds the offset of
`t` in its page, so the two together compute `t`.
-/

namespace Millipede.A64

/-! ## The word interface -/

/-- Which instructions carry which fixup, with the field zero in the template. -/
def fixable : Fixup → Instr → Bool
  | .branch26, .b _ imm => imm == 0
  | .cond19, .cbz _ _ _ imm => imm == 0
  | .adr21, .adr false _ imm => imm == 0
  | .page21, .adr true _ imm => imm == 0
  | .lo12 0, .addImm true false false _ _ imm false => imm == 0
  | _, _ => false

/-- arm64 for the fixed-width assembler. -/
def W : Asm.WordIsa where
  isa := isa
  word i := if i.valid then some (encode i).toNat else none
  ofWord w := if w < 2 ^ 32 then decodeWord (BitVec.ofNat 32 w) else none
  fixable := fixable

theorem ofWord_encode {i : Instr} (h : i.valid = true) : W.ofWord (encode i).toNat = some i := by
  simp only [W, (encode i).isLt, ite_true, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact decodeWord_encode h

/-! ## Field insertion (encoding lemmas) -/

/-- Inserting into a zero field adds the value. -/
theorem setBits_zero {w lo n : Nat} (h : w / 2 ^ lo % 2 ^ n = 0) (v : Nat) :
    setBits w lo n v = w + v % 2 ^ n * 2 ^ lo := by
  simp [setBits, h]

theorem enc_b (link : Bool) (imm : BitVec 26) :
    (encode (.b link imm)).toNat = (encode (.b link 0)).toNat + imm.toNat := by
  have : encode (.b link imm) = encode (.b link 0) + imm.setWidth 32 := by
    cases link <;> simp [encode, fld, bit] <;> bv_decide
  rw [this, BitVec.toNat_add]
  cases link <;> simp [encode, fld, bit] <;> omega

theorem enc_b0 (link : Bool) : (encode (.b link 0)).toNat / 2 ^ 0 % 2 ^ 26 = 0 := by
  cases link <;> decide

theorem enc_cbz (sf nz : Bool) (t : Reg) (imm : BitVec 19) :
    (encode (.cbz sf nz t imm)).toNat = (encode (.cbz sf nz t 0)).toNat + imm.toNat * 2 ^ 5 := by
  have : encode (.cbz sf nz t imm) = encode (.cbz sf nz t 0) + (imm.setWidth 32 <<< 5) := by
    cases sf <;> cases nz <;> simp [encode, fld, bit] <;> bv_decide
  have hz : encode (.cbz sf nz t 0) &&& (imm.setWidth 32 <<< 5) = 0#32 := by
    cases sf <;> cases nz <;> simp [encode, fld, bit] <;> bv_decide
  rw [this, BitVec.toNat_add_of_and_eq_zero hz, BitVec.toNat_shiftLeft]
  have := imm.isLt
  simp [Nat.shiftLeft_eq]; omega

theorem enc_cbz0 (sf nz : Bool) (t : Reg) : (encode (.cbz sf nz t 0)).toNat / 2 ^ 5 % 2 ^ 19 = 0 := by
  have h : (encode (.cbz sf nz t 0) >>> 5) &&& 0x7FFFF#32 = 0 := by
    cases sf <;> cases nz <;> simp [encode, fld, bit] <;> bv_decide
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight] at this
  have e : (0x7FFFF#32).toNat = 2 ^ 19 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow] at this
  simpa using this

theorem enc_adr (page : Bool) (d : Reg) (imm : BitVec 21) :
    (encode (.adr page d imm)).toNat = (encode (.adr page d 0)).toNat +
      imm.toNat % 4 * 2 ^ 29 + imm.toNat / 4 * 2 ^ 5 := by
  have : encode (.adr page d imm) = encode (.adr page d 0) +
      ((imm.extractLsb' 0 2).setWidth 32 <<< 29) + ((imm.extractLsb' 2 19).setWidth 32 <<< 5) := by
    cases page <;> simp [encode, fld, bit] <;> bv_decide
  have hz1 : encode (.adr page d 0) &&& ((imm.extractLsb' 0 2).setWidth 32 <<< 29) = 0#32 := by
    cases page <;> simp [encode, fld, bit] <;> bv_decide
  have hz2 : (encode (.adr page d 0) + ((imm.extractLsb' 0 2).setWidth 32 <<< 29)) &&&
      ((imm.extractLsb' 2 19).setWidth 32 <<< 5) = 0#32 := by
    cases page <;> simp [encode, fld, bit] <;> bv_decide
  rw [this, BitVec.toNat_add_of_and_eq_zero hz2, BitVec.toNat_add_of_and_eq_zero hz1,
    BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft]
  have := imm.isLt
  simp [Nat.shiftLeft_eq, BitVec.extractLsb'_toNat]
  omega

theorem enc_adr0 (page : Bool) (d : Reg) : (encode (.adr page d 0)).toNat / 2 ^ 29 % 2 ^ 2 = 0 ∧
    (encode (.adr page d 0)).toNat / 2 ^ 5 % 2 ^ 19 = 0 := by
  have h1 : (encode (.adr page d 0) >>> 29) &&& 3#32 = 0 := by
    cases page <;> simp [encode, fld, bit] <;> bv_decide
  have h2 : (encode (.adr page d 0) >>> 5) &&& 0x7FFFF#32 = 0 := by
    cases page <;> simp [encode, fld, bit] <;> bv_decide
  have e1 := congrArg BitVec.toNat h1
  have e2 := congrArg BitVec.toNat h2
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight] at e1 e2
  have c1 : (3#32).toNat = 2 ^ 2 - 1 := rfl
  have c2 : (0x7FFFF#32).toNat = 2 ^ 19 - 1 := rfl
  rw [c1, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow] at e1
  rw [c2, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow] at e2
  exact ⟨by simpa using e1, by simpa using e2⟩

theorem enc_addImm (d n : Reg) (imm : BitVec 12) :
    (encode (.addImm true false false d n imm false)).toNat =
      (encode (.addImm true false false d n 0 false)).toNat + imm.toNat * 2 ^ 10 := by
  have : encode (.addImm true false false d n imm false) =
      encode (.addImm true false false d n 0 false) + (imm.setWidth 32 <<< 10) := by
    simp [encode, fld, bit]; bv_decide
  have hz : encode (.addImm true false false d n 0 false) &&& (imm.setWidth 32 <<< 10) = 0#32 := by
    simp [encode, fld, bit]; bv_decide
  rw [this, BitVec.toNat_add_of_and_eq_zero hz, BitVec.toNat_shiftLeft]
  have := imm.isLt
  simp [Nat.shiftLeft_eq]; omega

theorem enc_addImm0 (d n : Reg) :
    (encode (.addImm true false false d n 0 false)).toNat / 2 ^ 10 % 2 ^ 12 = 0 := by
  have h : (encode (.addImm true false false d n 0 false) >>> 10) &&& 0xFFF#32 = 0 := by
    simp [encode, fld, bit]; bv_decide
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight] at this
  have e : (0xFFF#32).toNat = 2 ^ 12 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow] at this
  simpa using this

/-- Inserting `v` into the field of `b` or `bl` gives the branch with that field. -/
theorem insert_b (link : Bool) (v : Nat) :
    Fixup.insert .branch26 (encode (.b link 0)).toNat v =
      (encode (.b link (BitVec.ofNat 26 v))).toNat := by
  rw [Fixup.insert, setBits_zero (enc_b0 link), enc_b link (BitVec.ofNat 26 v)]; simp

theorem insert_cbz (sf nz : Bool) (t : Reg) (v : Nat) :
    Fixup.insert .cond19 (encode (.cbz sf nz t 0)).toNat v =
      (encode (.cbz sf nz t (BitVec.ofNat 19 v))).toNat := by
  rw [Fixup.insert, setBits_zero (enc_cbz0 sf nz t), enc_cbz sf nz t (BitVec.ofNat 19 v)]; simp

/-- Inserting `v` into the split field of `adr` or `adrp` gives the instruction with that field,
and `adr21` and `page21` insert alike. -/
theorem insert_adr21 (page : Bool) (d : Reg) (v : Nat) :
    setBits (setBits (encode (.adr page d 0)).toNat 29 2 v) 5 19 (v / 4) =
      (encode (.adr page d (BitVec.ofNat 21 v))).toNat := by
  obtain ⟨h1, h2⟩ := enc_adr0 page d
  rw [setBits_zero h1]
  have h3 : ((encode (.adr page d 0)).toNat + v % 2 ^ 2 * 2 ^ 29) / 2 ^ 5 % 2 ^ 19 = 0 := by
    have e : (encode (.adr page d 0)).toNat + v % 2 ^ 2 * 2 ^ 29 =
        (encode (.adr page d 0)).toNat + (v % 2 ^ 2 * 2 ^ 24 / 2 ^ 19) * 2 ^ 19 * 2 ^ 5 := by
      have : v % 2 ^ 2 * 2 ^ 24 / 2 ^ 19 = v % 2 ^ 2 * 2 ^ 5 := by omega
      rw [this]; omega
    rw [e, Nat.add_mul_div_right _ _ (by decide), Nat.add_mul_mod_self_right]; exact h2
  rw [setBits_zero h3, enc_adr page d (BitVec.ofNat 21 v)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem insert_adr (d : Reg) (v : Nat) :
    Fixup.insert .adr21 (encode (.adr false d 0)).toNat v =
      (encode (.adr false d (BitVec.ofNat 21 v))).toNat := insert_adr21 false d v

theorem insert_adrp (d : Reg) (v : Nat) :
    Fixup.insert .page21 (encode (.adr true d 0)).toNat v =
      (encode (.adr true d (BitVec.ofNat 21 v))).toNat := insert_adr21 true d v

theorem insert_lo12 (d n : Reg) (v : Nat) :
    Fixup.insert (.lo12 0) (encode (.addImm true false false d n 0 false)).toNat v =
      (encode (.addImm true false false d n (BitVec.ofNat 12 v) false)).toNat := by
  rw [Fixup.insert, setBits_zero (enc_addImm0 d n), enc_addImm d n (BitVec.ofNat 12 v)]; simp

theorem fixable_valid {k : Fixup} {i : Instr} (h : fixable k i = true) : i.valid = true := by
  cases i <;> first | rfl | (cases k <;> simp [fixable] at h)

theorem fix_insert {k : Fixup} {i : Instr} (h : fixable k i = true) (v : Nat) :
    ∃ i', i'.valid = true ∧ k.insert (encode i).toNat v = (encode i').toNat := by
  unfold fixable at h
  split at h
  · rename_i link imm; simp only [beq_iff_eq] at h; subst h
    exact ⟨_, rfl, insert_b link v⟩
  · rename_i sf nz t imm; simp only [beq_iff_eq] at h; subst h
    exact ⟨_, rfl, insert_cbz sf nz t v⟩
  · rename_i d imm; simp only [beq_iff_eq] at h; subst h
    exact ⟨_, rfl, insert_adr d v⟩
  · rename_i d imm; simp only [beq_iff_eq] at h; subst h
    exact ⟨_, rfl, insert_adrp d v⟩
  · rename_i d n imm; simp only [beq_iff_eq] at h; subst h
    exact ⟨_, rfl, insert_lo12 d n v⟩
  · cases h

/-- arm64 meets the word-assembler interface. -/
theorem W_laws : W.Laws where
  isa := laws
  encode_word i := by
    show isa.encode i = (if i.valid then some (encode i).toNat else none).map (natBytes 4)
    simp only [isa]; split <;> rfl
  word_lt i w h := by
    simp only [W] at h; split at h <;> cases h; exact (encode i).isLt
  word_ofWord w i h := by
    simp only [W] at h ⊢
    by_cases hw : w < 2 ^ 32
    · simp only [hw] at h
      obtain ⟨j, -, hc⟩ := Option.bind_eq_some_iff.mp h
      by_cases hv : (j.valid && encode j == BitVec.ofNat 32 w) = true
      · simp only [hv, ite_true] at hc
        cases hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hv
        simp [hv.1, hv.2, Nat.mod_eq_of_lt hw]
      · simp [hv] at hc
    · simp [hw] at h
  ofWord_fix k i w v hf hw := by
    have hv := fixable_valid (show fixable k i = true from hf)
    simp only [W, hv, ite_true, Option.some.injEq] at hw
    subst hw
    obtain ⟨i', hv', he⟩ := fix_insert (show fixable k i = true from hf) v
    rw [he, ofWord_encode hv']; rfl

/-- The arm64 symbolic layer, in which every instruction is 4 bytes and is either a plain
instruction or a template with a fixup to a reference. -/
abbrev arch : Asm.Arch := Asm.wordArch W

/-- The arm64 assembler. -/
abbrev asm : Asm.Assembler arch := Asm.wordAsm W

theorem asm_laws : asm.Laws := Asm.wordAsm_laws W_laws

/-! ## Reach -/

theorem sext_toNat {n : Nat} (hn : n ≤ 64) (x : BitVec n) :
    (sext x).toNat = x.toNat + if 2 * x.toNat ≥ 2 ^ n then 2 ^ 64 - 2 ^ n else 0 := by
  simp only [sext, UInt64.toNat_ofBitVec, BitVec.toNat_signExtend]
  have hm : x.msb = decide (2 * x.toNat ≥ 2 ^ n) := by
    rw [BitVec.msb_eq_decide]
    cases n with
    | zero => simp [BitVec.toNat_of_zero_length]
    | succ n =>
      simp only [Nat.add_sub_cancel, Nat.pow_succ]; rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, ge_iff_le]; omega
  rw [hm, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt
    (Nat.pow_le_pow_right (by omega) hn))]
  by_cases h : 2 * x.toNat ≥ 2 ^ n <;> simp [h]

/-- A branch field of `n` bits that holds `d / 4` reaches `P + d`. -/
theorem words_reach {n : Nat} (hn : n ≤ 60) {d : Int} {v : Nat}
    (h : wordsField n d = some v) {T P : UInt64} (hd : d = (T.toNat : Int) - P.toNat) :
    P + (sext (BitVec.ofNat n v) <<< 2) = T := by
  simp only [wordsField] at h
  split at h
  · rename_i hr
    cases h
    obtain ⟨h4, hlo, hhi⟩ := hr
    have hT := T.toNat_lt; have hP := P.toNat_lt
    have hpow : (2 : Int) ^ (n + 1) = 2 * 2 ^ n := by rw [Int.pow_succ]; omega
    have hpn : (2 : Nat) ^ n ≤ 2 ^ 60 := Nat.pow_le_pow_right (by omega) hn
    have hpn' : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by simp
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, sext_toNat (by omega)]
    simp only [BitVec.toNat_ofNat]
    have e2 : (2 : UInt64).toNat % 64 = 2 := rfl
    rw [e2]
    generalize hq : ((d / 4) % 2 ^ n).toNat = q
    have hq1 : (q : Int) = (d / 4) % 2 ^ n := by
      rw [← hq, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    have hq2 : (q : Int) < 2 ^ n := by rw [hq1]; exact Int.emod_lt_of_pos _ (by omega)
    have hql : q < 2 ^ n := by omega
    rw [Nat.mod_eq_of_lt hql, Nat.shiftLeft_eq]
    have hdq : d / 4 = q ∨ d / 4 = q - 2 ^ n := by
      rcases Int.lt_or_le (d / 4) 0 with hneg | hpos
      · right
        rw [hq1, ← Int.add_emod_right _ (2 ^ n), Int.emod_eq_of_lt (by omega) (by omega)]; omega
      · left; rw [hq1, Int.emod_eq_of_lt hpos (by omega)]
    rcases hdq with e | e
    · have hs : ¬ (2 * q ≥ 2 ^ n) := by omega
      simp only [hs, ite_false, Nat.add_zero]
      omega
    · have hs : 2 * q ≥ 2 ^ n := by omega
      simp only [hs, ite_true]
      omega
  · cases h

/-- The 21-bit field of an `adr` that holds `d` reaches `P + d`. -/
theorem field21_reach {d : Int} {v : Nat} (h : field21 d = some v) {T P : UInt64}
    (hd : d = (T.toNat : Int) - P.toNat) : P + sext (BitVec.ofNat 21 v) = T := by
  simp only [field21] at h
  split at h
  · rename_i hr
    cases h
    obtain ⟨hlo, hhi⟩ := hr
    have hT := T.toNat_lt; have hP := P.toNat_lt
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, sext_toNat (by omega)]
    simp only [BitVec.toNat_ofNat]
    generalize hq : (d % 2 ^ 21).toNat = q
    have hq1 : (q : Int) = d % 2 ^ 21 := by
      rw [← hq, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    have hq2 : (q : Int) < 2 ^ 21 := by rw [hq1]; exact Int.emod_lt_of_pos _ (by omega)
    have hql : q < 2 ^ 21 := by omega
    rw [Nat.mod_eq_of_lt hql]
    have hdq : d = q ∨ d = q - 2 ^ 21 := by
      rcases Int.lt_or_le d 0 with hneg | hpos
      · right
        rw [hq1, ← Int.add_emod_right _ (2 ^ 21), Int.emod_eq_of_lt (by omega) (by omega)]; omega
      · left; rw [hq1, Int.emod_eq_of_lt hpos (by omega)]
    rcases hdq with e | e
    · have hs : ¬ (2 * q ≥ 2 ^ 21) := by omega
      simp only [hs, ite_false, Nat.add_zero]
      omega
    · have hs : 2 * q ≥ 2 ^ 21 := by omega
      simp only [hs, ite_true]
      omega
  · cases h

/-! ## What a fixup resolves to -/

theorem resolve_fix {k : Fixup} {i i' : Instr} {ρ : Asm.Ref → Option UInt64} {a : UInt64}
    {r : Asm.Ref} (h : Asm.WSI.resolve W ρ a (.fix k i r) = some i') :
    ∃ t v, ρ r = some t ∧ k.value t a = some v ∧ fixable k i = true ∧
      W.ofWord (k.insert (encode i).toNat v) = some i' := by
  simp only [Asm.WSI.resolve] at h
  split at h
  · rename_i hf
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w', hw', h⟩ := Option.bind_eq_some_iff.mp h
    have hv := fixable_valid (show fixable k i = true from hf)
    simp only [W, hv, ite_true, Option.some.injEq] at hw
    subst hw
    simp only [Fixup.apply, Option.map_eq_some_iff] at hw'
    obtain ⟨v, hv', rfl⟩ := hw'
    exact ⟨t, v, ht, hv', hf, h⟩
  · cases h

/-- A resolved `b`/`bl` to `r` jumps to `r`'s address. -/
theorem resolve_b {link : Bool} {i' : Instr} {ρ : Asm.Ref → Option UInt64} {a : UInt64}
    {r : Asm.Ref} (h : Asm.WSI.resolve W ρ a (.fix .branch26 (.b link 0) r) = some i') :
    ∃ t imm, ρ r = some t ∧ i' = .b link imm ∧ a + (sext imm <<< 2) = t := by
  obtain ⟨t, v, ht, hv, -, hd⟩ := resolve_fix h
  rw [insert_b, ofWord_encode rfl] at hd
  cases hd
  exact ⟨t, _, ht, rfl, words_reach (by omega) hv rfl⟩

/-- A resolved `cbz`/`cbnz` to `r` branches to `r`'s address. -/
theorem resolve_cbz {sf nz : Bool} {x : Reg} {i' : Instr} {ρ : Asm.Ref → Option UInt64}
    {a : UInt64} {r : Asm.Ref} (h : Asm.WSI.resolve W ρ a (.fix .cond19 (.cbz sf nz x 0) r) = some i') :
    ∃ t imm, ρ r = some t ∧ i' = .cbz sf nz x imm ∧ a + (sext imm <<< 2) = t := by
  obtain ⟨t, v, ht, hv, -, hd⟩ := resolve_fix h
  rw [insert_cbz, ofWord_encode rfl] at hd
  cases hd
  exact ⟨t, _, ht, rfl, words_reach (by omega) hv rfl⟩

/-- The page of an address, as `adrp` sees `pc`. -/
theorem page_eq (P : UInt64) : P &&& ~~~(0xFFF : UInt64) = UInt64.ofNat (P.toNat / 4096) <<< 12 := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have t4095 : ∀ j, Nat.testBit 4095 j = decide (j < 12) := fun j => by
    rw [show 4095 = 2 ^ 12 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_not, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_ofNat, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.shiftLeft_eq',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, t4095, show (12#64 % 64).toNat = 12 from rfl]
  by_cases h : i < 12
  · simp [h]
  · simp only [h, hi, decide_true, decide_false, Bool.not_false, Bool.true_and, Bool.and_true,
      BitVec.getLsbD, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by have := P.toNat_lt; omega), show (4096 : Nat) = 2 ^ 12 from rfl,
      Nat.testBit_div_two_pow, show i - 12 + 12 = i by omega]

theorem shl12_eq (x : UInt64) : x <<< 12 = x * 4096 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_mul, Nat.shiftLeft_eq]; rfl

/-- The 21-bit page field of an `adrp` that holds the page difference reaches the page of `T`
from the page of `P`. -/
theorem page21_reach {v : Nat} {T P : UInt64}
    (h : field21 (((T.toNat / 4096 : Nat) : Int) - (P.toNat / 4096 : Nat)) = some v) :
    (P &&& ~~~(0xFFF : UInt64)) + (sext (BitVec.ofNat 21 v) <<< 12) = T &&& ~~~(0xFFF : UInt64) := by
  have hT := T.toNat_lt; have hP := P.toNat_lt
  have r := field21_reach h (T := UInt64.ofNat (T.toNat / 4096)) (P := UInt64.ofNat (P.toNat / 4096))
    (by simp only [UInt64.toNat_ofNat']; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)])
  rw [page_eq, page_eq, ← r, shl12_eq, shl12_eq, shl12_eq, UInt64.add_mul]

/-- `adrp` of `t`'s page, then `add :lo12:` of its offset, is `t`. -/
theorem page_add_lo12 (t : UInt64) :
    (t &&& ~~~(0xFFF : UInt64)) + (BitVec.ofNat 12 (t.toNat % 4096)).toNat.toUInt64 = t := by
  rw [page_eq, shl12_eq]
  apply UInt64.toNat_inj.mp
  have ht := t.toNat_lt
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', BitVec.toNat_ofNat,
    Nat.toUInt64_eq]
  rw [show (4096 : UInt64).toNat = 4096 from rfl, Nat.mod_eq_of_lt (show t.toNat / 4096 < 2 ^ 64 by omega)]
  omega

/-- A resolved `adrp` of `r` computes the page of `r`'s address. -/
theorem resolve_adrp {d : Reg} {i' : Instr} {ρ : Asm.Ref → Option UInt64} {a : UInt64}
    {r : Asm.Ref} (h : Asm.WSI.resolve W ρ a (.fix .page21 (.adr true d 0) r) = some i') :
    ∃ t imm, ρ r = some t ∧ i' = .adr true d imm ∧
      (a &&& ~~~(0xFFF : UInt64)) + (sext imm <<< 12) = t &&& ~~~(0xFFF : UInt64) := by
  obtain ⟨t, v, ht, hv, -, hd⟩ := resolve_fix h
  rw [insert_adrp, ofWord_encode rfl] at hd
  cases hd
  exact ⟨t, _, ht, rfl, page21_reach hv⟩

/-- A resolved `add :lo12:` of `r` adds the offset of `r`'s address in its page. -/
theorem resolve_lo12 {d n : Reg} {i' : Instr} {ρ : Asm.Ref → Option UInt64} {a : UInt64}
    {r : Asm.Ref}
    (h : Asm.WSI.resolve W ρ a (.fix (.lo12 0) (.addImm true false false d n 0 false) r) = some i') :
    ∃ t, ρ r = some t ∧
      i' = .addImm true false false d n (BitVec.ofNat 12 (t.toNat % 4096)) false := by
  obtain ⟨t, v, ht, hv, -, hd⟩ := resolve_fix h
  rw [insert_lo12, ofWord_encode rfl] at hd
  cases hd
  simp only [Fixup.value, Nat.pow_zero, Nat.mod_one, ite_true, Nat.div_one, Option.some.injEq] at hv
  subst hv
  exact ⟨t, ht, rfl⟩

end Millipede.A64
