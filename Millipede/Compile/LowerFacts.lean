import Millipede.Compile.Lower

/-!
# Facts about the lowering's definitions

This module holds equations and small facts about the data of `lower` that need nothing of the
memory refinement. They concern locations, tail modes, slot-resident types, parameter locations,
chunks of words, slot fields and fill loops. Both the refinement proofs and the stack and frame bounds import
them.
-/

namespace Millipede.Flat

/-! ## Locations and tail modes -/

/-- The slot-resident variables of a context have consecutive frame slots from `FR` in binding
order, so the next one starts at `FR + slotsIn ρ`. -/
def SlotsOk : List Loc → Prop
  | [] => True
  | l :: ρ => (∀ k, l.slot? = some k → k = FR + slotsIn ρ) ∧ SlotsOk ρ

@[simp] theorem Loc.slot?_own (o : Nat) : (Loc.own o).slot? = none := rfl
@[simp] theorem Loc.slot?_ref (o : Nat) : (Loc.ref o).slot? = none := rfl
@[simp] theorem Loc.slot?_ref2 (o : Nat) : (Loc.ref2 o).slot? = none := rfl
@[simp] theorem Loc.slot?_slot (o k n : Nat) : (Loc.slot o k n).slot? = some k := rfl
@[simp] theorem Loc.slot?_default : (default : Loc).slot? = none := rfl
@[simp] theorem Loc.isSlot_own (o : Nat) : (Loc.own o).isSlot = false := rfl
@[simp] theorem Loc.isSlot_ref (o : Nat) : (Loc.ref o).isSlot = false := rfl
@[simp] theorem Loc.isSlot_ref2 (o : Nat) : (Loc.ref2 o).isSlot = false := rfl
@[simp] theorem Loc.isSlot_slot (o k n : Nat) : (Loc.slot o k n).isSlot = true := rfl
@[simp] theorem Loc.nw_own (o : Nat) : (Loc.own o).nw = 0 := rfl
@[simp] theorem Loc.nw_ref (o : Nat) : (Loc.ref o).nw = 0 := rfl
@[simp] theorem Loc.nw_ref2 (o : Nat) : (Loc.ref2 o).nw = 0 := rfl
@[simp] theorem Loc.nw_slot (o k n : Nat) : (Loc.slot o k n).nw = n := rfl
@[simp] theorem Loc.holds_own (o x : Nat) : (Loc.own o).holds x = false := rfl
@[simp] theorem Loc.holds_ref (o x : Nat) : (Loc.ref o).holds x = false := rfl
@[simp] theorem Loc.holds_ref2 (o x : Nat) : (Loc.ref2 o).holds x = false := rfl
@[simp] theorem Loc.holds_default (x : Nat) : (default : Loc).holds x = false := rfl
@[simp] theorem Loc.holds_slot (o k n x : Nat) :
    (Loc.slot o k n).holds x = (decide (k ≤ x) && decide (x < k + n)) := rfl

theorem Loc.holds_iff {l : Loc} {x : Nat} :
    l.holds x = true ↔ ∃ k, l.slot? = some k ∧ k ≤ x ∧ x < k + l.nw := by
  cases l <;> simp

theorem Loc.holds_false {l : Loc} {k y : Nat} (h : l.slot? = some k) (hn : l.holds y = false) :
    y < k ∨ k + l.nw ≤ y := by
  cases l with
  | slot o k' n =>
    simp only [Loc.slot?_slot, Option.some.injEq] at h; subst h
    simp only [Loc.holds_slot, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hn
    simp only [Loc.nw_slot]; omega
  | _ => simp at h

/-- A slot-resident variable's slot is not the base pointer's. -/
theorem slot_ne_BP (j : Nat) : FR + j ≠ BP := by simp only [FR, BP]; omega

@[simp] theorem Frame.set_slot_BP (f : Frame) (j : Nat) (v : UInt64) :
    (f.set (FR + j) v) BP = f BP := Frame.set_ne _ _ (Ne.symm (slot_ne_BP j))

theorem Loc.isSlot_iff {l : Loc} : l.isSlot = true ↔ ∃ k, l.slot? = some k := by
  cases l <;> simp

theorem Loc.holds_of_isSlot {l : Loc} (h : l.isSlot = false) (x : Nat) : l.holds x = false := by
  cases l <;> simp_all

@[simp] theorem slotsIn_cons (l : Loc) (ρ : List Loc) :
    slotsIn (l :: ρ) = l.nw + slotsIn ρ := rfl

@[simp] theorem Tl.vars_up (tm : Tl) : tm.up.vars = tm.vars.map (· + 1) := by
  cases tm <;> simp [Tl.up, Tl.vars, Function.comp_def]

theorem Tl.zero_not_mem_up (tm : Tl) : 0 ∉ tm.up.vars := by simp

theorem Tl.succ_mem_up {tm : Tl} {i : Nat} : i + 1 ∈ tm.up.vars ↔ i ∈ tm.vars := by simp

theorem slotsIn_paramLocs (wp : Nat → Bool) :
    ∀ (ps : List Ty) (o j : Nat), slotsIn (paramLocs wp ps o j) = (paramWords wp ps j).length
  | [], _, _ => rfl
  | _ :: ts, o, j => by
    simp only [Flat.paramLocs, paramWords, slotsIn_cons, List.length_append,
      slotsIn_paramLocs wp ts]
    split <;> simp_all <;> omega

/-- A one-word scalar is 8 bytes, accessed as `w64`, or 1 byte, accessed as `w8`. -/
theorem Ty.wordTy_size {t : Ty} (h : t.wordTy = true) :
    (t.size = 8 ∧ scalarWidth t.size = .w64) ∨ (t.size = 1 ∧ scalarWidth t.size = .w8) := by
  unfold Ty.wordTy at h
  unfold Ty.size
  split at h
  · rename_i hs; rw [hs]; left; exact ⟨rfl, rfl⟩
  · rename_i hs; rw [hs]; right; exact ⟨rfl, rfl⟩
  · cases h

theorem Ty.wordTy_bytes {t : Ty} (h : t.wordTy = true) : (scalarWidth t.size).bytes = t.size := by
  rcases Ty.wordTy_size h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2, h1] <;> rfl

theorem Ty.wordTy_slotN {t : Ty} (h : t.wordTy = true) : t.slotN = 1 := by
  rcases Ty.wordTy_size h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [Ty.slotN, h1]

/-- A slot-resident type is one byte, a single `w8` chunk, or `slotN` whole words in `w64`
chunks. -/
theorem Ty.slotTy_cases {t : Ty} (h : t.slotTy = true) :
    (t.size = 1 ∧ t.slotN = 1 ∧ scalarWidth t.size = .w8) ∨
      (t.size = 8 * t.slotN ∧ 1 ≤ t.slotN ∧ scalarWidth t.size = .w64) := by
  unfold Ty.slotTy at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨_, h1⟩, _⟩ := h
  unfold Ty.slotN scalarWidth
  rcases h1 with h1 | ⟨⟨h2, h3⟩, _⟩
  · left; exact ⟨h1, by omega, by simp [h1]⟩
  · right; exact ⟨by omega, by omega, by simp only [show ¬ t.size = 1 by omega, ↓reduceIte]⟩

theorem Ty.slotN_pos {t : Ty} (h : t.slotTy = true) : 1 ≤ t.slotN := by
  rcases Ty.slotTy_cases h with ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;> omega

theorem Ty.wordTy_slotTy {t : Ty} (h : t.wordTy = true) : t.slotTy = true := by
  unfold Ty.wordTy at h
  unfold Ty.slotTy Ty.slotN Ty.size
  split at h
  · rename_i hs; rw [hs]; decide
  · rename_i hs; rw [hs]; decide
  · cases h

theorem chunks_length : ∀ (B : List UInt8) (n : Nat), (chunks B n).length = n
  | _, 0 => rfl
  | B, n + 1 => by simp [chunks, chunks_length (B.drop 8) n]

/-- A place with a slot field is a whole-word field of a slot-resident variable. -/
theorem _root_.Millipede.Place.slotField_some {Γ : List Ty} {t : Ty} {p : Place Γ t}
    {ρ : List Loc} {K nw : Nat} (h : p.slotField ρ = some (K, nw)) :
    ∃ (s : Ty) (m : Mem s Γ) (l : Lens s t) (o k n : Nat), p = .field (.var m) l ∧
      ρ.getD m.idx default = .slot o k n ∧ lensOff l % 8 = 0 ∧ t.size % 8 = 0 ∧ t.slotTy = true ∧
      K = k + lensOff l / 8 ∧ nw = n - lensOff l / 8 := by
  cases p with
  | field q l =>
    cases q with
    | var m =>
      simp only [Place.slotField] at h
      split at h
      · rename_i o k n hρ
        split at h
        · rename_i hw
          simp only [Place.wordField, Bool.and_eq_true, beq_iff_eq] at hw
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨_, m, l, o, k, n, rfl, hρ, hw.1.1.2, hw.1.2, hw.2, h.1.symm, h.2.symm⟩
        · cases h
      · cases h
    | _ => simp [Place.slotField] at h
  | _ => simp [Place.slotField] at h

@[simp] theorem _root_.Millipede.Place.refLoc_slot? {Γ : List Ty} {t : Ty} (p : Place Γ t) (o : Nat) :
    (p.refLoc o).slot? = none := by
  cases p <;> rfl

/-- A callee's parameters are in memory, so none is slot-resident. -/
theorem _root_.Millipede.RArgs.locs_slot? {Γ : List Ty} :
    ∀ {ps os : List Ty} (as : RArgs Γ ps os) (o i : Nat), ((as.locs o).getD i default).slot? = none
  | _, _, .nil, _, _ => rfl
  | _, _, .own _ as, o, i | _, _, .shr _ as, o, i | _, _, .mut _ as, o, i => by
    cases i with
    | zero => simp [RArgs.locs]
    | succ i => simp only [RArgs.locs, List.getD_cons_succ]; exact RArgs.locs_slot? as _ i

/-- The word parameters' slots are numbered as `SlotsOk` requires. -/
theorem SlotsOk.paramLocs (wp : Nat → Bool) :
    ∀ (ps : List Ty) (o j : Nat), SlotsOk (paramLocs wp ps o j)
  | [], _, _ => trivial
  | _ :: ts, o, j => by
    simp only [Flat.paramLocs]
    exact ⟨fun k hk => by split at hk <;> simp at hk; exact hk.symm, SlotsOk.paramLocs wp ts _ _⟩

/-- A slot-resident parameter has one slot. -/
theorem paramLocs_nw (wp : Nat → Bool) :
    ∀ (ps : List Ty) (o j i : Nat) {k : Nat}, ((paramLocs wp ps o j).getD i default).slot? = some k →
      ((paramLocs wp ps o j).getD i default).nw = 1
  | [], _, _, i, _, h => by simp [Flat.paramLocs] at h
  | _ :: ts, o, j, 0, _, h => by
    simp only [Flat.paramLocs, List.getD_cons_zero] at h ⊢; split at h
    · rename_i hj; simp [hj]
    · simp at h
  | _ :: ts, o, j, i + 1, _, h => by
    simp only [Flat.paramLocs, List.getD_cons_succ] at h ⊢; exact paramLocs_nw wp ts _ _ i h

theorem Ty.slotN_le {t : Ty} (h : t.slotTy = true) : t.slotN ≤ SLOT_CAP := by
  have := h; unfold Ty.slotTy at this
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  unfold Ty.slotN; simp only [SLOT_CAP] at *; omega

/-- A primitive's result is a one-word scalar. -/
theorem _root_.Millipede.Prim.wordTy {ps : List Ty} {r : Ty} (p : Prim ps r) : r.wordTy = true := by
  cases p <;> rfl

/-- The payload offset of `Result`. -/
abbrev rpo (ε α : Ty) : Nat := payloadOff (Data.shape (Except ε.carrier α.carrier))

/-- What `Ty.slotSum` gives. The `Result` is slot-resident, each payload is empty or whole words,
and a non-empty payload starts at byte 8, the word after the tag's. -/
theorem slotSum_facts {ε α : Ty} (h : Ty.slotSum ε α = true) :
    (Ty.result ε α).slotTy = true ∧ (rpo ε α = 8 ∨ (ε.size = 0 ∧ α.size = 0)) ∧
      (ε.size = 0 ∨ (ε.slotTy = true ∧ ε.size % 8 = 0)) ∧
      (α.size = 0 ∨ (α.slotTy = true ∧ α.size % 8 = 0)) := by
  simp only [Ty.slotSum, Ty.wordPay, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A place that is a slot-resident variable is a variable at that location. -/
theorem _root_.Millipede.Place.slotOf_some {Γ : List Ty} {t : Ty} {p : Place Γ t} {ρ : List Loc}
    {k : Nat} (h : p.slotOf ρ = some k) : ∃ m, p = .var m ∧ (ρ.getD m.idx default).slot? = some k := by
  cases p with
  | var m => exact ⟨m, rfl, h⟩
  | _ => simp [Place.slotOf] at h

/-- A slot-resident variable's slots are among the context's, from `FR` up to
`FR + slotsIn ρ`. -/
theorem SlotsOk.range : ∀ {ρ : List Loc}, SlotsOk ρ → ∀ i k, (ρ.getD i default).slot? = some k →
    FR ≤ k ∧ k + (ρ.getD i default).nw ≤ FR + slotsIn ρ
  | [], _, i, k, hk => by simp at hk
  | l :: _, h, 0, k, hk => by
    have e := h.1 k (by simpa using hk)
    simp only [List.getD_cons_zero, slotsIn_cons]; omega
  | _ :: _, h, i + 1, k, hk => by
    have := SlotsOk.range h.2 i k (by simpa using hk)
    simp only [slotsIn_cons, List.getD_cons_succ]; omega

/-- A term whose tails compute into slots has a slot-resident type. -/
theorem _root_.Millipede.Exp.slotTy_of_word {Γ : List Ty} {t : Ty} (e : Exp Γ t) :
    ∀ {k : Nat}, e.Conf (.word k) = true → t.slotTy = true := by
  induction e <;> intro k h <;> simp only [Exp.Conf, Tl.up, Bool.and_eq_true] at h
  case atom => exact h
  case prim p _ => exact Ty.wordTy_slotTy p.wordTy
  case read => exact h.2
  case ext => rfl
  case call => exact h
  case mk => simp only [Ctor.slotOk, Bool.and_eq_true] at h; exact h.1.1
  case ok => exact (slotSum_facts h).1
  case err => exact (slotSum_facts h).1
  case let_ _ ih => exact ih h
  case ite ih _ => exact ih h.1
  case match_ ih _ => exact ih h.1
  case assign ih => exact ih h
  case case ih _ => exact ih h.1
  case put ih => exact ih h
  case take ih => exact ih h
  case borrowShr _ ih => exact ih h
  case borrowMut _ ih => exact ih h
  case callRef _ ih => exact ih h
  case extMut ih => exact ih h
  case loop _ _ ih => exact ih h
  all_goals cases h

/-! ## Repeated bytes -/

@[simp] theorem reps_zero (B : List UInt8) : reps 0 B = [] := rfl

theorem reps_succ (n : Nat) (B : List UInt8) : reps (n + 1) B = B ++ reps n B := by
  simp [reps, List.replicate_succ]

@[simp] theorem reps_succ' (n : Nat) (B : List UInt8) : reps (n + 1) B = reps n B ++ B := by
  simp [reps, List.replicate_succ']

theorem reps_length (n : Nat) (B : List UInt8) : (reps n B).length = n * B.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [reps_succ, List.length_append, ih, Nat.succ_mul, Nat.add_comm]

theorem reps_add (m n : Nat) (B : List UInt8) : reps (m + n) B = reps m B ++ reps n B := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.add_right_comm, reps_succ, reps_succ, ih, List.append_assoc]

theorem reps_mul (m n : Nat) (B : List UInt8) : reps m (reps n B) = reps (m * n) B := by
  induction m with
  | zero => simp
  | succ m ih => rw [reps_succ, ih, Nat.succ_mul, Nat.add_comm (m * n), reps_add]

/-- The slice at element `j` of repeated elements is the element. -/
theorem slice_reps (B : List UInt8) : ∀ (n j : Nat), j < n →
    slice (reps n B) (j * B.length) B.length = B
  | n + 1, 0, _ => by rw [reps_succ]; simp [slice]
  | n + 1, j + 1, hj => by
    have := slice_reps B n j (by omega)
    rw [reps_succ, show (j + 1) * B.length = B.length + j * B.length by
      rw [Nat.succ_mul, Nat.add_comm]]
    simp only [slice] at this ⊢
    rw [← List.drop_drop, List.drop_left]; exact this

/-! ## What the lowering checked -/

/-- The bytes a fill writes: the loop's `k` words of `q` elements each and a tail of the rest. -/
theorem fill_bytes (B : List UInt8) (n s q : Nat) (hq : q * s = 8)
    (hP : natBytes 8 (decodeLE (reps q B)).toNat = reps q B) :
    reps (n * s / 8) (natBytes 8 (decodeLE (reps q B)).toNat) ++ reps (n - n * s / 8 * q) B =
      reps n B := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero fun h => by simp [h] at hq
  have hk : n * s / 8 * q ≤ n := by
    rw [← hq, Nat.mul_comm q s, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hs0]
    exact Nat.div_mul_le_self n q
  rw [hP, reps_mul, ← reps_add, Nat.add_sub_cancel' hk]

theorem fillCode?_spec {Γ ps : List Ty} {t : Ty} {c : Ctor ps t} {args : Args Γ ps} {d W : Nat}
    {code : Stmt} (h : fillCode? c args d W = some code) :
    ∃ k w P T, code = .seq (.tick (.ctor (W - k * w))) (.seq (fillLoop d k P w)
        (writeB (.slot BP) (d + 8 * k) T)) ∧
      k * w ≤ W ∧ c.plan.2 = none ∧ t.size = 8 * k + T.length ∧ 8 * k < UInt64.size ∧
      ∀ env, ArgsAt c.plan.1 (args.denote env) (reps k (natBytes 8 P.toNat) ++ T) := by
  unfold fillCode? at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i v
  · split at h
    · rename_i os hpl
      dsimp only at h
      split at h
      · rename_i hc
        obtain ⟨hs0, h8, hos, hsz, _, hkw, hsU⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        let B := Data.encodeBytes v
        have hq : 8 / B.length * B.length = 8 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h8)
        have hP : natBytes 8 (decodeLE (reps (8 / B.length) B)).toNat = reps (8 / B.length) B := by
          have hl : (reps (8 / B.length) B).length = 8 := by rw [reps_length, hq]
          have := natBytes_natOfBytes (reps (8 / B.length) B)
          rw [hl] at this; rw [decodeLE_toNat _ (by omega)]; exact this
        have hb := fill_bytes B os.length B.length (8 / B.length) hq hP
        refine ⟨_, _, _, _, rfl, hkw, by rw [hpl], ?_, ?_, fun env => ?_⟩
        · have hl := congrArg List.length hb
          simp only [List.length_append, reps_length, natBytes_length] at hl
          rw [hsz, reps_length, Nat.mul_comm 8]; exact hl.symm
        · have := Nat.div_mul_le_self (os.length * B.length) 8
          omega
        · rw [hpl, hb]
          refine ⟨fun o ho => ?_, trivial⟩
          rw [hos] at ho
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ho
          have e := (Data.encodeBytes_length v).symm
          simp only [Ty.size] at e ⊢
          rw [e, slice_reps B _ j (by simpa using hj)]
          exact Data.reprBytes_encode v
      · simp at h
    · simp at h

end Millipede.Flat
