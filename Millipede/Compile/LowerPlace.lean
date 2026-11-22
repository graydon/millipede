import Millipede.Compile.LowerCases
import Millipede.Compile.LowerDisj

/-!
# The memory refinement of places

A contiguous place such as `x`, `p.f`, `p[i]!` or `s[i]` is a range of bytes inside the value of
its root variable, at offset `Place.off` from the root's address. The root's address is its own
offset, or the address that its reference slot holds. This module proves that the lowered code
finds, reads and writes that range. Its main theorems are the following:

* `placeAddr_runs`: the address code computes the root's address plus the offset into `RA`;
* `place_get`: under the place's obligation, the range represents `Place.get`, also when the root
  is a lender with a hole, as long as the place does not overlap the lent place;
* `place_set`: writing bytes that represent `v` over the range of a writable root, and nowhere
  else, gives memory that represents the environment `Place.set env v`.

The proofs rest on the lens law of each selector and on the layout of the elements of arrays and
`Slots`. The method is described in doc/design/compiler.md.
-/

namespace Millipede.Flat

/-! ## Roots -/

/-- The value of a place's root variable. -/
def _root_.Millipede.Place.rootVal {Γ : List Ty} : {t : Ty} → (p : Place Γ t) → Env Γ →
    p.rootTy.carrier
  | _, .var m, env => env.get m
  | _, .field p _, env => p.rootVal env
  | _, .index (dflt := _) p _, env => p.rootVal env
  | _, .slot (dflt := _) p _, env => p.rootVal env
  | _, .range p _ _, env => p.rootVal env
  | _, .pair2 (dflt := _) p _ _, env => p.rootVal env
  | _, .rangeS m _ _, env => env.get m
  | _, .pair2S (dflt := _) m _ _, env => env.get m

/-- The facts about a place's root variable. -/
theorem MEnvRel.root {h : Heap} {bp : Nat} {Γ : List Ty} {env : Env Γ} {ρ : List Loc}
    {S : List SI} {t : Ty} (p : Place Γ t) (henv : MEnvRel h bp env ρ S)
    (hns : (ρ.getD p.root default).isSlot = false) :
    VarRel h p.rootTy (p.rootVal env) (S.getD p.root default) ∧
      PtrOk h bp (ρ.getD p.root default) (S.getD p.root default) := by
  induction p with
  | var m => exact henv.get m hns
  | field p _ ih => exact ih hns
  | index p _ ih => exact ih hns
  | slot p _ ih => exact ih hns
  | range p _ _ ih => exact ih hns
  | pair2 p _ _ ih => exact ih hns
  | rangeS m => exact henv.get m hns
  | pair2S m => exact henv.get m hns

theorem Lay.root {bp n : Nat} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool}
    {t : Ty} (p : Place Γ t) (hl : Lay bp n Γ ρ S W) :
    Single bp n p.rootTy (ρ.getD p.root default) (S.getD p.root default) (W.getD p.root false) := by
  induction p with
  | var m => exact hl.var m
  | field p _ ih => exact ih
  | index p _ ih => exact ih
  | slot p _ ih => exact ih
  | range p _ _ ih => exact ih
  | pair2 p _ _ ih => exact ih
  | rangeS m => exact hl.var m
  | pair2S m => exact hl.var m

theorem _root_.Millipede.Place.rootTy_of_isVarAt {Γ : List Ty} {t : Ty} (p : Place Γ t)
    (h : p.isVarAt p.root = true) : p.rootTy = t := by
  cases p <;> first | rfl | simp [Place.isVarAt] at h

/-- A place that is its root variable is a variable. -/
theorem _root_.Millipede.Place.eq_var_of_isVarAt {Γ : List Ty} {t : Ty} (p : Place Γ t)
    (h : p.isVarAt p.root = true) : ∃ m : Mem t Γ, p = .var m := by
  cases p <;> first | exact ⟨_, rfl⟩ | simp [Place.isVarAt] at h

/-- The address of a place's second piece, when the place is a pair reference with one. -/
def _root_.Millipede.Place.snd2 {Γ : List Ty} {t : Ty} (p : Place Γ t) (S : List SI) : Option Nat :=
  match p with
  | .var m => (S.getD m.idx default).snd.map (·.2)
  | _ => none

/-- The address of a contiguous place as `placeAddr` computes it: its root's address plus the
selectors' offsets. A field of a pair reference is at the address of that field's piece, and a
slice or a pair of elements is at its root's address. -/
def placeA {Γ : List Ty} : {t : Ty} → Place Γ t → List SI → Env Γ → Nat
  | _, .var m, S, _ => (S.getD m.idx default).A
  | _, .field p l, S, env =>
    match p.snd2 S with
    | some A2 => if l.index = 0 then (S.getD p.root default).A else A2
    | none => placeA p S env + lensOff l
  | _, .index (t := t) (dflt := _) p i, S, env => placeA p S env + (i.denote env).toNat * t.size
  | _, .slot (t := t) (dflt := _) p i, S, env => placeA p S env + (i.denote env).toNat * t.size
  | _, .range p _ _, S, _ => (S.getD p.root default).A
  | _, .pair2 (dflt := _) p _ _, S, _ => (S.getD p.root default).A
  | _, .rangeS m _ _, S, _ => (S.getD m.idx default).A
  | _, .pair2S (dflt := _) m _ _, S, _ => (S.getD m.idx default).A

/-- A place is not a pair reference as a whole. -/
def _root_.Millipede.Place.NotPair {Γ : List Ty} {t : Ty} (S : List SI) (p : Place Γ t) : Prop :=
  p.isVarAt p.root = true → (S.getD p.root default).snd = none

theorem _root_.Millipede.Place.snd2_none {Γ : List Ty} {t : Ty} {S : List SI} (p : Place Γ t)
    (hs : (S.getD p.root default).snd = none) : p.snd2 S = none := by
  cases p <;> simp_all [Place.snd2, Place.root]

/-- The address of a place whose variable has no second piece: the variable's address plus the
place's offset. -/
theorem placeA_plain {Γ : List Ty} {t : Ty} (p : Place Γ t) {S : List SI} {env : Env Γ}
    (hc : p.contig = true) (hs : (S.getD p.root default).snd = none) :
    placeA p S env = (S.getD p.root default).A + p.off env := by
  induction p with
  | var m => simp [placeA, Place.root, Place.off]
  | field p l ih =>
    simp only [placeA, Place.snd2_none p hs]
    rw [ih hc hs]; simp [Place.root, Place.off, Nat.add_assoc]
  | index p i ih => simp only [placeA]; rw [ih hc hs]; simp [Place.root, Place.off, Nat.add_assoc]
  | slot p i ih => simp only [placeA]; rw [ih hc hs]; simp [Place.root, Place.off, Nat.add_assoc]
  | range => simp [Place.contig] at hc
  | pair2 => simp [Place.contig] at hc
  | rangeS => simp [Place.contig] at hc
  | pair2S => simp [Place.contig] at hc

/-! ## Holes -/

/-- The index atoms of a place read no variable with a hole. -/
def _root_.Millipede.Place.IdxNH {Γ : List Ty} (S : List SI) : {t : Ty} → Place Γ t → Prop
  | _, .var _ => True
  | _, .field p _ => p.IdxNH S
  | _, .index (dflt := _) p i => p.IdxNH S ∧ ∀ m, i = .var m → (S.getD m.idx default).hole = none
  | _, .slot (dflt := _) p i => p.IdxNH S ∧ ∀ m, i = .var m → (S.getD m.idx default).hole = none
  | _, .range p lo len => p.IdxNH S ∧ (∀ m, lo = .var m → (S.getD m.idx default).hole = none) ∧
      ∀ m, len = .var m → (S.getD m.idx default).hole = none
  | _, .pair2 (dflt := _) p i j => p.IdxNH S ∧
      (∀ m, i = .var m → (S.getD m.idx default).hole = none) ∧
      ∀ m, j = .var m → (S.getD m.idx default).hole = none
  | _, .rangeS _ lo len => (∀ m, lo = .var m → (S.getD m.idx default).hole = none) ∧
      ∀ m, len = .var m → (S.getD m.idx default).hole = none
  | _, .pair2S (dflt := _) _ i j => (∀ m, i = .var m → (S.getD m.idx default).hole = none) ∧
      ∀ m, j = .var m → (S.getD m.idx default).hole = none

/-- A place the borrow checker lets a term use: its index atoms read no variable with a hole,
and if its root has a hole, its path does not overlap the lent place's. -/
def _root_.Millipede.Place.NH {Γ : List Ty} {t : Ty} (S : List SI) (p : Place Γ t) : Prop :=
  p.IdxNH S ∧ ∀ H, (S.getD p.root default).hole = some H → Sel.overlap H.path p.path = false

theorem _root_.Millipede.Place.idxNH_of {Γ : List Ty} {S : List SI} : {t : Ty} → (p : Place Γ t) →
    (∀ i H, (S.getD i default).hole = some H → p.IdxAvoids i ⟨true, H.path⟩) → p.IdxNH S
  | _, .var _, _ => trivial
  | _, .field p _, h => Place.idxNH_of p h
  | _, .index (dflt := _) p i, h => ⟨Place.idxNH_of p fun i H h' => (h i H h').1,
      i.noHole fun i' H h' => (h i' H h').2⟩
  | _, .slot (dflt := _) p i, h => ⟨Place.idxNH_of p fun i H h' => (h i H h').1,
      i.noHole fun i' H h' => (h i' H h').2⟩
  | _, .range p lo len, h => ⟨Place.idxNH_of p fun i H h' => (h i H h').1,
      lo.noHole fun i' H h' => (h i' H h').2.1, len.noHole fun i' H h' => (h i' H h').2.2⟩
  | _, .pair2 (dflt := _) p i j, h => ⟨Place.idxNH_of p fun i H h' => (h i H h').1,
      i.noHole fun i' H h' => (h i' H h').2.1, j.noHole fun i' H h' => (h i' H h').2.2⟩
  | _, .rangeS _ lo len, h =>
    ⟨lo.noHole fun i' H h' => (h i' H h').1, len.noHole fun i' H h' => (h i' H h').2⟩
  | _, .pair2S (dflt := _) _ i j, h =>
    ⟨i.noHole fun i' H h' => (h i' H h').1, j.noHole fun i' H h' => (h i' H h').2⟩

/-- A place access that respects every hole's loan is `NH`. -/
theorem _root_.Millipede.Place.nh_of {Γ : List Ty} {t : Ty} {S : List SI} (p : Place Γ t)
    (a : Acc) (h : ∀ i H, (S.getD i default).hole = some H → p.Avoids i ⟨true, H.path⟩ a) :
    p.NH S :=
  ⟨p.idxNH_of fun i H h' => (h i H h').1, fun H hH => by
    have := (h _ H hH).2 rfl
    simpa [Loan.blocks] using this⟩

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

theorem ofNat_toNat_mul (x : UInt64) (sz : Nat) :
    x * UInt64.ofNat sz = UInt64.ofNat (x.toNat * sz) := by
  rw [UInt64.ofNat_mul]; simp

/-! ## Addresses -/

/-- `elemAddr` adds `i * size` to `RA`. -/
theorem elemAddr_runs {Γ : List Ty} (i : Atom Γ .u64) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (sz A : Nat)
    (hf : f BP = UInt64.ofNat bp) (hA : f RA = UInt64.ofNat A) (henv : MEnvRel h bp env ρ S)
    (hfe : FEnvRel f env ρ)
    (hl : Lay bp n Γ ρ S W) (hnh : ∀ m, i = .var m → (S.getD m.idx default).hole = none)
    (hnL : bp + n ≤ L) (hnU : bp + n ≤ UInt64.size) :
    ∃ f', Runs κ ω L (elemAddr i ρ sz) f h f' h ∧ f' BP = f BP ∧
      f' RA = UInt64.ofNat (A + (i.denote env).toNat * sz) ∧
      ∀ x, x ≠ RA → x ≠ RX → f' x = f x := by
  refine ⟨_, Runs.seq (atomWord_u64 i RX hf henv hfe hl hnh hnL hnU) (Runs.seq (Runs.bin _ _ _ _ _ _)
    (Runs.bin _ _ _ _ _ _)), ?_, ?_, ?_⟩
  · simp [Frame.set]
  · simp only [Frame.set, eval_slot, eval_imm, BinOp.eval, ↓reduceIte,
      show RA = RX ↔ False by decide]
    rw [hA, ofNat_toNat_mul, ofNat_add_ofNat]
  · intro x h1 h2; simp [Frame.set, h1, h2]

/-- A variable with a second piece is at a two-address location. -/
theorem Single.snd_some {bp n : Nat} {t : Ty} {l : Loc} {s : SI} {w : Bool}
    (h : Single bp n t l s w) {q : Nat × Nat} (hs : s.snd = some q) : ∃ o, l = .ref2 o ∧ PairSI t s := by
  obtain ⟨_, h2, _⟩ := h
  cases l with
  | own o => rw [h2.2.2] at hs; cases hs
  | ref o => rw [h2.1] at hs; cases hs
  | ref2 o => exact ⟨o, rfl, h2.1⟩
  | slot o _ => rw [h2.2.2] at hs; cases hs

theorem _root_.Millipede.Place.loc2_some {Γ : List Ty} {t : Ty} {p : Place Γ t} {ρ : List Loc}
    {o : Nat} (h : p.loc2 ρ = some o) : ∃ m, p = .var m ∧ ρ.getD m.idx default = .ref2 o := by
  cases p with
  | var m =>
    simp only [Place.loc2] at h
    split at h
    · cases h; exact ⟨m, rfl, by assumption⟩
    · cases h
  | _ => simp [Place.loc2] at h

/-- A place of a type that is not a pair is not a pair reference as a whole. -/
theorem _root_.Millipede.Place.notPair_of_ty {Γ : List Ty} {t : Ty} {bp n : Nat} {ρ : List Loc}
    {S : List SI} {W : List Bool} (hl : Lay bp n Γ ρ S W) (p : Place Γ t)
    (ht : ∀ fs, t.data.shape ≠ .prod fs) : p.NotPair S := by
  intro hv
  obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hv
  exact (hl.var m).snd_none_of_ty ht

/-- A place that is not at a two-address location is not a pair reference as a whole. -/
theorem _root_.Millipede.Place.notPair_of_loc2 {Γ : List Ty} {t : Ty} {bp n : Nat} {ρ : List Loc}
    {S : List SI} {W : List Bool} (hl : Lay bp n Γ ρ S W) (p : Place Γ t) (h : p.loc2 ρ = none) :
    p.NotPair S := by
  intro hv
  obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hv
  cases hs : (S.getD m.idx default).snd with
  | none => simpa [Place.root] using hs
  | some q =>
    obtain ⟨o, hρ, _⟩ := (hl.var m).snd_some hs
    simp only [Place.loc2, hρ] at h; cases h

theorem arr_not_prod (t : Ty) (N : Nat) (fs : List Shape) : (Ty.arr t N).data.shape ≠ .prod fs := nofun
theorem slots_not_prod (t : Ty) (N : Nat) (fs : List Shape) : (Ty.slots t N).data.shape ≠ .prod fs :=
  nofun

/-- A lawful lens of a pair reference's type selects field `0` at offset `0` or field `1` at
offset `sh.size`, each of the field's shape. -/
theorem pair_lens {s t : Ty} {sh : Shape} (l : Lens s t) (hL : l.Lawful)
    (hsh : s.data.shape = .prod [sh, sh]) :
    (l.index = 0 ∧ lensOff l = 0 ∨ l.index = 1 ∧ lensOff l = sh.size) ∧ t.size = sh.size := by
  obtain ⟨fs, hfs, hfi⟩ := hL.2
  rw [hsh] at hfs; cases hfs
  have hlo : lensOff l = Shape.fieldOffset [sh, sh] l.index := by simp [lensOff, hsh]
  have hlt : l.index < 2 := by
    have := List.getElem?_eq_some_iff.mp hfi; simpa using this.1
  refine ⟨?_, ?_⟩
  · rcases (by omega : l.index = 0 ∨ l.index = 1) with h | h
    · left; refine ⟨h, ?_⟩; rw [hlo, h]; simp [Shape.fieldOffset, Shape.prodOffsets, alignUp_zero]
    · right; refine ⟨h, ?_⟩; rw [hlo, h]; exact (pairShape sh).1
  · have : [sh, sh][l.index]? = some sh := by
      rcases (by omega : l.index = 0 ∨ l.index = 1) with h | h <;> simp [h]
    rw [hfi] at this; cases this; rfl

/-- The address code of a contiguous place that is not a pair reference as a whole. -/
theorem placeAddr_runs {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (hc : p.contig = true)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hl : Lay bp n Γ ρ S W)
    (hnh : p.IdxNH S) (hL : p.Lawful) (hnp : p.NotPair S) (hnL : bp + n ≤ L)
    (hnU : bp + n ≤ UInt64.size) :
    ∃ f', Runs κ ω L (placeAddr p ρ) f h f' h ∧ f' BP = f BP ∧
      f' RA = UInt64.ofNat (placeA p S env) ∧ ∀ x, x ≠ RA → x ≠ RX → f' x = f x := by
  induction p generalizing f with
  | var m =>
    have hsn : (S.getD m.idx default).snd = none := hnp (by simp [Place.isVarAt, Place.root])
    simp only [placeAddr, varAddr]
    split
    · rename_i o hρ
      have hA : (S.getD m.idx default).A = bp + o := by
        have := (hl.var m).2.1; rw [hρ] at this; exact this.1
      refine ⟨_, Runs.bin _ _ _ _ _ _, by simp [Frame.set], ?_, fun x h1 _ => by simp [Frame.set, h1]⟩
      simp only [Frame.set, ↓reduceIte, eval_slot, eval_imm, BinOp.eval, hf, ofNat_add_ofNat]
      simp only [placeA, hA]
    · rename_i o k w hρ
      have hA : (S.getD m.idx default).A = bp + o := by
        have := (hl.var m).2.1; rw [hρ] at this; exact this.1
      refine ⟨_, Runs.bin _ _ _ _ _ _, by simp [Frame.set], ?_, fun x h1 _ => by simp [Frame.set, h1]⟩
      simp only [Frame.set, ↓reduceIte, eval_slot, eval_imm, BinOp.eval, hf, ofNat_add_ofNat]
      simp only [placeA, hA]
    · rename_i o hρ
      refine ⟨_, ptr_load (κ := κ) (ω := ω) (L := L) m RA hl henv hρ hf hnL hnU,
        by simp [Frame.set], by simp [placeA], fun x h1 _ => by simp [Frame.set, h1]⟩
    · rename_i o hρ; exact absurd hρ ((hl.var m).not_ref2 hsn o)
  | @field s t' p l ih =>
    simp only [placeAddr]
    cases hloc : p.loc2 ρ with
    | some o =>
      obtain ⟨m, rfl, hρ⟩ := Place.loc2_some hloc
      have hsing := hl.var m
      have hp := (henv.get' m).2
      rw [hρ] at hp
      have h2 := hsing.2.1
      rw [hρ] at h2
      obtain ⟨sh, A2, hsh, hsnd, -, -⟩ := h2.1
      have hslot := hsing.slotLe
      rw [hρ] at hslot
      simp only [Loc.off, Loc.size] at hslot
      have hpa : placeA (Place.field (.var m) l) S env =
          if l.index = 0 then (S.getD m.idx default).A else A2 := by
        simp only [placeA, Place.snd2, Place.root, hsnd, Option.map_some]
      rw [hpa]
      refine ⟨_, Runs.load _ _ _ _ _ _ (acc_off (b := 8) (by split <;> omega) (by split <;> omega) hf),
        by simp [Frame.set], ?_, fun x h1 _ => by simp [Frame.set, h1]⟩
      simp only [Frame.set_same, eval_slot, hf, ofNat_add_ofNat, load64_eq]
      split
      · exact hp.1
      · rw [show bp + (o + 8) = bp + o + 8 by omega]; exact hp.2 _ _ hsnd
    | none =>
      have hnp' := p.notPair_of_loc2 hl hloc
      have hs2 : p.snd2 S = none := by
        cases p with
        | var m => exact Place.snd2_none _ (hnp' (by simp [Place.isVarAt, Place.root]))
        | _ => rfl
      obtain ⟨f₁, hr, hb, ha, hx⟩ := ih hc hf hfe hnh hL.1 hnp'
      refine ⟨_, Runs.seq hr (Runs.bin _ _ _ _ _ _), by simp [Frame.set, hb], ?_,
        fun x h1 h2 => by simp [Frame.set, h1, hx x h1 h2]⟩
      simp only [Frame.set, ↓reduceIte, eval_slot, eval_imm, BinOp.eval, ha, ofNat_add_ofNat]
      simp only [placeA, hs2]
  | @index t' n' _ p i ih =>
    obtain ⟨f₁, hr, hb, ha, hx⟩ := ih hc hf hfe hnh.1 hL (p.notPair_of_ty hl (arr_not_prod t' n'))
    obtain ⟨f₂, hr₂, hb₂, ha₂, hx₂⟩ := elemAddr_runs (κ := κ) (ω := ω) i _ _ (hb.trans hf) ha henv
      (hfe.keep hr.keep) hl hnh.2 hnL hnU
    refine ⟨f₂, Runs.seq hr hr₂, hb₂.trans hb, ?_, fun x h1 h2 => (hx₂ x h1 h2).trans (hx x h1 h2)⟩
    rw [ha₂]; simp only [placeA]
  | @slot t' n' _ p i ih =>
    obtain ⟨f₁, hr, hb, ha, hx⟩ := ih hc hf hfe hnh.1 hL (p.notPair_of_ty hl (slots_not_prod t' n'))
    obtain ⟨f₂, hr₂, hb₂, ha₂, hx₂⟩ := elemAddr_runs (κ := κ) (ω := ω) i _ _ (hb.trans hf) ha henv
      (hfe.keep hr.keep) hl hnh.2 hnL hnU
    refine ⟨f₂, Runs.seq hr hr₂, hb₂.trans hb, ?_, fun x h1 h2 => (hx₂ x h1 h2).trans (hx x h1 h2)⟩
    rw [ha₂]; simp only [placeA]
  | range => simp [Place.contig] at hc
  | pair2 => simp [Place.contig] at hc
  | rangeS => simp [Place.contig] at hc
  | pair2S => simp [Place.contig] at hc

theorem vget_of_lt {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (d : α) (h : i < n) :
    vget v i d = v[i] := by simp [vget, h]

theorem slice_full (bs : List UInt8) (n : Nat) (h : bs.length = n) : slice bs 0 n = bs := by
  subst h; simp [slice]

/-! ## Reading -/

/-- Reading a place, stated on bytes: bytes that represent the root's value hold the place's value
at its offset. -/
theorem place_getB {Γ : List Ty} {t : Ty} (p : Place Γ t) {env : Env Γ} (hc : p.contig = true)
    (hL : p.Lawful) (hok : p.ok env) (B : List UInt8) (hB : Data.reprBytes (p.rootVal env) B) :
    Data.reprBytes (p.get env) (slice B (p.off env) t.size) := by
  induction p with
  | var m =>
    have hB' : Data.reprBytes (env.get m) B := hB
    simp only [Place.get, Place.off]
    rw [slice_full B _ (Data.reprBytes_length hB')]; exact hB'
  | @field s t' p l ih =>
    have hr := ih hc hL.1 hok hB
    obtain ⟨⟨hl1, hl2, _⟩, _⟩ := hL.2
    have := hl2 _ _ hr
    have hb := p.off_le env hc hL.1 hok
    rw [slice_slice _ _ _ _ _ hl1] at this
    simpa [Place.off, Place.get] using this
  | @index t' n' _ p i ih =>
    have hr := ih hc hL hok.1 hB
    have hi := hok.2
    obtain ⟨_, hv⟩ := hr
    have this : Data.reprBytes _ (slice (slice B (p.off env) (n' * t'.size))
        ((Data.shape t'.carrier).elemOffset (i.denote env).toNat) t'.size) := hv _ hi
    rw [slice_slice B (p.off env) (n' * t'.size) _ t'.size
      (Shape.elemOffset_add_size_le n' (Data.shape t'.carrier) _ hi)] at this
    simp only [Place.get, vget_of_lt _ _ _ hi]
    simpa [Place.off, Shape.elemOffset] using this
  | @slot t' n' _ p i ih =>
    have hr := ih hc hL hok.1 hB
    have hfull := hok.2
    generalize hs : (Place.get p env : Slots t'.carrier n') = sv at hfull hr
    generalize hjj : (i.denote env).toNat = j at hfull
    have hj : j < n' := by
      rcases Nat.lt_or_ge j n' with hj | hj
      · exact hj
      · exfalso; simp [Slots.isFull, Slots.cell, vget, Nat.not_lt.mpr hj] at hfull
    obtain ⟨x, hx⟩ : ∃ x, sv.cells[j] = some x := by
      simp [Slots.isFull, Slots.cell, vget, hj] at hfull; exact Option.isSome_iff_exists.mp hfull
    have hget : Place.get (.slot p i) env = x := by
      simp [Place.get, Slots.cell, vget, hj, hx, hs, hjj]
    obtain ⟨_, hv⟩ := hr
    have this : Slots.cellRepr sv.cells[j] (slice (slice B (p.off env) (n' * t'.size))
        ((Data.shape t'.carrier).elemOffset j) t'.size) := hv _ hj
    rw [slice_slice B (p.off env) (n' * t'.size) _ t'.size
      (Shape.cellOffset_add_size_le n' (Data.shape t'.carrier) _ hj)] at this
    rw [hget]
    have hx' : sv.cells[j] = some x := hx
    simp only [Slots.cells] at hx'
    simp only [hx', Slots.cellRepr] at this
    simpa [Place.off, Shape.elemOffset, hjj] using this
  | range => simp [Place.contig] at hc
  | pair2 => simp [Place.contig] at hc
  | rangeS => simp [Place.contig] at hc
  | pair2S => simp [Place.contig] at hc

/-! ## Slice views: their elements lie in their extent -/

/-- The place is not a slice view as a whole: either its root is not a view, or the place reaches
inside the view to one of its elements or a part of one. -/
def _root_.Millipede.Place.ExtOk {Γ : List Ty} {t : Ty} (S : List SI) (p : Place Γ t) : Prop :=
  (S.getD p.root default).ext = none ∨ p.isVarAt p.root = false

theorem VS.place {Γ : List Ty} {t : Ty} {S : List SI} {P : Nat → Bool} (p : Place Γ t)
    (hV : VS S P) (hp : ∀ i, P i = true → p.isVarAt i = false) : p.ExtOk S := by
  cases he : (S.getD p.root default).ext with
  | none => exact Or.inl he
  | some e => exact Or.inr (hp _ (hV _ (by rw [he]; nofun)))

theorem _root_.Millipede.Place.VSafe_isVarAt {Γ : List Ty} {t : Ty} {i : Nat} {p : Place Γ t}
    (h : p.VSafe i = true) : p.isVarAt i = false := by
  simp only [Place.VSafe, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2

/-- A view's value unfolded: its first `len` cells are full and the others empty. -/
theorem viewOK_slots {T : Ty} {N : Nat} {v : Slots T.carrier N} {e : Nat}
    (h : ViewOK (.slots T N) v e) :
    ∃ len, len ≤ N ∧ e = len * T.size ∧ ∀ k (hk : k < N), (v.cells[k]).isSome = decide (k < len) := by
  obtain ⟨cnt, len, sh, hs, hle, he, ho⟩ := h
  have hs' : Shape.slots N (Data.shape T.carrier) = .slots cnt sh := hs
  injection hs' with h1 h2
  subst h1 h2
  refine ⟨len, hle, he, fun k hk => ?_⟩
  have ho' : [some (v.cells.toList.map Option.isSome)] =
      [some ((List.range N).map fun k => decide (k < len))] := ho
  simp only [List.cons.injEq, Option.some.injEq, and_true] at ho'
  have := congrArg (fun l => l[k]?) ho'
  simpa [hk] using this

theorem viewOK_of_slots {T : Ty} {N len : Nat} {v : Slots T.carrier N} (hle : len ≤ N)
    (hv : ∀ k (hk : k < N), (v.cells[k]).isSome = decide (k < len)) :
    ViewOK (.slots T N) v (len * T.size) := by
  refine ⟨N, len, Data.shape T.carrier, rfl, hle, rfl, ?_⟩
  show [some _] = [some _]
  congr 2
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.length_map, Vector.length_toList] at h1
  simpa using hv k h1

/-- The elements of a view lie in its extent. A place that reaches inside a slice view through one
of its cells, whose obligation is that the cell is full, lies in the view's first `len · size`
bytes. -/
theorem _root_.Millipede.Place.view_bound {Γ : List Ty} {t : Ty} (p : Place Γ t) (env : Env Γ)
    (hc : p.contig = true) (hL : p.Lawful) (hok : p.ok env) (hnv : p.isVarAt p.root = false)
    {e : Nat} (hv : ViewOK p.rootTy (p.rootVal env) e) : p.off env + t.size ≤ e := by
  induction p with
  | var m => simp [Place.isVarAt, Place.root] at hnv
  | @field s t' p l ih =>
    by_cases hp : p.isVarAt p.root = true
    · exfalso
      obtain ⟨fs, hfs, _⟩ := hL.2.2
      obtain ⟨_, _, _, hs, _⟩ := hv
      have hs' : p.rootTy.data.shape = _ := hs
      rw [p.rootTy_of_isVarAt hp, hfs] at hs'; cases hs'
    · have := ih hc hL.1 hok (by simpa using hp) hv
      have := hL.2.1.1
      simp only [Place.off]; omega
  | @index t' n' _ p i ih =>
    by_cases hp : p.isVarAt p.root = true
    · exfalso
      obtain ⟨_, _, _, hs, _⟩ := hv
      have hs' : p.rootTy.data.shape = _ := hs
      rw [p.rootTy_of_isVarAt hp] at hs'; cases hs'
    · have := ih hc hL hok.1 (by simpa using hp) hv
      have hi := hok.2
      have : (i.denote env).toNat * t'.size + t'.size ≤ n' * t'.size := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
      have hsz : (Ty.arr t' n').size = n' * t'.size := rfl
      simp only [Place.off]; omega
  | @slot t' n' _ p i ih =>
    have hfull := hok.2
    generalize hjj : (i.denote env).toNat = j at hfull
    have hj : j < n' := by
      rcases Nat.lt_or_ge j n' with hj | hj
      · exact hj
      · exfalso; simp [Slots.isFull, Slots.cell, vget, Nat.not_lt.mpr hj] at hfull
    by_cases hp : p.isVarAt p.root = true
    · obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hp
      obtain ⟨len, _, he, hcells⟩ := viewOK_slots (v := env.get m) hv
      have hcj := hcells j hj
      have hfj : ((env.get m : Slots t'.carrier n').cells[j]).isSome = true := by
        simpa [Slots.isFull, Slots.cell, vget, hj, Place.get] using hfull
      rw [hfj] at hcj
      have hjl : j < len := by simpa using hcj.symm
      have : j * t'.size + t'.size ≤ len * t'.size := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hjl
      simp only [Place.off, hjj]; omega
    · have := ih hc hL hok.1 (by simpa using hp) hv
      have : j * t'.size + t'.size ≤ n' * t'.size := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
      have hsz : (Ty.slots t' n').size = n' * t'.size := rfl
      simp only [Place.off, hjj]; omega
  | range => simp [Place.contig] at hc
  | pair2 => simp [Place.contig] at hc
  | rangeS => simp [Place.contig] at hc
  | pair2S => simp [Place.contig] at hc

/-- A place that is not a view or pair reference as a whole lies in its root's storage, which for
a view is its extent. -/
theorem place_in_ext {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {h : Heap} (hc : p.contig = true) (hL : p.Lawful)
    (hok : p.ok env) (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W) (hpv : p.ExtOk S) :
    p.off env + t.size ≤ (S.getD p.root default).sz p.rootTy := by
  have hle := p.off_le env hc hL hok
  cases he : (S.getD p.root default).ext with
  | none => rw [SI.sz_none he]; exact hle
  | some e =>
    have hnv : p.isVarAt p.root = false := by
      rcases hpv with h | h
      · rw [he] at h; cases h
      · exact h
    cases hs : (S.getD p.root default).snd with
    | none =>
      obtain ⟨⟨_, _, _, hx⟩, _⟩ := henv.root p ((hl.root p).ns_of_ext (Or.inl (by rw [he]; nofun)))
      have := p.view_bound env hc hL hok hnv (hx e he hs)
      simp only [SI.sz, SI.lim, he]; omega
    | some q =>
      obtain ⟨_, _, hp⟩ := (hl.root p).snd_some hs
      rw [hp.sz]; exact hle

/-- The places of a pair reference, other than the reference as a whole, have consecutive bytes
from their address, inside the piece of the first field selected. -/
theorem pair_place {Γ : List Ty} {t : Ty} (p : Place Γ t) {S : List SI} {env : Env Γ} {sh : Shape}
    {A2 : Nat} (hc : p.contig = true) (hL : p.Lawful) (hok : p.ok env)
    (hnv : p.isVarAt p.root = false) (hsh : p.rootTy.data.shape = .prod [sh, sh])
    (hs : (S.getD p.root default).snd = some (sh.size, A2)) :
    (∀ k, k < t.size → placeA p S env + k = (S.getD p.root default).at (p.off env + k)) ∧
      ((S.getD p.root default).A ≤ placeA p S env ∧
          placeA p S env + t.size ≤ (S.getD p.root default).A + sh.size ∨
        A2 ≤ placeA p S env ∧ placeA p S env + t.size ≤ A2 + sh.size) := by
  induction p with
  | var m => simp [Place.isVarAt, Place.root] at hnv
  | @field s t' p l ih =>
    by_cases hpv : p.isVarAt p.root = true
    · obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hpv
      have hsh' : s.data.shape = .prod [sh, sh] := hsh
      obtain ⟨hix, hsz⟩ := pair_lens l hL.2 hsh'
      have hs' : (S.getD m.idx default).snd = some (sh.size, A2) := hs
      have hpa : placeA (Place.field (.var m) l) S env =
          if l.index = 0 then (S.getD m.idx default).A else A2 := by
        simp only [placeA, Place.snd2, Place.root, hs', Option.map_some]
      have hoff : (Place.field (.var m) l).off env = lensOff l := by
        simp [Place.off]
      simp only [Place.root] at hs' ⊢
      rw [hpa, hoff, hsz]
      rcases hix with ⟨h0, h0'⟩ | ⟨h1, h1'⟩
      · simp only [h0, h0', Nat.zero_add, ↓reduceIte]
        refine ⟨fun k hk => ?_, Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
        simp only [SI.at, hs', hk, ↓reduceIte]
      · simp only [h1, h1', Nat.one_ne_zero, ↓reduceIte]
        refine ⟨fun k hk => ?_, Or.inr ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
        simp only [SI.at, hs']; rw [ite_eq_right (by omega)]; omega
    · have hnv' : p.isVarAt p.root = false := by simpa using hpv
      obtain ⟨ih1, ih2⟩ := ih hc hL.1 hok hnv' hsh hs
      have hs2 : p.snd2 S = none := by cases p <;> simp_all [Place.snd2, Place.isVarAt, Place.root]
      have hl1 := hL.2.1.1
      have hpa : placeA (Place.field p l) S env = placeA p S env + lensOff l := by
        simp only [placeA, hs2]
      simp only [Place.root, Place.off] at ih1 ih2 hs ⊢
      rw [hpa]
      refine ⟨fun k hk => ?_, by omega⟩
      rw [Nat.add_assoc, ih1 (lensOff l + k) (by omega), Nat.add_assoc]
  | @index t' n' _ p i ih =>
    have hnv' : p.isVarAt p.root = false := by
      cases hv : p.isVarAt p.root with
      | false => rfl
      | true =>
        exfalso
        have := p.rootTy_of_isVarAt hv
        have hsh' : p.rootTy.data.shape = .prod [sh, sh] := hsh
        rw [this] at hsh'; cases hsh'
    obtain ⟨ih1, ih2⟩ := ih hc hL hok.1 hnv' hsh hs
    have hj := hok.2
    have hjb : (i.denote env).toNat * t'.size + t'.size ≤ n' * t'.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
    have hsz : (Ty.arr t' n').size = n' * t'.size := rfl
    simp only [Place.root, Place.off] at ih1 ih2 hs ⊢
    simp only [placeA]
    refine ⟨fun k hk => ?_, by omega⟩
    rw [Nat.add_assoc, ih1 _ (by omega), Nat.add_assoc]
  | @slot t' n' _ p i ih =>
    have hnv' : p.isVarAt p.root = false := by
      cases hv : p.isVarAt p.root with
      | false => rfl
      | true =>
        exfalso
        have := p.rootTy_of_isVarAt hv
        have hsh' : p.rootTy.data.shape = .prod [sh, sh] := hsh
        rw [this] at hsh'; cases hsh'
    obtain ⟨ih1, ih2⟩ := ih hc hL hok.1 hnv' hsh hs
    have hfull := hok.2
    have hj : (i.denote env).toNat < n' := by
      rcases Nat.lt_or_ge (i.denote env).toNat n' with hj | hj
      · exact hj
      · exfalso; simp [Slots.isFull, Slots.cell, vget, Nat.not_lt.mpr hj] at hfull
    have hjb : (i.denote env).toNat * t'.size + t'.size ≤ n' * t'.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
    have hsz : (Ty.slots t' n').size = n' * t'.size := rfl
    simp only [Place.root, Place.off] at ih1 ih2 hs ⊢
    simp only [placeA]
    refine ⟨fun k hk => ?_, by omega⟩
    rw [Nat.add_assoc, ih1 _ (by omega), Nat.add_assoc]
  | range => simp [Place.contig] at hc
  | pair2 => simp [Place.contig] at hc
  | rangeS => simp [Place.contig] at hc
  | pair2S => simp [Place.contig] at hc

/-- A contiguous place that is not a view or pair reference as a whole lies in its root's storage,
below the watermark, with its bytes consecutive from its address. -/
theorem place_at {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {h : Heap} (hc : p.contig = true) (hL : p.Lawful)
    (hok : p.ok env) (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W) (hpv : p.ExtOk S) :
    p.off env + t.size ≤ (S.getD p.root default).sz p.rootTy ∧
      placeA p S env + t.size ≤ bp + n ∧
      (∀ k, k < t.size → placeA p S env + k = (S.getD p.root default).at (p.off env + k)) ∧
      (S.getD p.root default).Holds p.rootTy (placeA p S env) t.size := by
  have hin := place_in_ext p hc hL hok henv hl hpv
  have hsing := hl.root p
  refine ⟨hin, ?_⟩
  cases hs : (S.getD p.root default).snd with
  | none =>
    have hdl := hsing.dataLe hs
    rw [placeA_plain p hc hs]
    refine ⟨by omega, fun k _ => by rw [SI.at_none hs]; omega, ?_⟩
    simp only [SI.Holds, hs]; omega
  | some q =>
    obtain ⟨o, -, hp⟩ := hsing.snd_some hs
    have hsz := hp.sz
    obtain ⟨sh, A2, hsh, hs', he, -⟩ := hp
    have hnv : p.isVarAt p.root = false := by
      rcases hpv with h | h
      · rw [he] at h; cases h
      · exact h
    obtain ⟨h1, h2⟩ := pair_place p hc hL hok hnv hsh hs'
    have hb := hsing.below
    simp only [SI.Below, hs'] at hb
    have h2s : p.rootTy.size = 2 * sh.size := by
      show p.rootTy.data.shape.size = _; rw [hsh]; exact (pairShape sh).2
    rw [hsz, h2s] at hb
    refine ⟨by rcases h2 with h2 | h2 <;> omega, h1, ?_⟩
    simp only [SI.Holds, hs', hsz, h2s]
    rcases h2 with h2 | h2
    · exact Or.inl ⟨h2.1, by rw [Nat.min_eq_left (by omega)]; exact h2.2⟩
    · exact Or.inr ⟨h2.1, by omega⟩

/-- A place's bytes lie in its root's storage. -/
theorem place_in {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {h : Heap} (hc : p.contig = true) (hL : p.Lawful)
    (hok : p.ok env) (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W) (hpv : p.ExtOk S)
    {x : Nat} (hx : InR (placeA p S env) t.size x) : (S.getD p.root default).In p.rootTy x := by
  obtain ⟨hin, -, hat, -⟩ := place_at p hc hL hok henv hl hpv
  obtain ⟨k, hk, rfl⟩ : ∃ k, k < t.size ∧ x = placeA p S env + k := ⟨x - placeA p S env, by
    unfold InR at hx; omega, by unfold InR at hx; omega⟩
  rw [hat k hk]; exact SI.In_at (by omega)

/-! ## Reading -/

/-- Reading a place: its bytes represent its value. This holds when its root is a lender as long
as the place does not overlap the lent place, when its root is a view as long as the place is one
of the view's elements or inside one, and when its root is a pair reference as long as the place is
inside one of its fields. -/
theorem place_get {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {h : Heap} (hc : p.contig = true) (hL : p.Lawful)
    (hok : p.ok env) (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W)
    (hnh : ∀ H, (S.getD p.root default).hole = some H → Sel.overlap H.path p.path = false)
    (hpv : p.ExtOk S) (hns : (ρ.getD p.root default).isSlot = false) :
    placeA p S env + t.size ≤ bp + n ∧
      Data.reprBytes (p.get env) (rd h (placeA p S env) t.size) := by
  obtain ⟨⟨B, hB, hm, _⟩, _⟩ := henv.root p hns
  have hsing := hl.root p
  obtain ⟨hin, hbd, hat, -⟩ := place_at p hc hL hok henv hl hpv
  have hle := p.off_le env hc hL hok
  refine ⟨hbd, ?_⟩
  have hBl := Data.reprBytes_length hB
  have e : rd h (placeA p S env) t.size = slice B (p.off env) t.size := by
    rw [rd_of_getD (B := slice B (p.off env) t.size) (by rw [slice_length_of_le (by
      show _ ≤ B.length; rw [hBl]; exact hle)]) fun i hi => ?_]
    rw [hat i hi, hm (p.off env + i) (by omega) ?_]
    · simp only [slice, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hi,
        ↓reduceIte]
    · intro hin
      unfold SI.inHole at hin
      split at hin
      · exact hin
      · rename_i H hH
        exact (hsing.2.2.2 H hH).2 p env rfl hc hL hok (hnh H hH) i hi hin
  rw [e]; exact place_getB p hc hL hok B hB

/-- A view without a hole is represented by its whole nominal layout: its full cells lie in its
extent, and its other cells are empty, whatever their bytes. -/
theorem VarRel.exact_slots {h : Heap} {T : Ty} {N : Nat} {v : Slots T.carrier N} {s : SI}
    (hv : VarRel h (.slots T N) v s) (hs : s.hole = none) (hsn : s.snd = none) :
    Data.reprBytes v (rd h s.A (Ty.slots T N).size) := by
  cases he : s.ext with
  | none => exact hv.exact hs he hsn
  | some e =>
    obtain ⟨B, hB, hm, hx⟩ := hv
    obtain ⟨len, hle, he', hcells⟩ := viewOK_slots (hx e he hsn)
    have hsz : (Ty.slots T N).size = N * T.size := rfl
    refine ⟨by rw [rd_length], fun k hk => ?_⟩
    show Slots.cellRepr v.cells[k] (slice (rd h s.A (N * T.size)) (k * T.size) T.size)
    have hck := hcells k hk
    cases hvk : v.cells[k] with
    | none => trivial
    | some x =>
      rw [hvk] at hck
      have hkl : k < len := by simpa using hck.symm
      have hkb : k * T.size + T.size ≤ len * T.size := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hkl
      have hkN : k * T.size + T.size ≤ N * T.size := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
      have hB' := hB.2 k hk
      rw [hvk] at hB'
      have hBl := Data.reprBytes_length hB
      rw [← rd_slice _ _ _ _ _ hkN]
      have : rd h (s.A + k * T.size) T.size = slice B (k * T.size) T.size := by
        rw [rd_of_getD (B := slice B (k * T.size) T.size) (by
          rw [slice_length_of_le (by show _ ≤ B.length; rw [hBl]; exact hkN)]) fun i hi => ?_]
        have := hm (k * T.size + i) (by
          simp only [SI.sz, SI.lim, he]; have : k * T.size + i < len * T.size := by omega
          have : k * T.size + i < (Ty.slots T N).size := by rw [hsz]; omega
          omega) (by simp [SI.inHole, hs])
        rw [SI.at_none hsn] at this
        rw [Nat.add_assoc, this]
        simp only [slice, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hi,
          ↓reduceIte]
      rw [this]; exact hB'

/-! ## Writing -/

/-- Another variable's visible bytes are outside a writable variable's storage. -/
theorem CompatAll.vis_out {bp : Nat} {t : Ty} {l : Loc} {s : SI} :
    ∀ {ts : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {x : Nat},
    CompatAll bp t l s true ts ρ S W → Vis bp ts ρ S x → ¬ s.In t x
  | _ :: _, _ :: _, _ :: _, _, x, hc, hv, hin => by
    rcases hv with ⟨h1, h2⟩ | ⟨o, w, e, h1⟩ | hv
    · exact h2 (hc.1.2.2.2.1 rfl x hin h1)
    · exact (hc.1.2.2.1 o w e).not_In h1 hin
    · exact CompatAll.vis_out hc.2 hv hin
  | [], _, _, _, _, _, hv, _ => hv
  | _ :: _, [], _, _, _, _, hv, _ => hv
  | _ :: _, _ :: _, [], _, _, _, hv, _ => hv

theorem VarRel.of_exact' {h : Heap} {t : Ty} {v : t.carrier} {s : SI}
    (hv : Data.reprBytes v (rd h s.A t.size)) (hx : ∀ e, s.ext = some e → ViewOK t v e)
    (hsn : s.snd = none) : VarRel h t v s :=
  ⟨_, hv, fun i hi _ => by
    rw [SI.at_none hsn]; exact (rd_getD h s.A t.size i (by have := s.sz_le t; omega)).symm,
    fun e he _ => hx e he⟩

/-- Writing a writable variable's whole storage, which is its extent for a view and its two pieces
for a pair reference, represents the new value there unless the variable is slot-resident. A
view's new value must be a view of the same extent. -/
theorem MEnvRel.set_var' {h h' : Heap} {bp n : Nat} : ∀ {t : Ty} {Γ : List Ty} {env : Env Γ}
    {ρ : List Loc} {S : List SI} {W : List Bool} (m : Mem t Γ) (v : t.carrier),
    MEnvRel h bp env ρ S → Lay bp n Γ ρ S W → W.getD m.idx false = true → bp + n ≤ UInt64.size →
    (∀ a, a < bp + n → ¬ (S.getD m.idx default).In t a →
      h' (UInt64.ofNat a) = h (UInt64.ofNat a)) →
    ((ρ.getD m.idx default).isSlot = false ∨ t.slotTy = false →
      VarRel h' t v (S.getD m.idx default)) → MEnvRel h' bp (env.set m v) ρ S
  | t, _, .cons _ env, l :: ρ, s :: S, W, .here, v, henv, hl, hw, hbn, hout, hv => by
    simp only [Mem.idx, List.getD_cons_zero] at hout hv
    have hw' : W.headD false = true := by rw [headD_eq_getD]; exact hw
    have hs := hl.1
    rw [hw'] at hs
    have hca := hl.2.1
    rw [hw'] at hca
    refine ⟨hv, henv.2.1.congr fun o w e x hx => hout x ?_ ?_, ?_⟩
    · have := hs.slotLe; obtain ⟨e1, e2⟩ := Loc.ptr_size e t; unfold InR at hx; omega
    · exact (hs.ptrOut o w e).not_In hx
    · exact henv.2.2.congr fun x hx => hout x (hl.2.2.vis_lt hx) (hca.vis_out hx)
  | _, _, .cons (t := t₀) x env, l :: ρ, s :: S, W, .there m, v, henv, hl, hw, hbn, hout, hv => by
    simp only [Mem.idx, List.getD_cons_succ] at hout hv
    have hlen := Lay.length hl.2.2
    have hcm := CompatAll.get m hl.2.1 hlen.1 hlen.2
    rw [tail_getD] at hcm
    simp only [Mem.idx] at hw
    rw [hw] at hcm
    refine ⟨fun hs => (henv.1 hs).congr fun y h1 h2 => hout y ?_ ?_,
      henv.2.1.congr fun o w e y hy => hout y ?_ ?_,
      MEnvRel.set_var' m v henv.2.2 hl.2.2 (by rw [tail_getD]; exact hw) hbn hout hv⟩
    · exact hl.1.lt h1
    · exact fun hin => h2 (hcm.2.2.2.2 rfl y hin h1)
    · have := hl.1.slotLe; obtain ⟨e1, e2⟩ := Loc.ptr_size e t₀; unfold InR at hy; omega
    · exact (hcm.2.1 o w e).not_In hy
  | _, _, .cons _ _, [], _, _, _, _, henv, _, _, _, _, _ => henv.elim
  | _, _, .cons _ _, _ :: _, [], _, _, _, henv, _, _, _, _, _ => henv.elim

/-- Writing a writable variable's whole storage with bytes that represent the new value. A view's
new value must be a view of the same extent. -/
theorem MEnvRel.set_var {h h' : Heap} {bp n : Nat} {t : Ty} {Γ : List Ty} {env : Env Γ}
    {ρ : List Loc} {S : List SI} {W : List Bool} (m : Mem t Γ) (v : t.carrier)
    (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W) (hw : W.getD m.idx false = true)
    (hbn : bp + n ≤ UInt64.size) (hsn : (S.getD m.idx default).snd = none)
    (hout : ∀ a, a < bp + n → ¬ InR (S.getD m.idx default).A ((S.getD m.idx default).sz t) a →
      h' (UInt64.ofNat a) = h (UInt64.ofNat a))
    (hv : Data.reprBytes v (rd h' (S.getD m.idx default).A t.size))
    (hx : ∀ e, (S.getD m.idx default).ext = some e → ViewOK t v e) : MEnvRel h' bp (env.set m v) ρ S :=
  henv.set_var' m v hl hw hbn (fun a ha hn => hout a ha (by rwa [← SI.In_none hsn]))
    fun _ => VarRel.of_exact' hv hx hsn

/-- The parent of a field is not a view as a whole, since a view has no fields, unless it is a pair
reference. -/
theorem extOk_parent_field {Γ : List Ty} {s t : Ty} {S : List SI} {ρ : List Loc} {bp n : Nat}
    {W : List Bool} {env : Env Γ} {h : Heap} (p : Place Γ s) (l : Lens s t) (hL : l.Lawful)
    (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W) (hnp : p.NotPair S) : p.ExtOk S := by
  cases he : (S.getD p.root default).ext with
  | none => exact Or.inl he
  | some e =>
    refine Or.inr ?_
    cases hp : p.isVarAt p.root with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨⟨_, _, _, hx⟩, _⟩ := henv.root p ((hl.root p).ns_of_ext (Or.inl (by rw [he]; nofun)))
      obtain ⟨_, _, _, hs, _⟩ := hx e he (hnp hp)
      obtain ⟨fs, hfs, _⟩ := hL.2
      rw [p.rootTy_of_isVarAt hp, hfs] at hs; cases hs

theorem extOk_parent_arr {Γ : List Ty} {t : Ty} {N : Nat} {S : List SI} {ρ : List Loc} {bp n : Nat}
    {W : List Bool} {env : Env Γ} {h : Heap} (p : Place Γ (.arr t N)) (henv : MEnvRel h bp env ρ S)
    (hl : Lay bp n Γ ρ S W) : p.ExtOk S := by
  cases he : (S.getD p.root default).ext with
  | none => exact Or.inl he
  | some e =>
    refine Or.inr ?_
    cases hp : p.isVarAt p.root with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨⟨_, _, _, hx⟩, _⟩ := henv.root p ((hl.root p).ns_of_ext (Or.inl (by rw [he]; nofun)))
      obtain ⟨_, _, _, hs, _⟩ := hx e he (p.notPair_of_ty hl (arr_not_prod t N) hp)
      rw [p.rootTy_of_isVarAt hp] at hs; cases hs

/-- Writing an element `r[j]!` of a view, whose cell is full so `j < len`: the view keeps its extent
and its occupancy, and only that element's bytes change. -/
theorem view_set_cell {Γ : List Ty} {t' : Ty} {n' : Nat} (m : Mem (.slots t' n') Γ) {ρ : List Loc}
    {S : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ} {h h' : Heap} {j : Nat} {e : Nat}
    (he : (S.getD m.idx default).ext = some e)
    (hfull : (env.get m : Slots t'.carrier n').isFull j = true)
    (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W)
    (hW : W.getD m.idx false = true) (hbn : bp + n ≤ UInt64.size) (v : t'.carrier)
    (hout : ∀ a, a < bp + n → ¬ InR ((S.getD m.idx default).A + j * t'.size) t'.size a →
      h' (UInt64.ofNat a) = h (UInt64.ofNat a))
    (hv : Data.reprBytes v (rd h' ((S.getD m.idx default).A + j * t'.size) t'.size)) :
    MEnvRel h' bp (env.set m (Slots.setCell (env.get m) j (some v))) ρ S := by
  have hsing := hl.var m
  have hsn := hsing.snd_none_of_ty (slots_not_prod t' n')
  have hnoh : (S.getD m.idx default).hole = none := hsing.2.2.1 hW
  obtain ⟨hvr, _⟩ := henv.get m (hsing.ns_of_ext (Or.inl (by rw [he]; nofun)))
  have hx := hvr
  obtain ⟨B, hB, hm, hxv⟩ := hx
  obtain ⟨len, hle, he', hcells⟩ := viewOK_slots (hxv e he hsn)
  have hj : j < n' := by
    rcases Nat.lt_or_ge j n' with hj | hj
    · exact hj
    · exfalso; simp [Slots.isFull, Slots.cell, vget, Nat.not_lt.mpr hj] at hfull
  have hcj := hcells j hj
  have hfj : ((env.get m : Slots t'.carrier n').cells[j]).isSome = true := by
    simpa [Slots.isFull, Slots.cell, vget, hj] using hfull
  rw [hfj] at hcj
  have hjl : j < len := by simpa using hcj.symm
  have hsz : (Ty.slots t' n').size = n' * t'.size := rfl
  have hszA : (S.getD m.idx default).sz (Ty.slots t' n') = len * t'.size := by
    simp only [SI.sz, SI.lim, he]; rw [hsz, he']
    exact Nat.min_eq_left (Nat.mul_le_mul_right _ hle)
  have hjb : j * t'.size + t'.size ≤ len * t'.size := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hjl
  have hdl := hsing.dataLe hsn
  rw [hszA] at hdl
  have hold := hvr.exact_slots hnoh hsn
  refine henv.set_var m _ hl hW hbn hsn (fun a ha hn => hout a ha (by
      rw [hszA] at hn; unfold InR at hn ⊢; omega)) ⟨rd_length _ _ _, fun k hk => ?_⟩ ?_
  · show Slots.cellRepr _ (slice (rd h' (S.getD m.idx default).A (n' * t'.size)) (k * t'.size) t'.size)
    have hkN : k * t'.size + t'.size ≤ n' * t'.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
    rw [← rd_slice _ _ _ _ _ hkN]
    simp only [Slots.setCell, Slots.cells, vset, hj, ↓reduceDIte]
    erw [Vector.getElem_set hj hk]
    split
    · rename_i hjk; subst hjk; exact hv
    · rename_i hjk
      have hk' : k ≠ j := fun e => hjk e.symm
      have hck := hcells k hk
      cases hvk : (env.get m : Slots t'.carrier n').cells[k] with
      | none => trivial
      | some x =>
        rw [hvk] at hck
        have hkl : k < len := by simpa using hck.symm
        have hkb : k * t'.size + t'.size ≤ len * t'.size := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hkl
        have e1 : rd h' ((S.getD m.idx default).A + k * t'.size) t'.size =
            rd h ((S.getD m.idx default).A + k * t'.size) t'.size := rd_congr fun y hy => by
          refine hout _ (by omega) ?_
          rintro ⟨h1, h2⟩
          have := elem_disj_of_ne (A := 0) (sz := t'.size) hk'; unfold Disj at this; omega
        rw [e1, rd_slice _ _ (n' * t'.size) _ _ hkN]
        have := hold.2 k hk
        rw [hvk] at this
        exact this
  · intro e₂ he₂
    rw [he] at he₂; cases he₂
    rw [he']
    refine viewOK_of_slots hle fun k hk => ?_
    simp only [Slots.setCell, Slots.cells, vset, hj, ↓reduceDIte]
    erw [Vector.getElem_set hj hk]
    split
    · rename_i hjk; subst hjk; simpa using hjl
    · exact hcells k hk

/-- The bytes of a splice. -/
theorem splice_getD (bs vb : List UInt8) (o i : Nat) (h : o + vb.length ≤ bs.length) :
    (splice bs o vb).getD i 0 = if o ≤ i ∧ i < o + vb.length then vb.getD (i - o) 0 else bs.getD i 0 := by
  simp only [splice, List.getD_eq_getElem?_getD, List.append_assoc]
  by_cases h1 : i < o
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take]; simp [h1]; omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_take, Nat.min_eq_left (by omega : o ≤ bs.length)]
    by_cases h2 : i - o < vb.length
    · rw [List.getElem?_append_left h2]; simp; omega
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
      simp only [show ¬ (o ≤ i ∧ i < o + vb.length) by omega, ↓reduceIte]
      congr 2; omega

/-- Writing a field `r.fst` or `r.snd` of a pair reference. The field fills one of the reference's
pieces, and the reference's new value is represented by its old bytes with the field's bytes
spliced in. -/
theorem pair_set_field {Γ : List Ty} {s t : Ty} (m : Mem s Γ) (l : Lens s t) {ρ : List Loc}
    {S : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ} {h h' : Heap} (hL : l.Lawful)
    (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W) (hW : W.getD m.idx false = true)
    (hbn : bp + n ≤ UInt64.size) {q : Nat × Nat} (hs : (S.getD m.idx default).snd = some q)
    (v : t.carrier)
    (hout : ∀ a, a < bp + n → ¬ InR (placeA (Place.field (.var m) l) S env) t.size a →
      h' (UInt64.ofNat a) = h (UInt64.ofNat a))
    (hv : Data.reprBytes v (rd h' (placeA (Place.field (.var m) l) S env) t.size)) :
    MEnvRel h' bp ((Place.field (.var m) l).set env v) ρ S := by
  have hsing := hl.var m
  obtain ⟨o, -, hp⟩ := hsing.snd_some hs
  have hsz := hp.sz
  obtain ⟨sh, A2, hsh, hs', he, hdj⟩ := hp
  obtain ⟨hix, htz⟩ := pair_lens l hL hsh
  have h2s : s.size = 2 * sh.size := by
    show s.data.shape.size = _; rw [hsh]; exact (pairShape sh).2
  have hnoh : (S.getD m.idx default).hole = none := hsing.2.2.1 hW
  obtain ⟨⟨B, hB, hm, -⟩, -⟩ := henv.get m (hsing.ns_of_ext (Or.inr (by rw [hs]; nofun)))
  have hBl := Data.reprBytes_length hB
  have hpa : placeA (Place.field (.var m) l) S env =
      if l.index = 0 then (S.getD m.idx default).A else A2 := by
    simp only [placeA, Place.snd2, Place.root, hs', Option.map_some]
  have hlo := hL.1.1
  have hat : ∀ i, i < s.size → lensOff l ≤ i → i < lensOff l + t.size →
      (S.getD m.idx default).at i = placeA (Place.field (.var m) l) S env + (i - lensOff l) := by
    intro i hi h1 h2
    rw [hpa]
    rcases hix with ⟨h0, h0'⟩ | ⟨h1', h1''⟩
    · simp only [h0, ↓reduceIte, SI.at, hs']; rw [ite_eq_left (by omega)]; omega
    · simp only [h1', Nat.one_ne_zero, ↓reduceIte, SI.at, hs']; rw [ite_eq_right (by omega)]; omega
  have hout' : ∀ i, i < s.size → ¬ (lensOff l ≤ i ∧ i < lensOff l + t.size) →
      ¬ InR (placeA (Place.field (.var m) l) S env) t.size ((S.getD m.idx default).at i) := by
    intro i hi hn hin
    rw [hpa] at hin
    unfold InR at hin
    unfold Disj at hdj
    rcases hix with ⟨h0, h0'⟩ | ⟨h1', h1''⟩
    · simp only [h0, ↓reduceIte, SI.at, hs'] at hin
      split at hin <;> omega
    · simp only [h1', Nat.one_ne_zero, ↓reduceIte, SI.at, hs'] at hin
      split at hin <;> omega
  have hvl := Data.reprBytes_length hv
  rw [rd_length] at hvl
  refine henv.set_var' m _ hl hW hbn (fun a ha hn => hout a ha fun hin => hn ?_) fun _ => ⟨_, hL.1.2.2 _ _ _ _ hB hv,
    fun i hi _ => ?_, fun e _ hsn => by rw [hs'] at hsn; cases hsn⟩
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < t.size ∧ a = placeA (Place.field (.var m) l) S env + k :=
      ⟨a - placeA (Place.field (.var m) l) S env, by unfold InR at hin; omega,
        by unfold InR at hin; omega⟩
    have := hat (lensOff l + k) (by omega) (by omega) (by omega)
    rw [Nat.add_sub_cancel_left] at this
    rw [← this]; exact SI.In_at (by rw [hsz]; omega)
  · rw [hsz] at hi
    rw [splice_getD _ _ _ _ (by rw [rd_length, hBl]; omega), rd_length]
    split
    · rename_i hin
      rw [hat i hi hin.1 hin.2, rd_getD _ _ _ _ (by omega)]
    · rename_i hin
      rw [hout _ (hsing.lt (SI.In_at (by rw [hsz]; omega))) (hout' i hi hin)]
      exact hm i (by rw [hsz]; omega) ‹_›

/-- Writing a place of a writable root: bytes that represent `v`, written over the place's range
and nowhere else, represent the environment in which the place holds `v`. A view is written only
through its elements and a pair reference only through its fields. -/
theorem place_set {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n bp : Nat} {env : Env Γ} {h : Heap} (hc : p.contig = true) (hL : p.Lawful)
    (hok : p.ok env) (henv : MEnvRel h bp env ρ S) (hl : Lay bp n Γ ρ S W)
    (hW : W.getD p.root false = true) (hbn : bp + n ≤ UInt64.size) (hpv : p.ExtOk S)
    (hns : (ρ.getD p.root default).isSlot = false) (h' : Heap) :
    ∀ (v : t.carrier),
    (∀ a, a < bp + n → ¬ InR (placeA p S env) t.size a →
      h' (UInt64.ofNat a) = h (UInt64.ofNat a)) →
    Data.reprBytes v (rd h' (placeA p S env) t.size) → MEnvRel h' bp (p.set env v) ρ S := by
  induction p with
  | var m =>
    intro v hout hv
    have he : (S.getD m.idx default).ext = none := by
      rcases hpv with h | h
      · exact h
      · simp [Place.isVarAt, Place.root] at h
    have hsn := (hl.var m).snd_none he
    exact henv.set_var m v hl hW hbn hsn (fun a ha hn => hout a ha (by
        rw [SI.sz_none he] at hn; simpa [placeA] using hn))
      (by simpa [placeA] using hv) (fun e h => by rw [he] at h; cases h)
  | @field s t' p l ih =>
    intro v hout hv
    by_cases hp2 : p.isVarAt p.root = true ∧ (S.getD p.root default).snd ≠ none
    · obtain ⟨hv', hsn⟩ := hp2
      obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hv'
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hsn
      exact pair_set_field m l hL.2 henv hl hW hbn hq v hout hv
    have hnp : p.NotPair S := fun hv' => by
      cases hs : (S.getD p.root default).snd with
      | none => rfl
      | some _ => exact absurd ⟨hv', by rw [hs]; nofun⟩ hp2
    obtain ⟨⟨hl1, _, hl3⟩, _⟩ := hL.2
    have hpv' := extOk_parent_field p l hL.2 henv hl hnp
    have hg := place_get p hc hL.1 hok henv hl (fun H hH => by
      rw [(hl.root p).2.2.1 hW] at hH; cases hH) hpv' hns
    have hs2 : p.snd2 S = none := by
      cases p with
      | var m => exact Place.snd2_none _ (hnp (by simp [Place.isVarAt, Place.root]))
      | _ => rfl
    have hA : placeA (p.field l) S env = placeA p S env + lensOff l := by
      simp only [placeA, hs2]
    rw [hA] at hout hv
    refine ih hc hL.1 hok hW hpv' hns (l.set (p.get env) v)
      (fun a ha hn => hout a ha (by unfold InR at hn ⊢; omega)) ?_
    rw [rd_splice hl1 fun i hi hout' => hout _ (by have := hg.1; omega) (by unfold InR; omega)]
    exact hl3 _ _ _ _ hg.2 hv
  | @index t' n' _ p i ih =>
    intro v hout hv
    have hpv' := extOk_parent_arr p henv hl
    have hg := place_get p hc hL hok.1 henv hl (fun H hH => by
      rw [(hl.root p).2.2.1 hW] at hH; cases hH) hpv' hns
    have hj := hok.2
    generalize hjj : (i.denote env).toNat = j at hj
    have hA : placeA (p.index i) S env = placeA p S env + j * t'.size := by
      simp [placeA, hjj]
    rw [hA] at hout hv
    have hsz : (Ty.arr t' n').size = n' * t'.size := rfl
    have hjb : j * t'.size + t'.size ≤ n' * t'.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
    show MEnvRel h' bp (p.set env (vset (p.get env) (i.denote env).toNat v)) ρ S
    rw [hjj]
    refine ih hc hL hok.1 hW hpv' hns _
      (fun a ha hn => hout a ha (by unfold InR at hn ⊢; omega)) ⟨rd_length _ _ _, fun k hk => ?_⟩
    show Data.reprBytes _ (slice (rd h' (placeA p S env) (n' * t'.size)) (k * t'.size) t'.size)
    have hkb : k * t'.size + t'.size ≤ n' * t'.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
    rw [← rd_slice _ _ _ _ _ hkb]
    simp only [vset, hj, dite_true, Vector.getElem_set hj hk]
    split
    · rename_i hjk; subst hjk; exact hv
    · rename_i hjk
      have hk' : k ≠ j := fun e => hjk e.symm
      have e1 : rd h' (placeA p S env + k * t'.size) t'.size =
          rd h (placeA p S env + k * t'.size) t'.size := rd_congr fun x hx => by
        refine hout _ (by omega) ?_
        rintro ⟨h1, h2⟩
        have := elem_disj_of_ne (A := 0) (sz := t'.size) hk'; unfold Disj at this; omega
      rw [e1, rd_slice _ _ (n' * t'.size) _ _ hkb]
      exact hg.2.2 k hk
  | @slot t' n' _ p i ih =>
    intro v hout hv
    have hfull := hok.2
    by_cases hpv' : p.ExtOk S
    · have hg := place_get p hc hL hok.1 henv hl (fun H hH => by
        rw [(hl.root p).2.2.1 hW] at hH; cases hH) hpv' hns
      generalize hjj : (i.denote env).toNat = j at hfull
      have hj : j < n' := by
        rcases Nat.lt_or_ge j n' with hj | hj
        · exact hj
        · exfalso; simp [Slots.isFull, Slots.cell, vget, Nat.not_lt.mpr hj] at hfull
      have hA : placeA (p.slot i) S env = placeA p S env + j * t'.size := by
        simp [placeA, hjj]
      rw [hA] at hout hv
      have hjb : j * t'.size + t'.size ≤ n' * t'.size := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
      show MEnvRel h' bp (p.set env (Slots.setCell (p.get env) (i.denote env).toNat (some v))) ρ S
      rw [hjj]
      have hsz : (Ty.slots t' n').size = n' * t'.size := rfl
      refine ih hc hL hok.1 hW hpv' hns _
        (fun a ha hn => hout a ha (by unfold InR at hn ⊢; omega)) ⟨rd_length _ _ _, fun k hk => ?_⟩
      show Slots.cellRepr _ (slice (rd h' (placeA p S env) (n' * t'.size)) (k * t'.size) t'.size)
      have hkb : k * t'.size + t'.size ≤ n' * t'.size := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
      rw [← rd_slice _ _ _ _ _ hkb]
      simp only [Slots.setCell, Slots.cells, vset, hj, ↓reduceDIte]
      erw [Vector.getElem_set hj hk]
      split
      · rename_i hjk; subst hjk; exact hv
      · rename_i hjk
        have hk' : k ≠ j := fun e => hjk e.symm
        have e1 : rd h' (placeA p S env + k * t'.size) t'.size =
            rd h (placeA p S env + k * t'.size) t'.size := rd_congr fun x hx => by
          refine hout _ (by omega) ?_
          rintro ⟨h1, h2⟩
          have := elem_disj_of_ne (A := 0) (sz := t'.size) hk'; unfold Disj at this; omega
        rw [e1, rd_slice _ _ (n' * t'.size) _ _ hkb]
        exact hg.2.2 k hk
    · -- the parent is a view as a whole, so the place is an element of a view
      have hp : p.isVarAt p.root = true := by
        cases h : p.isVarAt p.root with
        | true => rfl
        | false => exact absurd (Or.inr h) hpv'
      obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hp
      have he : ∃ e, (S.getD m.idx default).ext = some e := by
        cases he : (S.getD m.idx default).ext with
        | none => exact absurd (Or.inl he) hpv'
        | some e => exact ⟨e, rfl⟩
      obtain ⟨e, he⟩ := he
      have hA : placeA (Place.slot (.var m) i) S env =
          (S.getD m.idx default).A + (i.denote env).toNat * t'.size := by
        simp [placeA]
      rw [hA] at hout hv
      exact view_set_cell m he hfull henv hl hW hbn v hout hv
  | range => simp [Place.contig] at hc
  | pair2 => simp [Place.contig] at hc
  | rangeS => simp [Place.contig] at hc
  | pair2S => simp [Place.contig] at hc

theorem placeRead_contig {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc) (d : Nat)
    (hc : p.contig = true) :
    placeRead p ρ d = .seq (placeAddr p ρ) (copyB (.slot RA) 0 (.slot BP) d t.size) := by
  cases p <;> first | rfl | simp [Place.contig] at hc

theorem placeWrite_contig {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc) (src : Nat)
    (hc : p.contig = true) :
    placeWrite p ρ src = .seq (placeAddr p ρ) (copyB (.slot BP) src (.slot RA) 0 t.size) := by
  cases p <;> first | rfl | simp [Place.contig] at hc

/-- A writable root's storage is in `InW`. -/
theorem InW.var : ∀ {t : Ty} {Γ : List Ty} {S : List SI} {W : List Bool} {x : Nat}
    (m : Mem t Γ), W.getD m.idx false = true → (S.getD m.idx default).In t x →
    S.length = Γ.length → InW Γ S W x
  | _, _ :: _, _ :: _, W, _, .here, hw, h, _ => Or.inl ⟨by rw [headD_eq_getD]; exact hw, h⟩
  | _, _ :: _, _ :: _, W, _, .there m, hw, h, hS => Or.inr (InW.var m
      (by rw [tail_getD]; exact hw) h (by simpa using hS))
  | _, _ :: _, [], _, _, _, _, _, hS => by simp at hS

theorem InW.place {Γ : List Ty} {t : Ty} (p : Place Γ t) {S : List SI} {W : List Bool} {x : Nat}
    (hw : W.getD p.root false = true) (h : (S.getD p.root default).In p.rootTy x)
    (hS : S.length = Γ.length) : InW Γ S W x := by
  induction p with
  | var m => exact InW.var m hw h hS
  | field p _ ih => exact ih hw h
  | index p _ ih => exact ih hw h
  | slot p _ ih => exact ih hw h
  | range p _ _ ih => exact ih hw h
  | pair2 p _ _ ih => exact ih hw h
  | rangeS m => exact InW.var m hw h hS
  | pair2S m => exact InW.var m hw h hS

/-- The root's storage of a place is away from a destination away from all variables. -/
theorem Away.root {bp o sz : Nat} {Γ : List Ty} {ρ : List Loc} {S : List SI} {t : Ty}
    (p : Place Γ t) (ha : Away bp o sz Γ ρ S) (hρ : ρ.length = Γ.length) (hS : S.length = Γ.length) :
    (S.getD p.root default).Out p.rootTy (bp + o) sz := by
  induction p with
  | var m => exact (Away.var m ha hρ hS).2
  | field p _ ih => exact ih
  | index p _ ih => exact ih
  | slot p _ ih => exact ih
  | range p _ _ ih => exact ih
  | pair2 p _ _ ih => exact ih
  | rangeS m => exact (Away.var m ha hρ hS).2
  | pair2S m => exact (Away.var m ha hρ hS).2

/-- A place that is not a view or a pair reference as a whole is not a pair reference as a whole. -/
theorem _root_.Millipede.Place.ExtOk.notPair {Γ : List Ty} {t : Ty} {S : List SI} {bp n : Nat}
    {ρ : List Loc} {W : List Bool} {p : Place Γ t} (hl : Lay bp n Γ ρ S W) (hpv : p.ExtOk S) :
    p.NotPair S := fun hv => by
  rcases hpv with h | h
  · exact (hl.root p).snd_none h
  · rw [h] at hv; cases hv

/-- Two ranges of one length without a common address are disjoint. -/
theorem disj_of_pt {a b len : Nat} (h : ∀ x, InR a len x → ¬ InR b len x) :
    a + len ≤ b ∨ b + len ≤ a := by
  rcases Nat.lt_or_ge a b with hab | hab
  · rcases Nat.lt_or_ge b (a + len) with h1 | h1
    · exact absurd ⟨by omega, by omega⟩ (h b ⟨by omega, h1⟩)
    · exact Or.inl h1
  · rcases Nat.lt_or_ge a (b + len) with h1 | h1
    · by_cases hz : len = 0
      · subst hz; omega
      · exact absurd ⟨hab, h1⟩ (h a ⟨Nat.le_refl _, by omega⟩)
    · exact Or.inr h1

/-- Two ranges without a common address are disjoint, or one of them is empty. -/
theorem disj_of_pt2 {a la b lb : Nat} (h : ∀ x, InR a la x → ¬ InR b lb x) :
    a + la ≤ b ∨ b + lb ≤ a ∨ la = 0 ∨ lb = 0 := by
  by_cases h0 : la = 0
  · exact Or.inr (Or.inr (Or.inl h0))
  by_cases h1 : lb = 0
  · exact Or.inr (Or.inr (Or.inr h1))
  rcases Nat.lt_or_ge a b with hab | hab
  · rcases Nat.lt_or_ge b (a + la) with h2 | h2
    · exact absurd ⟨Nat.le_refl _, by omega⟩ (h b ⟨by omega, h2⟩)
    · exact Or.inl h2
  · rcases Nat.lt_or_ge a (b + lb) with h2 | h2
    · exact absurd ⟨hab, h2⟩ (h a ⟨Nat.le_refl _, by omega⟩)
    · exact Or.inr (Or.inl h2)

/-- A place's bytes are away from a destination that is away from all variables. -/
theorem Away.place {bp o sz n : Nat} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool}
    {t : Ty} {env : Env Γ} {h : Heap} (p : Place Γ t) (ha : Away bp o sz Γ ρ S)
    (hl : Lay bp n Γ ρ S W) (henv : MEnvRel h bp env ρ S) (hc : p.contig = true) (hL : p.Lawful)
    (hok : p.ok env) (hpv : p.ExtOk S) {x : Nat} (hx : InR (placeA p S env) t.size x) :
    ¬ InR (bp + o) sz x := fun hd =>
  (Away.root p ha hl.length.1 hl.length.2).not_In hd (place_in p hc hL hok henv hl hpv hx)

/-- Reading a contiguous place into a destination away from the variables. -/
theorem placeRead_runs {Γ : List Ty} {t : Ty} (p : Place Γ t) {ρ : List Loc} {S : List SI}
    {W : List Bool} {n d bp : Nat} {env : Env Γ} {f : Frame} {h : Heap} (hc : p.contig = true)
    (hL : p.Lawful) (hok : p.ok env) (hnh : p.NH S) (hl : Lay bp n Γ ρ S W)
    (hd : Away bp d t.size Γ ρ S) (hdn : d + t.size ≤ n) (hbn : bp + n ≤ UInt64.size)
    (hf : f BP = UInt64.ofNat bp) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hnL : bp + n ≤ L) (hpv : p.ExtOk S) (hns : (ρ.getD p.root default).isSlot = false) :
    ∃ f', f' BP = f BP ∧ Runs κ ω L (placeRead p ρ d) f h f'
      (wr h (bp + d) (rd h (placeA p S env) t.size)) := by
  obtain ⟨f₁, hr₁, hb₁, ha₁, _⟩ := placeAddr_runs (κ := κ) (ω := ω) p hc hf henv hfe hl hnh.1 hL
    (hpv.notPair hl) hnL hbn
  have hg := place_get p hc hL hok henv hl hnh.2 hpv hns
  obtain ⟨f₂, hf₂, hr₂⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot RA) (.slot BP) (by decide)
    (by decide) t.size 0 d (placeA p S env) bp f₁ h ha₁ (hb₁.trans hf)
    (by omega) (by omega) (by
      have := disj_of_pt fun x h1 h2 => Away.place p hd hl henv hc hL hok hpv h1 h2
      omega)
    (by omega) (by omega)
  rw [placeRead_contig p ρ d hc]
  exact ⟨f₂, (hf₂ BP (by decide)).trans hb₁, Runs.seq hr₁ (by simpa using hr₂)⟩

/-! ## Whole-word fields of slot-resident variables -/

/-- The words of a whole-word field of a slot-resident structure held from slot `k`: its slots from
`k + lensOff l / 8` hold the field, by the lens's byte law on the structure's words. -/
theorem field_words {Γ : List Ty} {s t : Ty} (m : Mem s Γ) (l : Lens s t) {ρ : List Loc}
    {env : Env Γ} {f : Frame} {o k n : Nat} (hfe : FEnvRel f env ρ)
    (hρ : ρ.getD m.idx default = .slot o k n) (hL : l.Lawful) (ho : lensOff l % 8 = 0)
    (h8 : t.size % 8 = 0) (hts : t.slotTy = true) :
    lensOff l / 8 + t.slotN ≤ n ∧ s.slotTy = true ∧ n = s.slotN ∧ s.size = 8 * n ∧
      WordsRel s (env.get m) f k ∧ WordsRel t (l.get (env.get m)) f (k + lensOff l / 8) := by
  obtain ⟨hss, hnw, B, hB, hw⟩ := hfe.get m (k := k) (by rw [hρ]; rfl)
  rw [hρ, Loc.nw_slot] at hnw
  have hle := hL.1.1
  have ht8 := wordPay_size h8
  have hsz : s.size = 8 * n := by
    rcases Ty.slotTy_cases hss with ⟨h1, _, _⟩ | ⟨h8', _, _⟩
    · have := Ty.slotN_pos hts; omega
    · rw [hnw]; exact h8'
  have hBl : B.length = 8 * n := by rw [Data.reprBytes_length hB]; exact hsz
  have hfit : lensOff l / 8 + t.slotN ≤ n := by omega
  have hw' : WordsAt f k B n := by rw [hnw]; exact hw
  refine ⟨hfit, hss, hnw, hsz, ⟨B, hB, hw⟩, _, hL.1.2.1 _ _ hB, ?_⟩
  rw [← wordsBytes_eq hBl hw', show lensOff l = 8 * (lensOff l / 8) by omega, ht8,
    wordsBytes_slice _ _ _ _ _ hfit, show 8 * (lensOff l / 8) / 8 = lensOff l / 8 by omega]
  exact wordsAt_wordsBytes _ _ _

/-- The words of a structure after its field's `j` words from `k + i` are rewritten: the
structure's bytes with the field's bytes spliced in. -/
theorem wordsBytes_update {f f' : Frame} {k i j n : Nat} (hij : i + j ≤ n)
    (hout : ∀ y, k ≤ y → y < k + n → (y < k + i ∨ k + i + j ≤ y) → f' y = f y) :
    wordsBytes f' k n = splice (wordsBytes f k n) (8 * i) (wordsBytes f' (k + i) j) := by
  have e1 : wordsBytes f' k i = wordsBytes f k i :=
    wordsBytes_congr fun y hy => hout _ (by omega) (by omega) (Or.inl (by omega))
  have e2 : wordsBytes f' (k + i + j) (n - i - j) = wordsBytes f (k + i + j) (n - i - j) :=
    wordsBytes_congr fun y hy => hout _ (by omega) (by omega) (Or.inr (by omega))
  rw [show n = i + (j + (n - i - j)) by omega, wordsBytes_add, wordsBytes_add,
    wordsBytes_add f, wordsBytes_add f (k + i), e1, e2]
  simp only [splice, wordsBytes_length]
  rw [List.take_left' (by simp), ← List.append_assoc, ← List.append_assoc,
    show 8 * i + 8 * j = (wordsBytes f k i ++ wordsBytes f (k + i) j).length by simp,
    List.drop_left' rfl]

/-- A place rooted at a slot-resident variable, which the term addresses only through whole-word
fields, has a slot field. -/
theorem _root_.Millipede.Place.slotField_of {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc)
    (hs : (ρ.getD p.root default).isSlot = true) (hw : p.wordField p.root = true) :
    p.slotField ρ ≠ none := by
  cases p with
  | field q l =>
    cases q with
    | var m =>
      simp only [Place.root] at hs hw
      simp only [Place.slotField]
      cases hl : ρ.getD m.idx default with
      | slot o k n => simp [hw]
      | _ => rw [hl] at hs; simp at hs
    | _ => simp [Place.wordField] at hw
  | _ => simp [Place.wordField] at hw

/-- A read or write of a place that is not a whole-word field, under a term that addresses its root
only through whole-word fields, has its root in memory. -/
theorem SlotHyp.ns_of_field {Γ : List Ty} {t u : Ty} {e : Exp Γ u} {tm : Tl} {ρ : List Loc}
    {env : Env Γ} {f : Frame} (H : SlotHyp e tm ρ env f) (p : Place Γ t)
    (hna : e.noAddr p.root = true → p.wordField p.root = true) (hsf : p.slotField ρ = none) :
    (ρ.getD p.root default).isSlot = false := by
  cases hs : (ρ.getD p.root default).isSlot
  · rfl
  · exact absurd hsf (p.slotField_of ρ hs (hna (H.na _ hs).1))

/-- `read p` of a whole-word field of a slot-resident variable copies its slots to the destination
slots or bytes. -/
theorem msound_read_field {Γ : List Ty} {t : Ty} (p : Place Γ t) {K nw : Nat} {tm : Tl} {L : Nat}
    {W : List Bool} {ρ : List Loc} {S : List SI} {n d bp : Nat} {env : Env Γ} {k : List Kont}
    {f : Frame} {h : Heap} {w : World} {c : Nat} (hsf : p.slotField ρ = some (K, nw))
    (H : MHyp ω (.read p) tm L W ρ S n d bp env f h w) :
    MSim κ ω L ⟨lowerM (.read p) tm ρ n d, k, f, h, w, c⟩ k (TQ tm bp d ρ S t)
      (Prot bp n d (tm.dsz t) Γ S W) ((Exp.read p).exec ω κ tm.hb env w) (SProt ρ W) := by
  obtain ⟨s, m, l, o, kk, nn, rfl, hρ, ho, h8, hts, rfl, rfl⟩ := Place.slotField_some hsf
  obtain ⟨hfit, -, hnn, -, -, hwf⟩ := field_words m l H.sl.rel hρ H.lawful.2 ho h8 hts
  have hmin : min t.slotN (nn - lensOff l / 8) = t.slotN := by omega
  have hran := H.sl.ok.range m.idx kk (by rw [hρ]; rfl)
  rw [hρ, Loc.nw_slot] at hran
  have hval : (Exp.read (.field (.var m) l)).exec ω κ tm.hb env w =
      ⟨l.get (env.get m), w, (Tick.mem (Place.field (.var m) l).depth (width t)).cost κ⟩ := by
    simp [Exp.exec, Place.get, Tick.cost]
  simp only [lowerM, hsf, hmin]
  rw [hval]
  cases tm with
  | word K' =>
    simp only
    have hov : K' ≤ kk + lensOff l / 8 ∨ kk + lensOff l / 8 + t.slotN ≤ K' := by
      rcases H.tmOk.2.2 m.idx kk (by rw [hρ]; rfl) with h1 | ⟨h1, _⟩
      · rw [hρ, Loc.nw_slot] at h1; right; omega
      · left; omega
    obtain ⟨f', hr, hout, hv⟩ := movSlots_reach (κ := κ) (ω := ω) (L := L) t.slotN (x := K')
      (k := kk + lensOff l / 8) (f := f) (h := h) hov
    have hK := H.tmOk.1
    obtain ⟨B, hB, hwB⟩ := hwf
    exact MSim.tick_word H.run hr rfl rfl (hout BP (Or.inl (by simp only [FR, BP] at hK ⊢; omega)))
      (fun x _ hx => hout x (Or.inl hx))
      ⟨B, hB, wordsAt_iff.2 fun j hj => by rw [hv j hj]; exact wordsAt_iff.1 hwB j hj⟩
      fun x hx => SProt.lt_word H.tmOk hx
  | none =>
    simp only
    have hdn := H.dn0; have hnU := H.nU; have hnL := H.nL
    obtain ⟨B, hBl, hBr, hr⟩ := stSlots_words (κ := κ) (ω := ω) (L := L) (o := d) hts H.bpOk hwf
      (by omega) (by omega)
    refine MSim.tick_done H.run hr rfl rfl rfl ?_ fun x hx => ?_
    · show Data.reprBytes _ (rd _ _ t.size); rw [← hBl, rd_wr _ _ _ (by omega)]; exact hBr
    · simp only [Tl.dsz] at hx; unfold Prot InR at hx; exact wr_out (by omega) (by omega) (by omega)
  | whole _ | split _ _ => exact absurd H.conf Bool.false_ne_true

/-- `read p` copies the place to the destination. -/
theorem msound_read {Γ : List Ty} {t : Ty} (p : Place Γ t) (hc : p.contig = true) :
    MSoundAt κ ω (.read p) := by
  refine .intro fun tm L W ρ S n d bp env k f h w c H => ?_
  cases hsf : p.slotField ρ with
  | some Kn => exact msound_read_field p hsf H
  | none =>
  have hns := H.sl.ns_of_field p (fun h => by
    simpa [Exp.noAddr] using h) hsf
  cases tm with
  | word K =>
    have hts : t.slotTy = true := by simpa [Exp.Conf, hc] using H.conf
    have hnh := p.nh_of .read H.hole
    have hpv : p.ExtOk S :=
      VS.place p H.vs fun i h => Place.VSafe_isVarAt (by simpa [Exp.VSafe] using h)
    obtain ⟨f₁, hr₁, hb₁, ha₁, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) p hc H.bpOk
      H.envRel H.sl.rel H.lay hnh.1 H.lawful (hpv.notPair H.lay) H.nL H.nU
    have hg := place_get p hc H.lawful H.safe H.envRel H.lay hnh.2 hpv hns
    have hnL := H.nL; have hnU := H.nU
    obtain ⟨f', hld, hfb, hlo, hv⟩ := load_words (κ := κ) (ω := ω) (L := L) (K := K) (o := 0)
      hts ha₁ (by decide) H.tmOk.1 (by simpa using hg.2) (by omega) (by omega)
    simp only [lowerM, hsf]
    exact MSim.tick_word H.run (Reaches.seq hr₁.run hld) rfl (by simp [Exp.exec, Tick.cost])
      (hfb.trans hb₁) (fun x hx hlt => (hlo x hlt).trans (hr₁.keep x hx))
      (by simpa [Exp.exec] using hv) fun x hx => SProt.lt_word H.tmOk hx
  | none =>
    have hdn := H.dn0; have hb := H.nU; have hbL := H.nL
    have hnh := p.nh_of .read H.hole
    have hpv : p.ExtOk S := VS.place p H.vs fun i h => Place.VSafe_isVarAt (by simpa [Exp.VSafe] using h)
    obtain ⟨f', hf', hr⟩ := placeRead_runs (κ := κ) (ω := ω) (L := L) p hc H.lawful H.safe hnh H.lay
      H.away hdn (by omega) H.bpOk H.envRel H.sl.rel (by omega) hpv hns
    have hg := place_get p hc H.lawful H.safe H.envRel H.lay hnh.2 hpv hns
    simp only [lowerM, hsf]
    refine MSim.tick_done H.run hr rfl (by simp [Exp.exec, Tick.cost]) hf' ?_ ?_
    · show Data.reprBytes _ (rd _ _ t.size)
      have := rd_wr h (bp + d) (rd h (placeA p S env) t.size) (by simp; omega)
      rw [rd_length] at this; rw [this]; exact hg.2
    · intro x hx; simp only [Tl.dsz] at hx; unfold Prot InR at hx
      exact wr_out (by simp; omega) (by omega) (by simp; omega)
  | whole _ | split _ _ => exact absurd H.conf Bool.false_ne_true

/-- A value `B` staged at the watermark `bp + n` and copied to the address `A` in `RA`, below the
watermark: the bytes at `A` are then `B`, and nothing outside them changes. -/
theorem stash_copy {f : Frame} {h : Heap} {B : List UInt8} {n bp A sz : Nat}
    (hf : f BP = UInt64.ofNat bp) (ha : f RA = UInt64.ofNat A) (hBl : B.length = sz)
    (hA : A + sz ≤ bp + n) (hU : bp + n + sz ≤ UInt64.size) (hL : bp + n + sz ≤ L) :
    ∃ f', f' BP = f BP ∧
      Runs κ ω L (copyB (.slot BP) n (.slot RA) 0 sz) f (wr h (bp + n) B) f'
        (wr (wr h (bp + n) B) A B) ∧
      rd (wr (wr h (bp + n) B) A B) A sz = B ∧
      ∀ x, x < UInt64.size → ¬ InR A sz x →
        wr (wr h (bp + n) B) A B (UInt64.ofNat x) = wr h (bp + n) B (UInt64.ofNat x) := by
  obtain ⟨f', hf', hr⟩ := copyB_runs (κ := κ) (ω := ω) (L := L) (.slot BP) (.slot RA) (by decide)
    (by decide) sz n 0 bp A f (wr h (bp + n) B) hf ha (by omega) (by omega) (Or.inr (by omega))
    (by omega) (by omega)
  have hB : rd (wr h (bp + n) B) (bp + n) sz = B := by
    have := rd_wr h (bp + n) B (by omega); rwa [hBl] at this
  rw [hB, Nat.add_zero] at hr
  exact ⟨f', hf' BP (by decide), hr, by rw [← hBl, rd_wr _ _ _ (by omega)],
    fun x hx hn => wr_out (by omega) hx (by unfold InR at hn; omega)⟩

/-- `x := a; k` for a slot-resident `x` writes the atom's words straight into `x`'s slots. -/
theorem msound_assign_slot {Γ : List Ty} {t u : Ty} (m : Mem t Γ) (a : Atom Γ t) (k : Exp Γ u)
    (ih : MSoundAt κ ω k) {tm : Tl} {L : Nat} {W : List Bool} {ρ : List Loc} {S : List SI}
    {n d bp : Nat} {env : Env Γ} {kk : List Kont} {f : Frame} {h : Heap} {w : World} {c : Nat}
    {x : Nat} (hx : (ρ.getD m.idx default).slot? = some x)
    (H : MHyp ω (.assign (.var m) a k) tm L W ρ S n d bp env f h w) :
    MSim κ ω L ⟨.seq (.tick (.mem (Place.var m).depth (width t)))
        (.seq (atomSlots a ρ x (ρ.getD m.idx default).nw)
        (lowerM k tm ρ n d)), kk, f, h, w, c⟩ kk (TQ tm bp d ρ S u) (Prot bp n d (tm.dsz u) Γ S W)
      ((Exp.assign (.var m) a k).exec ω κ tm.hb env w) (SProt ρ W) := by
  have hs := H.safe
  simp only [Exp.safe] at hs
  obtain ⟨hts, hnw, -⟩ := H.sl.rel.get m hx
  rw [hnw]
  have hFR : FR ≤ x := H.sl.rel.ge m.idx x (Loc.holds_iff.2 ⟨x, hx, Nat.le_refl _, by
    rw [hnw]; have := Ty.slotN_pos hts; omega⟩)
  obtain ⟨f', hr, hfb, hout, hv⟩ := atomSlots_reach (κ := κ) (ω := ω) (L := L) a x hts H.bpOk
    H.envRel H.sl.rel H.lay (a.noHole fun i H' h' => (H.hole i H' h').1)
    (H.vs.atom a fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; simpa using h.1.2)
    H.nL H.nU (rp_lt hFR) fun m' k' _ hk' => by
      have := H.sl.ok.ov hx (by rw [hnw]; exact Ty.slotN_pos hts) hk'
      obtain ⟨_, hn', _⟩ := H.sl.rel.get m' hk'
      rw [hn'] at this; exact this
  have hxs : (ρ.getD m.idx default).isSlot = true := Loc.isSlot_iff.2 ⟨x, hx⟩
  have hfe : FEnvRel f' ((Place.var m).set env (a.denote env)) ρ :=
    H.sl.rel.set_slots m _ H.sl.ok hx hv fun y hy hn => hout y hy (by
      have := Loc.holds_false hx hn; rw [hnw] at this; exact this)
  have hW : W.getD m.idx false = true := H.restr.1
  have hK := ih.app (H.cont (by have := H.conf; cases tm <;> simp_all [Exp.Conf]) H.restr.2
    H.lawful.2 H.frozen (H.hole.sub fun _ _ h => h.2.2)
    (hfb.trans H.bpOk) (H.envRel.set_slot m _ hts hxs) hfe hs.2
    (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2)) kk
    (c + (Tick.mem (Place.var m).depth (width t)).cost κ)
  have := MSim.tick H.run (MSim.reach H.run hr hfb (fun _ _ => rfl) (fun y hy hp => by
      obtain ⟨i, hi, hwi⟩ := hp
      refine hout y hy ?_
      cases hm : (ρ.getD m.idx default).holds y with
      | true => rw [H.sl.ok.inj hi hm, hW] at hwi; cases hwi
      | false => have := Loc.holds_false hx hm; rw [hnw] at this; exact this) hK)
  exact this.of_eq (by simp [Exp.exec, Place.set]) (by simp [Exp.exec, Place.set])
    (by simp [Exp.exec, Tick.cost, Place.set])

/-- `x.f := a; k` for a whole-word field of a slot-resident `x` writes the atom's words straight
into the field's slots. -/
theorem msound_assign_field {Γ : List Ty} {t u : Ty} (p : Place Γ t) (a : Atom Γ t) (k : Exp Γ u)
    (ih : MSoundAt κ ω k) {tm : Tl} {L : Nat} {W : List Bool} {ρ : List Loc} {S : List SI}
    {n d bp : Nat} {env : Env Γ} {kk : List Kont} {f : Frame} {h : Heap} {w : World} {c : Nat}
    {K nw : Nat} (hsf : p.slotField ρ = some (K, nw))
    (H : MHyp ω (.assign p a k) tm L W ρ S n d bp env f h w) :
    MSim κ ω L ⟨.seq (.tick (.mem p.depth (width t)))
        (.seq (atomSlotsS a ρ K (min t.slotN nw)) (lowerM k tm ρ n d)), kk, f, h, w, c⟩ kk
      (TQ tm bp d ρ S u) (Prot bp n d (tm.dsz u) Γ S W)
      ((Exp.assign p a k).exec ω κ tm.hb env w) (SProt ρ W) := by
  obtain ⟨s, m, l, o, k0, nn, rfl, hρ, ho, h8, hts, rfl, rfl⟩ := Place.slotField_some hsf
  have hs := H.safe
  simp only [Exp.safe] at hs
  have hL : l.Lawful := H.lawful.1.2
  obtain ⟨hfit, hss, hnn, hsz, hws, -⟩ := field_words m l H.sl.rel hρ hL ho h8 hts
  have hmin : min t.slotN (nn - lensOff l / 8) = t.slotN := by omega
  rw [hmin]
  have hran := H.sl.ok.range m.idx k0 (by rw [hρ]; rfl)
  rw [hρ, Loc.nw_slot] at hran
  obtain ⟨f', hr, hfb, hout, hv⟩ := atomSlotsS_reach (κ := κ) (ω := ω) (L := L) a
    (k0 + lensOff l / 8) hts H.bpOk H.envRel H.sl.rel H.lay
    (a.noHole fun i H' h' => (H.hole i H' h').1)
    (H.vs.atom a fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; simpa using h.1.2)
    H.nL H.nU (by omega)
  -- the structure's new value in its slots
  obtain ⟨B, hB, hwB⟩ := hws
  obtain ⟨PB, hPB, hwP⟩ := hv
  have hBl : B.length = 8 * nn := by rw [Data.reprBytes_length hB]; exact hsz
  have ht8 := wordPay_size h8
  have hPl : PB.length = 8 * t.slotN := by rw [Data.reprBytes_length hPB]; exact ht8
  have hws' : WordsRel s (l.set (env.get m) (a.denote env)) f' k0 := by
    refine ⟨_, hL.1.2.2 _ _ _ _ hB hPB, ?_⟩
    rw [← hnn, ← wordsBytes_eq hBl (by rw [hnn]; exact hwB), show lensOff l = 8 * (lensOff l / 8) by omega,
      ← wordsBytes_eq hPl hwP, ← wordsBytes_update (n := nn) hfit fun y h1 h2 hy =>
        hout y (by omega) hy]
    exact wordsAt_wordsBytes _ _ _
  have hk : (ρ.getD m.idx default).slot? = some k0 := by rw [hρ]; rfl
  have hxs : (ρ.getD m.idx default).isSlot = true := Loc.isSlot_iff.2 ⟨k0, hk⟩
  have hFR := hran.1
  have hfe : FEnvRel f' ((Place.field (.var m) l).set env (a.denote env)) ρ :=
    H.sl.rel.set_slots m _ H.sl.ok hk hws' fun y hy hn => hout y hy (by
      have := Loc.holds_false hk hn; rw [hρ, Loc.nw_slot] at this; omega)
  have hW : W.getD m.idx false = true := H.restr.1
  have hK := ih.app (H.cont (by have := H.conf; cases tm <;> simp_all [Exp.Conf]) H.restr.2
    H.lawful.2 H.frozen (H.hole.sub fun _ _ h => h.2.2)
    (hfb.trans H.bpOk) (H.envRel.set_slot m _ hss hxs) hfe hs.2
    (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2)) kk
    (c + (Tick.mem (Place.field (.var m) l).depth (width t)).cost κ)
  have := MSim.tick H.run (MSim.reach H.run hr hfb (fun _ _ => rfl) (fun y hy hp => by
      obtain ⟨i, hi, hwi⟩ := hp
      refine hout y hy ?_
      cases hm : (ρ.getD m.idx default).holds y with
      | true => rw [H.sl.ok.inj hi hm, hW] at hwi; cases hwi
      | false =>
        have := Loc.holds_false hk hm; rw [hρ, Loc.nw_slot] at this; omega) hK)
  exact this.of_eq (by simp [Exp.exec, Place.set]) (by simp [Exp.exec, Place.set])
    (by simp [Exp.exec, Tick.cost, Place.set])

/-- `p := a; k` writes the atom to a temporary, copies it over the place and continues. -/
theorem msound_assign {Γ : List Ty} {t u : Ty} (p : Place Γ t) (a : Atom Γ t) (k : Exp Γ u)
    (hc : p.contig = true) (ih : MSoundAt κ ω k) : MSoundAt κ ω (.assign p a k) := by
  refine .intro fun tm L W ρ S n d bp env kk f h w c H => ?_
  cases hso : p.slotOf ρ with
  | some x =>
    obtain ⟨m, rfl, hx⟩ := Place.slotOf_some hso
    simp only [lowerM, hso]
    exact msound_assign_slot m a k ih hx H
  | none =>
  cases hsf : p.slotField ρ with
  | some Kn =>
    simp only [lowerM, hso, hsf]
    exact msound_assign_field p a k ih hsf H
  | none =>
  simp only [lowerM, hso, hsf]
  have hb := H.size; have hbL := H.room; have hs := H.safe; have hl := H.lay
  simp only [Exp.memNeed] at hb hbL
  simp only [Exp.safe] at hs
  have hmt := Nat.le_max_left t.size k.memNeed
  have hnh := p.nh_of .write fun i H' h' => (H.hole i H' h').2.1
  have hVs : VS S fun i => p.VSafe i && !a.isVar i := H.vs.mono fun i h => by
    simp only [Exp.VSafe, Bool.and_eq_true] at h ⊢; exact h.1
  have hpv : p.ExtOk S := VS.place p hVs fun i h => Place.VSafe_isVarAt (by
    simp only [Bool.and_eq_true] at h; exact h.1)
  have hns : (ρ.getD p.root default).isSlot = false := by
    cases hp : p.isVarAt p.root with
    | false => exact H.sl.ns_of_field p (fun h => by simp [Exp.noAddr, hp] at h; exact h.1) hsf
    | true =>
      obtain ⟨m, rfl⟩ := p.eq_var_of_isVarAt hp
      simp only [Place.slotOf] at hso
      simp only [Place.root]
      cases hl' : ρ.getD m.idx default <;> simp_all [Loc.slot?, Loc.isSlot]
  obtain ⟨f₁, B, hf₁, hBl, hBr, hr₁⟩ := atomTo_runs (κ := κ) (ω := ω) (L := L) a (d := n) hl
    (hl.away (Nat.le_refl _)) (by omega) (by omega) H.bpOk H.envRel H.sl.rel
    (a.noHole fun i H' h' => (H.hole i H' h').1) (by omega) (by omega)
    (hVs.atom a fun i h => by simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2)
  have henv₁ : MEnvRel (wr h (bp + n) B) bp env ρ S :=
    H.envRel.above hl fun x hx => wr_out (by omega) (by omega) (by omega)
  have hfb₁ : f₁ BP = UInt64.ofNat bp := (hf₁ BP (by decide) (by decide)).trans H.bpOk
  obtain ⟨f₂, hr₂, hb₂, ha₂, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) p hc hfb₁ henv₁
    (H.sl.rel.keep hr₁.keep) hl hnh.1 H.lawful.1 (hpv.notPair hl) (by omega) (by omega)
  have hg := place_get p hc H.lawful.1 hs.1 henv₁ hl hnh.2 hpv hns
  obtain ⟨f₃, hf₃, hr₃, hH'', hHout⟩ := stash_copy (κ := κ) (ω := ω) (L := L) (h := h) (n := n)
    (hb₂.trans hfb₁) ha₂ hBl (by omega) (by omega) (by omega)
  generalize wr (wr h (bp + n) B) (placeA p S env) B = H' at hr₃ hH'' hHout
  have henv₂ := place_set p hc H.lawful.1 hs.1 henv₁ hl H.restr.1 (by omega) hpv hns H'
    (a.denote env) (fun x hx hn => hHout x (by omega) hn) (by rw [hH'']; exact hBr)
  have hfe₃ : FEnvRel f₃ (p.set env (a.denote env)) ρ :=
    ((H.sl.rel.keep fun x hx => (hr₃.keep x hx).trans ((hr₂.keep x hx).trans (hr₁.keep x hx))).place_set
      p hns _)
  have hK := ih.app (H.cont (by have := H.conf; cases tm <;> simp_all [Exp.Conf]) H.restr.2
    H.lawful.2 H.frozen (H.hole.sub fun _ _ h => h.2.2)
    (hf₃.trans (hb₂.trans hfb₁)) henv₂ hfe₃ hs.2
    (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2)) kk
    (c + (Tick.mem p.depth (width t)).cost κ)
  refine (MSim.tick (Q := TQ tm bp d ρ S u) (prot := Prot bp n d (tm.dsz u) Γ S W) H.run
    (MSim.runs H.run hr₁ (hf₁ BP (by decide) (by decide))
      (fun x hx => wr_out (by omega) (by unfold Prot at hx; omega) (by unfold Prot at hx; omega))
    (MSim.runs H.run (by rw [placeWrite_contig p ρ n hc]; exact Runs.seq hr₂ hr₃)
      (hf₃.trans hb₂) (fun x hx => ?_) hK))).of_eq rfl rfl
    (by simp [Exp.exec, Tick.cost])
  obtain ⟨hx1, hx2, hx3⟩ := hx
  exact hHout x (by omega) fun hin => hx3 (InW.place p H.restr.1
    (place_in p hc H.lawful.1 hs.1 henv₁ hl hpv hin) hl.length.2)


end

end Millipede.Flat
