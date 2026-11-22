import Millipede.Compile.LowerPair2

/-!
# Scoped borrows as pointers

A borrow `borrowShr p body k`, written `&p`, or `borrowMut p body k`, written `&mut p`, stores the
address of `p` in an 8-byte slot at the watermark. The binder's location is `Loc.ref` and its
storage is `p`'s storage, so nothing is copied when the borrow begins or ends.

Under `&p` the body reads `p` in place, and nothing writes `p` while the body runs. The lender is
outside the body's block and so read-only, the binder is a `&` binder and never written, and every
other writable variable's storage is disjoint from the lender's.

Under `&mut p` the body writes `p` in place through the binder, so the lender's source value at `p`
is stale until the write-back when the borrow ends. The refinement records the lent place as a hole
in the lender, whose value is then represented by its bytes outside the hole only. Every access the
body makes to the lender avoids the hole, because the borrow checker forbids the use of an
overlapping place and places with non-overlapping paths have disjoint storage. The body hands back
the binder itself in place, so when the borrow ends the bytes of the place represent the
handed-back value, and the memory represents the write-back `p.set env v` without any copy.

The design of references is described in doc/design/memory.md.
-/

namespace Millipede.Flat

/-! ## Reference slots -/

/-- `x` is in some variable's pointer slot. -/
def RefSlot (bp : Nat) : List Ty → List Loc → Nat → Prop
  | _ :: ts, l :: ρ, x => (∃ o w, l.ptr = some (o, w) ∧ InR (bp + o) w x) ∨ RefSlot bp ts ρ x
  | _, _, _ => False

/-- The root variable of a place. -/
def _root_.Millipede.Place.rootMem {Γ : List Ty} : {t : Ty} → (p : Place Γ t) → Mem p.rootTy Γ
  | _, .var m => m
  | _, .field p _ => p.rootMem
  | _, .index (dflt := _) p _ => p.rootMem
  | _, .slot (dflt := _) p _ => p.rootMem
  | _, .range p _ _ => p.rootMem
  | _, .pair2 (dflt := _) p _ _ => p.rootMem
  | _, .rangeS m _ _ => m
  | _, .pair2S (dflt := _) m _ _ => m

@[simp] theorem _root_.Millipede.Place.rootMem_idx {Γ : List Ty} {t : Ty} (p : Place Γ t) :
    p.rootMem.idx = p.root := by
  induction p with
  | var m => rfl
  | field p _ ih => exact ih
  | index p _ ih => exact ih
  | slot p _ ih => exact ih
  | range p _ _ ih => exact ih
  | pair2 p _ _ ih => exact ih
  | rangeS => rfl
  | pair2S => rfl

/-! ## Pushing a reference binder -/

/-- Every pointer slot is away from `[A, A + sz)`. -/
def RefsAway (bp A sz : Nat) : List Ty → List Loc → Prop
  | _ :: ts, l :: ρ => (∀ o w, l.ptr = some (o, w) → Disj (bp + o) w A sz) ∧ RefsAway bp A sz ts ρ
  | _, _ => True

theorem RefsAway.of_get {bp A sz : Nat} : ∀ {Γ : List Ty} {ρ : List Loc},
    (∀ (T : Ty) (m : Mem T Γ) (o w : Nat), (ρ.getD m.idx default).ptr = some (o, w) →
      Disj (bp + o) w A sz) →
    RefsAway bp A sz Γ ρ
  | t :: ts, l :: ρ, h => ⟨fun o w e => h t .here o w (by simpa [Mem.idx] using e),
      RefsAway.of_get fun T m o w e => h T (.there m) o w (by simpa [Mem.idx] using e)⟩
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial

/-- Storage inside one piece of a variable's storage is away from every pointer slot. -/
theorem Lay.refsAway {bp n : Nat} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool}
    {T : Ty} (hl : Lay bp n Γ ρ S W) (m : Mem T Γ) {A sz : Nat}
    (hh : (S.getD m.idx default).Holds T A sz) : RefsAway bp A sz Γ ρ := by
  refine RefsAway.of_get fun T' m' o w e => ?_
  by_cases he : m'.idx = m.idx
  · exact ((hl.var m).ptrOut o w (by rw [← he]; exact e)).holds hh
  · exact ((hl.pair m' m he).2.1 o w e).holds hh

/-- A reference binder for the storage `[A, A + sz)` below the watermark, with its slot at `o ≥ n`.
The storage is all of a value of type `s`, or the extent `E` of a slice view. The layout extends
when every pointer slot is away from that storage and, if the binder is writable, that storage is
no variable's visible storage. -/
theorem Lay.pushRefE {bp n : Nat} (s : Ty) (b : Bool) (E : Option Nat) {Γ : List Ty} {ρ : List Loc}
    {S : List SI} {W : List Bool} {o m A : Nat} (hl : Lay bp n Γ ρ S (Flat.noW W)) (ho : n ≤ o)
    (hom : o + 8 ≤ m)
    (hA : A + (SI.mk A none E none).sz s ≤ bp + n)
    (hrs : RefsAway bp A ((SI.mk A none E none).sz s) Γ ρ)
    (hw : b = true → ∀ x, InR A ((SI.mk A none E none).sz s) x → ¬ Vis bp Γ ρ S x) :
    Lay bp m (s :: Γ) (.ref o :: ρ) (⟨A, none, E, none⟩ :: S) (b :: Flat.noW W) := by
  refine ⟨⟨by simp [Loc.off, Loc.size]; omega, ⟨rfl, show A + (SI.mk A none E none).sz s ≤ bp + m by omega,
    Or.inr (show A + (SI.mk A none E none).sz s ≤ bp + o by omega)⟩, fun _ => rfl,
    fun H h => by cases h⟩, ?_, hl.mono (by omega)⟩
  show CompatAll bp s (.ref o) ⟨A, none, E, none⟩ b Γ ρ S (Flat.noW W)
  induction Γ generalizing ρ S W with
  | nil => trivial
  | cons t ts ih =>
    cases ρ with
    | nil => trivial
    | cons l ρ =>
      cases S with
      | nil => trivial
      | cons s' S =>
        have h1 := hl.1.slotLe
        have h2 := hl.1.below
        have hrest := hl.2.2
        rw [noW_tail] at hrest
        refine ⟨⟨Or.inr (show l.off + l.size t ≤ o by omega), (fun o' w e => ?_),
          (fun o' w e => by rw [SI.Out_mk]; exact hrs.1 o' w e),
          (fun hb x hx hx' => ?_), (fun hb x hx hx' => ?_)⟩, ?_⟩
        · simp only [Loc.ptr, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          exact h2.out (by omega)
        · rw [SI.In_mk] at hx
          exact Classical.byContradiction fun hc => hw hb x hx (Or.inl ⟨hx', hc⟩)
        · rw [noW_headD] at hb; cases hb
        · rw [noW_tail]
          exact ih hrest hrs.2 (fun hb x hx hv => hw hb x hx (Or.inr (Or.inr hv)))

/-- A reference binder for the storage `[A, A + s.size)`, which is `Lay.pushRefE` without an
extent. -/
theorem Lay.pushRef {bp n : Nat} (s : Ty) (b : Bool) {Γ : List Ty} {ρ : List Loc} {S : List SI}
    {W : List Bool} {o m A : Nat} (hl : Lay bp n Γ ρ S (Flat.noW W)) (ho : n ≤ o) (hom : o + 8 ≤ m)
    (hA : A + s.size ≤ bp + n) (hrs : RefsAway bp A s.size Γ ρ)
    (hw : b = true → ∀ x, InR A s.size x → ¬ Vis bp Γ ρ S x) :
    Lay bp m (s :: Γ) (.ref o :: ρ) (⟨A, none, none, none⟩ :: S) (b :: Flat.noW W) :=
  Lay.pushRefE s b none hl ho hom (by simpa using hA) (by simpa using hrs) (by simpa using hw)

/-! ## Holes -/

/-- Give variable number `i` the hole `H`. -/
def setHoleAt : List SI → Nat → Hole → List SI
  | [], _, _ => []
  | s :: S, 0, H => { s with hole := some H } :: S
  | s :: S, i + 1, H => s :: setHoleAt S i H

theorem setHoleAt_getD_A : ∀ (S : List SI) (i j : Nat) (H : Hole),
    ((setHoleAt S i H).getD j default).A = (S.getD j default).A
  | [], _, _, _ => rfl
  | _ :: _, 0, 0, _ => rfl
  | _ :: _, 0, _ + 1, _ => rfl
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: S, i + 1, j + 1, H => by simpa [setHoleAt] using setHoleAt_getD_A S i j H

theorem setHoleAt_getD_ext : ∀ (S : List SI) (i j : Nat) (H : Hole),
    ((setHoleAt S i H).getD j default).ext = (S.getD j default).ext
  | [], _, _, _ => rfl
  | _ :: _, 0, 0, _ => rfl
  | _ :: _, 0, _ + 1, _ => rfl
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: S, i + 1, j + 1, H => by simpa [setHoleAt] using setHoleAt_getD_ext S i j H

theorem setHoleAt_getD_snd : ∀ (S : List SI) (i j : Nat) (H : Hole),
    ((setHoleAt S i H).getD j default).snd = (S.getD j default).snd
  | [], _, _, _ => rfl
  | _ :: _, 0, 0, _ => rfl
  | _ :: _, 0, _ + 1, _ => rfl
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: S, i + 1, j + 1, H => by simpa [setHoleAt] using setHoleAt_getD_snd S i j H

theorem setHoleAt_getD_at (S : List SI) (i j : Nat) (H : Hole) (k : Nat) :
    ((setHoleAt S i H).getD j default).at k = (S.getD j default).at k := by
  simp only [SI.at, setHoleAt_getD_snd, setHoleAt_getD_A]

theorem setHoleAt_getD_In (S : List SI) (i j : Nat) (H : Hole) (T : Ty) (x : Nat) :
    ((setHoleAt S i H).getD j default).In T x ↔ (S.getD j default).In T x := by
  simp only [SI.In, setHoleAt_getD_at, SI.sz, SI.lim, setHoleAt_getD_ext]

theorem VS.setHole {S : List SI} {P : Nat → Bool} (i : Nat) (H : Hole) (h : VS S P) :
    VS (setHoleAt S i H) P := fun j hj => h j (by rwa [setHoleAt_getD_ext] at hj)

theorem setHoleAt_getD_same : ∀ (S : List SI) (i : Nat) (H : Hole), i < S.length →
    ((setHoleAt S i H).getD i default).hole = some H
  | _ :: _, 0, _, _ => rfl
  | _ :: S, i + 1, H, h => by simpa [setHoleAt] using setHoleAt_getD_same S i H (by simp at h; omega)
  | [], _, _, h => by simp at h

theorem setHoleAt_getD_ne : ∀ (S : List SI) (i j : Nat) (H : Hole), j ≠ i →
    (setHoleAt S i H).getD j default = S.getD j default
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: S, i + 1, j + 1, H, h => by
    simpa [setHoleAt] using setHoleAt_getD_ne S i j H (by omega)

theorem CompatAll.setHole_noW {bp : Nat} {t : Ty} {l : Loc} {s : SI} {w : Bool} :
    ∀ {ts : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} (i : Nat) (H : Hole),
    CompatAll bp t l s w ts ρ S W → CompatAll bp t l s false ts ρ (setHoleAt S i H) (noW W)
  | _ :: _, _ :: _, s' :: S, W, i, H, h => by
    cases i with
    | zero =>
      refine ⟨?_, by rw [noW_tail]; exact h.2.mono_noW⟩
      rw [noW_headD]
      exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, (fun e => by cases e), (fun e => by cases e)⟩
    | succ i =>
      refine ⟨by rw [noW_headD]; exact h.1.noW, ?_⟩
      rw [noW_tail]; exact CompatAll.setHole_noW i H h.2
  | [], _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _, _, _ => trivial

theorem CompatAll.headHole_noW {bp : Nat} {t : Ty} {l : Loc} {s : SI} {w : Bool} (H : Option Hole) :
    ∀ {ts : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool},
    CompatAll bp t l s w ts ρ S W → CompatAll bp t l { s with hole := H } false ts ρ S (Flat.noW W)
  | _ :: _, _ :: _, _ :: _, W, h => by
    refine ⟨by rw [noW_headD]; exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, (fun e => by cases e),
      (fun e => by cases e)⟩, ?_⟩
    rw [noW_tail]; exact CompatAll.headHole_noW H h.2
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _ => trivial

/-- Lending a place of a writable variable with `&mut`. Inside the borrow, the variable is
read-only and the place is its hole. -/
theorem Lay.setHole {bp n : Nat} : ∀ {T : Ty} {Γ : List Ty} {ρ : List Loc} {S : List SI}
    {W : List Bool} (m : Mem T Γ) (H : Hole), Lay bp n Γ ρ S W →
    (∀ x, InR H.a H.len x → (S.getD m.idx default).In T x) →
    HoleOK (S.getD m.idx default) T H →
    Lay bp n Γ ρ (setHoleAt S m.idx H) (Flat.noW W)
  | _, _ :: _, _ :: _, s :: S, W, .here, H, hl, h1, hok => by
    refine ⟨?_, ?_, by rw [noW_tail]; exact hl.2.2.noW⟩
    · rw [noW_headD]
      exact ⟨hl.1.1, hl.1.2.1, (fun e => by cases e), fun H' e => by
        simp only [setHoleAt, Option.some.injEq] at e; subst e
        exact ⟨h1, hok⟩⟩
    · rw [noW_headD, noW_tail]
      exact CompatAll.headHole_noW (some H) hl.2.1
  | _, _ :: _, _ :: _, s :: S, W, .there m, H, hl, h1, hok => by
    simp only [Mem.idx] at h1 hok ⊢
    refine ⟨by rw [noW_headD]; exact hl.1.noW, ?_, ?_⟩
    · rw [noW_headD, noW_tail]
      exact CompatAll.setHole_noW m.idx H hl.2.1
    · rw [noW_tail]
      have e : ((s :: S).getD (m.idx + 1) default) = S.getD m.idx default := by simp
      rw [e] at h1 hok
      exact Lay.setHole m H hl.2.2 h1 hok
  | _, _ :: _, [], _, _, _, _, hl, _, _ => hl.elim
  | _, _ :: _, _ :: _, [], _, _, _, hl, _, _ => hl.elim

/-- A representation without the hole is one with it. -/
theorem MEnvRel.setHole {h : Heap} {bp : Nat} : ∀ {Γ : List Ty} {env : Env Γ} {ρ : List Loc}
    {S : List SI} (i : Nat) (H : Hole), (S.getD i default).hole = none →
    MEnvRel h bp env ρ S → MEnvRel h bp env ρ (setHoleAt S i H)
  | _, .nil, _, _, _, _, _, _ => trivial
  | _, .cons _ _, _ :: _, s :: S, 0, H, hs, hr => by
    obtain ⟨hv, hp, hr⟩ := hr
    have hs' : s.hole = none := hs
    refine ⟨fun hns => ?_, hp, hr⟩
    obtain ⟨B, hB, hm, hx⟩ := hv hns
    exact ⟨B, hB, fun i hi _ => hm i (by simpa [SI.sz, SI.lim] using hi) (by simp [SI.inHole, hs']),
      fun e he hsn => hx e he hsn⟩
  | _, .cons _ _, _ :: _, s :: S, i + 1, H, hs, hr =>
    ⟨hr.1, hr.2.1, MEnvRel.setHole i H (by simpa using hs) hr.2.2⟩
  | _, .cons _ _, [], _, _, _, _, hr => hr.elim
  | _, .cons _ _, _ :: _, [], _, _, _, hr => hr.elim

theorem _root_.Millipede.Mem.idx_lt : ∀ {t : Ty} {Γ : List Ty} (m : Mem t Γ), m.idx < Γ.length
  | _, _ :: _, .here => by simp [Mem.idx]
  | _, _ :: _, .there m => by have := Mem.idx_lt m; simp [Mem.idx]; omega

/-! ## Visible storage, by variable -/

theorem Vis.mem {bp : Nat} : ∀ {Γ : List Ty} {ρ : List Loc} {S : List SI} {x : Nat},
    Vis bp Γ ρ S x →
    (∃ (T : Ty) (m : Mem T Γ), (S.getD m.idx default).In T x ∧
      ¬ (S.getD m.idx default).inHole x) ∨ RefSlot bp Γ ρ x
  | t :: _, _ :: _, _ :: _, _, Or.inl h => Or.inl ⟨t, .here, h⟩
  | _ :: _, _ :: _, _ :: _, _, Or.inr (Or.inl h) => Or.inr (Or.inl h)
  | _ :: _, _ :: _, _ :: _, _, Or.inr (Or.inr h) => by
    rcases Vis.mem h with ⟨T, m, hm⟩ | hr
    · exact Or.inl ⟨T, .there m, by simpa [Mem.idx] using hm⟩
    · exact Or.inr (Or.inr hr)
  | [], _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim

theorem RefsAway.not_refSlot {bp A sz : Nat} : ∀ {Γ : List Ty} {ρ : List Loc} {x : Nat},
    RefsAway bp A sz Γ ρ → InR A sz x → ¬ RefSlot bp Γ ρ x
  | _ :: _, _ :: _, x, ha, hx, Or.inl ⟨o, w, e, h⟩ => by
    have := ha.1 o w e; unfold InR Disj at *; omega
  | _ :: _, _ :: _, x, ha, hx, Or.inr h => RefsAway.not_refSlot ha.2 hx h
  | [], _, _, _, _, h => h
  | _ :: _, [], _, _, _, h => h

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-- Storing the address in `RA` into the slot at `bp + n`. -/
theorem store_ptr {n bp A : Nat} {f : Frame} {h : Heap} (hf : f BP = UInt64.ofNat bp)
    (hRA : f RA = UInt64.ofNat A) (hL : bp + n + 8 ≤ L) (hU : bp + n + 8 ≤ UInt64.size) :
    Runs κ ω L (.store .w64 (.slot BP) (UInt64.ofNat n) (.slot RA)) f h f
      (wr h (bp + n) (natBytes 8 (UInt64.ofNat A).toNat)) :=
  Runs.congr (Runs.store _ _ _ _ _ _ (acc_off (b := 8) hL (by omega) hf)) rfl (by
    simp only [eval_slot, hf, hRA, ofNat_add_ofNat]; rw [store64_eq])

theorem ptr_bytes (h : Heap) (bp n A : Nat) (hU : bp + n + 8 ≤ UInt64.size) :
    decodeLE (rd (wr h (bp + n) (natBytes 8 (UInt64.ofNat A).toNat)) (bp + n) 8) = UInt64.ofNat A := by
  have := rd_wr h (bp + n) (natBytes 8 (UInt64.ofNat A).toNat) (by simp; omega)
  rw [natBytes_length] at this
  rw [this, decodeLE_natBytes8]

theorem _root_.Millipede.Place.slotW_contig {Γ : List Ty} {t : Ty} (p : Place Γ t)
    (hc : p.contig = true) : p.slotW = 8 := by
  cases p <;> first | rfl | simp [Place.contig] at hc

theorem refStore_contig {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc) (n : Nat)
    (hc : p.contig = true) :
    refStore p ρ n = .store .w64 (.slot BP) (UInt64.ofNat n) (.slot RA) := by
  cases p <;> first | rfl | simp [Place.contig] at hc

theorem _root_.Millipede.Place.refLoc_contig {Γ : List Ty} {t : Ty} (p : Place Γ t) (n : Nat)
    (hc : p.contig = true) : p.refLoc n = .ref n := by
  cases p <;> first | rfl | simp [Place.contig] at hc

theorem conf_borrowShr {Γ : List Ty} {t u v : Ty} {p : Place Γ t} {body : Exp (t :: Γ) u}
    {k : Exp (u :: Γ) v} {tm : Tl} (h : (Exp.borrowShr p body k).Conf tm = true) :
    k.Conf tm.up = true := by
  cases tm <;> first | exact k.conf_none | simpa [Exp.Conf] using h

theorem conf_borrowMut {Γ : List Ty} {t u v : Ty} {p : Place Γ t} {body : Exp (t :: Γ) (.pair u t)}
    {k : Exp (u :: Γ) v} {tm : Tl} (h : (Exp.borrowMut p body k).Conf tm = true) :
    k.Conf tm.up = true := by
  cases tm <;> first | exact k.conf_none | simpa [Exp.Conf] using h

/-- The reference binder's location: one address, or the two addresses of a pair. -/
def RefLoc (lr : Nat → Loc) : Prop := ∀ o, lr o = .ref o ∨ lr o = .ref2 o

theorem RefLoc.slot? {lr : Nat → Loc} (h : RefLoc lr) (o : Nat) : (lr o).slot? = none := by
  rcases h o with e | e <;> rw [e] <;> rfl

theorem RefLoc.slotRel {lr : Nat → Loc} (h : RefLoc lr) (o : Nat) (f : Frame) (t : Ty)
    (v : t.carrier) : SlotRel f t v (lr o) := by
  rcases h o with e | e <;> rw [e] <;> trivial

/-- The setup of a borrow of `p` in a state that satisfies `MHyp`. The place's address code and
the reference store reach `f₂` and `H₁`, keeping `BP` and changing no byte below the watermark. The
reference binder, at location `lr n` with run-time knowledge `s₀`, is laid out on top of the
lender's storage `S'`, which is `S` for a shared borrow and `S` with the lent place's hole for a
mutable one, and `H₁` represents the environment with the place's value bound. -/
structure BorrowSetup (p : Place Γ t) (lr : Nat → Loc) (wd : Nat) (b : Bool) (ρ : List Loc)
    (S S' : List SI) (W : List Bool) (n bp : Nat) (env : Env Γ) (f : Frame) (h : Heap)
    (f₂ : Frame) (H₁ : Heap) (s₀ : SI) : Prop where
  addr : ∃ f₁, Runs κ ω L (placeAddr p ρ) f h f₁ h ∧ f₁ BP = f BP ∧
    Runs κ ω L (refStore p ρ n) f₁ h f₂ H₁ ∧ f₂ BP = f BP
  below : ∀ x, x < bp + n → H₁ (UInt64.ofNat x) = h (UInt64.ofNat x)
  lay : Lay bp (n + wd) (t :: Γ) (lr n :: ρ) (s₀ :: S') (b :: noW W)
  nohole : s₀.hole = none
  envRel : MEnvRel H₁ bp (.cons (p.get env) env) (lr n :: ρ) (s₀ :: S')

theorem BorrowSetup.runs {p : Place Γ t} {lr : Nat → Loc} {wd : Nat} {b : Bool} {ρ : List Loc}
    {S S' : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap}
    {f₂ : Frame} {H₁ : Heap} {s₀ : SI} (B : BorrowSetup (κ := κ) (ω := ω) (L := L) p lr wd b ρ S S'
      W n bp env f h f₂ H₁ s₀) {u : Ty} {rest : Stmt} {k : List Kont} {w : World} {c : Nat}
    {Q : u.carrier → Frame → Heap → Prop} {prot : Nat → Prop} {r : Out u.carrier}
    {pf : Nat → Prop} (hw : w.halted = false) (hp : ∀ x, prot x → x < bp + n)
    (hr : MSim κ ω L ⟨rest, k, f₂, H₁, w, c⟩ k Q prot r pf) :
    MSim κ ω L ⟨.seq (placeAddr p ρ) (.seq (refStore p ρ n) rest), k, f, h, w, c⟩ k Q prot r pf :=
  have ⟨_, hr₁, hb₁, hst, hb₂⟩ := B.addr
  MSim.runs hw hr₁ hb₁ (fun _ _ => rfl)
    (MSim.runs hw hst (hb₂.trans hb₁.symm) (fun x hx => B.below x (hp x hx)) hr)

theorem BorrowSetup.keep {p : Place Γ t} {lr : Nat → Loc} {wd : Nat} {b : Bool} {ρ : List Loc}
    {S S' : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame} {h : Heap}
    {f₂ : Frame} {H₁ : Heap} {s₀ : SI} (B : BorrowSetup (κ := κ) (ω := ω) (L := L) p lr wd b ρ S S'
      W n bp env f h f₂ H₁ s₀) : ∀ x, FR ≤ x → f₂ x = f x :=
  have ⟨_, hr₁, _, hst, _⟩ := B.addr
  fun x hx => (hst.keep x hx).trans (hr₁.keep x hx)

/-- A shared borrow `let x := { let r = &p; body }; k`, given the setup of its reference with the
lender's storage unchanged. The body runs with the reference bound read-only, then `k` with the
body's value. The kinds of reference differ only in the setup. -/
theorem msound_borrowShr_of {Γ : List Ty} {t u v : Ty} (p : Place Γ t) (body : Exp (t :: Γ) u)
    (k : Exp (u :: Γ) v) {wd : Nat} {lr : Nat → Loc} (hW : p.slotW = wd)
    (hloc : ∀ o, p.refLoc o = lr o) (hlr : RefLoc lr)
    (setup : ∀ {tm L W ρ S n d bp env f h w}, MHyp ω (.borrowShr p body k) tm L W ρ S n d bp env f h w →
      ∃ f₂ H₁ s₀, BorrowSetup (κ := κ) (ω := ω) (L := L) p lr wd false ρ S S W n bp env f h f₂ H₁ s₀ ∧
        (s₀.ext = none ∨ body.VSafe 0 .none = true))
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowShr p body k) := by
  refine .intro fun tm L W ρ S n d bp env kk f h w c H => ?_
  have hb := H.size; have hbL := H.room
  simp only [lowerM, hW, hloc]
  simp only [Exp.memNeed, hW] at hb hbL
  have hCk := conf_borrowShr H.conf
  have hmb := Nat.le_max_left body.memNeed k.memNeed
  have hmk := Nat.le_max_right body.memNeed k.memNeed
  obtain ⟨f₂, H₁, s₀, B, hV0⟩ := setup H
  have hfb₂ : f₂ BP = UInt64.ofNat bp := (B.addr.choose_spec.2.2.2).trans H.bpOk
  have hfe₂ := H.sl.rel.keep B.keep
  have hV := H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.1.2
  have hB := ihb.app (tm := .none) (L := L) (W := false :: noW W) (n := n + wd + u.size)
    (d := n + wd) (env := .cons (p.get env) env) (h := H₁) ⟨by simp, trivial,
      H.restr.1, H.lawful.2.1, H.frozen.2.1, H.hole.push _ B.nohole fun _ _ h => h.2.1,
      B.lay.mono (by omega), by simp [Tl.dsz], by simp only [Tl.dsz]; exact B.lay.away (Nat.le_refl _),
      by omega, hfb₂, B.envRel, H.safe.2.1, H.run, by omega,
      hV0.elim (fun e => VS.push _ e hV) (fun e => VS.push_view _ e hV),
      H.sl.pushT (lr n) (by simp [hlr.slot?]) ⟨hlr.slotRel n _ _ _, hfe₂⟩ (by simp [Loc.isSlot_iff, hlr.slot?])
        (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.1.2)
        (by simp [Tl.vars])⟩
    (.seq (lowerM k tm.up (.own (n + wd) :: ρ) (n + wd + u.size) d) :: kk)
    (c + (Tick.ref p.depth).cost κ)
  have hbind := MSim.bindF (pf := SProt ρ W) (prot := Prot bp n d (tm.dsz v) Γ S W)
    (prot₂ := Prot bp n d (tm.dsz v) Γ S W)
    (Q := TQ tm bp d ρ S v)
    (r₂ := k.exec ω κ tm.up.hb (.cons (body.exec ω κ .copy (.cons (p.get env) env) w).val env)
      (body.exec ω κ .copy (.cons (p.get env) env) w).world) hB
    (fun hh => exec_halted ω κ k _ _ hh)
    (fun a ha => by
      obtain ⟨h1, h2, h3⟩ := ha
      refine ⟨⟨by omega, by simp only [Tl.dsz, InR]; omega, ?_⟩, ⟨h1, h2, h3⟩⟩
      rintro (⟨e, _⟩ | h5)
      · cases e
      · exact InW.noW h5)
    (fun x hx => ⟨hx.noW.push _ _, hx⟩)
    (fun f₃ m₂ hf₃ hfk hv hm hh => by
      simp only at hf₃ hm hfk
      exact .unpush (by omega) (ihk.app (H.push _ (n' := n + wd) (by omega) hCk H.restr.2
        H.lawful.2.2 H.frozen.2.2 (H.hole.push _ rfl fun _ _ h => h.2.2) (by omega) (by omega)
        (hf₃.trans hfb₂)
        (H.envRel.congr fun x hx => by
          have hxn := H.lay.vis_lt hx
          rw [hm x ⟨by omega, by simp only [Tl.dsz, InR]; omega, by
            rintro (⟨e, _⟩ | h5)
            · cases e
            · exact InW.noW h5⟩]
          exact B.below _ hxn) (hfe₂.prot fun x hx hp => hfk x hx (hp.push _ _)) hv
        (by rw [Exp.exec_val, Exp.exec_world]; exact H.safe.2.2)
        (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2) hh)
        kk _))
  refine (MSim.tick (Q := TQ tm bp d ρ S v) (prot := Prot bp n d (tm.dsz v) Γ S W) H.run
    (B.runs H.run (fun x hx => hx.1) (MSim.seq_intro H.run hbind))).of_eq (by simp [Exp.exec, Tl.hb_up]) (by simp [Exp.exec, Tl.hb_up])
    (by simp only [Exp.exec, Tick.cost, width, Ty.words, Tl.hb_up, Tl.hb_none]; omega)

/-- `let x := { let r = &p; body }; k`, where the binder holds `p`'s address. -/
theorem msound_borrowShr {Γ : List Ty} {t u v : Ty} (p : Place Γ t) (body : Exp (t :: Γ) u)
    (k : Exp (u :: Γ) v) (hc : p.contig = true) (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowShr p body k) := by
  refine msound_borrowShr_of p body k (p.slotW_contig hc) (p.refLoc_contig · hc)
    (fun _ => .inl rfl) (fun {tm L W ρ S n d bp env f h w} H => ?_) ihb ihk
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed, p.slotW_contig hc] at hb hbL
  have hnh := p.nh_of .read fun i H' h' => (H.hole i H' h').1
  have hpv : p.ExtOk S := VS.place p H.vs fun i h => by
    simp only [Exp.VSafe, Bool.and_eq_true] at h; exact Place.VSafe_isVarAt h.1.1
  have hns : (ρ.getD p.root default).isSlot = false := H.sl.ns_of_addr (by simp [Exp.noAddr])
  obtain ⟨f₁, hr₁, hb₁, ha₁, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) p hc H.bpOk H.envRel
    H.sl.rel H.lay hnh.1 H.lawful.1 (hpv.notPair H.lay) (by omega) (by omega)
  have hg := place_get p hc H.lawful.1 H.safe.1 H.envRel H.lay hnh.2 hpv hns
  have hhold := (place_at p hc H.lawful.1 H.safe.1 H.envRel H.lay hpv).2.2.2
  generalize placeA p S env = A at hg ha₁ hhold
  have hst := store_ptr (κ := κ) (ω := ω) (L := L) (h := h) (n := n) (hb₁.trans H.bpOk) ha₁
    (by omega) (by omega)
  have hH₁o : ∀ x, x < bp + n → wr h (bp + n) (natBytes 8 (UInt64.ofNat A).toNat) (UInt64.ofNat x) =
      h (UInt64.ofNat x) := fun x hx => wr_out (by simp; omega) (by omega) (by simp; omega)
  refine ⟨_, _, ⟨A, none, none, none⟩, ⟨⟨f₁, hr₁, hb₁, by rw [refStore_contig p ρ n hc]; exact hst, hb₁⟩,
    hH₁o, Lay.pushRef t false H.lay.noW (Nat.le_refl _) (Nat.le_refl _) hg.1
      (H.lay.refsAway p.rootMem (by simpa only [Place.rootMem_idx] using hhold)) (fun e => by cases e),
    rfl, ⟨fun _ => VarRel.of_exact ?_, ?_, H.envRel.above H.lay hH₁o⟩⟩, .inl rfl⟩
  · show Data.reprBytes _ (rd _ A t.size)
    rw [rd_congr fun j hj => hH₁o _ (by omega)]; exact hg.2
  · exact ptr_bytes h bp n A (by omega)

/-- Lending a place: the lender's storage with the hole `Hl`, which lies inside the root's
storage, is a layout, and the bytes `X` of the borrowed storage, in the root's storage and in the
hole but not in a reference slot, are visible to no variable. -/
theorem Lay.lend {bp n : Nat} {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {t : Ty}
    (hl : Lay bp n Γ ρ S W) (p : Place Γ t) (Hl : Hole)
    (hin : ∀ x, InR Hl.a Hl.len x → (S.getD p.root default).In p.rootTy x)
    (hok : HoleOK (S.getD p.root default) p.rootTy Hl) (hW : W.getD p.root false = true)
    (X : Nat → Prop) (hXr : ∀ x, X x → (S.getD p.root default).In p.rootTy x)
    (hXh : ∀ x, X x → InR Hl.a Hl.len x) (hXs : ∀ x, X x → ¬ RefSlot bp Γ ρ x) :
    Lay bp n Γ ρ (setHoleAt S p.root Hl) (Flat.noW W) ∧
      ∀ x, X x → ¬ Vis bp Γ ρ (setHoleAt S p.root Hl) x := by
  have hlt : p.root < S.length := by rw [hl.length.2, ← Place.rootMem_idx]; exact Mem.idx_lt _
  refine ⟨by simpa only [Place.rootMem_idx] using (Lay.setHole p.rootMem Hl hl
    (by simpa only [Place.rootMem_idx] using hin)
    (by simp only [Place.rootMem_idx]; exact fun {_ _} => hok)),
    fun x hx hv => ?_⟩
  rcases hv.mem with ⟨T', m, hin', hnot⟩ | hr
  · rw [setHoleAt_getD_In] at hin'
    by_cases he : m.idx = p.root
    · apply hnot; rw [he]; unfold SI.inHole; rw [setHoleAt_getD_same _ _ _ hlt]; exact hXh x hx
    · rw [setHoleAt_getD_ne _ _ _ _ he] at hnot
      have hc' := hl.pair p.rootMem m (by rw [Place.rootMem_idx]; exact Ne.symm he)
      rw [Place.rootMem_idx] at hc'
      exact hnot (hc'.2.2.2.1 hW x (hXr x hx) hin')
  · exact hXs x hx hr

/-- A mutable borrow `let x := { let r = &mut p; body }; k`, given the setup of its reference on
top of the lender with the lent place's hole `Hl`, and given `back`, which says how memory that
represents the handed-back value at the reference's storage represents the write-back. The body
runs with the reference bound and hands it back in place, then `k` runs with the body's first
component. The kinds of reference differ only in the setup and the write-back. -/
theorem msound_borrowMut_of {Γ : List Ty} {t u v : Ty} (p : Place Γ t)
    (body : Exp (t :: Γ) (.pair u t)) (k : Exp (u :: Γ) v) {wd : Nat} {lr : Nat → Loc}
    (hW : p.slotW = wd) (hloc : ∀ o, p.refLoc o = lr o) (hlr : RefLoc lr)
    (hCb : body.Conf (borrowTl u t) = true)
    (setup : ∀ {tm L W ρ S n d bp env f h w}, MHyp ω (.borrowMut p body k) tm L W ρ S n d bp env f h w →
      ∃ f₂ H₁ s₀ Hl, BorrowSetup (κ := κ) (ω := ω) (L := L) p lr wd true ρ S (setHoleAt S p.root Hl)
          W n bp env f h f₂ H₁ s₀ ∧ Hl.path = p.path ∧
        (s₀.ext = none ∨ body.VSafe 0 (borrowTl u t) = true) ∧
        (∀ x, s₀.In t x → InW Γ S W x) ∧
        ∀ (m : Heap) (bs : List UInt8),
          (∀ x, x < bp + n → ¬ s₀.In t x → m (UInt64.ofNat x) = h (UInt64.ofNat x)) →
          Data.reprBytes (body.exec ω κ .split (.cons (p.get env) env) w).val.2 (slice bs (sndOff u t) t.size) →
          slice bs (sndOff u t) (s₀.lim t.size) = rdS m s₀ (s₀.lim t.size) →
          MEnvRel m bp (p.set env (body.exec ω κ .split (.cons (p.get env) env) w).val.2) ρ S)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowMut p body k) := by
  refine .intro fun tm L W ρ S n d bp env kk f h w c H => ?_
  have hb := H.size; have hbL := H.room
  simp only [lowerM, hW, hloc]
  simp only [Exp.memNeed, hW] at hb hbL
  have hCk := conf_borrowMut H.conf
  have hmb := Nat.le_max_left body.memNeed k.memNeed
  have hmk := Nat.le_max_right body.memNeed k.memNeed
  have hns : (ρ.getD p.root default).isSlot = false := H.sl.ns_of_addr (by simp [Exp.noAddr])
  obtain ⟨f₂, H₁, s₀, Hl, B, hpath, hV0, hsW, hback⟩ := setup H
  have hfb₂ : f₂ BP = UInt64.ofNat bp := (B.addr.choose_spec.2.2.2).trans H.bpOk
  have hfe₂ := H.sl.rel.keep B.keep
  have hlt : p.root < S.length := by
    rw [H.lay.length.2, ← Place.rootMem_idx]; exact Mem.idx_lt _
  have hHb : HoleAv body (s₀ :: setHoleAt S p.root Hl) := by
    intro i H' hH'
    cases i with
    | zero => simp [B.nohole] at hH'
    | succ i =>
      simp only [List.getD_cons_succ] at hH'
      by_cases he : i = p.root
      · subst he
        rw [setHoleAt_getD_same _ _ _ hlt] at hH'
        cases hH'; rw [hpath]; exact H.frozen.1
      · rw [setHoleAt_getD_ne _ _ _ _ he] at hH'
        exact (H.hole i H' hH').2.1
  have hV := VS.setHole p.root Hl (H.vs.mono fun i h => by
    simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.1.2)
  have hB := ihb.app (L := L) (W := true :: noW W) (n := n + wd + u.size) (d := n + wd)
    (env := .cons (p.get env) env) (h := H₁) ⟨hCb, by intro c' hc'; simp at hc'; subst hc'; rfl,
      H.restr.2.1, H.lawful.2.1, H.frozen.2.1, hHb, B.lay.mono (by omega), by simp [Tl.dsz],
      by simp only [Tl.dsz]; exact B.lay.away (Nat.le_refl _), by omega, hfb₂, B.envRel, H.safe.2.1,
      H.run, by omega, hV0.elim (fun e => VS.push _ e hV) (fun e => VS.push_view _ e hV),
      H.sl.pushT (lr n) (by simp [hlr.slot?]) ⟨hlr.slotRel n _ _ _, hfe₂⟩ (by simp [Loc.isSlot_iff, hlr.slot?])
        (fun i h => by simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.1.2)
        (by simp [Tl.vars])⟩
    (.seq (lowerM k tm.up (.own (n + wd) :: ρ) (n + wd + u.size) d) :: kk)
    (c + (Tick.ref p.depth).cost κ)
  rw [show (borrowTl u t).hb = .split from rfl] at hB
  generalize hBV : body.exec ω κ .split (.cons (p.get env) env) w = rb at hB hback
  have hbind := MSim.bindF (pf := SProt ρ W) (prot := Prot bp n d (tm.dsz v) Γ S W)
    (prot₂ := Prot bp n d (tm.dsz v) Γ S W)
    (Q := TQ tm bp d ρ S v)
    (r₂ := k.exec ω κ tm.up.hb (.cons rb.val.1 (p.set env rb.val.2)) rb.world) hB
    (fun hh => exec_halted ω κ k _ _ hh)
    (fun a ha => by
      obtain ⟨h1, h2, h3⟩ := ha
      refine ⟨⟨by omega, by simp only [Tl.dsz, InR]; omega, ?_⟩, ⟨h1, h2, h3⟩⟩
      rintro (⟨_, h5⟩ | h5)
      · exact h3 (hsW a h5)
      · exact InW.noW h5)
    (fun x hx => ⟨hx.noW.push _ _, hx⟩)
    (fun f₃ m₂ hf₃ hfk hv hm hh => by
      simp only at hf₃ hm hfk
      obtain ⟨bs, hbs, hs0, hsc⟩ := hv
      have hsc' := hsc _ (List.mem_singleton_self _)
      simp only [List.getD_cons_zero, CompAt, hlr.slot?] at hsc'
      obtain ⟨hv1, hv2⟩ := pair_repr rb.val bs hbs
      rw [hs0] at hv1
      have henv₂ := hback m₂ bs (fun x hx hn => by
          rw [hm x ⟨by omega, by simp only [Tl.dsz, InR]; omega, by
            rintro (⟨_, h5⟩ | h5)
            · exact hn h5
            · exact InW.noW h5⟩]
          exact B.below x hx) hv2 hsc'
      have hsk := H.safe.2.2
      rw [← Exp.exec_val ω κ, ← Exp.exec_world ω κ, hBV] at hsk
      exact .unpush (by omega) (ihk.app (H.push _ (n' := n + wd) (by omega) hCk H.restr.2.2
        H.lawful.2.2 H.frozen.2.2 (H.hole.push _ rfl fun _ _ h => h.2.2) (by omega) (by omega)
        (hf₃.trans hfb₂) henv₂
        ((hfe₂.prot fun x hx hp => hfk x hx (hp.push _ _)).place_set p hns _) hv1 hsk
        (H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2) hh)
        kk _))
  refine (MSim.tick (Q := TQ tm bp d ρ S v) (prot := Prot bp n d (tm.dsz v) Γ S W) H.run
    (B.runs H.run (fun x hx => hx.1) (MSim.seq_intro H.run hbind))).of_eq ?_ ?_ ?_
  · simp [Exp.exec, hBV, Tl.hb_up]
  · simp [Exp.exec, hBV, Tl.hb_up]
  · simp only [Exp.exec, Tick.cost, width, Ty.words, hBV, Tl.hb_up]; omega

/-- `let x := { let r = &mut p; body }; k`, where the binder holds `p`'s address. The body updates
`p` in place and hands the binder back in place, and when the borrow ends the memory represents the
write-back. -/
theorem msound_borrowMut {Γ : List Ty} {t u v : Ty} (p : Place Γ t) (body : Exp (t :: Γ) (.pair u t))
    (k : Exp (u :: Γ) v) (hc : p.contig = true) (hCb : body.Conf (borrowTl u t) = true)
    (ihb : MSoundAt κ ω body) (ihk : MSoundAt κ ω k) :
    MSoundAt κ ω (.borrowMut p body k) := by
  refine msound_borrowMut_of p body k (p.slotW_contig hc) (p.refLoc_contig · hc)
    (fun _ => .inl rfl) hCb (fun {tm L W ρ S n d bp env f h w} H => ?_) ihb ihk
  have hb := H.size; have hbL := H.room
  simp only [Exp.memNeed, p.slotW_contig hc] at hb hbL
  have hnh := p.nh_of .write fun i H' h' => (H.hole i H' h').1
  have hpv : p.ExtOk S := VS.place p H.vs fun i h => by
    simp only [Exp.VSafe, Bool.and_eq_true] at h; exact Place.VSafe_isVarAt h.1.1
  have hns : (ρ.getD p.root default).isSlot = false := H.sl.ns_of_addr (by simp [Exp.noAddr])
  obtain ⟨f₁, hr₁, hb₁, ha₁, _⟩ := placeAddr_runs (κ := κ) (ω := ω) (L := L) p hc H.bpOk H.envRel
    H.sl.rel H.lay hnh.1 H.lawful.1 (hpv.notPair H.lay) (by omega) (by omega)
  have hg := place_get p hc H.lawful.1 H.safe.1 H.envRel H.lay hnh.2 hpv hns
  obtain ⟨-, -, hat, hhold⟩ := place_at p hc H.lawful.1 H.safe.1 H.envRel H.lay hpv
  have hin := fun x (hx : InR (placeA p S env) t.size x) =>
    place_in p hc H.lawful.1 H.safe.1 H.envRel H.lay hpv hx
  generalize hA : placeA p S env = A at hg ha₁ hat hhold hin
  have hst := store_ptr (κ := κ) (ω := ω) (L := L) (h := h) (n := n) (hb₁.trans H.bpOk) ha₁
    (by omega) (by omega)
  have hH₁o : ∀ x, x < bp + n → wr h (bp + n) (natBytes 8 (UInt64.ofNat A).toNat) (UInt64.ofNat x) =
      h (UInt64.ofNat x) := fun x hx => wr_out (by simp; omega) (by omega) (by simp; omega)
  have hrA : RefsAway bp A t.size Γ ρ :=
    H.lay.refsAway p.rootMem (by simpa only [Place.rootMem_idx] using hhold)
  obtain ⟨hlh, hvis⟩ := H.lay.lend p ⟨A, t.size, p.path⟩ hin
    (holeOK_of_place p env _ A hc H.lawful.1 H.safe.1 (H.lay.root p).ok hat) H.restr.1 _ hin
    (fun _ hx => hx) (fun _ hx => hrA.not_refSlot hx)
  refine ⟨_, _, ⟨A, none, none, none⟩, ⟨A, t.size, p.path⟩,
    ⟨⟨f₁, hr₁, hb₁, by rw [refStore_contig p ρ n hc]; exact hst, hb₁⟩, hH₁o,
      Lay.pushRef t true hlh (Nat.le_refl _) (Nat.le_refl _) hg.1 hrA (fun _ => hvis), rfl,
      ⟨fun _ => VarRel.of_exact ?_, ptr_bytes h bp n A (by omega),
        (H.envRel.above H.lay hH₁o).setHole _ _ ((H.lay.root p).2.2.1 H.restr.1)⟩⟩,
    rfl, .inl rfl, fun x hx => InW.place p H.restr.1 (hin x (by simpa using hx)) H.lay.length.2,
    fun m bs hm hv hsc => ?_⟩
  · show Data.reprBytes _ (rd _ A t.size)
    rw [rd_congr fun j hj => hH₁o _ (by omega)]; exact hg.2
  · rw [SI.lim_mk_none, rdS_none (s := ⟨A, none, none, none⟩) rfl] at hsc
    rw [hsc] at hv
    exact place_set p hc H.lawful.1 H.safe.1 H.envRel H.lay H.restr.1 (by omega) hpv hns m _
      (fun x hx hn => hm x hx (by rw [hA] at hn; simpa using hn)) (by rw [hA]; exact hv)

end

end Millipede.Flat
