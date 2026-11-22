import Millipede.Compile.Lower
import Millipede.Compile.HandBack
import Millipede.Core.WfSound

/-!
# Occupancy windows

The value semantics writes the `&mut` arguments of a reference call back one after the other, so
the obligation of a later argument through a `Slots` cell, that the cell is full, is about the value
after the earlier write-backs. Bytes do not show whether a cell is full, so the byte law of the
lenses cannot say that writing one field keeps another field's cells full. The occupancy law
`Flat.LensOccs`, which every lens certificate includes, can, and this module proves the following:

* `Place.occWin_spec`: a variable followed by certified fields, with `Place.occWin = some (o, n)`,
  has the root's occupancies at `[o, o + n)`, and writing it replaces exactly those;
* `Place.setWin_spec`: a valid write changes the root's occupancies only inside its window
  `Place.setWin`, and not at all when it goes through a full cell of a `Slots` on certified fields;
* `Place.ok_of_slotsAway`: a place whose `Slots` cells are on certified fields apart from that
  window keeps its obligations across the write.

The last theorem justifies the `&mut` arguments that `RArgs.mutOk` admits after an earlier one on
the same root, such as `&mut pool.count` followed by `&mut pool.slots[k]`.
-/

namespace Millipede.Flat

/-! ## List windows -/

theorem win_eq {α : Type} {A pre G post : List α} (h : A = pre ++ G ++ post) :
    G = (A.drop pre.length).take G.length := by
  subst h; simp [List.append_assoc]

theorem win_inj {α : Type} {pre G post pre' G' post' : List α}
    (h : pre ++ G ++ post = pre' ++ G' ++ post') (h1 : pre.length = pre'.length)
    (h2 : G.length = G'.length) : pre = pre' ∧ post = post' := by
  obtain ⟨e1, e2⟩ := List.append_inj h (by simp [h1, h2])
  exact ⟨(List.append_inj e1 h1).1, e2⟩

theorem win_frame {α : Type} (pre M M' post : List α) (hM : M.length = M'.length) (o n : Nat)
    (h : o + n ≤ pre.length ∨ pre.length + M.length ≤ o) :
    ((pre ++ M ++ post).drop o).take n = ((pre ++ M' ++ post).drop o).take n := by
  rcases h with h | h
  · simp only [List.append_assoc]
    rw [List.drop_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp; omega), List.take_append_of_le_length (by simp; omega)]
  · have e1 : (pre ++ M ++ post).drop o = post.drop (o - (pre.length + M.length)) := by
      rw [List.drop_append, List.length_append]
      simp only [List.drop_eq_nil_of_le (show (pre ++ M).length ≤ o by simp; omega), List.nil_append,
]
    have e2 : (pre ++ M' ++ post).drop o = post.drop (o - (pre.length + M'.length)) := by
      rw [List.drop_append, List.length_append]
      simp only [List.drop_eq_nil_of_le (show (pre ++ M').length ≤ o by simp; omega),
        List.nil_append]
    rw [e1, e2, hM]

/-! ## Windows of places -/

section
variable {Γ : List Ty}

/-- A variable followed by certified fields has its root's occupancies at its window, and a write to
it replaces exactly those. -/
theorem _root_.Millipede.Place.occWin_spec : ∀ {t : Ty} (p : Place Γ t) {o n : Nat},
    p.occWin = some (o, n) →
    n = Data.occsN t.carrier ∧
    (∀ env : Env Γ, ∃ pre post, env.occsAt p.root = pre ++ Data.occs (p.get env) ++ post ∧
      pre.length = o) ∧
    (∀ (env : Env Γ) (y : t.carrier) pre post,
      env.occsAt p.root = pre ++ Data.occs (p.get env) ++ post → pre.length = o →
      (p.set env y).occsAt p.root = pre ++ Data.occs y ++ post)
  | _, .var m, o, n, h => by
    simp only [Place.occWin, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, fun env => ⟨[], [], by simp [Place.root, Place.get, Env.occsAt_get], rfl⟩,
      fun env y pre post he hpre => ?_⟩
    have hp : pre = [] := List.eq_nil_of_length_eq_zero hpre
    subst hp
    have hpost : post = [] := by
      have := congrArg List.length he
      simp only [Place.root, Place.get, Env.occsAt_get, List.nil_append, List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hpost
    simp [Place.root, Place.set, Env.occsAt_set_same]
  | _, .field (s := s) (t := t) p l, o, n, h => by
    simp only [Place.occWin] at h
    split at h
    · rename_i o0 n0 hp
      split at h
      · rename_i hlaw
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hn0, hget, hset⟩ := Place.occWin_spec p hp
        obtain ⟨cert⟩ := l.law.get hlaw
        obtain ⟨hle, hgo, hso⟩ := cert.2
        -- the structure's occupancies, split at the field
        have hsplit : ∀ x : s.carrier, Data.occs x =
            (Data.occs x).take (Data.occsOff s.carrier l.index) ++ Data.occs (l.get x) ++
              (Data.occs x).drop (Data.occsOff s.carrier l.index + Data.occsN t.carrier) := by
          intro x
          have hlen := Data.occsN_eq x
          rw [hgo x, List.append_assoc, ← List.drop_drop, List.take_append_drop,
            List.take_append_drop]
        have hglen : ∀ x : s.carrier, (Data.occs (l.get x)).length = Data.occsN t.carrier :=
          fun x => Data.occsN_eq _
        have htk : ∀ x : s.carrier,
            ((Data.occs x).take (Data.occsOff s.carrier l.index)).length =
              Data.occsOff s.carrier l.index := fun x => by
          simp only [List.length_take, Data.occsN_eq x]; omega
        refine ⟨rfl, fun env => ?_, fun env y pre post he hpre => ?_⟩
        · obtain ⟨pre, post, he, hpre⟩ := hget env
          rw [hsplit (p.get env)] at he
          refine ⟨pre ++ (Data.occs (p.get env)).take (Data.occsOff s.carrier l.index),
            (Data.occs (p.get env)).drop (Data.occsOff s.carrier l.index + Data.occsN t.carrier) ++
              post, ?_, by simp only [List.length_append, htk, hpre]⟩
          simp only [Place.root, Place.get] at he ⊢
          rw [he]; simp [List.append_assoc]
        · obtain ⟨pre0, post0, he0, hpre0⟩ := hget env
          simp only [Place.root, Place.get, Place.set] at he ⊢
          rw [hset env _ pre0 post0 he0 hpre0, hso]
          rw [hsplit (p.get env)] at he0
          have e : (pre0 ++ (Data.occs (p.get env)).take (Data.occsOff s.carrier l.index)) ++
              Data.occs (l.get (p.get env)) ++
              ((Data.occs (p.get env)).drop (Data.occsOff s.carrier l.index + Data.occsN t.carrier) ++
                post0) = pre ++ Data.occs (l.get (p.get env)) ++ post := by
            rw [← he, he0]; simp only [List.append_assoc]
          obtain ⟨rfl, rfl⟩ := win_inj e (by simp only [List.length_append, htk, hpre0, hpre]) rfl
          simp only [List.append_assoc]
      · cases h
    · cases h
  | _, .index (dflt := _) _ _, _, _, h => by simp [Place.occWin] at h
  | _, .slot (dflt := _) _ _, _, _, h => by simp [Place.occWin] at h
  | _, .range _ _ _, _, _, h => by simp [Place.occWin] at h
  | _, .pair2 (dflt := _) _ _ _, _, _, h => by simp [Place.occWin] at h
  | _, .rangeS _ _ _, _, _, h => by simp [Place.occWin] at h
  | _, .pair2S (dflt := _) _ _ _, _, _, h => by simp [Place.occWin] at h

/-- A write changes its root's occupancies only inside its window `Place.setWin`. -/
theorem _root_.Millipede.Place.setWin_spec : ∀ {t : Ty} (p : Place Γ t) (env : Env Γ) (y : t.carrier),
    p.ok env → ∃ pre M M' post, env.occsAt p.root = pre ++ M ++ post ∧
      (p.set env y).occsAt p.root = pre ++ M' ++ post ∧ pre.length = p.setWin.1 ∧
      M.length = p.setWin.2 ∧ M'.length = p.setWin.2
  | _, .var (t := t) m, env, y, _ =>
    ⟨[], Data.occs (env.get m), Data.occs y, [], by simp [Place.root, Env.occsAt_get],
      by simp [Place.root, Place.set, Env.occsAt_set_same], rfl, Data.occsN_eq _, Data.occsN_eq _⟩
  | _, .field (t := t) p l, env, y, hok => by
    cases hw : (Place.field p l).occWin with
    | some w =>
      obtain ⟨hn, hget, hset⟩ := Place.occWin_spec (Place.field p l) hw
      obtain ⟨pre, post, he, hpre⟩ := hget env
      have hsw : (Place.field p l).setWin = w := by simp [Place.setWin, hw]
      refine ⟨pre, _, Data.occs y, post, he, hset env y pre post he hpre, by rw [hsw, hpre], ?_, ?_⟩
      · rw [hsw, hn]; exact Data.occsN_eq _
      · rw [hsw, hn]; exact Data.occsN_eq _
    | none =>
      have hsw : (Place.field p l).setWin = p.setWin := by simp [Place.setWin, hw]
      rw [hsw]; exact Place.setWin_spec p env _ hok
  | _, .index (dflt := _) p _, env, _, hok => Place.setWin_spec p env _ hok.1
  | _, .slot (dflt := _) p i, env, y, hok => by
    cases hw : p.occWin with
    | some w =>
      -- a write through a full cell keeps the occupancies of the `Slots`, and so the root's
      obtain ⟨o, n⟩ := w
      obtain ⟨-, hget, hset⟩ := Place.occWin_spec p hw
      obtain ⟨pre, post, he, hpre⟩ := hget env
      have hsw : (Place.slot p i).setWin = (o, 0) := by simp [Place.setWin, hw]
      refine ⟨pre, [], [], Data.occs (p.get env) ++ post, by simp only [Place.root]; rw [he]; simp, ?_,
        by rw [hsw, hpre], by rw [hsw]; rfl, by rw [hsw]; rfl⟩
      simp only [Place.root, Place.set]
      rw [hset env _ pre post he hpre, Slots.occs_setCell_full _ _ _ hok.2]
      simp
    | none =>
      have hsw : (Place.slot p i).setWin = p.setWin := by simp [Place.setWin, hw]
      rw [hsw]; exact Place.setWin_spec p env _ hok.1
  | _, .range p _ _, env, _, hok => Place.setWin_spec p env _ hok.1
  | _, .pair2 (dflt := _) p _ _, env, _, hok => Place.setWin_spec p env _ hok.1
  | _, .rangeS m lo len, env, y, _ =>
    ⟨[], Data.occs (env.get m), Data.occs ((Place.set (.rangeS m lo len) env y).get m), [], by simp [Place.root, Env.occsAt_get],
      by simp [Place.root, Place.set, Env.occsAt_set_same, Env.get_set_same], rfl, Data.occsN_eq _,
      Data.occsN_eq _⟩
  | _, .pair2S (dflt := _) m i j, env, y, _ =>
    ⟨[], Data.occs (env.get m), Data.occs ((Place.set (.pair2S m i j) env y).get m), [], by simp [Place.root, Env.occsAt_get],
      by simp [Place.root, Place.set, Env.occsAt_set_same, Env.get_set_same], rfl, Data.occsN_eq _,
      Data.occsN_eq _⟩

/-- A place on certified fields whose window is apart from a write's keeps its occupancies across
the write. -/
theorem _root_.Millipede.Place.occs_get_set {t t' : Ty} (p : Place Γ t) (q : Place Γ t')
    (hr : q.root = p.root) {o n : Nat} (hq : q.occWin = some (o, n))
    (hd : p.setWin.1 + p.setWin.2 ≤ o ∨ o + n ≤ p.setWin.1) (env : Env Γ) (y : t.carrier)
    (hok : p.ok env) : Data.occs (q.get (p.set env y)) = Data.occs (q.get env) := by
  obtain ⟨hn, hget, -⟩ := Place.occWin_spec q hq
  obtain ⟨pre, M, M', post, he, he', hpre, hM, hM'⟩ := Place.setWin_spec p env y hok
  obtain ⟨pre1, post1, h1, hl1⟩ := hget env
  obtain ⟨pre2, post2, h2, hl2⟩ := hget (p.set env y)
  have g1 := win_eq h1
  have g2 := win_eq h2
  rw [Data.occsN_eq, ← hn] at g1 g2
  rw [hl1] at g1; rw [hl2] at g2
  rw [g1, g2, hr, he, he']
  exact (win_frame pre M M' post (by rw [hM, hM']) o n (by rw [hpre, hM]; omega)).symm

/-- Equal occupancies give equal full cells. -/
theorem slots_isFull_of_occs {T : Ty} {k : Nat} (a b : (Ty.slots T k).carrier)
    (h : Data.occs a = Data.occs b) (i : Nat) :
    (a : Slots _ _).isFull i = (b : Slots _ _).isFull i := by
  have h' : (a : Slots T.carrier k).cells.toList.map Option.isSome =
      (b : Slots T.carrier k).cells.toList.map Option.isSome := by
    have : [some ((a : Slots T.carrier k).cells.toList.map Option.isSome)] =
        [some ((b : Slots T.carrier k).cells.toList.map Option.isSome)] := h
    simpa using this
  unfold Slots.isFull Slots.cell vget
  split
  · rename_i hi
    have := congrArg (fun l => l[i]?) h'
    simpa [hi] using this
  · rfl

/-- The obligations of a place survive a write on its root when every `Slots` cell it goes through
is on certified fields apart from the write's window. Its indices do not read the root, by the
borrow checker's separation, and its cells stay full. -/
theorem _root_.Millipede.Place.ok_of_slotsAway {t t' : Ty} (p : Place Γ t) (env : Env Γ)
    (y : t.carrier) {π : List Sel} (hokp : p.ok env) :
    ∀ (q : Place Γ t'), q.root = p.root → q.slotsAway p.setWin = true →
      q.IdxAvoids p.root ⟨true, π⟩ → q.ok env → q.ok (p.set env y) := by
  have he : EqExcept p.root env (p.set env y) := fun m hm => (Place.get_set_ne p env y m hm).symm
  intro q
  induction q with
  | var m => intro _ _ _ _; trivial
  | field q l ih => intro hr hs hq hok; exact ih hr hs hq hok
  | index q i ih =>
    intro hr hs hq hok
    exact ⟨ih hr hs hq.1 hok.1, by rw [← i.denote_eqExcept hq.2 he]; exact hok.2⟩
  | slot q i ih =>
    intro hr hs hq hok
    simp only [Place.slotsAway, Bool.and_eq_true] at hs
    obtain ⟨hs, hw⟩ := hs
    refine ⟨ih hr hs hq.1 hok.1, ?_⟩
    split at hw
    · rename_i o n hq'
      rw [← i.denote_eqExcept hq.2 he, slots_isFull_of_occs _ _
        (Place.occs_get_set p q hr hq' (by simpa using hw) env y hokp)]
      exact hok.2
    · cases hw
  | range q lo len ih =>
    intro hr hs hq hok
    exact ⟨ih hr hs hq.1 hok.1, by
      rw [← lo.denote_eqExcept hq.2.1 he, ← len.denote_eqExcept hq.2.2 he]; exact hok.2⟩
  | pair2 q i j ih =>
    intro hr hs hq hok
    refine ⟨ih hr hs hq.1 hok.1, ?_⟩
    rw [← i.denote_eqExcept hq.2.1 he, ← j.denote_eqExcept hq.2.2 he]; exact hok.2
  | rangeS => intro _ hs; simp [Place.slotsAway] at hs
  | pair2S => intro _ hs; simp [Place.slotsAway] at hs

end

end Millipede.Flat
