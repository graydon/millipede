import Millipede.Format.Code

/-!
# Format descriptions: repetitions in Millipede

A repetition `array k e max f` is held in a `Seq α M`: a count and an array of `M` elements, of
which the first `count` are the values. Its value is `Val.ofList` of the elements' values. A
generated parser reads the elements one after another in a loop; its invariant is `ItemsP`, which
is `parseItems` as `ParsedT` is `Fmt.parseT`, and `Parsed.array` turns it into the contract of the
whole repetition. The writer's invariant is `Writes` of the elements written so far, and the
validator's `ItemsC`, over `checkItems`.
-/

namespace Millipede.Format

open Millipede

/-- The value of a repetition with the elements `l`. -/
def Val.ofList : List Val → Val
  | [] => .unit
  | v :: l => .pair v (Val.ofList l)

@[simp] theorem Val.count_ofList (l : List Val) : (Val.ofList l).count = l.length := by
  induction l <;> simp_all [Val.ofList, Val.count]

theorem Val.allItems_ofList (p : Val → Bool) (l : List Val) :
    (Val.ofList l).allItems p = l.all p := by
  induction l <;> simp_all [Val.ofList, Val.allItems]

theorem Val.writeItems_ofList (w : Val → List UInt8) (l : List Val) :
    (Val.ofList l).writeItems w = (l.map w).flatten := by
  induction l <;> simp_all [Val.ofList, Val.writeItems]

/-- A repetition of at most `M` values of type `α`: the first `len` elements of `data`. -/
structure Seq (α : Type) (M : Nat) where
  len : UInt64
  data : Arr α M
deriving Data

/-- The elements of a repetition. -/
def Seq.items {α : Type} {M : Nat} (s : Seq α M) : List α := s.data.toList.take s.len.toNat

/-- The value of a repetition whose elements' values are given by `g`. -/
def Seq.toValWith {α : Type} {M : Nat} (g : α → Val) (s : Seq α M) : Val :=
  Val.ofList (s.items.map g)

/-- A repetition of at most `max` elements, each within the bounds `b`. -/
def Seq.Bound {α : Type} {M : Nat} (b : α → Prop) (max : Nat) (s : Seq α M) : Prop :=
  s.len.toNat ≤ max ∧ ∀ i (h : i < M), i < s.len.toNat → b s.data[i]

/-! ## Reading the elements one after another -/

variable {p : List UInt8 → Option (Val × List UInt8)}

theorem parseItems_snoc {c : Nat} {bs r : List UInt8} {l : List Val}
    (h : parseItems p c bs = some (Val.ofList l, r)) {v : Val} {r' : List UInt8}
    (hv : p r = some (v, r')) : parseItems p (c + 1) bs = some (Val.ofList (l ++ [v]), r') := by
  induction c generalizing bs l with
  | zero =>
    cases l with
    | nil =>
      simp only [parseItems, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [parseItems, hv, Val.ofList]
    | cons a l => simp [parseItems, Val.ofList] at h
  | succ c ih =>
    simp only [parseItems] at h
    split at h
    · cases h
    · rename_i v0 r0 hp0
      split at h
      · cases h
      · rename_i vs r1 hp1
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hl, rfl⟩ := h
        cases l with
        | nil => simp [Val.ofList] at hl
        | cons a l =>
          simp only [Val.ofList, Val.pair.injEq] at hl
          obtain ⟨rfl, rfl⟩ := hl
          rw [parseItems, hp0]
          simp only [ih hp1, Val.ofList, List.cons_append]

theorem parseItems_snoc_none {c : Nat} {bs r : List UInt8} {l : List Val}
    (h : parseItems p c bs = some (Val.ofList l, r)) (hv : p r = none) :
    parseItems p (c + 1) bs = none := by
  induction c generalizing bs l with
  | zero =>
    simp only [parseItems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [parseItems, hv]
  | succ c ih =>
    simp only [parseItems] at h
    split at h
    · cases h
    · rename_i v0 r0 hp0
      split at h
      · cases h
      · rename_i vs r1 hp1
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hl, rfl⟩ := h
        cases l with
        | nil => simp [Val.ofList] at hl
        | cons a l =>
          simp only [Val.ofList, Val.pair.injEq] at hl
          obtain ⟨rfl, rfl⟩ := hl
          rw [parseItems, hp0]
          simp only [ih hp1]

theorem parseItems_none_le {c c' : Nat} {bs : List UInt8} (h : parseItems p c bs = none)
    (hle : c ≤ c') : parseItems p c' bs = none := by
  induction c generalizing c' bs with
  | zero => simp [parseItems] at h
  | succ c ih =>
    obtain ⟨c', rfl⟩ : ∃ c'', c' = c'' + 1 := ⟨c' - 1, by omega⟩
    simp only [parseItems] at h
    split at h
    · rename_i hp0
      rw [parseItems, hp0]
    · rename_i v0 r0 hp0
      split at h
      · rename_i hp1
        rw [parseItems, hp0]
        simp only [ih (c' := c') hp1 (by omega)]
      · cases h

theorem parseItems_suffix {f : Fmt} {c : Nat} {bs v r : _}
    (h : parseItems (f.parseT 0) c bs = some (v, r)) : ∃ pre, bs = pre ++ r := by
  induction c generalizing bs v with
  | zero =>
    simp only [parseItems, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by simp [h.2]⟩
  | succ c ih =>
    simp only [parseItems] at h
    split at h
    · cases h
    · rename_i v0 r0 hp0
      split at h
      · cases h
      · rename_i vs r1 hp1
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨-, pre, rfl, -⟩ := Fmt.parseT_sound f 0 _ _ _ hp0
        obtain ⟨pre', rfl⟩ := ih hp1
        exact ⟨pre ++ pre', by simp⟩

/-- What a loop that reads `c` elements of `f` from `p` did, against `parseItems`: when they parse,
`ok` is true, `p'` is the position after them and `l` their values; otherwise `ok` is false. -/
def ItemsP (f : Fmt) (B : List UInt8) (p : UInt64) (c : Nat) (ok : Bool) (p' : UInt64)
    (l : List Val) : Prop :=
  match parseItems (f.parseT 0) c (B.drop p.toNat) with
  | none => ok = false
  | some (w, rest) => ok = true ∧ p'.toNat + rest.length = B.length ∧ Val.ofList l = w

namespace ItemsP

variable {f : Fmt} {B : List UInt8} {p p1 p2 : UInt64} {c : Nat} {l : List Val}

theorem zero (hp : p.toNat ≤ B.length) : ItemsP f B p 0 true p [] := by
  simp [ItemsP, parseItems, Val.ofList]; omega

theorem ok_eq (h : ItemsP f B p c true p1 l) (hp : p.toNat ≤ B.length) :
    parseItems (f.parseT 0) c (B.drop p.toNat) = some (Val.ofList l, B.drop p1.toNat) ∧
      p1.toNat ≤ B.length := by
  unfold ItemsP at h
  split at h
  · cases h
  · rename_i w rest he
    obtain ⟨-, hl, rfl⟩ := h
    obtain ⟨pre, hpre⟩ := parseItems_suffix he
    have hlen := congrArg List.length hpre
    simp only [List.length_drop, List.length_append] at hlen
    refine ⟨?_, by omega⟩
    rw [he]
    congr
    rw [show p1.toNat = p.toNat + pre.length by omega, ← List.drop_drop, hpre]
    simp

/-- One more element, read from where the others ended. -/
theorem snoc {ok : Bool} {x : Val} (hp : p.toNat ≤ B.length) (h : ItemsP f B p c true p1 l)
    (hx : Parsed f B p1 ok p2 x) : ItemsP f B p (c + 1) ok p2 (l ++ [x]) := by
  obtain ⟨hi, hp1⟩ := h.ok_eq hp
  cases ok
  · have := parseItems_snoc_none (p := f.parseT 0) hi (ParsedT.none_of_false hx)
    simp [ItemsP, this]
  · obtain ⟨hx', -, hp2⟩ := hx.ok_eq hp1
    have := parseItems_snoc (p := f.parseT 0) hi hx'
    simp only [ItemsP, this, true_and]
    simp; omega

/-- A failure stays a failure for more elements. -/
theorem stop {c' : Nat} {l' : List Val} (h : ItemsP f B p c false p1 l) (hle : c ≤ c') :
    ItemsP f B p c' false p2 l' := by
  have : parseItems (f.parseT 0) c (B.drop p.toNat) = none := by
    unfold ItemsP at h; split at h <;> simp_all
  simp [ItemsP, parseItems_none_le this hle]

end ItemsP

/-- A repetition parses as its count, then that many elements from where the count ended. -/
theorem Parsed.array {k : Nat} {e : Endian} {m : Nat} {f : Fmt} {B : List UInt8} {p p1 p2 : UInt64}
    {c : Nat} {ok : Bool} {l : List Val} {t : Nat} (hp : p.toNat ≤ B.length)
    (ht : Parsed (.uint k e) B p true p1 (.num c)) (hc : c ≤ m) (hi : ItemsP f B p1 c ok p2 l) :
    ParsedT (.array k e m f) t B p ok p2 (Val.ofList l) := by
  obtain ⟨hpt, -, hp1⟩ := ht.ok_eq hp
  simp only [Fmt.parseT, Option.map_eq_some_iff] at hpt
  obtain ⟨⟨n, r⟩, hr, he⟩ := hpt
  simp only [Prod.mk.injEq, Val.num.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  unfold ItemsP at hi
  unfold ParsedT
  simp only [Fmt.parseT, hr, hc, ite_true]
  exact hi

/-- A repetition stops when its count does not parse. -/
theorem Parsed.array_stop {k : Nat} {e : Endian} {m : Nat} {f : Fmt} {B : List UInt8}
    {p p1 p' : UInt64} {vt v : Val} {t : Nat} (ht : Parsed (.uint k e) B p false p1 vt) :
    ParsedT (.array k e m f) t B p false p' v := by
  have h := ParsedT.none_of_false ht
  apply ParsedT.of_none
  simp only [Fmt.parseT, Option.map_eq_none_iff] at h ⊢
  rw [h]

/-- A repetition stops when its count is above its bound. -/
theorem Parsed.array_big {k : Nat} {e : Endian} {m : Nat} {f : Fmt} {B : List UInt8}
    {p p1 p' : UInt64} {c : Nat} {v : Val} {t : Nat} (hp : p.toNat ≤ B.length)
    (ht : Parsed (.uint k e) B p true p1 (.num c)) (hc : m < c) :
    ParsedT (.array k e m f) t B p false p' v := by
  obtain ⟨hpt, -, -⟩ := ht.ok_eq hp
  simp only [Fmt.parseT, Option.map_eq_some_iff] at hpt
  obtain ⟨⟨n, r⟩, hr, he⟩ := hpt
  simp only [Prod.mk.injEq, Val.num.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  apply ParsedT.of_none
  simp only [Fmt.parseT, hr]
  rw [ite_eq_right (by omega)]

/-! ## Writing the elements one after another -/

/-- What a loop that writes the elements `l` of `f` from `p` did: it wrote their bytes at `p` and
nothing else, and `p'` is the position after them. -/
def WrittenItems {N : Nat} (f : Fmt) (d d' : Slots UInt8 N) (p p' : UInt64) (l : List Val) : Prop :=
  p'.toNat = p.toNat + ((l.map f.write).flatten).length ∧ Writes d d' p.toNat (l.map f.write).flatten

namespace WrittenItems

variable {N : Nat} {f : Fmt} {d d' d1 d2 : Slots UInt8 N} {p p' p1 p2 : UInt64} {l : List Val}

theorem zero : WrittenItems f d d p p [] := ⟨by simp, by simpa using Writes.nil d p.toNat⟩

theorem snoc {x : Val} (h : WrittenItems f d d1 p p1 l) (hx : Written f d1 d2 p1 p2 x) :
    WrittenItems f d d2 p p2 (l ++ [x]) := by
  obtain ⟨h1, w1⟩ := h
  obtain ⟨h2, w2⟩ := hx
  rw [h1] at w2 h2
  refine ⟨by simp [h2, Fmt.write]; omega, ?_⟩
  simpa [Fmt.write] using w1.append w2

theorem isFull {j : Nat} (hw : WrittenItems f d d' p p' l) (hf : d.isFull j = true) :
    d'.isFull j = true := hw.2.isFull hf


end WrittenItems

/-- A repetition writes its count, then its elements after it. -/
theorem Written.array {N : Nat} {k : Nat} {e : Endian} {m : Nat} {f : Fmt} {d d1 d2 : Slots UInt8 N}
    {p p1 p2 : UInt64} {c : Nat} {l : List Val} {t : Nat} (hl : l.length = c)
    (ht : Written (.uint k e) d d1 p p1 (.num c)) (hi : WrittenItems f d1 d2 p1 p2 l) :
    WrittenT (.array k e m f) t d d2 p p2 (Val.ofList l) := by
  obtain ⟨h1, w1⟩ := ht
  obtain ⟨h2, w2⟩ := hi
  rw [h1] at w2 h2
  subst hl
  have hw : f.write = f.writeT 0 := rfl
  rw [hw] at h2 w2
  refine ⟨by simp [Fmt.writeT, h2, Val.writeItems_ofList]; omega, ?_⟩
  simpa [Fmt.writeT, Val.writeItems_ofList] using w1.append w2

/-! ## Checking the elements one after another -/

/-- What a loop that checks `c` elements of `f` from `p` did, against `checkItems`. -/
def ItemsC (f : Fmt) (B : List UInt8) (p : UInt64) (c : Nat) (ok : Bool) (p' : UInt64) : Prop :=
  match checkItems (f.checkT 0) c (B.drop p.toNat) with
  | none => ok = false
  | some rest => ok = true ∧ p'.toNat + rest.length = B.length

theorem parseItems_ofList {c : Nat} {bs : List UInt8} {v : Val} {r : List UInt8}
    (h : parseItems p c bs = some (v, r)) : ∃ l, v = Val.ofList l := by
  induction c generalizing bs v with
  | zero =>
    simp only [parseItems, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by simp [← h.1, Val.ofList]⟩
  | succ c ih =>
    simp only [parseItems] at h
    split at h
    · cases h
    · rename_i v0 r0 hp0
      split at h
      · cases h
      · rename_i vs r1 hp1
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨l, rfl⟩ := ih hp1
        exact ⟨v0 :: l, rfl⟩

namespace ItemsC

variable {f : Fmt} {B : List UInt8} {p p1 p2 : UInt64} {c : Nat} {ok : Bool}

theorem iff_items : ItemsC f B p c ok p1 ↔ ∃ l, ItemsP f B p c ok p1 l := by
  unfold ItemsC ItemsP
  rw [checkItems_eq (p := f.parseT 0) (fun bs => Fmt.checkT_eq f 0 bs)]
  cases h : parseItems (f.parseT 0) c (B.drop p.toNat) with
  | none => exact ⟨fun h => ⟨[], h⟩, fun ⟨_, h⟩ => h⟩
  | some r =>
    obtain ⟨w, rest⟩ := r
    obtain ⟨l, rfl⟩ := parseItems_ofList h
    exact ⟨fun h => ⟨l, h.1, h.2, rfl⟩, fun ⟨_, h1, h2, _⟩ => ⟨h1, h2⟩⟩

theorem zero (hp : p.toNat ≤ B.length) : ItemsC f B p 0 true p :=
  iff_items.mpr ⟨[], ItemsP.zero hp⟩

theorem snoc (hp : p.toNat ≤ B.length) (h : ItemsC f B p c true p1)
    (hx : Checked f B p1 ok p2) : ItemsC f B p (c + 1) ok p2 := by
  obtain ⟨l, h⟩ := iff_items.mp h
  obtain ⟨x, hx⟩ := CheckedT.iff_parsed.mp hx
  exact iff_items.mpr ⟨_, h.snoc hp hx⟩

theorem stop {c' : Nat} (h : ItemsC f B p c false p1) (hle : c ≤ c') :
    ItemsC f B p c' false p2 := by
  obtain ⟨l, h⟩ := iff_items.mp h
  exact iff_items.mpr ⟨[], h.stop hle⟩

end ItemsC

theorem Checked.array {k : Nat} {e : Endian} {m : Nat} {f : Fmt} {B : List UInt8}
    {p p1 p2 : UInt64} {c : Nat} {ok : Bool} {t : Nat} (hp : p.toNat ≤ B.length)
    (ht : Parsed (.uint k e) B p true p1 (.num c)) (hc : c ≤ m) (hi : ItemsC f B p1 c ok p2) :
    CheckedT (.array k e m f) t B p ok p2 := by
  obtain ⟨l, hi⟩ := ItemsC.iff_items.mp hi
  exact CheckedT.of_parsed (Parsed.array hp ht hc hi)

theorem Checked.array_stop {k : Nat} {e : Endian} {m : Nat} {f : Fmt} {B : List UInt8}
    {p p1 p' : UInt64} {vt : Val} {t : Nat} (ht : Parsed (.uint k e) B p false p1 vt) :
    CheckedT (.array k e m f) t B p false p' :=
  CheckedT.of_parsed (Parsed.array_stop (v := .unit) ht)

theorem Checked.array_big {k : Nat} {e : Endian} {m : Nat} {f : Fmt} {B : List UInt8}
    {p p1 p' : UInt64} {c : Nat} {t : Nat} (hp : p.toNat ≤ B.length)
    (ht : Parsed (.uint k e) B p true p1 (.num c)) (hc : m < c) :
    CheckedT (.array k e m f) t B p false p' :=
  CheckedT.of_parsed (Parsed.array_big (v := .unit) hp ht hc)


/-! ## The invariant of a generated element loop -/

theorem take_vset_succ {α : Type} {M : Nat} (o : Vector α M) {j : Nat} (x : α) (h : j < M) :
    (vset o j x).toList.take (j + 1) = o.toList.take j ++ [x] := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_take, Vector.length_toList] at h1
  by_cases e : i = j
  · subst e
    rw [List.getElem_append_right (by simp; omega)]
    simp [vset, h]
  · rw [List.getElem_append_left (by simp; omega)]
    simp [vset, h, Ne.symm e]

theorem vset_getElem_ne {α : Type} {M : Nat} (o : Vector α M) {i j : Nat} (x : α) (hi : i < M)
    (h : i ≠ j) : (vset o j x)[i] = o[i] := by
  unfold vset; split <;> simp [Ne.symm h]

theorem vset_getElem_same {α : Type} {M : Nat} (o : Vector α M) {j : Nat} (x : α) (hj : j < M) :
    (vset o j x)[j] = x := by
  simp [vset, hj]

/-- The invariant of the loop of a generated element parser after `j` elements: while the
elements parse, `ItemsP` of the first `j` elements of `o`, the position within `sl` and the
elements within their bounds `b`; after one that does not, `ItemsP` that fails. -/
def ItemsInv {α : Type} {M : Nat} (f : Fmt) (g : α → Val) (b : α → Prop) (B : List UInt8)
    (p0 : UInt64) (j : Nat) (good : Bool) (p : UInt64) (o : Vector α M) : Prop :=
  (good = true → ItemsP f B p0 j true p ((o.toList.take j).map g) ∧ p.toNat ≤ B.length ∧
    ∀ i (h : i < M), i < j → b o[i]) ∧
  (good = false → ItemsP f B p0 j false p [])

namespace ItemsInv

variable {α : Type} {M : Nat} {f : Fmt} {g : α → Val} {b : α → Prop} {B : List UInt8}
  {p0 p p' : UInt64} {j : Nat} {o : Vector α M}

theorem init (hp : p0.toNat ≤ B.length) : ItemsInv f g b B p0 0 true p0 o :=
  ⟨fun _ => ⟨ItemsP.zero hp, hp, fun _ _ h => absurd h (by omega)⟩, fun h => nomatch h⟩

theorem pos_le (h : ItemsInv f g b B p0 j true p o) : p.toNat ≤ B.length := (h.1 rfl).2.1

/-- One element parsed into `o[j]`. -/
theorem call {ok : Bool} {x : α} (hp0 : p0.toNat ≤ B.length) (h : ItemsInv f g b B p0 j true p o)
    (hj : j < M) (hx : Parsed f B p ok p' (g x)) (hb : ok = true → p'.toNat ≤ B.length ∧ b x) :
    ItemsInv f g b B p0 (j + 1) ok p' (vset o j x) := by
  obtain ⟨hi, -, hbs⟩ := h.1 rfl
  have hs := hi.snoc hp0 hx
  unfold ItemsInv
  rw [take_vset_succ o x hj, List.map_append, List.map_singleton]
  cases ok
  · exact ⟨fun h => (nomatch h), fun _ => hs.stop (Nat.le_refl _)⟩
  · refine ⟨fun _ => ⟨hs, (hb rfl).1, fun i hi' hij => ?_⟩, fun h => nomatch h⟩
    by_cases e : i = j
    · subst e; rw [vset_getElem_same o x hj]; exact (hb rfl).2
    · rw [vset_getElem_ne o x hi' e]; exact hbs i hi' (by omega)

/-- An element skipped after a failure. -/
theorem skip (h : ItemsInv f g b B p0 j false p o) : ItemsInv f g b B p0 (j + 1) false p o :=
  ⟨fun h' => (nomatch h'), fun _ => (h.2 rfl).stop (by omega)⟩

/-- The contract of the loop, after `n` elements. -/
theorem done {good : Bool} {n : Nat} (h : ItemsInv f g b B p0 n good p o) :
    ItemsP f B p0 n good p ((o.toList.take n).map g) ∧
      (good = true → p.toNat ≤ B.length ∧ ∀ i (h : i < M), i < n → b o[i]) := by
  cases good
  · exact ⟨(h.2 rfl).stop (Nat.le_refl _), fun h => nomatch h⟩
  · obtain ⟨hi, hp, hb⟩ := h.1 rfl
    exact ⟨hi, fun _ => ⟨hp, hb⟩⟩

end ItemsInv


theorem take_succ_vget {α : Type} {M : Nat} (a : Vector α M) {j : Nat} (d : α) (h : j < M) :
    a.toList.take (j + 1) = a.toList.take j ++ [vget a j d] := by
  rw [List.take_add_one]
  simp [vget, h]

/-- The invariant of the loop of a generated element writer after `j` elements: the bytes of the
first `j` elements of `a` written from `p0`, at most `sz` bytes each, with the cells below `len`
full. -/
def WItemsInv {α : Type} {M N : Nat} (f : Fmt) (g : α → Val) (sz len : Nat) (a : Vector α M)
    (d0 : Slots UInt8 N) (p0 : UInt64) (j : Nat) (d : Slots UInt8 N) (p : UInt64) : Prop :=
  WrittenItems f d0 d p0 p ((a.toList.take j).map g) ∧ p.toNat ≤ p0.toNat + j * sz ∧
    ∀ k < len, d.isFull k = true

namespace WItemsInv

variable {α : Type} {M N : Nat} {f : Fmt} {g : α → Val} {sz len : Nat} {a : Vector α M}
  {d0 d d' : Slots UInt8 N} {p0 p p' : UInt64} {j : Nat}

theorem init (hf : ∀ k < len, d0.isFull k = true) : WItemsInv f g sz len a d0 p0 0 d0 p0 :=
  ⟨by simpa using WrittenItems.zero, by simp, hf⟩

/-- One element written. -/
theorem call [Inhabited α] (h : WItemsInv f g sz len a d0 p0 j d p) (hj : j < M)
    (hx : Written f d d' p p' (g (vget a j default)) ∧ p'.toNat ≤ p.toNat + sz) :
    WItemsInv f g sz len a d0 p0 (j + 1) d' p' := by
  obtain ⟨hw, hp, hf⟩ := h
  refine ⟨?_, by rw [Nat.succ_mul]; omega, fun k hk => hx.1.isFull (hf k hk)⟩
  rw [take_succ_vget a default hj, List.map_append, List.map_singleton]
  exact hw.snoc hx.1

theorem done {n : Nat} (h : WItemsInv f g sz len a d0 p0 n d p) :
    WrittenItems f d0 d p0 p ((a.toList.take n).map g) ∧ p.toNat ≤ p0.toNat + n * sz :=
  ⟨h.1, h.2.1⟩

end WItemsInv


/-- The invariant of the loop of a generated element validator after `j` elements. -/
def CItemsInv (f : Fmt) (B : List UInt8) (p0 : UInt64) (j : Nat) (good : Bool) (p : UInt64) :
    Prop :=
  (good = true → ItemsC f B p0 j true p ∧ p.toNat ≤ B.length) ∧
  (good = false → ItemsC f B p0 j false p)

namespace CItemsInv

variable {f : Fmt} {B : List UInt8} {p0 p p' : UInt64} {j : Nat}

theorem init (hp : p0.toNat ≤ B.length) : CItemsInv f B p0 0 true p0 :=
  ⟨fun _ => ⟨ItemsC.zero hp, hp⟩, fun h => (nomatch h)⟩

theorem pos_le (h : CItemsInv f B p0 j true p) : p.toNat ≤ B.length := (h.1 rfl).2

/-- One element checked. -/
theorem call {ok : Bool} (hp0 : p0.toNat ≤ B.length) (h : CItemsInv f B p0 j true p)
    (hx : Checked f B p ok p') (hb : ok = true → p'.toNat ≤ B.length) :
    CItemsInv f B p0 (j + 1) ok p' := by
  have hs := (h.1 rfl).1.snoc hp0 hx
  cases ok
  · exact ⟨fun h => (nomatch h), fun _ => hs⟩
  · exact ⟨fun _ => ⟨hs, hb rfl⟩, fun h => (nomatch h)⟩

/-- An element skipped after a failure. -/
theorem skip (h : CItemsInv f B p0 j false p) : CItemsInv f B p0 (j + 1) false p :=
  ⟨fun h' => (nomatch h'), fun _ => (h.2 rfl).stop (by omega)⟩

theorem done {good : Bool} {n : Nat} (h : CItemsInv f B p0 n good p) :
    ItemsC f B p0 n good p ∧ (good = true → p.toNat ≤ B.length) := by
  cases good
  · exact ⟨h.2 rfl, fun h => (nomatch h)⟩
  · exact ⟨(h.1 rfl).1, fun _ => (h.1 rfl).2⟩

end CItemsInv

end Millipede.Format
