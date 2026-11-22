import Millipede.Core.Safe

/-!
# Checked forms of the partial operations

Every partial operation has an obligated form, written with `!`, whose obligation `Exp.safe`
collects. An operation whose obligation can be tested at run time, such as an array index, a
slice's range or the distinct indices of a pair, also has a checked form, which tests the
obligation and returns a `Result`. A checked form is built from `Exp.guard`, which is `ok ()`
exactly when the obligation holds, and a `match` whose `ok` arm runs the obligated form.
`Exp.readChk p` reads a place this way.

The operations on `Slots` have no checked form, because their cells have no tags and so their
occupancy is known only to proofs. An arena offers checked access through its own run-time state,
such as a pool's bitmap.

The obligations of a checked read hold in every environment. A program that uses only checked operations is
therefore safe without any proof about its data. Atoms and places are weakened here, because the
obligated form in the `ok` arm runs under the two binders that the `match` introduces.
-/

namespace Millipede

/-- Weakens an atom under one more binder. -/
def Atom.shift {Γ : List Ty} {s t : Ty} : Atom Γ t → Atom (s :: Γ) t
  | .var m => .var (.there m)
  | .lit v => .lit v

@[simp] theorem Atom.denote_shift {Γ : List Ty} {s t : Ty} (a : Atom Γ t) (x : s.carrier)
    (env : Env Γ) : a.shift.denote (.cons x env) = a.denote env := by
  cases a <;> rfl

/-- Weakens a place under one more binder. -/
def Place.shift {Γ : List Ty} {s : Ty} : {t : Ty} → Place Γ t → Place (s :: Γ) t
  | _, .var m => .var (.there m)
  | _, .field p l => .field p.shift l
  | _, .index (dflt := _) p i => .index p.shift i.shift
  | _, .slot (dflt := _) p i => .slot p.shift i.shift
  | _, .range p lo len => .range p.shift lo.shift len.shift
  | _, .pair2 (dflt := _) p i j => .pair2 p.shift i.shift j.shift
  | _, .rangeS m lo len => .rangeS (.there m) lo.shift len.shift
  | _, .pair2S (dflt := _) m i j => .pair2S (.there m) i.shift j.shift

@[simp] theorem Place.get_shift {Γ : List Ty} {s t : Ty} (p : Place Γ t) (x : s.carrier)
    (env : Env Γ) : p.shift.get (.cons x env) = p.get env := by
  induction p with
  | var => rfl
  | field p l ih => simp [Place.shift, Place.get, ih]
  | index p i ih => simp [Place.shift, Place.get, ih]
  | slot p i ih => simp [Place.shift, Place.get, ih]
  | range p lo len ih => simp only [Place.shift, Place.get, Atom.denote_shift, ih]
  | pair2 p i j ih => simp [Place.shift, Place.get, ih]
  | rangeS m lo len => simp only [Place.shift, Place.get, Atom.denote_shift]; rfl
  | pair2S m i j => simp only [Place.shift, Place.get, Atom.denote_shift]; rfl

@[simp] theorem Place.ok_shift {Γ : List Ty} {s t : Ty} (p : Place Γ t) (x : s.carrier)
    (env : Env Γ) : p.shift.ok (.cons x env) ↔ p.ok env := by
  induction p with
  | var => simp [Place.shift, Place.ok]
  | field p l ih => simp [Place.shift, Place.ok, ih]
  | index p i ih => simp [Place.shift, Place.ok, ih]
  | slot p i ih => simp [Place.shift, Place.ok, ih]
  | range p lo len ih => simp [Place.shift, Place.ok, ih]
  | pair2 p i j ih => simp [Place.shift, Place.ok, ih]
  | rangeS m lo len => simp only [Place.shift, Place.ok, Atom.denote_shift]; rfl
  | pair2S m i j => simp only [Place.shift, Place.ok, Atom.denote_shift]; rfl

/-! ## Guards -/

/-! ## The checked read -/

/-- The checked form of reading a place with obligations, such as `a[i]?` or a slice element,
which is `ok v` when the obligations hold and `err ()` otherwise. -/
def Exp.readChk {Γ : List Ty} {t : Ty} (p : Place Γ t) (h : p.checkable = true) :
    Exp Γ (.result .unit t) :=
  .let_ (.guard (.valid p h))
    (.match_ (.var .here) (.err (.lit ()))
      (.let_ (.read p.shift.shift) (.ok (.var .here))))

/-- The checked read has no obligation left, so it is safe everywhere. -/
theorem Exp.readChk_safe {Γ : List Ty} {t : Ty} (ω : Oracle) (p : Place Γ t)
    (h : p.checkable = true) (env : Env Γ) (w : World) : (Exp.readChk p h).safe ω env w := by
  simp only [Exp.readChk, Exp.safe, Exp.denote, Guard.denote, Atom.denote, Env.get_here,
    Place.ok_shift]
  refine ⟨trivial, fun _ _ => trivial, fun a ha => ⟨?_, trivial⟩⟩
  by_cases hc : p.check env = true
  · exact (p.check_iff env).mp hc
  · simp [hc] at ha

end Millipede
