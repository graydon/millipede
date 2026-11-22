import Millipede.Core.Exp

/-!
# Places as lenses

The value semantics has no pointers, so a place such as `x`, `p.f` or `p[i]` is a path into the
value of a variable. `Place.get` reads the value at the path, and `Place.set` rebuilds the
variable's value along the path and stores it in the environment.

Partial selectors are total in this semantics. An index out of range reads `default` and writes
nothing, and an empty `Slots` cell reads `default`. The obligations of a place are the
proposition `Place.ok`, which `Exp.safe` collects, and `Place.check` decides them for the checked
forms. A slice `p[lo..lo+len]` is a view whose value `vview` holds the elements from `lo` in its
first `len` cells and leaves the other cells empty, and `vunview` writes the full cells back to
the array at `lo + k`.

The file also defines `Env.set`, the helpers on arrays, `Slots` and views, the meaning of call
arguments with modes and of guards, and the meaning of extern arguments. `RArgs.denote` reads
call arguments, and `RArgs.writeBack` stores the callee's updated `mut` parameters back into the
argument places.
-/

namespace Millipede

/-! ## Environments -/

/-- Replaces the value of a variable. -/
def Env.set {t : Ty} : {Γ : List Ty} → Env Γ → Mem t Γ → t.carrier → Env Γ
  | _, .cons _ env, .here, v => .cons v env
  | _, .cons x env, .there m, v => .cons x (env.set m v)

@[simp] theorem Env.set_here {t : Ty} {Γ : List Ty} (x : t.carrier) (env : Env Γ) (v : t.carrier) :
    (Env.cons x env).set .here v = .cons v env := rfl
@[simp] theorem Env.set_there {t s : Ty} {Γ : List Ty} (x : s.carrier) (env : Env Γ)
    (m : Mem t Γ) (v : t.carrier) : (Env.cons x env).set (.there m) v = .cons x (env.set m v) :=
  rfl

theorem Env.get_set_same {t : Ty} : {Γ : List Ty} → (env : Env Γ) → (m : Mem t Γ) →
    (v : t.carrier) → (env.set m v).get m = v
  | _, .cons _ _, .here, _ => rfl
  | _, .cons _ env, .there m, v => Env.get_set_same env m v

/-- The values of a loop's carried variables, in order. -/
def Carry.get {Γ : List Ty} : {ts : List Ty} → Carry Γ ts → Env Γ → (Ty.tup ts).carrier
  | _, .nil, _ => ()
  | _, .cons m cs, env => (env.get m, cs.get env)

/-- Stores the values `vs` of a loop's carried variables, in order. -/
def Carry.set {Γ : List Ty} : {ts : List Ty} → Carry Γ ts → Env Γ → (Ty.tup ts).carrier → Env Γ
  | _, .nil, env, _ => env
  | _, .cons m cs, env, vs => cs.set (env.set m vs.1) vs.2

/-! ## Arrays, `Slots`, slices -/

/-- Element `i` of a vector, or `d` when `i` is out of range. -/
def vget {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (d : α) : α :=
  if h : i < n then v[i] else d

/-- Replaces element `i` of a vector, and changes nothing when `i` is out of range. -/
def vset {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (x : α) : Vector α n :=
  if h : i < n then v.set i x h else v

/-- Writes `xs` to the positions `i, i+1, …`, skipping positions out of range. -/
def vwrite {α : Type} {n : Nat} : Vector α n → Nat → List α → Vector α n
  | v, _, [] => v
  | v, i, x :: xs => vwrite (vset v i x) (i + 1) xs

/-- The elements `lo … lo+len-1`, fewer when the range leaves the vector. -/
def vrange {α : Type} {n : Nat} (v : Vector α n) (lo len : Nat) : List α :=
  (v.toList.drop lo).take len

@[simp] theorem vget_vset_same {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (x d : α)
    (h : i < n) : vget (vset v i x) i d = x := by
  simp [vget, vset, h]

theorem vget_vset_ne {α : Type} {n : Nat} (v : Vector α n) (i j : Nat) (x d : α) (h : i ≠ j) :
    vget (vset v i x) j d = vget v j d := by
  unfold vget vset
  by_cases hi : i < n <;> by_cases hj : j < n <;> simp [hi, hj, h]

/-- The content of cell `i`, which is `none` when the cell is empty or out of range. -/
def Slots.cell {α : Type} {n : Nat} (s : Slots α n) (i : Nat) : Option α :=
  vget s.cells i none

/-- Whether cell `i` exists and is full. -/
def Slots.isFull {α : Type} {n : Nat} (s : Slots α n) (i : Nat) : Bool := (s.cell i).isSome

/-- Whether cell `i` exists and is empty. -/
def Slots.isVacant {α : Type} {n : Nat} (s : Slots α n) (i : Nat) : Bool :=
  decide (i < n) && (s.cell i).isNone

/-- Replaces the content of cell `i`. -/
def Slots.setCell {α : Type} {n : Nat} (s : Slots α n) (i : Nat) (o : Option α) : Slots α n :=
  vset s.cells i o

/-- The empty `Slots`. -/
def Slots.empty {α : Type} (n : Nat) : Slots α n := Vector.replicate n none

/-- The view of the slice `v[lo..lo+len]`, whose cell `k` holds element `lo + k` when `k < len`
and that element exists, and whose other cells are empty. -/
def vview {α : Type} {n : Nat} (v : Vector α n) (lo len : Nat) : Slots α n :=
  Vector.ofFn fun k => if k.val < len then v.toList[lo + k.val]? else none

/-- Writes a view back into the array it was taken from. Element `lo + k` becomes the content of
cell `k` of `s` when `k < len` and the cell is full, and everything else is unchanged. -/
def vunview {α : Type} {n : Nat} (v : Vector α n) (lo len : Nat) (s : Slots α n) : Vector α n :=
  Vector.ofFn fun j =>
    if lo ≤ j.val ∧ j.val - lo < len then ((s.cell (j.val - lo)).getD v[j]) else v[j]

/-- The view of the sub-slice `s[lo..lo+len]` of a view or `Slots` value `s`, whose cell `k` is
`s`'s cell `lo + k` when `k < len`, and whose other cells are empty. -/
def sview {α : Type} {n : Nat} (s : Slots α n) (lo len : Nat) : Slots α n :=
  Vector.ofFn fun k => if k.val < len then s.cell (lo + k.val) else none

/-- Writes a sub-slice's view back into the view it was taken from. Cell `lo + k` becomes the
content of cell `k` of `v` when `k < len` and that cell is full, and everything else is unchanged,
so no cell is emptied. -/
def sunview {α : Type} {n : Nat} (s : Slots α n) (lo len : Nat) (v : Slots α n) : Slots α n :=
  Vector.ofFn fun j =>
    if lo ≤ j.val ∧ j.val - lo < len ∧ (v.cell (j.val - lo)).isSome then v.cell (j.val - lo)
    else s.cell j.val

/-- Cell `k` of a sub-slice's view. -/
theorem sview_cell {α : Type} {n : Nat} (s : Slots α n) (lo len k : Nat) :
    (sview s lo len).cell k = if k < len ∧ k < n then s.cell (lo + k) else none := by
  unfold Slots.cell vget sview
  by_cases hk : k < n <;> by_cases hl : k < len <;> simp [hk, hl, Slots.cells, Slots.cell, vget]

/-- Cell `k` of a written-back sub-slice. -/
theorem sunview_cell {α : Type} {n : Nat} (s : Slots α n) (lo len : Nat) (v : Slots α n) (k : Nat) :
    (sunview s lo len v).cell k =
      if k < n ∧ lo ≤ k ∧ k - lo < len ∧ (v.cell (k - lo)).isSome then v.cell (k - lo)
      else s.cell k := by
  conv => lhs; unfold Slots.cell vget sunview
  by_cases hk : k < n
  · simp only [hk, ↓reduceDIte, Vector.getElem_ofFn, true_and]
  · simp only [hk, ↓reduceDIte, false_and, ↓reduceIte]
    simp [Slots.cell, vget, hk]

/-- The full cells of a written-back sub-slice are those of the view, together with those of the
handed-back sub-view inside the range. -/
@[simp] theorem sunview_isFull {α : Type} {n : Nat} (s : Slots α n) (lo len : Nat) (v : Slots α n)
    (k : Nat) : (sunview s lo len v).isFull k =
      (s.isFull k || decide (k < n ∧ lo ≤ k ∧ k - lo < len) && v.isFull (k - lo)) := by
  unfold Slots.isFull
  rw [sunview_cell]
  by_cases h3 : k < n ∧ lo ≤ k ∧ k - lo < len <;> by_cases h4 : (v.cell (k - lo)).isSome <;>
    simp [h3, h4]

/-- Which cells of a sub-slice's view are full, in the simp form used for the obligations of a
sub-slice's elements. -/
@[simp] theorem sview_isFull {α : Type} {n : Nat} (s : Slots α n) (lo len k : Nat) :
    (sview s lo len).isFull k = (decide (k < len) && decide (k < n) && s.isFull (lo + k)) := by
  unfold Slots.isFull
  rw [sview_cell]
  by_cases h1 : k < len <;> by_cases h2 : k < n <;> simp [h1, h2]

/-- Cell `k` of a view. -/
theorem vview_cell {α : Type} {n : Nat} (v : Vector α n) (lo len k : Nat) :
    (vview v lo len).cell k = if k < len ∧ k < n then v.toList[lo + k]? else none := by
  unfold Slots.cell vget vview
  by_cases hk : k < n <;> by_cases hl : k < len <;> simp [hk, hl, Slots.cells]

/-- The full cells of a view are exactly its first `len` cells when the range fits. -/
theorem vview_full_iff {α : Type} {n : Nat} (v : Vector α n) (lo len k : Nat) (h : lo + len ≤ n) :
    (vview v lo len).isFull k = true ↔ k < len := by
  simp only [Slots.isFull, vview_cell]
  constructor
  · intro hf
    by_cases hk : k < len
    · exact hk
    · simp [hk] at hf
  · intro hk
    have : lo + k < v.toList.length := by simp; omega
    simp [hk, show k < n by omega, List.getElem?_eq_getElem this]

/-- The full cells of a view are exactly the cells `k < len` whose element `lo + k` exists. This
is the simp form that the automatic discharge of `Place.backOk` uses. -/
@[simp] theorem vview_isFull {α : Type} {n : Nat} (v : Vector α n) (lo len k : Nat) :
    (vview v lo len).isFull k = (decide (k < len) && decide (lo + k < n)) := by
  simp only [Slots.isFull, vview_cell]
  by_cases hk : k < len <;> by_cases hn : lo + k < n
  · simp [hk, hn, show k < n by omega]
  · simp [hk, hn]
  · simp [hk]
  · simp [hk]

/-- Which cells are full after a cell is replaced, in the simp form used for writes through a
view's elements `r[i]! := …`. -/
@[simp] theorem Slots.isFull_setCell {α : Type} {n : Nat} (s : Slots α n) (i : Nat) (o : Option α)
    (k : Nat) : (s.setCell i o).isFull k = if k = i ∧ i < n then o.isSome else s.isFull k := by
  unfold Slots.isFull Slots.cell Slots.setCell
  by_cases hk : k = i
  · subst hk
    by_cases hi : k < n
    · simp [hi]
    · simp [hi, vget]
  · simp [hk, vget_vset_ne _ _ _ _ _ (Ne.symm hk)]

/-- A cell after a cell is replaced, where a write out of range changes nothing. -/
@[simp] theorem Slots.cell_setCell {α : Type} {n : Nat} (s : Slots α n) (i : Nat) (o : Option α)
    (k : Nat) : (s.setCell i o).cell k = if k = i ∧ i < n then o else s.cell k := by
  unfold Slots.cell Slots.setCell
  by_cases hk : k = i
  · subst hk; by_cases hi : k < n <;> simp [hi, vget, vset]
  · simp [hk, vget_vset_ne _ _ _ _ _ (Ne.symm hk)]

theorem Slots.cell_setCell_same {α : Type} {n : Nat} (s : Slots α n) (i : Nat) (o : Option α)
    (h : i < n) : (s.setCell i o).cell i = o := by simp [h]

theorem Slots.cell_setCell_ne {α : Type} {n : Nat} (s : Slots α n) (i j : Nat) (o : Option α)
    (h : i ≠ j) : (s.setCell i o).cell j = s.cell j := by simp [Ne.symm h]

/-- A full cell is in range. -/
theorem Slots.lt_of_isFull {α : Type} {n k : Nat} {s : Slots α n} (h : s.isFull k = true) :
    k < n := by
  simp only [Slots.isFull, Slots.cell, vget] at h
  split at h
  · assumption
  · simp at h

/-! ## Places -/

namespace Place
variable {Γ : List Ty}

/-- The value at a place. -/
def get : {t : Ty} → Place Γ t → Env Γ → t.carrier
  | _, .var m, env => env.get m
  | _, .field p l, env => l.get (p.get env)
  | _, .index (dflt := _) p i, env => vget (p.get env) (i.denote env).toNat default
  | _, .slot (dflt := _) p i, env => ((p.get env : Slots _ _).cell (i.denote env).toNat).getD default
  | _, .range p lo len, env =>
    vview (p.get env) (lo.denote env).toNat (len.denote env).toNat
  | _, .pair2 (dflt := _) p i j, env =>
    (vget (p.get env) (i.denote env).toNat default, vget (p.get env) (j.denote env).toNat default)
  | _, .rangeS m lo len, env => sview (env.get m) (lo.denote env).toNat (len.denote env).toNat
  | _, .pair2S (dflt := _) m i j, env =>
    (((env.get m : Slots _ _).cell (i.denote env).toNat).getD default,
      ((env.get m : Slots _ _).cell (j.denote env).toNat).getD default)

/-- Stores `v` at a place, updating the place's variable along the path. Index atoms are evaluated
in the environment before the update. -/
def set : {t : Ty} → Place Γ t → Env Γ → t.carrier → Env Γ
  | _, .var m, env, v => env.set m v
  | _, .field p l, env, v => p.set env (l.set (p.get env) v)
  | _, .index (dflt := _) p i, env, v => p.set env (vset (p.get env) (i.denote env).toNat v)
  | _, .slot (dflt := _) p i, env, v =>
    p.set env (Slots.setCell (p.get env) (i.denote env).toNat (some v))
  | _, .range p lo len, env, v =>
    p.set env (vunview (p.get env) (lo.denote env).toNat (len.denote env).toNat v)
  | _, .pair2 (dflt := _) p i j, env, v =>
    p.set env (vset (vset (p.get env) (i.denote env).toNat v.1) (j.denote env).toNat v.2)
  | _, .rangeS m lo len, env, v =>
    env.set m (sunview (env.get m) (lo.denote env).toNat (len.denote env).toNat v)
  | _, .pair2S (dflt := _) m i j, env, v =>
    env.set m (((env.get m : Slots _ _).setCell (i.denote env).toNat (some v.1)).setCell
      (j.denote env).toNat (some v.2))

/-- The obligations of a place, which say that every index is in range, every `Slots` cell reached
is full, and the two indices of `pair2` differ. -/
def ok : {t : Ty} → Place Γ t → Env Γ → Prop
  | _, .var _, _ => True
  | _, .field p _, env => p.ok env
  | _, .index (dflt := _) (n := n) p i, env => p.ok env ∧ (i.denote env).toNat < n
  | _, .slot (dflt := _) p i, env => p.ok env ∧ (p.get env : Slots _ _).isFull (i.denote env).toNat = true
  | _, .range (n := n) p lo len, env =>
    p.ok env ∧ (lo.denote env).toNat + (len.denote env).toNat ≤ n
  | _, .pair2 (dflt := _) (n := n) p i j, env =>
    p.ok env ∧ (i.denote env).toNat < n ∧ (j.denote env).toNat < n ∧
      (i.denote env).toNat ≠ (j.denote env).toNat
  | _, .rangeS (n := n) m lo len, env =>
    (lo.denote env).toNat + (len.denote env).toNat ≤ n ∧
      ∀ k, k < (lo.denote env).toNat + (len.denote env).toNat →
        (env.get m : Slots _ _).isFull k = true
  | _, .pair2S (dflt := _) m i j, env =>
    (env.get m : Slots _ _).isFull (i.denote env).toNat = true ∧
      (env.get m : Slots _ _).isFull (j.denote env).toNat = true ∧
      (i.denote env).toNat ≠ (j.denote env).toNat

/-- Decides the obligations of a place, as the checked forms do at run time. -/
def check : {t : Ty} → Place Γ t → Env Γ → Bool
  | _, .var _, _ => true
  | _, .field p _, env => p.check env
  | _, .index (dflt := _) (n := n) p i, env => p.check env && decide ((i.denote env).toNat < n)
  | _, .slot (dflt := _) p i, env => p.check env && (p.get env : Slots _ _).isFull (i.denote env).toNat
  | _, .range (n := n) p lo len, env =>
    p.check env && decide ((lo.denote env).toNat + (len.denote env).toNat ≤ n)
  | _, .pair2 (dflt := _) (n := n) p i j, env =>
    p.check env && decide ((i.denote env).toNat < n) && decide ((j.denote env).toNat < n) &&
      decide ((i.denote env).toNat ≠ (j.denote env).toNat)
  | _, .rangeS (n := n) m lo len, env =>
    decide ((lo.denote env).toNat + (len.denote env).toNat ≤ n) &&
      (List.range ((lo.denote env).toNat + (len.denote env).toNat)).all fun k =>
        (env.get m : Slots _ _).isFull k
  | _, .pair2S (dflt := _) m i j, env =>
    (env.get m : Slots _ _).isFull (i.denote env).toNat &&
      (env.get m : Slots _ _).isFull (j.denote env).toNat &&
      decide ((i.denote env).toNat ≠ (j.denote env).toNat)

theorem check_iff {t : Ty} (p : Place Γ t) (env : Env Γ) : p.check env = true ↔ p.ok env := by
  induction p with
  | var => simp [check, ok]
  | field p _ ih => simp [check, ok, ih]
  | index p i ih => simp [check, ok, ih]
  | slot p i ih => simp [check, ok, ih]
  | range p lo len ih => simp [check, ok, ih]
  | pair2 p i j ih => simp [check, ok, ih, Bool.and_assoc]
  | rangeS m lo len => simp [check, ok]
  | pair2S m i j => simp [check, ok, Bool.and_assoc]

/-- The number of selectors, each of which costs an address computation. -/
def depth : {t : Ty} → Place Γ t → Nat
  | _, .var _ => 0
  | _, .field p _ => p.depth + 1
  | _, .index (dflt := _) p _ => p.depth + 1
  | _, .slot (dflt := _) p _ => p.depth + 1
  | _, .range p _ _ => p.depth + 1
  | _, .pair2 (dflt := _) p _ _ => p.depth + 1
  | _, .rangeS _ _ _ => 1
  | _, .pair2S (dflt := _) _ _ _ => 1

/-- The place has no partial selector, and so no obligation. -/
def total : {t : Ty} → Place Γ t → Bool
  | _, .var _ => true
  | _, .field p _ => p.total
  | _, _ => false

/-- The write-back condition of a `&mut` borrow, which the handed-back value `v` must satisfy for
the write-back `p.set env v` to agree with the machine's updates in place. For a slice
`p[lo..lo+len]` the view must still hold every viewed element, with its cells below `len` full,
because `vunview` writes back exactly those while at the machine the view is the elements
themselves. Every other place has no condition. The layout laws do not imply the condition, since
a certified constructor may drop the view's cells. The compiler checks a hand-back condition that
implies it in every environment, so it is not an obligation of `Exp.safe`. -/
def backOk : {t : Ty} → Place Γ t → Env Γ → t.carrier → Prop
  | _, .var _, _, _ => True
  | _, .field _ _, _, _ => True
  | _, .index (dflt := _) _ _, _, _ => True
  | _, .slot (dflt := _) _ _, _, _ => True
  | _, .range _ _ len, env, v => ∀ k, k < (len.denote env).toNat → (v : Slots _ _).isFull k = true
  | _, .pair2 (dflt := _) _ _ _, _, _ => True
  | _, .rangeS _ _ len, env, v => ∀ k, k < (len.denote env).toNat → (v : Slots _ _).isFull k = true
  | _, .pair2S (dflt := _) _ _ _, _, _ => True

theorem ok_of_total {t : Ty} (p : Place Γ t) (h : p.total = true) (env : Env Γ) : p.ok env := by
  induction p with
  | var => trivial
  | field p _ ih => exact ih h
  | _ => simp [total] at h

end Place

/-! ## Guards -/

/-- Whether a guard holds. -/
def Guard.denote {Γ : List Ty} : Guard Γ → Env Γ → Bool
  | .valid p _, env => p.check env

/-! ## Call arguments with modes -/

namespace RArgs
variable {Γ : List Ty}

/-- The callee's parameter values, which are the atoms and the values at the argument places. -/
def denote : {ps os : List Ty} → RArgs Γ ps os → Env Γ → Env ps
  | _, _, .nil, _ => .nil
  | _, _, .own a as, env => .cons (a.denote env) (as.denote env)
  | _, _, .shr p as, env => .cons (p.get env) (as.denote env)
  | _, _, .mut p as, env => .cons (p.get env) (as.denote env)

/-- Stores the updated `mut` parameters back into their argument places, in order. -/
def writeBack : {ps os : List Ty} → RArgs Γ ps os → Env Γ → (Ty.tup os).carrier → Env Γ
  | _, _, .nil, env, _ => env
  | _, _, .own _ as, env, vs => as.writeBack env vs
  | _, _, .shr _ as, env, vs => as.writeBack env vs
  | _, _, .mut p as, env, vs => as.writeBack (p.set env vs.1) vs.2

/-- The write-back conditions of the `&mut` arguments for the handed-back values `vs`, with the
argument places' indices evaluated at the call. -/
def backOk : {ps os : List Ty} → RArgs Γ ps os → Env Γ → (Ty.tup os).carrier → Prop
  | _, _, .nil, _, _ => True
  | _, _, .own _ as, env, vs => as.backOk env vs
  | _, _, .shr _ as, env, vs => as.backOk env vs
  | _, _, .mut p as, env, vs => p.backOk env vs.1 ∧ as.backOk env vs.2

/-- The obligations of the argument places. -/
def ok : {ps os : List Ty} → RArgs Γ ps os → Env Γ → Prop
  | _, _, .nil, _ => True
  | _, _, .own _ as, env => as.ok env
  | _, _, .shr p as, env => p.ok env ∧ as.ok env
  | _, _, .mut p as, env => p.ok env ∧ as.ok env

/-- The number of selectors of the argument places. -/
def depth : {ps os : List Ty} → RArgs Γ ps os → Nat
  | _, _, .nil => 0
  | _, _, .own _ as => as.depth
  | _, _, .shr p as => p.depth + as.depth
  | _, _, .mut p as => p.depth + as.depth

/-- No argument place has a partial selector. -/
def total : {ps os : List Ty} → RArgs Γ ps os → Bool
  | _, _, .nil => true
  | _, _, .own _ as => as.total
  | _, _, .shr p as => p.total && as.total
  | _, _, .mut p as => p.total && as.total

end RArgs

/-! ## Extern arguments -/

/-- The bytes a buffer holds, either constant bytes or the viewed elements of a byte array. -/
def Buf.denote {Γ : List Ty} : Buf Γ → Env Γ → List UInt8
  | .const bs, _ => bs
  | .slice a lo len, env => vrange (a.get env) (lo.denote env).toNat (len.denote env).toNat

namespace EArgs
variable {Γ : List Ty}

/-- The word arguments, in order. -/
def words : {ps : List ExtParam} → EArgs Γ ps → Env Γ → List UInt64
  | _, .nil, _ => []
  | _, .word a as, env => a.denote env :: as.words env
  | _, .bufIn _ as, env => as.words env
  | _, .bufOut as, env => as.words env
  | _, .sliceOut _ _ _ as, env => as.words env

/-- The contents of the input buffers, in order. -/
def bytesIn : {ps : List ExtParam} → EArgs Γ ps → Env Γ → List (List UInt8)
  | _, .nil, _ => []
  | _, .word _ as, env => as.bytesIn env
  | _, .bufIn b as, env => b.denote env :: as.bytesIn env
  | _, .bufOut as, env => as.bytesIn env
  | _, .sliceOut _ _ _ as, env => as.bytesIn env

/-- The capacities of the output buffers, in order, where a mutable slice's capacity is its
run-time length. -/
def outCaps : {ps : List ExtParam} → EArgs Γ ps → Env Γ → List Nat
  | _, .nil, _ => []
  | _, .word _ as, env => as.outCaps env
  | _, .bufIn _ as, env => as.outCaps env
  | _, .bufOut (cap := cap) as, env => cap :: as.outCaps env
  | _, .sliceOut _ _ cap as, env => (cap.denote env).toNat :: as.outCaps env

/-- Writes the output slices of `Exp.extMut`. `bss` has one byte list per output buffer, in
order, each at most its capacity, and each mutable slice `a[lo..lo+cap]` gets its list written
from element `lo`, with the indices evaluated at the call. -/
def fill : {ps : List ExtParam} → EArgs Γ ps → Env Γ → Env Γ → List (List UInt8) → Env Γ
  | _, .nil, _, env', _ => env'
  | _, .word _ as, env, env', bss => as.fill env env' bss
  | _, .bufIn _ as, env, env', bss => as.fill env env' bss
  | _, .bufOut as, env, env', bss => as.fill env env' bss.tail
  | _, .sliceOut a lo _ as, env, env', bss =>
    as.fill env (a.set env' (vwrite (a.get env') (lo.denote env).toNat (bss.headD []))) bss.tail

/-- The obligations of the slices, which are the array places' own and the slice lying inside the
array. -/
def ok : {ps : List ExtParam} → EArgs Γ ps → Env Γ → Prop
  | _, .nil, _ => True
  | _, .word _ as, env => as.ok env
  | _, .bufIn (.const _) as, env => as.ok env
  | _, .bufIn (.slice (n := n) a lo len) as, env =>
    (a.ok env ∧ (lo.denote env).toNat + (len.denote env).toNat ≤ n) ∧ as.ok env
  | _, .bufOut as, env => as.ok env
  | _, .sliceOut (n := n) a lo cap as, env =>
    (a.ok env ∧ (lo.denote env).toNat + (cap.denote env).toNat ≤ n) ∧ as.ok env

/-- The number of slice arguments, each of which is passed as an address and a length. -/
def slices : {ps : List ExtParam} → EArgs Γ ps → Nat
  | _, .nil => 0
  | _, .word _ as => as.slices
  | _, .bufIn (.const _) as => as.slices
  | _, .bufIn (.slice _ _ _) as => as.slices + 1
  | _, .bufOut as => as.slices
  | _, .sliceOut _ _ _ as => as.slices + 1

/-- The number of selectors of the slice arguments' places, where the slice itself counts as one. -/
def depth : {ps : List ExtParam} → EArgs Γ ps → Nat
  | _, .nil => 0
  | _, .word _ as => as.depth
  | _, .bufIn (.const _) as => as.depth
  | _, .bufIn (.slice a _ _) as => a.depth + 1 + as.depth
  | _, .bufOut as => as.depth
  | _, .sliceOut a _ _ as => a.depth + 1 + as.depth

/-- There is no slice argument, so there is no obligation and nothing to write. -/
def total : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => true
  | _, .word _ as => as.total
  | _, .bufIn (.const _) as => as.total
  | _, .bufIn (.slice _ _ _) _ => false
  | _, .bufOut as => as.total
  | _, .sliceOut _ _ _ _ => false

theorem ok_of_total {ps : List ExtParam} (as : EArgs Γ ps) (h : as.total = true) (env : Env Γ) :
    as.ok env := by
  induction as with
  | nil => trivial
  | word _ _ ih => exact ih h
  | bufIn b _ ih => cases b <;> simp_all [total, ok]
  | bufOut _ ih => exact ih h
  | sliceOut => simp [total] at h

end EArgs

/-- The call record for an extern applied to arguments. -/
def ExtSig.call {Γ : List Ty} (sig : ExtSig) (args : EArgs Γ sig.params) (env : Env Γ) : Call :=
  { sym := sig.sym, args := args.words env, bytesIn := args.bytesIn env,
    outCaps := args.outCaps env }

end Millipede
