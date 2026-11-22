import Millipede.Meta.MpDef
import Millipede.Lib.Bitmap
import Std.Tactic.Do
import Std.WP

/-!
# The allocator interface

`Alloc V` is an interface, a Lean structure whose fields are an abstract state type `S`, an
abstract key type `K`, the operations and their contracts. The operations are the normal forms
of `mp def`s, so that a client's normal form calls them, and the contracts are stated over an
abstract model. In the model `Inv s` is the implementation's invariant, `Owns s k` says that `k`
names a live cell of `s`, `cell s k` is that cell's content, `used s` counts the allocations not
yet given back, and `cap` is the capacity, below which `alloc` cannot fail.

| operation | requires | ensures |
|---|---|---|
| `new : S` | | `Inv`, `used = 0` |
| `alloc (s : &mut S) (v : V) : Result Full K` | `Inv s` | `Inv s'`; on `ok k`, `k` is fresh, owned now and holds `v`, `used` grows by one, and every owned key keeps its content; on `err`, `s' = s` and `cap ≤ used s` |
| `alloc! (s : &mut S) (v : V) : K` | `Inv s ∧ used s < cap` | as for `ok` above |
| `get (s : &S) (k : &K) : V` | `Inv s ∧ Owns s k` | `cell s k = some result` |
| `free (s : &mut S) (k : K) : V` | `Inv s ∧ Owns s k` | `cell s k = some result`, `Inv s'`, `used s' + 1 = used s` if `reuse` and `used s' = used s` otherwise, and every other owned key keeps its content |

`free` gives the cell back exactly when `reuse` holds, as in a bitmap pool, where `used` drops by
one. Otherwise it only forgets the key and `used` stays, as in a bump arena, whose cells come back
at `reset`.

A key's type is its brand. A concrete arena's key type carries the arena's parameters, as
`Pool.Key T n W` and `Bump.Ix T n` do, so an operation of an arena at other parameters does not
accept it and the mismatch is a Lean type error at the argument. A generic client sees `A.K`,
tied to `A.S` by the interface, and with two implementation variables `A` and `B` the types `A.K`
and `B.K` differ. The brand costs nothing at run time, since a key's layout is its index alone.
Two arenas of one type share a key type, and what separates them is the obligation of access
`Owns s k`, which a client discharges from its accounting of that arena and cannot discharge for
another.

A pool's keys are linear and sealed, so the borrow checker rejects using a key after its `free`,
freeing it twice, or dropping it. In a generic client the key type `A.K` is linear, because its
linearity is unknown, so the client frees each key at most once and uses none after its `free`
whatever implementation it is compiled against. The model's `Owns` is exact for the pool, whose
`free` empties the cell. A bump arena's index stays owned until `reset`, after which every old
index is refuted.

What a client needs about ownership comes once from the contracts. `Holds s ks` says that the
keys `ks` a client holds are distinct, each owned by the arena, and, for a reusing arena, as many
as the cells in use. `Holds.push` and `Holds.pop` are proved here once for every implementation,
so a client's invariant only states `A.Holds s ks`, or `A.KeyStack s ks n` for keys kept in a
`Slots` stack, and proves nothing about ownership itself.

The implementations are `Pool.impl`, a bitmap pool whose cells are reused after `free`, and
`Bump.impl`, a bump arena without reuse, each proving these contracts from its own. Clients are
`mp def`s under `variable (A : Alloc V)`, written once, with contracts proved once against these
fields, and compiled against either implementation. Arenas are described in
doc/design/arenas.md.
-/

namespace Millipede.Lib

open Millipede Std.WP

/-- The error of a full arena. -/
structure Full where
deriving Data, Repr, DecidableEq

/-- The allocator interface, with an abstract state and key, a model, and the operations with
their contracts over the model, as the module doc describes. Each operation consists of the
implementation's Core function with its normal form, the link between the two, its `requires`,
and its safety, purity and contract. -/
mp interface Alloc (V : Type) [Data V] where
  S : Type
  K : Type
  copyS : Data.Copy S
  inhK : Inhabited K
  cap : Nat
  reuse : Bool
  Inv : S → Prop
  Owns : S → K → Prop
  cell : S → K → Option V
  used : S → Nat
  op new ensures Inv result ∧ used result = 0 : S
  op alloc (s : &mut S) (v : V) requires Inv s
    ensures Inv s' ∧ match result with
      | .ok k => ¬ Owns s k ∧ Owns s' k ∧ cell s' k = some v ∧ used s' = used s + 1 ∧
          ∀ k', Owns s k' → Owns s' k' ∧ cell s' k' = cell s k'
      | .error _ => s' = s ∧ cap ≤ used s : Result Full K
  op alloc! (s : &mut S) (v : V) requires Inv s ∧ used s < cap
    ensures Inv s' ∧ ¬ Owns s result ∧ Owns s' result ∧ cell s' result = some v ∧
      used s' = used s + 1 ∧ ∀ k', Owns s k' → Owns s' k' ∧ cell s' k' = cell s k' : K
  op get (s : &S) (k : &K) requires Inv s ∧ Owns s k ensures cell s k = some result : V
  op free (s : &mut S) (k : K) requires Inv s ∧ Owns s k
    ensures cell s k = some result ∧ Inv s' ∧ used s' + (if reuse then 1 else 0) = used s ∧
      ∀ k', Owns s k' → k' ≠ k → Owns s' k' ∧ cell s' k' = cell s k' : V

namespace Alloc
variable {V : Type} [Data V] (A : Alloc V)

/-! ## The keys a client holds -/

/-- The keys `ks` are held by a client of `s`, which means they are distinct, each owned, and as
many as the cells in use. -/
structure Holds (s : A.S) (ks : List A.K) : Prop where
  nodup : ks.Nodup
  owns : ∀ k ∈ ks, A.Owns s k
  used : A.used s = ks.length

variable {A} {s s' : A.S} {ks : List A.K} {k : A.K}

theorem Holds.nil (h : A.used s = 0) : A.Holds s [] := ⟨List.nodup_nil, by simp, h⟩

/-- A key that `alloc` hands out joins the keys held. Such a key was not owned before and is owned
after, one more cell is in use, and the owned keys are kept. -/
theorem Holds.push (h : A.Holds s ks) (hn : ¬ A.Owns s k) (ho : A.Owns s' k)
    (hu : A.used s' = A.used s + 1)
    (hf : ∀ k', A.Owns s k' → A.Owns s' k' ∧ A.cell s' k' = A.cell s k') :
    A.Holds s' (ks ++ [k]) := by
  have := h.owns; have := h.nodup; have := h.used
  exact ⟨by grind [List.nodup_append], by grind, by grind⟩

/-- After `free` of the last key held, in an arena that gives cells back, the rest are held. -/
theorem Holds.pop (hr : A.reuse = true) (h : A.Holds s (ks ++ [k]))
    (hu : A.used s' + (if A.reuse then 1 else 0) = A.used s)
    (hf : ∀ k', A.Owns s k' → k' ≠ k → A.Owns s' k' ∧ A.cell s' k' = A.cell s k') :
    A.Holds s' ks := by
  have := h.owns; have := h.nodup; have := h.used
  exact ⟨by grind [List.nodup_append], by grind [List.nodup_append], by grind⟩

end Alloc

/-! ## Lemmas the implementations share -/

/-- Cells of a copyable type are copyable, so an arena's state is not linear when its cells are
not, which is the interface's `copyS`. -/
theorem Data.linear_slots {α : Type} [Data α] (n : Nat) :
    Data.linear (Slots α n) = Data.linear α := rfl
theorem Data.linear_vector {α : Type} [Data α] (n : Nat) :
    Data.linear (Vector α n) = Data.linear α := rfl

/-- Writing a vacant cell keeps every full cell and its content. -/
theorem Slots.frame_put {T : Type} {n : Nat} (s : Slots T n) (i j : Nat) (v : Option T)
    (hi : s.isFull i = true) (hj : s.isVacant j = true) :
    (s.setCell j v).isFull i = true ∧ (s.setCell j v).cell i = s.cell i := by
  have hne : i ≠ j := by
    rintro rfl; simp only [Slots.isFull, Slots.isVacant, Bool.and_eq_true] at hi hj
    simp_all
  simp only [Slots.isFull, Slots.cell_setCell_ne _ _ _ _ (Ne.symm hne)] at hi ⊢
  exact ⟨hi, trivial⟩

/-- A vacant cell is not full. -/
theorem Slots.not_full_of_vacant {T : Type} {n : Nat} {s : Slots T n} {j : Nat}
    (hj : s.isVacant j = true) : s.isFull j = false := by
  simp only [Slots.isFull, Slots.isVacant, Bool.and_eq_true] at hj ⊢; simp_all

/-! ## Stacks kept in `Slots`

`BumpInv slots len` says that cells `0 … len-1` are full and the rest empty, which describes the
cells of a bump arena or a client's stack of keys. `Alloc.KeyStack A s ks n` is the standard
invariant of a client that keeps the keys of an arena in such a stack `ks : Slots A.K m`, holding
`n` keys with the newest on top. It says the keys are distinct, owned, and as many as the arena's
cells in use. Its `push` and `pop` lemmas are tagged `@[mp_auto]`, so `mp_auto` and the automatic
attempts use them. -/

open Std.WP in
section
/-- The cells `0 … len-1` as a list, in order, with empty cells skipped. It is the list view of a
stack kept in `Slots`, such as a bump arena's cells or the keys a client holds. -/
def Slots.upTo {T : Type} {n : Nat} (s : Slots T n) : Nat → List T
  | 0 => []
  | k + 1 => Slots.upTo s k ++ (s.cell k).toList

/-- Writing at or above `len` does not change the cells below. -/
theorem Slots.upTo_set_ge {T : Type} {n : Nat} (s : Slots T n) (i : Nat) (o : Option T) :
    ∀ len, len ≤ i → Slots.upTo (s.setCell i o) len = Slots.upTo s len := by
  intro len; induction len <;> intro h
  all_goals grind [Slots.upTo, Slots.cell_setCell]

/-- A push, which fills cell `len`. -/
theorem Slots.upTo_push {T : Type} {n : Nat} (s : Slots T n) (len : Nat) (v : T) (h : len < n) :
    Slots.upTo (s.setCell len (some v)) (len + 1) = Slots.upTo s len ++ [v] := by
  simp [Slots.upTo, Slots.upTo_set_ge _ _ _ len (Nat.le_refl _), h]

/-- The last of `len + 1` cells. -/
theorem Slots.upTo_succ {T : Type} {n : Nat} (s : Slots T n) (len : Nat) (k : T)
    (h : s.cell len = some k) : Slots.upTo s (len + 1) = Slots.upTo s len ++ [k] := by
  simp [Slots.upTo, h]

/-- The bump invariant, which says that `len ≤ n` and that exactly the cells below `len` are
full. -/
structure BumpInv {T : Type} {n : Nat} (slots : Slots T n) (len : UInt64) : Prop where
  le : len.toNat ≤ n
  full_iff : ∀ i < n, (slots.cell i).isSome = decide (i < len.toNat)

namespace BumpInv
variable {T : Type} {n : Nat} {slots : Slots T n} {len : UInt64}

theorem empty : BumpInv (Slots.empty n : Slots T n) 0 :=
  ⟨Nat.zero_le _, fun i _ => by simp⟩

/-- The cell at `len` is vacant. -/
theorem vacant (h : BumpInv slots len) (hl : len.toNat < n) : slots.isVacant len.toNat = true := by
  have := h.full_iff _ hl
  simp only [Nat.lt_irrefl, decide_false] at this
  simp only [Slots.isVacant, hl, decide_true, Bool.true_and]
  cases hc : slots.cell len.toNat
  · rfl
  · simp [hc] at this

/-- A cell below `len` is full. -/
theorem full (h : BumpInv slots len) (i : Nat) (hi : i < len.toNat) : slots.isFull i = true := by
  have := h.full_iff i (by have := h.le; omega)
  simp only [hi, decide_true] at this
  exact this

/-- Filling cell `len` and incrementing `len` keeps the invariant. -/
theorem push (h : BumpInv slots len) (v : T) (hl : len.toNat < n) (hn : n < 2 ^ 64) :
    BumpInv (slots.setCell len.toNat (some v)) (len + 1) := by
  have hs : (len + 1).toNat = len.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; rw [Nat.mod_eq_of_lt (by omega)]
  refine ⟨by have := h.le; omega, fun i hi => ?_⟩
  rw [hs]
  by_cases hil : i = len.toNat
  · subst hil; simp [Slots.cell_setCell_same _ _ _ hl]
  · rw [Slots.cell_setCell_ne _ _ _ _ (Ne.symm hil), h.full_iff i hi]
    simp only [decide_eq_decide]; omega

/-- Emptying cell `len - 1` and decrementing `len`, which is a stack's pop, keeps the
invariant. -/
theorem pop (h : BumpInv slots len) (hl : 0 < len.toNat) :
    BumpInv (slots.setCell (len - 1).toNat none) (len - 1) := by
  have hs : (len - 1).toNat = len.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
  have hle := h.le
  refine ⟨by omega, fun i hi => ?_⟩
  rw [hs]
  by_cases hil : i = len.toNat - 1
  · subst hil; simp [Slots.cell_setCell_same _ _ _ (by omega : len.toNat - 1 < n)]
  · rw [Slots.cell_setCell_ne _ _ _ _ (by omega), h.full_iff i hi]
    simp only [decide_eq_decide]; omega

/-- Under the invariant the cells below `len` are all full, so their list has `len` elements. -/
theorem upTo_length (h : BumpInv slots len) : (Slots.upTo slots len.toNat).length = len.toNat := by
  have : ∀ m, m ≤ len.toNat → (Slots.upTo slots m).length = m := by
    intro m; induction m with
    | zero => intro; rfl
    | succ m ih => intro hm; have := h.full m (by omega); grind [Slots.upTo, Slots.isFull]
  exact this _ (Nat.le_refl _)

/-- On a non-empty stack, cell `len - 1` holds the last element of the list. -/
theorem upTo_pop (h : BumpInv slots len) (hl : 0 < len.toNat) :
    ∃ k, slots.cell (len - 1).toNat = some k ∧ (len - 1).toNat + 1 = len.toNat ∧
      Slots.upTo slots len.toNat = Slots.upTo slots (len - 1).toNat ++ [k] := by
  have hs : (len - 1).toNat + 1 = len.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp; omega
  have hf := h.full (len - 1).toNat (by omega)
  simp only [Slots.isFull, Option.isSome_iff_exists] at hf
  obtain ⟨k, hk⟩ := hf
  exact ⟨k, hk, hs, by rw [← hs, Slots.upTo_succ _ _ _ hk]⟩

end BumpInv

/-! ## A stack of held keys -/

/-- A stack of keys held from the arena `s`, kept in `Slots` as `ks` with cells `0 … n-1` full and
the newest on top. The keys are held in the sense of `Alloc.Holds`. This is the ownership
accounting of a client that keeps its keys this way, proved once for every implementation. -/
structure Alloc.KeyStack {V : Type} [Data V] {m : Nat} (A : Alloc V) (s : A.S) (ks : Slots A.K m)
    (n : UInt64) : Prop where
  bump : BumpInv ks n
  holds : A.Holds s (Slots.upTo ks n.toNat)

namespace Alloc.KeyStack
variable {V : Type} [Data V] {m : Nat} {A : Alloc V} {s s' : A.S} {ks : Slots A.K m} {n : UInt64} {k : A.K}

theorem empty (h : A.used s = 0) : A.KeyStack s (Slots.empty m) 0 :=
  ⟨BumpInv.empty, Alloc.Holds.nil h⟩

/-- As many cells in use as keys held. -/
theorem used (h : A.KeyStack s ks n) : A.used s = n.toNat := by
  rw [h.holds.used, h.bump.upTo_length]

/-- The cell above the top is vacant, which is where `push` puts the next key. -/
theorem vacant (h : A.KeyStack s ks n) (hn : n.toNat < m) : ks.isVacant n.toNat = true :=
  h.bump.vacant hn

/-- At most `m` keys. -/
theorem le (h : A.KeyStack s ks n) : n.toNat ≤ m := h.bump.le

/-- Push a key that `alloc` handed out, as in `Alloc.Holds.push`. -/
theorem push (h : A.KeyStack s ks n) (hn : n.toNat < m) (hm : m < 2 ^ 64) (hk : ¬ A.Owns s k)
    (ho : A.Owns s' k) (hu : A.used s' = A.used s + 1)
    (hf : ∀ k', A.Owns s k' → A.Owns s' k' ∧ A.cell s' k' = A.cell s k') :
    A.KeyStack s' (ks.setCell n.toNat (some k)) (n + 1) := by
  refine ⟨h.bump.push k hn hm, ?_⟩
  have : (n + 1).toNat = n.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; rw [Nat.mod_eq_of_lt (by omega)]
  rw [this, Slots.upTo_push _ _ _ hn]
  exact h.holds.push hk ho hu hf

/-- The top of a non-empty stack is a key held, and so owned. -/
theorem top (h : A.KeyStack s ks n) (hn : 0 < n.toNat) :
    ∃ k, ks.cell (n - 1).toNat = some k ∧ A.Owns s k ∧ (n - 1).toNat + 1 = n.toNat := by
  obtain ⟨k, hk, hs, hu⟩ := h.bump.upTo_pop hn
  exact ⟨k, hk, h.holds.owns k (by simp [hu]), hs⟩

/-- The cell of the top key is full, which is where `pop` takes it. -/
theorem full_top (h : A.KeyStack s ks n) (hn : 0 < n.toNat) : ks.isFull (n - 1).toNat = true := by
  obtain ⟨k, hk, -, -⟩ := h.top hn
  simp [Slots.isFull, hk]

/-- Pop the top key and `free` it, in an arena that gives cells back, as in `Alloc.Holds.pop`. -/
theorem pop (hr : A.reuse = true) (h : A.KeyStack s ks n) (hn : 0 < n.toNat)
    (hk : ks.cell (n - 1).toNat = some k)
    (hu : A.used s' + (if A.reuse then 1 else 0) = A.used s)
    (hf : ∀ k', A.Owns s k' → k' ≠ k → A.Owns s' k' ∧ A.cell s' k' = A.cell s k') :
    A.KeyStack s' (ks.setCell (n - 1).toNat none) (n - 1) := by
  obtain ⟨k', hk', -, hl⟩ := h.bump.upTo_pop hn
  rw [hk] at hk'; cases hk'
  refine ⟨h.bump.pop hn, ?_⟩
  rw [Slots.upTo_set_ge _ _ _ _ (Nat.le_refl _)]
  exact Alloc.Holds.pop hr (hl ▸ h.holds) hu hf

end Alloc.KeyStack

-- The facts that `mp_auto` passes to `grind`, which are the interface's contracts as facts and
-- the accounting of held keys.
attribute [grind] Alloc.new.post
attribute [mp_auto] Alloc.new.post Alloc.alloc!.post Alloc.free.post Alloc.KeyStack.empty
  Alloc.KeyStack.push Alloc.KeyStack.pop
attribute [mp_auto_fwd] Alloc.KeyStack.used Alloc.KeyStack.top Alloc.KeyStack.le
attribute [mp_auto] Alloc.KeyStack.vacant Alloc.KeyStack.full_top

end

end Millipede.Lib
