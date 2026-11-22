import Millipede.Lib.Alloc
import Millipede.Lib.Bitmap

/-!
# The bump arena and byte buffers

A bump arena `Bump T n` is written in Millipede. It holds `n` cells of type `T` and a length
`len`, and its invariant says that the cells below `len` are full and the others empty. `alloc`
fills cell `len` and `free` gives nothing back, so cells are reused only after `reset` empties
them all. A cell is named by a copyable index `Ix`, and access through it is either tested at run
time by `get`, which returns a `Result`, or carries the obligation `idx < len` with `get!`. A byte
buffer `Buf16` is `Bump U8 16`, whose `alloc` appends a byte.

The arena is generic over the cell type `T` and the capacity `n < 2 ^ 64`, so its operations,
obligations and contracts are proved once for every `T` and `n`. `Bump8`, with 8 `UInt64` cells,
and `Buf16`, with 16 bytes, are instances.

The contracts of the operations say that the invariant holds of `new` and is kept by every
operation, and that `alloc` returns the index `len` and fails only when the arena is full, so
indices are handed out in order and not reused before `reset`. The obligation `len < n` of
`alloc!` is enough to need no check, `get` returns `ok v` exactly for an allocated index holding
`v`, and `reset` empties the arena. `Bump.impl` implements the allocator interface `Alloc T` with
`reuse = false`. The invariant `BumpInv` and the list view `Slots.upTo` are in
Millipede/Lib/Alloc.lean, beside `Alloc.KeyStack`, which rests on them. Arenas are described in
doc/design/arenas.md.
-/

namespace Millipede.Lib

open Millipede Std.WP

set_option experimental.vcgen true

/-! ## The bump arena: `n` cells of `T` -/

/-- A bump arena of `n` cells of `T`. -/
structure Bump (T : Type) (n : Nat) where
  slots : Slots T n
  len : UInt64
deriving Data

/-- A copyable index into a `Bump T n`, whose type is the arena's brand. -/
structure Bump.Ix (T : Type) (n : Nat) where
  idx : UInt64
deriving Data, Repr, DecidableEq, Inhabited

instance {T : Type} [Data T] {n : Nat} : Data.Copy (Bump.Ix T n) := ⟨rfl⟩

section
variable {T : Type} [Data T] {n : Nat}

/-- The bump invariant. -/
def Bump.Inv (b : Bump T n) : Prop := BumpInv b.slots b.len

namespace Bump

/-! The model of the allocator interface of `Millipede/Lib/Alloc.lean`. -/

/-- An index is live when it is below `len`. -/
abbrev Owns (b : Bump T n) (x : Ix T n) : Prop := x.idx.toNat < b.len.toNat
/-- The content of an index's cell. -/
abbrev cell (b : Bump T n) (x : Ix T n) : Option T := b.slots.cell x.idx.toNat
/-- The cells handed out since `reset`. -/
abbrev used (b : Bump T n) : Nat := b.len.toNat

/-- Allocating cell `len`, seen in the model as a fresh index, its content and the frame. -/
theorem fresh (b b' : Bump T n) (x : Ix T n) (v : T) (hi : b'.Inv) (hx : x.idx = b.len)
    (hs : b'.slots = b.slots.setCell b.len.toNat (some v)) (hl : b'.len.toNat = b.len.toNat + 1) :
    ¬ b.Owns x ∧ b'.Owns x ∧ b'.cell x = some v ∧
      ∀ x', b.Owns x' → b'.Owns x' ∧ b'.cell x' = b.cell x' := by
  have := hi.le
  simp only [Owns, cell, hs, hx]
  refine ⟨by omega, by omega, by simp; omega, fun x' hx' => ⟨by omega, ?_⟩⟩
  rw [Slots.cell_setCell_ne _ _ _ _ (by omega)]

theorem lt_of_ltN {x : UInt64} (hn : n < 2 ^ 64) (h : x < UInt64.ofNat n) : x.toNat < n := by
  simpa [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hn] using h

/-- A cell below `len` holds a value. -/
theorem cell_some (b : Bump T n) (h : b.Inv) (i : Nat) (hi : i < b.len.toNat) :
    ∃ v, b.slots.cell i = some v := by
  have hf := BumpInv.full h i hi
  simp only [Slots.isFull] at hf
  exact Option.isSome_iff_exists.mp hf

end Bump
end

section
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat) (hn : n < 2 ^ 64)
include hn

set_option mp.autoSpec false in
/-- The empty arena. -/
mp def Bump.new ensures result.Inv ∧ result.len = 0 : Bump T n :=
  { slots := Slots.empty n, len := 0 }

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- `alloc` returns the next cell, the index `len`, or `Full` exactly when the arena is full. -/
mp def Bump.alloc (b : &mut Bump T n) (v : T) requires b.Inv
    ensures b'.Inv ∧ match result with
      | .ok x => x.idx = b.len ∧ b'.slots = b.slots.setCell b.len.toNat (some v) ∧
          b'.len.toNat = b.len.toNat + 1
      | .error _ => b' = b ∧ b.len.toNat = n : Result Full (Bump.Ix T n) := do
  let i := b.len
  if i < n then
    let _ := b.slots.put! i v
    b.len := i +! 1
    ok { idx := i }
  else err Full.mk

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- `alloc!` returns the next cell. The obligation `len < n` replaces the check. -/
mp def Bump.alloc! (b : &mut Bump T n) (v : T) requires b.Inv ∧ b.len.toNat < n
    ensures b'.Inv ∧ ¬ b.Owns result ∧ b'.Owns result ∧ b'.cell result = some v ∧
      b'.used = b.used + 1 ∧ (∀ x', b.Owns x' → b'.Owns x' ∧ b'.cell x' = b.cell x') ∧
      result.idx = b.len ∧ b'.slots = b.slots.setCell b.len.toNat (some v) : Bump.Ix T n := do
  let i := b.len
  let _ := b.slots.put! i v
  b.len := i +! 1
  { idx := i }

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- Checked access, which gives `ok v` exactly for an allocated index whose cell holds `v`. -/
mp def Bump.get (b : &Bump T n) (x : Bump.Ix T n) requires b.Inv
    ensures match result with
      | .ok v => x.idx.toNat < b.len.toNat ∧ b.slots.cell x.idx.toNat = some v
      | .error _ => b.len.toNat ≤ x.idx.toNat : Result Unit T :=
  let i := x.idx
  if i < b.len then ok b.slots[i]! else err ()

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- Access with the obligation `idx < len` and no check. -/
mp def Bump.get! (b : &Bump T n) (x : &Bump.Ix T n) requires b.Inv ∧ x.idx.toNat < b.len.toNat
    ensures b.slots.cell x.idx.toNat = some result : T :=
  let i := x.idx
  b.slots[i]!

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- The allocator interface's `free` of an index. A bump arena does not reuse cells before
`reset`, so this reads the cell and changes nothing. -/
mp def Bump.free (b : &mut Bump T n) (x : Bump.Ix T n) requires b.Inv ∧ x.idx.toNat < b.len.toNat
    ensures b.slots.cell x.idx.toNat = some result ∧ b' = b : T :=
  let i := x.idx
  b.slots[i]!

set_option mp.autoSpec false in
/-- Empty the arena. -/
mp def Bump.reset (b : &mut Bump T n) ensures b'.Inv ∧ b'.len = 0 : Unit := do
  b.slots := Slots.empty n
  b.len := 0
  ()

mp prove Bump.alloc.safe := by mp_auto [Bump.Inv, BumpInv.vacant, BumpInv.full, BumpInv.empty]

/-- `alloc!` compiles to no check. -/
mp prove Bump.alloc!.safe := by mp_auto [Bump.Inv, BumpInv.vacant, BumpInv.full, BumpInv.empty]

mp prove Bump.get.safe := by mp_auto [Bump.Inv, BumpInv.vacant, BumpInv.full, BumpInv.empty]

mp prove Bump.get!.safe := by mp_auto [Bump.Inv, BumpInv.vacant, BumpInv.full, BumpInv.empty]

mp prove Bump.new.spec := by mp_auto [Bump.Inv, BumpInv.vacant, BumpInv.full, BumpInv.empty]

mp prove Bump.alloc.spec := by
  intro b v
  vcgen [Bump.alloc]
  case vc1 h hlt =>
    have hl := Bump.lt_of_ltN hn hlt
    have hp := h.push v hl hn
    and_intros
    all_goals first
      | exact hp
      | rfl
      | (rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; rw [Nat.mod_eq_of_lt (by omega)])
  case vc2 h hlt =>
    have := h.le
    have : ¬ b.len.toNat < n := fun h => hlt (by simpa [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hn] using h)
    and_intros
    all_goals first | exact h | rfl | omega

mp prove Bump.alloc!.spec := by
  intro b v
  vcgen [Bump.alloc!]
  rename_i h
  have hl : (b.len + 1).toNat = b.len.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; rw [Nat.mod_eq_of_lt (by omega)]
  have hf := Bump.fresh b { slots := b.slots.setCell b.len.toNat (some v), len := b.len + 1 }
    { idx := b.len } v (h.1.push v h.2 hn) rfl rfl hl
  and_intros
  all_goals first
    | exact h.1.push v h.2 hn | exact hf.1 | exact hf.2.1 | exact hf.2.2.1 | exact hl
    | exact hf.2.2.2 | rfl

mp prove Bump.get.spec := by
  intro b x
  vcgen [Bump.get]
  case vc1 h hlt =>
    have hi : x.idx.toNat < b.len.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hlt
    have hf := h.full _ hi
    simp only [Slots.isFull] at hf
    refine ⟨hi, ?_⟩
    cases hc : b.slots.cell x.idx.toNat with
    | none => simp [hc] at hf
    | some a => rfl
  case vc2 hlt => simpa [UInt64.lt_iff_toNat_lt] using hlt

mp prove Bump.reset.spec := by mp_auto [Bump.Inv, BumpInv.vacant, BumpInv.full, BumpInv.empty]

mp prove Bump.free.safe := by mp_auto [Bump.Inv, BumpInv.vacant, BumpInv.full, BumpInv.empty]

mp prove Bump.get!.spec := by
  intro b x
  vcgen [Bump.get!]
  rename_i h
  obtain ⟨v, hv⟩ := Bump.cell_some b h.1 _ h.2
  simp [hv]

mp prove Bump.free.spec := by
  intro b x
  vcgen [Bump.free]
  rename_i h
  obtain ⟨v, hv⟩ := Bump.cell_some b h.1 _ h.2
  simp [hv]

/-! ### The bump arena as an allocator -/

/-- The bump arena implements the allocator interface from its own contracts. Its `free` gives
nothing back, so `used` stays. -/
mp implementation Bump.impl : Alloc T where
  S := Bump T n
  K := Bump.Ix T n
  copyS := ⟨by
    have := (inferInstance : Data.Copy T).linear_false
    show Fields.linear _ = false
    simp [Fields.linear, Data.linear_slots, Data.linear_vector, this] <;> rfl⟩
  inhK := inferInstance
  cap := n
  reuse := false
  Inv := Bump.Inv
  Owns := Bump.Owns
  cell := Bump.cell
  used := Bump.used
  op new := Bump.new T n hn
  new_spec := Spec.triple_of_run fun _ => by
    obtain ⟨hi, hl⟩ := Bump.new.post T n hn; exact ⟨hi, by simp [Bump.used, hl]⟩
  op alloc := Bump.alloc T n hn
  alloc_spec s v := Spec.triple_of_run fun h => by
    have hp := Bump.alloc.post T n hn s v h
    revert hp; generalize (Bump.alloc T n hn s v).run = r; obtain ⟨_ | x, s', _⟩ := r
    · rintro ⟨hi, rfl, hl⟩; exact ⟨hi, rfl, by simp [hl]⟩
    · rintro ⟨hi, hx, hs, hl⟩
      have hf := Bump.fresh s s' x v hi hx hs hl
      exact ⟨hi, hf.1, hf.2.1, hf.2.2.1, hl, hf.2.2.2⟩
  op alloc! := Bump.alloc! T n hn
  alloc!_spec s v := Spec.triple_of_run fun h =>
    let ⟨a, b, c, d, e, f, _⟩ := Bump.alloc!.post T n hn s v h; ⟨a, b, c, d, e, f⟩
  op get := Bump.get! T n hn
  get_spec s x := Spec.triple_of_run fun h => Bump.get!.post T n hn s x h
  op free := Bump.free T n hn
  free_spec s x := Spec.triple_of_run fun h => by
    obtain ⟨hc, he⟩ := Bump.free.post T n hn s x h
    rw [he]; exact ⟨hc, h.1, rfl, fun x' hx' _ => ⟨hx', rfl⟩⟩

end

-- The interface's view of an instance's model, as equations for the `grind` of `mp_auto`.
section
variable {T : Type} [Data T] [Data.Copy T] [Inhabited T] {n : Nat} {hn : n < 2 ^ 64}
@[mp_auto] theorem Bump.impl_Owns (b : Bump T n) (x : Bump.Ix T n) :
    (Bump.impl T n hn).Owns b x = b.Owns x := rfl
@[mp_auto] theorem Bump.impl_cell (b : Bump T n) (x : Bump.Ix T n) :
    (Bump.impl T n hn).cell b x = b.cell x := rfl
@[mp_auto] theorem Bump.impl_used (b : Bump T n) : (Bump.impl T n hn).used b = b.len.toNat := rfl
@[mp_auto] theorem Bump.impl_Inv (b : Bump T n) : (Bump.impl T n hn).Inv b = b.Inv := rfl
@[mp_auto] theorem Bump.impl_cap : (Bump.impl T n hn).cap = n := rfl
@[mp_auto] theorem Bump.impl_reuse : (Bump.impl T n hn).reuse = false := rfl
end

/-! ## Instances -/

/-- `Bump8` has 8 cells of `UInt64`. -/
abbrev Bump8 := Bump UInt64 8
/-- The index of `Bump8`. -/
abbrev Bump8.Ix := Bump.Ix UInt64 8
/-- `Bump8` as an allocator. -/
abbrev Bump8.impl : Alloc UInt64 := Bump.impl UInt64 8 (by decide)

/-- `Buf16` is a byte buffer, `Bump U8 16`. -/
abbrev Buf16 := Bump UInt8 16

end Millipede.Lib
