import Millipede.Lib.Bitmap
import Millipede.Lib.Alloc
import Millipede.Lib.Linear
import Millipede.Meta.MpDef
import Std.Tactic.Do
import Std.WP

/-!
# The pool arena

`Pool T n W` is an arena written in Millipede. It holds `n` cells of type `T` as `Slots T n`, a
bitmap of `W` words that records which cells are full, and a live count. `Slots` cells carry no
tag, so the bitmap is what lets a program test at run time whether a cell is occupied.

A stored value is named by a key or by an index. A key `Pool.Key T n W` is an 8-byte linear
value made of an index and a ghost token. `alloc` creates one with the private constructor
`Key.mint` and `free` consumes it with the private `Key.burn`. The structure is sealed, so outside
this module a key cannot be built, its index cannot be overwritten, and it cannot be dropped,
which means each key is freed exactly once. An index `Pool.Ix` is copyable, and access through it
is checked and returns a `Result`.

The arena is generic over the cell type `T`, the capacity `n` and the number `W` of bitmap words,
under the hypotheses `n ≤ 64 * W` and `n < 2 ^ 64`, so its operations, obligations and contracts
are proved once for every `T`, `n` and `W`. The bitmap and counting lemmas and the invariant
`PoolInv` are in `Millipede/Lib/Bitmap.lean`. `Pool8`, with 8 cells of `UInt64` and one bitmap
word, and `Pool100`, with 100 cells of a struct and two bitmap words, are instances.

The operations are the following `mp def`s, shown for `Pool8`.

| operation | requires | run-time check |
|---|---|---|
| `new : Pool8` | | |
| `alloc (p : &mut Pool8) (v) : Result Full Key` | `p.Inv` | the free-bit search |
| `alloc! (p : &mut Pool8) (v) : Key` | `p.Inv ∧ p.live < 8` | none, an obligation |
| `free (p : &mut Pool8) (k : Key) : UInt64` | `p.Inv ∧ p.Owns k` | none |
| `get (p : &Pool8) (k : &Key) : UInt64` | `p.Owns k` | none |
| `set (p : &mut Pool8) (k : &Key) (v) : Unit` | `p.Owns k` | none |
| `ix (k : &Key) : Ix` | | |
| `getIx (p : &Pool8) (x : Ix) : Result Unit UInt64` | `p.Inv` | the bit test |

Access by key needs no check, because `p.Owns k`, which says that the key's cell is full, is the
obligation of `p.slots[k.idx]!`. A client discharges `Owns` from the contracts, either through
the accounting of the keys it holds in `Alloc.Holds` or `Alloc.KeyStack`, or through the frame
conditions of the calls before it. A client may also borrow the cell itself with
`let r := &mut p.slots[i]!`.

The invariant `Inv`, which says that a bit is set exactly when its cell is full and that `live`
is the number of bits set, holds of `new` and is kept by every operation. Every operation has a
contract. `alloc` fails only when the pool is full, the key it returns is owned by the new state,
and the obligation `live < 8` of `alloc!` is enough to need no run-time check. The pool
implements the allocator interface as `Pool.impl : Alloc T`, so the ownership accounting proved
once in `Millipede/Lib/Alloc.lean` applies to its keys. Arenas are described in
doc/design/arenas.md.
-/

namespace Millipede.Lib

open Millipede Std.WP

set_option experimental.vcgen true


/-! ## The search loop, once for every capacity -/

/-- The normal form of every pool's `findFree`, which is the first clear bit below `n`, or `top`,
equal to `n`, if there is none. -/
def findFreeLoop {W : Nat} (n : Nat) (top : UInt64) (bits : Vector UInt64 W) : Id UInt64 :=
  forIn (List.range n) top fun i acc =>
    if acc = top then
      (if vget bits (UInt64.ofNat i >>> 6).toNat default >>> UInt64.ofNat i &&& 1 = 0
        then pure (UInt64.ofNat i) else pure top) >>= fun a => pure (ForInStep.yield a)
    else pure (ForInStep.done acc)

/-- The search finds a clear bit, or reports that every bit below `n` is set. -/
theorem findFreeLoop_spec {W : Nat} (n : Nat) (top : UInt64) (bits : Vector UInt64 W)
    (hn : top.toNat = n) :
    ⦃True⦄ findFreeLoop n top bits
    ⦃fun r => (r.toNat < n ∧ bmBit bits r.toNat = false) ∨
      (r = top ∧ ∀ i < n, bmBit bits i = true)⦄ := by
  vcgen [findFreeLoop] invariants
  · fun pref _ acc => (acc.toNat < n ∧ bmBit bits acc.toNat = false) ∨
      (acc = top ∧ ∀ i < pref.length, bmBit bits i = true)
  case vc1 => simp
  case vc2 _ h => simpa using h
  case vc3 pref cur suff hr acc _ _ ht =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    have hc : (UInt64.ofNat pref.length).toNat = pref.length :=
      UInt64.toNat_ofNat_of_lt' (by
        have := top.toNat_lt; rw [show UInt64.size = 2 ^ 64 from rfl]; omega)
    left
    rw [bm_test_iff, hc] at ht
    rw [hc]; exact ⟨hlt, ht⟩
  case vc4 pref cur suff hr acc ih hacc ht =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    have hc : (UInt64.ofNat pref.length).toNat = pref.length :=
      UInt64.toNat_ofNat_of_lt' (by
        have := top.toNat_lt; rw [show UInt64.size = 2 ^ 64 from rfl]; omega)
    rw [bm_test_iff, hc] at ht
    right
    refine ⟨rfl, fun i hi => ?_⟩
    simp only [List.length_append, List.length_singleton] at hi
    rcases ih with ⟨h1, _⟩ | ⟨_, h2⟩
    · subst hacc; omega
    · by_cases hic : i = pref.length
      · subst hic; simpa using ht
      · exact h2 i (by omega)
  case vc5 _ ih hne =>
    rcases ih with h | ⟨h, _⟩
    · exact .inl h
    · exact absurd h hne

/-- The search as a value. -/
theorem findFreeLoop_run {W : Nat} (n : Nat) (top : UInt64) (bits : Vector UInt64 W)
    (hn : top.toNat = n) :
    ((findFreeLoop n top bits).run.toNat < n ∧ bmBit bits (findFreeLoop n top bits).run.toNat = false) ∨
      ((findFreeLoop n top bits).run = top ∧ ∀ i < n, bmBit bits i = true) := by
  exact Spec.run_of_triple (Q := fun r => (r.toNat < n ∧ bmBit bits r.toNat = false) ∨
    (r = top ∧ ∀ i < n, bmBit bits i = true)) (findFreeLoop_spec n top bits hn) trivial

/-- With fewer than `n` bits set, the search finds a clear bit below `n`. -/
theorem findFreeLoop_found {W : Nat} (n : Nat) (top : UInt64) (bits : Vector UInt64 W)
    (hn : top.toNat = n) (hc : cnt n (bmBit bits) < n) :
    (findFreeLoop n top bits).run.toNat < n ∧
      bmBit bits (findFreeLoop n top bits).run.toNat = false := by
  rcases findFreeLoop_run n top bits hn with h | ⟨_, h⟩
  · exact h
  · rw [cnt_all n _ h] at hc; omega

/-! ## The pool: `n` cells of `T`, a bitmap of `W` words -/

/-- A pool of `n` cells of `T`: the cells, a bitmap of `W` words, the live count. -/
structure Pool (T : Type) (n W : Nat) where
  slots : Slots T n
  bits : Vector UInt64 W
  live : UInt64
deriving Data

/-- A key of `Pool`, which is linear through its `LinTok` field and sealed by its private
constructor. -/
structure Pool.Key (T : Type) (n W : Nat) where
  private mk ::
  idx : UInt64
  tok : LinTok
deriving Data

/-- The value of a `take!` or `!` access to an empty `Slots Key` cell. Only the Core model reads
it, and only when the access's obligation that the cell is full fails, which `safe` excludes.
Programs cannot name it, so it does not forge keys. -/
instance {T : Type} {n W : Nat} : Inhabited (Pool.Key T n W) := ⟨⟨0, ⟨⟩⟩⟩

/-- A copyable index into a `Pool`. -/
structure Pool.Ix (T : Type) (n W : Nat) where
  idx : UInt64
deriving Data, Repr, DecidableEq

/-- Mint a key. It is private, so that only this module creates keys. The layout of a key, an
index and a ghost token, does not depend on the parameters, so its law is the closed one,
transported. -/
private abbrev Pool.Key.mint (T : Type) [Data T] (n W : Nat) : Ctor [Ty.u64] ⟨Pool.Key T n W⟩ :=
  ⟨"Key.mint", .struct, fun env => ⟨env.get .here, ⟨⟩⟩,
    some ⟨Flat.CtorLaw.struct _ rfl _ (by
      have h1 : Data.shape (Pool.Key T n W) = Data.shape (Pool.Key Unit 0 0) := rfl
      have h2 : Flat.planOf [Ty.u64] ⟨Pool.Key T n W⟩ .struct =
          Flat.planOf [Ty.u64] ⟨Pool.Key Unit 0 0⟩ .struct := rfl
      rw [h1, h2]; decide) (by
      intro env bs ha
      match env, ha with
      | .cons a .nil, ⟨h0, _⟩ =>
        exact ⟨h0 _ (List.mem_singleton_self _),
          ⟨by show (slice _ _ 0).length = 0; simp [slice], trivial⟩, trivial⟩)⟩, none⟩

/-- Consume a key. It is private, so that only `free` consumes keys. -/
private abbrev Pool.Key.burn (T : Type) [Data T] (n W : Nat) : Ctor [⟨Pool.Key T n W⟩] Ty.unit :=
  ⟨"Key.burn", .struct, fun _ => (), some ⟨Flat.CtorLaw.unit _ _ _⟩, none⟩

section
variable {T : Type} [Data T] {n W : Nat}

namespace Pool

/-- The pool invariant. -/
abbrev Inv (p : Pool T n W) : Prop := PoolInv p.slots p.bits p.live

/-- The key's cell is full, which is the obligation of access by key. -/
abbrev Owns (p : Pool T n W) (k : Key T n W) : Prop := p.slots.isFull k.idx.toNat = true

/-- Two keys with the same index are equal, since keys are compared by index and their token is
a ghost. -/
theorem Key.ext' {k₁ k₂ : Key T n W} (h : k₁.idx = k₂.idx) : k₁ = k₂ := by
  cases k₁; cases k₂; cases h; rfl

/-! The contracts below are stated in the model of the allocator interface of
`Millipede/Lib/Alloc.lean`, so closed clients get what generic ones get from `Alloc`. -/

/-- The content of a key's cell. -/
abbrev cell (p : Pool T n W) (k : Key T n W) : Option T := p.slots.cell k.idx.toNat
/-- The live cells. -/
abbrev used (p : Pool T n W) : Nat := p.live.toNat
/-- Allocating a vacant cell, seen in the model as a fresh key, its content and the frame. -/
theorem fresh (p p' : Pool T n W) (k : Key T n W) (v : T) (hv : p.slots.isVacant k.idx.toNat = true)
    (hlt : k.idx.toNat < n) (hs : p'.slots = p.slots.setCell k.idx.toNat (some v)) :
    ¬ p.Owns k ∧ p'.Owns k ∧ p'.cell k = some v ∧
      ∀ k', p.Owns k' → p'.Owns k' ∧ p'.cell k' = p.cell k' := by
  simp only [Owns, cell, hs, Slots.not_full_of_vacant hv]
  refine ⟨by simp, by simp [Slots.isFull, hlt], by simp [hlt], fun k' hk' => ?_⟩
  exact Slots.frame_put _ _ _ _ hk' hv

/-- Emptying the cell of `k`: every other owned key keeps its cell. -/
theorem frame_free (p p' : Pool T n W) (k : Key T n W) (hs : p'.slots = p.slots.setCell k.idx.toNat none) :
    ∀ k', p.Owns k' → k' ≠ k → p'.Owns k' ∧ p'.cell k' = p.cell k' := by
  intro k' hk' hne
  have hne' : k'.idx.toNat ≠ k.idx.toNat := fun he => hne (Key.ext' (UInt64.toNat_inj.mp he))
  simp only [Owns, cell, hs, Slots.isFull, Slots.cell_setCell_ne _ _ _ _ (Ne.symm hne')] at hk' ⊢
  exact ⟨hk', trivial⟩

theorem lt_of_ltN {x : UInt64} (hn : n < 2 ^ 64) (h : x < UInt64.ofNat n) : x.toNat < n := by
  simpa [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hn] using h

theorem ofNat_toNat (hn : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hn]

end Pool
end

section
variable (T : Type) [Data T] [Inhabited T] [Data.Copy T] (n W : Nat) (hW : n ≤ 64 * W)
  (hn : n < 2 ^ 64)
include hW hn

set_option mp.autoSpec false in
/-- The empty pool. -/
mp def Pool.new ensures result.Inv ∧ result.live = 0 : Pool T n W :=
  { slots := Slots.empty n, bits := Vector.replicate W 0, live := 0 }

set_option mp.autoSpec false in
/-- The first free cell, or `n` when every bit is set. -/
mp def Pool.findFree (p : &Pool T n W)
    ensures (result.toNat < n ∧ bmBit p.bits result.toNat = false) ∨
      (result = UInt64.ofNat n ∧ ∀ i < n, bmBit p.bits i = true) : UInt64 := do
  let mut acc := n
  for j in 0...n do
    if acc != n then break
    let w := p.bits[j >>> 6]!
    acc := if ((w >>> j) &&& 1) == 0 then j else n
  acc

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- `alloc` returns a fresh key whose cell now holds `v`, or `Full` exactly when all `n` cells are
live. -/
mp def Pool.alloc (p : &mut Pool T n W) (v : T) requires p.Inv
    ensures p'.Inv ∧ match result with
      | .ok k => p'.Owns k ∧ k.idx.toNat < n ∧ p.slots.isVacant k.idx.toNat = true ∧
          p'.slots = p.slots.setCell k.idx.toNat (some v) ∧ p'.live.toNat = p.live.toNat + 1
      | .error _ => p' = p ∧ p.live.toNat = n : Result Full (Pool.Key T n W) := do
  let i := Pool.findFree (&p)
  if i < n then
    let wi := i >>> 6
    let w := p.bits[wi]!
    if ((w >>> i) &&& 1) == 0 then
      let _ := p.slots.put! i v
      p.bits[wi]! := w ||| (1 <<< i)
      p.live := p.live +! 1
      ok (Pool.Key.mint T n W i)
    else err Full.mk
  else err Full.mk

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- `alloc!` returns a fresh key whose cell now holds `v`. The obligation `live < n` replaces the
check. -/
mp def Pool.alloc! (p : &mut Pool T n W) (v : T) requires p.Inv ∧ p.live.toNat < n
    ensures p'.Inv ∧ ¬ p.Owns result ∧ p'.Owns result ∧ p'.cell result = some v ∧
      p'.used = p.used + 1 ∧ (∀ k', p.Owns k' → p'.Owns k' ∧ p'.cell k' = p.cell k') ∧
      p'.slots = p.slots.setCell result.idx.toNat (some v) : Pool.Key T n W := do
  let i := Pool.findFree (&p)
  let _ := p.slots.put! i v
  let wi := i >>> 6
  let w := p.bits[wi]!
  p.bits[wi]! := w ||| (1 <<< i)
  p.live := p.live +! 1
  Pool.Key.mint T n W i

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- `free` consumes the key, empties its cell and returns its value, leaving one fewer live
cell. -/
mp def Pool.free (p : &mut Pool T n W) (k : Pool.Key T n W) requires p.Inv ∧ p.Owns k
    ensures p.cell k = some result ∧ p'.Inv ∧ p'.used + 1 = p.used ∧
      (∀ k', p.Owns k' → k' ≠ k → p'.Owns k' ∧ p'.cell k' = p.cell k') ∧
      p'.slots = p.slots.setCell k.idx.toNat none : T := do
  let i := k.idx
  let _ := Pool.Key.burn T n W k
  let v := p.slots.take! i
  let wi := i >>> 6
  let w := p.bits[wi]!
  p.bits[wi]! := w &&& ~~~(1 <<< i)
  p.live := p.live -! 1
  v

set_option mp.autoSpec false in
/-- Read the cell of a key, with no run-time check. -/
mp def Pool.get (p : &Pool T n W) (k : &Pool.Key T n W) requires p.Owns k
    ensures p.slots.cell k.idx.toNat = some result : T :=
  let i := k.idx
  p.slots[i]!

set_option mp.autoSpec false in
/-- Write the cell of a key, with no run-time check. The invariant and the live count are kept. -/
mp def Pool.set (p : &mut Pool T n W) (k : &Pool.Key T n W) (v : T) requires p.Owns k
    ensures (p.Inv → p'.Inv) ∧ p'.slots = p.slots.setCell k.idx.toNat (some v) ∧
      p'.live = p.live : Unit := do
  let i := k.idx
  p.slots[i]! := v
  ()

/-- The copyable index of a key. -/
mp def Pool.ix (k : &Pool.Key T n W) : Pool.Ix T n W := { idx := k.idx }

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- Checked access by index, which tests the bitmap and gives `ok v` exactly when the index's
cell holds `v` and `err` when it is empty. -/
mp def Pool.getIx (p : &Pool T n W) (x : Pool.Ix T n W) requires p.Inv
    ensures match result with
      | .ok v => p.slots.cell x.idx.toNat = some v
      | .error _ => p.slots.cell x.idx.toNat = none : Result Unit T :=
  let i := x.idx
  if i < n then
    let w := p.bits[i >>> 6]!
    if ((w >>> i) &&& 1) == 0 then err () else ok p.slots[i]!
  else err ()

/-- The live count. -/
mp def Pool.count (p : &Pool T n W) ensures result = p.live : UInt64 := p.live

/-! ### Proofs for `Pool` -/

theorem Pool.findFree_eq (p : Pool T n W) :
    Pool.findFree T n W hW hn p =
      (do let v ← findFreeLoop n (UInt64.ofNat n) p.bits; pure (v, ())) := rfl

theorem Pool.findFree_run (p : Pool T n W) :
    (Pool.findFree T n W hW hn p).run.1 = (findFreeLoop n (UInt64.ofNat n) p.bits).run := rfl

mp prove Pool.new.spec := by mp_auto [PoolInv.empty, PoolInv.live_pos, PoolInv.live_lt, Slots.lt_of_isFull, shr6_toNat]

mp prove Pool.findFree.spec := by
  intro p; rw [Pool.findFree_eq T n W hW hn]
  vcgen [findFreeLoop_spec n (UInt64.ofNat n) p.bits (Pool.ofNat_toNat hn)]
  case vc1 h => exact h

mp prove Pool.alloc.spec := by
  intro p v
  vcgen [Pool.alloc]
  case vc1 h x _ hs hlt ht =>
    have hx := Pool.lt_of_ltN hn hlt
    have hb : bmBit p.bits x.toNat = false := (bm_test_iff _ _).mp ht
    exact ⟨h.put x v hx hW hb hn, by simp [hx], hx, h.vacant_of_clear _ hx hb,
      rfl, h.live_succ _ hx hb hn⟩
  case vc2 h x _ hs hlt ht =>
    exfalso
    rcases hs with ⟨_, hb⟩ | ⟨rfl, _⟩
    · exact ht ((bm_test_iff _ _).mpr hb)
    · simp at hlt
  case vc3 h x _ hs hlt =>
    rcases hs with ⟨h1, _⟩ | ⟨_, hall⟩
    · exact absurd (by simpa [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hn] using h1) hlt
    · exact ⟨h, by rw [h.live_eq, cnt_all n _ hall]⟩

/-! ### Obligations, discharged from the invariant and `requires` -/

mp prove Pool.alloc.safe := by
  intro ω w p v h
  mp_safe [Pool.alloc.exp, Pool.findFree.req, Pool.findFree.exp_denote, shr6_toNat]
    using Pool.findFree.Safe'
  all_goals rename_i hlt ht
  all_goals have hb := (bm_test_iff' _ _).mp ht
  · exact h.vacant_of_clear _ (Pool.lt_of_ltN hn hlt) hb
  · have := h.live_lt _ (Pool.lt_of_ltN hn hlt) hb; omega

/-- `alloc!` compiles to no check, because `live < n` and the invariant make the search
succeed. -/
mp prove Pool.alloc!.safe := by
  intro ω w p v h
  mp_safe [Pool.alloc!.exp, Pool.findFree.req, Pool.findFree.exp_denote, shr6_toNat]
    using Pool.findFree.Safe'
  all_goals
    have hf := findFreeLoop_found n (UInt64.ofNat n) p.bits (Pool.ofNat_toNat hn) (by rw [← h.1.live_eq]; exact h.2)
    rw [← Pool.findFree_run T n W hW hn] at hf
  · exact h.1.vacant_of_clear _ hf.1 hf.2
  all_goals omega

mp prove Pool.free.safe := by
  intro ω w p k h
  mp_safe [Pool.free.exp, shr6_toNat]
  all_goals have := Slots.lt_of_isFull h.2
  all_goals have := h.1.live_pos _ h.2
  all_goals omega

mp prove Pool.getIx.safe := by
  intro ω w p x h
  mp_safe [Pool.getIx.exp, shr6_toNat]
  rename_i hlt ht
  exact h.full_of_set _ (Pool.lt_of_ltN hn hlt) (by simpa using mt (bm_test_iff' _ _).mpr ht)

/-! ### Contracts -/

mp prove Pool.alloc!.spec := by
  intro p v
  apply Triple.iff.mpr
  intro ⟨h, hl⟩
  have hf := findFreeLoop_found n (UInt64.ofNat n) p.bits (Pool.ofNat_toNat hn) (by rw [← h.live_eq]; exact hl)
  rw [← Pool.findFree_run T n W hW hn] at hf
  have ho : (p.slots.setCell (Pool.findFree T n W hW hn p).run.1.toNat (some v)).isFull
      (Pool.findFree T n W hW hn p).run.1.toNat = true := by simp [hf.1]
  have hfr := Pool.fresh p (Pool.alloc! T n W hW hn p v).run.2.1 (Pool.alloc! T n W hW hn p v).run.1 v
    (h.vacant_of_clear _ hf.1 hf.2) hf.1 rfl
  exact ⟨h.put _ v hf.1 hW hf.2 hn, hfr.1, ho, hfr.2.2.1, h.live_succ _ hf.1 hf.2 hn,
    hfr.2.2.2, rfl⟩

mp prove Pool.free.spec := by
  intro p k
  vcgen [Pool.free]
  rename_i hh
  obtain ⟨h, ho⟩ := hh
  have hx := Slots.lt_of_isFull ho
  have hp := h.take k.idx hW ho
  and_intros
  · simp only [Slots.isFull] at ho
    cases hc : p.slots.cell k.idx.toNat with
    | none => simp [hc] at ho
    | some a => rfl
  · exact hp
  · have := hp.live_eq; have := h.live_eq
    have := cnt_flip_off n k.idx.toNat (bmBit p.bits) (bmBit (bmClr p.bits k.idx)) hx
      (h.set_of_full _ ho) (by rw [bmBit_clr _ _ _ (by omega)]; simp)
      (fun i _ hne => by rw [bmBit_clr _ _ _ (by omega)]; simp [hne])
    simp only [bmClr] at *
    omega
  · exact Pool.frame_free p _ k rfl

mp prove Pool.get.spec := by
  intro p k
  vcgen [Pool.get]
  rename_i ho
  simp only [Slots.isFull] at ho
  cases hc : p.slots.cell k.idx.toNat with
  | none => simp [hc] at ho
  | some a => rfl

mp prove Pool.set.spec := by
  intro p k v
  vcgen [Pool.set]
  rename_i ho
  exact fun h => h.write _ v ho

mp prove Pool.getIx.spec := by
  intro p x
  vcgen [Pool.getIx]
  case vc1 h hlt ht =>
    have hb := (bm_test_iff _ _).mp ht
    have := h.bit_iff _ (Pool.lt_of_ltN hn hlt)
    rw [hb] at this
    cases hc : p.slots.cell x.idx.toNat with
    | none => rfl
    | some a => simp [hc] at this
  case vc2 h hlt ht =>
    have hf := h.full_of_set _ (Pool.lt_of_ltN hn hlt) (by simpa using mt (bm_test_iff _ _).mpr ht)
    simp only [Slots.isFull] at hf
    cases hc : p.slots.cell x.idx.toNat with
    | none => simp [hc] at hf
    | some a => rfl
  case vc3 hlt =>
    simp only [Slots.cell, vget]
    rw [dite_eq_right_iff.mpr (fun h' => absurd h' (by simpa [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hn] using hlt))]

/-! ### The pool as an allocator -/

/-- The pool implements the allocator interface `Alloc T`, from its own contracts. -/
mp implementation Pool.impl : Alloc T where
  S := Pool T n W
  K := Pool.Key T n W
  copyS := ⟨by
    have := (inferInstance : Data.Copy T).linear_false
    show Fields.linear _ = false
    simp [Fields.linear, Data.linear_slots, Data.linear_vector, this] <;> rfl⟩
  inhK := inferInstance
  cap := n
  reuse := true
  Inv := Pool.Inv
  Owns := Pool.Owns
  cell := Pool.cell
  used := Pool.used
  op new := Pool.new T n W hW hn
  new_spec := Spec.triple_of_run fun _ => by
    obtain ⟨hi, hl⟩ := Pool.new.post T n W hW hn; exact ⟨hi, by simp [Pool.used, hl]⟩
  op alloc := Pool.alloc T n W hW hn
  alloc_spec s v := Spec.triple_of_run fun h => by
    have hp := Pool.alloc.post T n W hW hn s v h
    revert hp; generalize (Pool.alloc T n W hW hn s v).run = r; obtain ⟨_ | k, s', _⟩ := r
    · rintro ⟨hi, rfl, hl⟩; exact ⟨hi, rfl, by simp [hl]⟩
    · rintro ⟨hi, _, hlt, hv, hs, hl⟩
      exact ⟨hi, (Pool.fresh s s' k v hv hlt hs).1, (Pool.fresh s s' k v hv hlt hs).2.1,
        (Pool.fresh s s' k v hv hlt hs).2.2.1, hl, (Pool.fresh s s' k v hv hlt hs).2.2.2⟩
  op alloc! := Pool.alloc! T n W hW hn
  alloc!_spec s v := Spec.triple_of_run fun h =>
    let ⟨a, b, c, d, e, f, _⟩ := Pool.alloc!.post T n W hW hn s v h; ⟨a, b, c, d, e, f⟩
  op get := Pool.get T n W hW hn
  get_spec s k := Spec.triple_of_run fun h => Pool.get.post T n W hW hn s k h.2
  op free := Pool.free T n W hW hn
  free_spec s k := Spec.triple_of_run fun h =>
    let ⟨a, b, c, d, _⟩ := Pool.free.post T n W hW hn s k h; ⟨a, b, c, d⟩

end

-- The interface's view of an instance's types and model, as equations for the `grind` of
-- `mp_auto`, `rw` and `simp only`. `Pool.impl` is reducible, so the two forms are also the same
-- up to reducible unfolding.
section
variable {T : Type} [Data T] [Inhabited T] [Data.Copy T] {n W : Nat} {hW : n ≤ 64 * W}
  {hn : n < 2 ^ 64}
@[mp_auto] theorem Pool.impl_Owns (p : Pool T n W) (k : Pool.Key T n W) :
    (Pool.impl T n W hW hn).Owns p k = p.Owns k := rfl
@[mp_auto] theorem Pool.impl_cell (p : Pool T n W) (k : Pool.Key T n W) :
    (Pool.impl T n W hW hn).cell p k = p.cell k := rfl
@[mp_auto] theorem Pool.impl_used (p : Pool T n W) :
    (Pool.impl T n W hW hn).used p = p.live.toNat := rfl
@[mp_auto] theorem Pool.impl_Inv (p : Pool T n W) : (Pool.impl T n W hW hn).Inv p = p.Inv := rfl
@[mp_auto] theorem Pool.impl_cap : (Pool.impl T n W hW hn).cap = n := rfl
@[mp_auto] theorem Pool.impl_reuse : (Pool.impl T n W hW hn).reuse = true := rfl
end

/-! ## Instances -/

/-- `Pool8` has 8 cells of `UInt64` and one bitmap word. -/
abbrev Pool8 := Pool UInt64 8 1
/-- The key of `Pool8`. -/
abbrev Pool8.Key := Pool.Key UInt64 8 1
/-- `Pool8` as an allocator. -/
abbrev Pool8.impl : Alloc UInt64 := Pool.impl UInt64 8 1 (by decide) (by decide)

/-- The element type of `Pool100`, which has two words. -/
structure Cell2 where
  x : UInt64
  y : UInt64
deriving Data, Inhabited, Repr, DecidableEq

instance : Data.Copy Cell2 := ⟨rfl⟩

/-- `Pool100` has 100 cells of a struct, so its bitmap spans two words, with cells `64…99` in word
1, and the search crosses a word boundary. -/
abbrev Pool100 := Pool Cell2 100 2

end Millipede.Lib
