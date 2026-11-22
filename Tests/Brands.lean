import Millipede.Lib.Pool
import Millipede.Lib.Bump

/-!
# Tests of branded arena keys

A key's type carries its arena's parameters, so a key of one arena given to another is a Lean
type error at the argument. The tests give a `Pool.Key UInt64 8 1` to a `Pool Cell2 100 2` and to a
bump arena, and in a generic client they give `A.K` to an operation of `B`. When two arenas have
the same type the types cannot tell their keys apart, so the obligation that `b` owns a key of `a`
is left undischarged, and it is refuted for two fresh pools.

A double free in a generic client is rejected, because the key type of an implementation variable
is treated as linear. Using a bump index after `reset` leaves an obligation, which is refuted. A
key takes the 8 bytes of its index. Two seeded bugs in arenas, an `alloc!` that returns a key
already live and a `free` that returns `0` instead of the cell's value, have contracts that are
refuted, so neither can be built into an implementation.
-/

namespace Millipede.Tests.Brands

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true

theorem h8W : 8 ≤ 64 * 1 := by decide
theorem h8n : 8 < 2 ^ 64 := by decide

/-! ## The brand: a key of one arena is not one of another -/

/-- error: type mismatch: expected Millipede.Lib.Pool.Key Cell2 100 2, but this has type Millipede.Lib.Pool.Key UInt64 8 1 -/
#guard_msgs in
mp def mixInst (a : &mut Pool8) (b : &mut Pool100) (k : Pool8.Key) requires a.Inv ∧ a.Owns k :
    Cell2 :=
  Pool100.free (&mut b) k

/-- error: type mismatch: expected Millipede.Lib.Bump.Ix UInt64 8, but this has type Millipede.Lib.Pool.Key UInt64 8 1 -/
#guard_msgs in
mp def mixKinds (a : &mut Pool8) (b : &mut Bump8) (k : Pool8.Key) requires a.Inv ∧ a.Owns k :
    UInt64 :=
  Bump8.free (&mut b) k

section
variable (A B : Alloc UInt64)
/-- error: type mismatch: expected B.K, but this has type A.K -/
#guard_msgs in
mp def Mix.f (a : &mut A.S) (b : &mut B.S) (v : UInt64) requires A.Inv a ∧ A.used a < A.cap :
    UInt64 := do
  let k := A.alloc! (&mut a) v
  B.free (&mut b) k
end

/-! ## Two arenas of one type, whose obligation is left and is false -/

mp def mix2 (a b : &mut Pool8) (v : UInt64) requires a.Inv ∧ a.live.toNat < 8 ∧ b.Inv : UInt64 :=
  let k := Pool8.alloc! (&mut a) v
  Pool8.free (&mut b) k

run_cmd do
  if (← Lean.getEnv).contains `Millipede.Tests.Brands.mix2.safe then
    throwError "mix2.safe should not exist"

/-- The obligation left, that `b` owns `k`, is false, since `b` is a fresh pool. -/
example (ω : Oracle) : ¬ mix2.SafeGoal := fun h => by
  have hn := Pool.new.post UInt64 8 1 h8W h8n
  have := h ω World.init (Pool.new UInt64 8 1 h8W h8n).run (Pool.new UInt64 8 1 h8W h8n).run 0
    ⟨hn.1, by simp [hn.2], hn.1⟩
  simp only [mix2.exp, Exp.safe, Pool.free.req, Pool.alloc!.exp_denote, RArgs.denote,
    RArgs.writeBack, Place.get, Place.set, Env.get_here, Env.get_there, Atom.denote] at this
  have := this.2.2.2.2.1.2
  revert this; decide

/-! ## Liveness -/

section
variable (A : Alloc UInt64)
/-- error: linear let `k` of type A.K is used 2 times; it must be used exactly once -/
#guard_msgs in
/-- A double free in a generic client, which is rejected for every implementation because the key
type of an implementation variable is linear. -/
mp def Twice.f (a : &mut A.S) (v : UInt64) requires A.Inv a ∧ A.used a < A.cap : UInt64 := do
  let k := A.alloc! (&mut a) v
  let x := A.free (&mut a) k
  let y := A.free (&mut a) k
  x + y
end

/-- Use of a bump index after `reset`. -/
mp def stale (b : &mut Bump8) (x : &Bump8.Ix) requires b.Inv ∧ x.idx.toNat < b.len.toNat :
    UInt64 :=
  let _ := Bump8.reset (&mut b)
  Bump8.get! (&b) (&x)

run_cmd do
  if (← Lean.getEnv).contains `Millipede.Tests.Brands.stale.safe then
    throwError "stale.safe should not exist"

/-- The obligation left is false, since no index is live after `reset`. -/
example (ω : Oracle) : ¬ stale.SafeGoal := fun h => by
  have hn := Bump.new.post UInt64 8 h8n
  have hb := Bump.alloc!.post UInt64 8 h8n (Bump.new UInt64 8 h8n).run 7 ⟨hn.1, by simp [hn.2]⟩
  have := h ω World.init (Bump.alloc! UInt64 8 h8n (Bump.new UInt64 8 h8n).run 7).run.2.1 ⟨0⟩
    ⟨hb.1, by simp only [hb.2.2.2, hn.2]; decide⟩
  simp only [stale.exp, Exp.safe, Bump.get!.req, Bump.reset.exp_denote, RArgs.denote,
    RArgs.writeBack, Place.get, Place.set, Env.get_here, Env.get_there] at this
  have := this.2.2.2.2.1.2
  revert this; decide

/-! ## A key is its index -/

example : (Data.shape Pool8.Key).size = 8 := by decide
example : (Data.shape Pool8.Key).size = (Data.shape UInt64).size := by decide
example : (Data.shape (Pool.Key Cell2 100 2)).size = (Data.shape Pool8.Key).size := by decide

/-! ## Seeded bugs in an arena, whose contracts cannot be proved -/

/-- An `alloc!` that hands out the default key `0` whatever cell it filled. -/
def badAlloc! (s : Pool8) (v : UInt64) : Id (Pool8.Key × (Pool8 × Unit)) :=
  (fun r => (default, r.2)) <$> Pool.alloc! UInt64 8 1 h8W h8n s v

/-- Its `alloc!_spec` is false, because with cell `0` already live key `0` is not fresh. -/
example : ¬ ∀ (s : Pool8) (v : UInt64), ⦃s.Inv ∧ s.live.toNat < 8⦄ badAlloc! s v
    ⦃fun r => ¬ s.Owns r.1⦄ := fun h => by
  have hn := Pool.new.post UInt64 8 1 h8W h8n
  have h1 := Pool.alloc!.post UInt64 8 1 h8W h8n (Pool.new UInt64 8 1 h8W h8n).run 1
    ⟨hn.1, by simp [hn.2]⟩
  have := Spec.run_of_triple
    (h (Pool.alloc! UInt64 8 1 h8W h8n (Pool.new UInt64 8 1 h8W h8n).run 1).run.2.1 2)
    ⟨h1.1, by
      have := h1.2.2.2.2.1; simp only [Pool.used] at this; simp only [this, hn.2]; decide⟩
  revert this; decide

/-- A `free` that returns `0` instead of the cell's value. -/
mp def BadBump.free (b : &mut Bump8) (x : Bump8.Ix) requires b.Inv ∧ x.idx.toNat < b.len.toNat :
    UInt64 := 0

/--
error: unsolved goals
s : Bump8
k : Bump8.Ix
⊢ ⦃ Bump.Inv s ∧ Bump.Owns s k ⦄ BadBump.free s k ⦃ fun r =>
    let result := r.fst;
    let s' := r.snd.fst;
    Bump.cell s k = some result ∧
      Bump.Inv s' ∧
        (Bump.used s' + if false = true then 1 else 0) = Bump.used s ∧
          ∀ (k' : Bump8.Ix), Bump.Owns s k' → k' ≠ k → Bump.Owns s' k' ∧ Bump.cell s' k' = Bump.cell s k' ⦄
-/
#guard_msgs in
mp implementation badImpl : Alloc UInt64 where
  S := Bump8
  K := Bump8.Ix
  copyS := Bump8.impl.copyS
  inhK := inferInstance
  cap := 8
  reuse := false
  Inv := Bump.Inv
  Owns := Bump.Owns
  cell := Bump.cell
  used := Bump.used
  op new := Bump.new UInt64 8 h8n
  new_spec := Bump8.impl.new_spec
  op alloc := Bump.alloc UInt64 8 h8n
  alloc_spec := Bump8.impl.alloc_spec
  op alloc! := Bump.alloc! UInt64 8 h8n
  alloc!_spec := Bump8.impl.alloc!_spec
  op get := Bump.get! UInt64 8 h8n
  get_spec := Bump8.impl.get_spec
  op free := BadBump.free
  free_spec s k := by skip

/-- The goal is false, since a cell holding `1` is freed as `0`, so no proof of it exists. -/
example : ¬ ∀ (s : Bump8) (k : Bump8.Ix), ⦃s.Inv ∧ s.Owns k⦄ BadBump.free s k
    ⦃fun r => s.cell k = some r.1⦄ := fun h => by
  have hn := Bump.new.post UInt64 8 h8n
  have := Spec.run_of_triple (h (Bump.alloc! UInt64 8 h8n (Bump.new UInt64 8 h8n).run 1).run.2.1 ⟨0⟩)
    ⟨(Bump.alloc!.post UInt64 8 h8n _ _ ⟨hn.1, by simp [hn.2]⟩).1, by decide⟩
  revert this; decide

end Millipede.Tests.Brands
