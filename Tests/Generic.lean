import Millipede.Lib.Bump
import Millipede.Top.Sound
import Millipede.Meta.Emit

/-!
# Tests for generic definitions

An `mp def` under `variable` binders is elaborated once, with its type and size parameters as
Lean variables. Its Core term, normal form, borrow check, obligations and contract are each one
declaration quantified over those variables, and an instance is an application of them.

This suite checks generic functions over `Arr T n` and loops whose bounds involve `n`, and
derives `Data` for a parameterised struct and two parameterised enums, whose lenses,
constructors and splits are lawful for every `T` and `n`. It proves a bump arena's operations
once for every `T` and every `n < 2 ^ 64` and compiles a program that uses the arena at
`UInt64` and 8. It also checks how a generic callee's variables are inferred at a call, from the
arguments' types, the caller's context or a named argument.

An obligation that fails for some `n` stays open, and the images of the program at two arena
sizes differ, so the suite would notice a size that is ignored.

Generic definitions are described in doc/design/modules.md.
-/

namespace Millipede.Tests.Generic

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true

/-! ## 1. Open types and sizes -/

section
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat)

/-- Element `i` of an array, with the obligation `i < n`. -/
mp def get (a : &Arr T n) (i : UInt64) requires i.toNat < n : T := a[i]!

/-- A loop up to a size variable, in which `a[i]` for the counter of `0...n` on `Arr T n` needs no
obligation. -/
mp def fill (a : &mut Arr T n) (v : T) : Unit := do
  for i in 0...n do
    a[i] := v

/-- A generic caller of a generic callee, with a contract. -/
mp def get2 (a : &Arr T n) (i : UInt64) requires i.toNat < n
    ensures result = vget a i.toNat default : T :=
  get (&a) i

/-- Loops whose bounds involve `n`, with a lower bound, an inclusive bound and a `min` cap. -/
mp def count (x : UInt64) : UInt64 := do
  let mut c := 0
  for _ in 1...n do
    c := c + 1
  for _ in 0...=n do
    c := c + 1
  for _ in 0...min x n do
    c := c + 1
  c

end

/-- The Core term is a Lean function of the type and the size. -/
example : (T : Type) → [inst : Data T] → [Data.Copy T] → [Inhabited T] → (n : Nat) →
    Exp [Ty.u64, Ty.arr (@Ty.mk T inst) n] (Ty.pair (@Ty.mk T inst) (Ty.tup [])) := @get.exp
/-- The borrow check holds once for every copyable `T` and every `n`. -/
example : ∀ (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat),
    (get.fnRef T n).wf [.own, .shr] = true := @get.wf
/-- The obligations are discharged once, from `i < n`, for every `n`. -/
example : ∀ (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat) (ω : Oracle) (w : World)
    (a : Vector T n) (i : UInt64), i.toNat < n →
    Exp.safe ω (get.exp T n) (.cons i (.cons a .nil)) w := @get.safe
example : ∀ (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat) (ω : Oracle) (w : World)
    (a : Vector T n) (v : T), Exp.safe ω (fill.exp T n) (.cons v (.cons a .nil)) w := @fill.safe
/-- The contract holds once for every `T` and `n`. -/
example : ∀ (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat) (a : Vector T n)
    (i : UInt64), ⦃i.toNat < n⦄ get2 T n a i ⦃fun r => r.1 = vget a i.toNat default⦄ :=
  @get2.spec
/-- A definition takes only the variables it uses, so `count`, which mentions no type, takes
only `n`. -/
example : (n : Nat) → UInt64 → Id UInt64 := count
/-- An instance is an application, and at a closed instance the borrow check can also be decided. -/
example : (get.fnRef UInt64 8).wf [.own, .shr] = true := by decide
example : (count 5 3).run = 4 + 6 + 3 := by decide
example : (count 5 9).run = 4 + 6 + 5 := by decide

/-! ## 2. A parameterised struct -/

/-- A bump arena of `n` cells of `T`, for every `T` and `n`. -/
structure GBump (T : Type) (n : Nat) where
  slots : Slots T n
  len : UInt64
deriving Data

/-- An index into a bump arena. -/
structure GIx where
  idx : UInt64
deriving Data, Repr, DecidableEq, Inhabited

/-- `deriving Data` gives the instance for every `T` with `Data T` and every `n`. -/
example : (T : Type) → [Data T] → (n : Nat) → Data (GBump T n) := @GBump.instData
/-- The lens of a field has a law, certified once for every `T` and `n`. -/
example (T : Type) [Data T] (n : Nat) : (GBump.slots.lens T n).law.isSome = true := rfl
/-- The constructor's law is certified once for every `T` and `n`, from a placement that holds
for every C layout. -/
example (T : Type) [Data T] (n : Nat) : (GBump.ctor T n).law.isSome = true := rfl
/-- At an instance the layout is concrete, 8 cells of 8 bytes followed by the length. -/
example : (Data.shape (GBump UInt64 8)).size = 72 := by decide

/-- A parameterised enum. Its constructors and the splits of a `match` have laws for every `T`,
because their side conditions are about the list of variants. -/
inductive Opt (T : Type) where
  | none
  | some (v : T)
deriving Data

/-- Three variants, one with an array of a size variable. -/
inductive Tri (T : Type) (n : Nat) where
  | one (v : T)
  | many (w : Arr UInt64 n)
  | empty
deriving Data

example : (T : Type) → [Data T] → Data (Opt T) := @Opt.instData
example (T : Type) [Data T] : (Opt.some.ctor T).law.isSome = true := rfl
example (T : Type) [Data T] : (Opt.split0 T).law.isSome = true := rfl
example (T : Type) [Data T] (n : Nat) : (Tri.split1 T n).law.isSome = true := rfl

section
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat)

/-- A `match` on a parameterised enum. -/
mp def getOr (o : Opt T) (d : T) : T :=
  match o with
  | .some v => v
  | .none => d

mp def wrapSome (v : T) : Opt T := Opt.some v

/-- A `match` over three variants, one carrying `Arr UInt64 n`. -/
mp def triSum (t : Tri T n) : UInt64 := do
  match t with
  | .one _ => 1
  | .many w =>
    let mut s := 0
    for i in 0...n do
      s := s + w[i]
    s
  | .empty => 0

end

example : ∀ (T : Type) [Data T] [Data.Copy T] [Inhabited T],
    (getOr.fn T).wf = true := @getOr.wf
example : (getOr UInt64 (.some 3) 5).run = 3 := by decide
example : (getOr UInt64 .none 5).run = 5 := by decide
example : ((wrapSome UInt64 4).run matches .some 4) := by decide
example : (triSum UInt64 3 (.many #v[1, 2, 3])).run = 6 := by decide
example : (triSum UInt64 3 .empty).run = 0 := by decide

/-! ## 3. The bump arena, proved once -/

section
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat) (hn : n < 2 ^ 64)
include hn
set_option mp.autoSafe false
set_option mp.autoSpec false

/-- The bump arena's invariant, that `len ≤ n` and exactly the cells below `len` are full. -/
def GBump.Inv (b : GBump T n) : Prop := BumpInv b.slots b.len

/-- The empty arena. -/
mp def GBump.new ensures GBump.Inv T n result ∧ result.len = 0 : GBump T n :=
  { slots := Slots.empty n, len := 0 }

/-- Stores `v` in the next cell, with the obligation `len < n` in place of a run-time check. -/
mp def GBump.alloc! (b : &mut GBump T n) (v : T) requires GBump.Inv T n b ∧ b.len.toNat < n
    ensures GBump.Inv T n b' ∧ result.idx = b.len ∧
      b'.slots = b.slots.setCell b.len.toNat (some v) ∧ b'.len.toNat = b.len.toNat + 1 :
    GIx := do
  let i := b.len
  let _ := b.slots.put! i v
  b.len := i +! 1
  { idx := i }

/-- Reads a cell, with the obligation `idx < len`. -/
mp def GBump.get! (b : &GBump T n) (x : &GIx)
    requires GBump.Inv T n b ∧ x.idx.toNat < b.len.toNat
    ensures b.slots.cell x.idx.toNat = some result : T :=
  let i := x.idx
  b.slots[i]!

mp prove GBump.new.spec := by mp_auto [GBump.Inv, BumpInv.vacant, BumpInv.full, BumpInv.empty]
mp prove GBump.alloc!.safe := by mp_auto [GBump.Inv, BumpInv.vacant, BumpInv.full, BumpInv.empty]
mp prove GBump.get!.safe := by mp_auto [GBump.Inv, BumpInv.vacant, BumpInv.full, BumpInv.empty]

mp prove GBump.alloc!.spec := by
  intro b v
  vcgen [GBump.alloc!]
  rename_i h
  have hl : (b.len + 1).toNat = b.len.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; rw [Nat.mod_eq_of_lt (by omega)]
  and_intros
  all_goals first | exact h.1.push v h.2 hn | rfl | exact hl

mp prove GBump.get!.spec := by
  intro b x
  vcgen [GBump.get!]
  rename_i h
  have hf := BumpInv.full h.1 _ h.2
  simp only [Slots.isFull] at hf
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hf
  simp [hv]

end

/-- `alloc!` meets its contract for every `T` and every `n < 2 ^ 64`, by one theorem. -/
example : ∀ (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat) (_ : n < 2 ^ 64)
    (b : GBump T n) (v : T), ⦃GBump.Inv T n b ∧ b.len.toNat < n⦄ GBump.alloc! T n ‹_› b v
    ⦃fun r => GBump.Inv T n r.2.1 ∧ r.1.idx = b.len ∧
      r.2.1.slots = b.slots.setCell b.len.toNat (some v) ∧
      r.2.1.len.toNat = b.len.toNat + 1⦄ := @GBump.alloc!.spec
/-- Its obligations are discharged once for every `T` and `n`. -/
example : ∀ (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat) (hn : n < 2 ^ 64)
    (ω : Oracle) (w : World) (b : GBump T n) (v : T), GBump.Inv T n b ∧ b.len.toNat < n →
    Exp.safe ω (GBump.alloc!.exp T n hn) (.cons v (.cons b .nil)) w := @GBump.alloc!.safe
/-- The equation between the Core term and the normal form holds once for every `T` and `n`. -/
example : ∀ (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat) (hn : n < 2 ^ 64)
    (b : GBump T n) (v : T),
    (GBump.alloc!.exp T n hn).run (.cons v (.cons b .nil)) = GBump.alloc! T n hn b v :=
  @GBump.alloc!.exp_run

/-! ## 4. Instances by application -/

mp extern "read" gRead (fd : UInt64) (buf : OutByte) : UInt64
mp extern noreturn "exit" gExit (code : UInt64) : UInt64

/-- The root, a generic arena at `UInt64` and 8 together with a total. -/
mp def gInit ensures GBump.Inv UInt64 8 result.1 : GBump UInt64 8 × UInt64 :=
  ⟨GBump.new, 0⟩

/-- Each step reads a byte `c`, stores `c` and `c + 1` in a fresh arena, reads the first back and
adds it to the total. At the end of input it exits with the total's low byte. Each generic callee
is instantiated at the call, with `T` and `n` taken from the arguments' types, its instances
synthesised and its hypothesis `8 < 2 ^ 64` decided. -/
mp def gStep (r : &mut (GBump UInt64 8 × UInt64)) requires GBump.Inv UInt64 8 r.fst
    ensures GBump.Inv UInt64 8 r'.fst : Unit := do
  let c := gRead 0
  if c < 256 then
    let s : GBump UInt64 8 := GBump.new
    r.fst := s
    let k := GBump.alloc! (&mut r.fst) c
    let _k2 := GBump.alloc! (&mut r.fst) (c + 1)
    let v := GBump.get! (&r.fst) (&k)
    r.snd := r.snd + v
  else
    let _x := gExit (r.snd &&& 255)

mp program gProg (root : GBump UInt64 8 × UInt64) init gInit step gStep
  invariant (fun r => GBump.Inv UInt64 8 r.1)

/-- The same program with an arena of 4 cells. -/
mp def gInit4 ensures GBump.Inv UInt64 4 result.1 : GBump UInt64 4 × UInt64 :=
  ⟨GBump.new, 0⟩

mp def gStep4 (r : &mut (GBump UInt64 4 × UInt64)) requires GBump.Inv UInt64 4 r.fst
    ensures GBump.Inv UInt64 4 r'.fst : Unit := do
  let c := gRead 0
  if c < 256 then
    let s : GBump UInt64 4 := GBump.new
    r.fst := s
    let k := GBump.alloc! (&mut r.fst) c
    let _k2 := GBump.alloc! (&mut r.fst) (c + 1)
    let v := GBump.get! (&r.fst) (&k)
    r.snd := r.snd + v
  else
    let _x := gExit (r.snd &&& 255)

mp program gProg4 (root : GBump UInt64 4 × UInt64) init gInit4 step gStep4
  invariant (fun r => GBump.Inv UInt64 4 r.1)

/-- The compiler's soundness theorem applies to the instance as it is. -/
example (b : ByteArray) (hc : compile gProg x64Linux = .ok b) :
    ∃ s₀, x64Linux.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle,
        let m := Machine.run x64Linux s₀ ω
        m.NeverStuck ∧ TraceEq m.trace (gProg.events ω) ∧
        m.StackWithin (gProg.stackBytes x64Linux.φ) ∧
        m.StepsWithin (gProg.events ω) (fun k => gProg.stepCost k ω x64Linux.κ) :=
  compile_sound gProg b hc gProg.safe

/-! ### Inference from the context -/

section
variable (A : Alloc UInt64) (h2 : 2 ≤ A.cap)
include h2

/-- Allocates `v` in a fresh arena and frees it again. The variable `A` occurs in no parameter's
type, only in the body. -/
mp def Ctx.first (v : UInt64) : UInt64 := do
  let mut s := A.new
  let r := A.alloc (&mut s) v
  match r with
  | ok k => A.free (&mut s) k
  | err _ => 0

/-- The calls of `Ctx.first` take the caller's `A`, the one `Alloc UInt64` in the context. -/
mp def Ctx.twice (v : UInt64) : UInt64 :=
  let a := Ctx.first v
  let b := Ctx.first (v + 1)
  a + b

/-- A definition that uses no variable of the section is closed, although the section has
`include h2`. -/
mp def Ctx.plain (v : UInt64) : UInt64 := v + 1
end

example : (A : Alloc UInt64) → 2 ≤ A.cap → UInt64 → Id UInt64 := Ctx.twice
example : UInt64 → Id UInt64 := Ctx.plain
#guard (Ctx.twice Bump8.impl (by decide) 3).run = 7

/--
error: cannot infer the variable `A` of the generic `Millipede.Tests.Generic.Ctx.first` from the arguments' types, the expected type or the context; give it by name, as the argument `(A := …)`, of type
  Alloc UInt64
-/
#guard_msgs in
mp def outside (v : UInt64) : UInt64 := Ctx.first v

/-- A closed caller gives the variable by name. -/
mp def outside8 (v : UInt64) : UInt64 := Ctx.first (A := Bump8.impl) v

#guard (outside8 5).run = 5

/-! ## 5. Negative checks -/

-- The images of the two instances differ.
#guard (match compile gProg x64Linux, compile gProg4 x64Linux with
  | .ok a, .ok b => a.data != b.data
  | _, _ => false)

section
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat)
-- An obligation that does not hold for every `n` is not discharged, so `badGet.safe` does not
-- exist.
/--
info: the obligations of `badGet` were not discharged automatically; prove them with `mp prove badGet.safe := …` (the goal is `badGet.SafeGoal`); left:
n : Nat
i : UInt64
⊢ i.toNat < n
-/
#guard_msgs in
mp def badGet (a : &Arr T n) (i : UInt64) : T := a[i]!
end
run_cmd do
  if (← Lean.getEnv).contains `Millipede.Tests.Generic.badGet.safe then
    throwError "badGet.safe should not exist"

end Millipede.Tests.Generic

/-! An interface's generated declarations are hygienic. An operation parameter named `r` or `env`
is not captured by the generated binders, `ensures` needs no `open Std.WP`, and an error in an
item is reported at the user's source. -/
namespace Millipede.Tests.GenericIface
open Millipede

mp interface Cnt where
  S : Type
  val : S → Nat
  op peek (r : &S) requires val r < 100 ensures result.toNat = val r : UInt64
  op bump (env : &mut S) requires val env < 100 ensures val env' = val env + 1 : Unit

example : ∀ (A : Cnt) (r : A.S), A.val r < 100 → (A.peek r).run.1.toNat = A.val r :=
  @Cnt.peek.post
example : ∀ (A : Cnt) (env : A.S), A.val env < 100 → A.val (A.bump env).run.2.1 = A.val env + 1 :=
  @Cnt.bump.post

/--
error: Invalid field `toNatt`: The environment does not contain `UInt64.toNatt`, so it is not possible to project the field `toNatt` from an expression
  result
of type `UInt64`
-/
#guard_msgs in
mp interface Bad where
  S : Type
  val : S → Nat
  op peek (r : &S) ensures result.toNatt = val r : UInt64

end Millipede.Tests.GenericIface
