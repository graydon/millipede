import Millipede.Meta.MpDef

/-!
# Tests of `deriving Data`

For a structure, the derived instance is a struct of the fields in order with the C layout, so
its sizes, alignments and offsets are those `gcc` gives the corresponding C struct. A structure is
linear when one of its fields is, it may nest structures and arrays, and a proof field takes no
space. The tests check the generated lenses and constructor. For an enum, the derived instance is
a tag and a union, and the tests check its constructors and the chain of splits that a `match`
is built from, including that every value reaches exactly the arm of its constructor. The derived
types are used in an `mp def`, and the types that cannot be derived are refused with their
messages.
-/

namespace Millipede.Tests.Derive

open Millipede

/-! ## Structs -/

/-- `struct Pt { uint64_t x, y; }` -/
structure Pt where
  x : UInt64
  y : UInt64
deriving Data, DecidableEq, Repr, Inhabited

/-- `struct Mixed { uint8_t a; uint64_t b; bool c; }`, which is padded after `a` and at the end. -/
structure Mixed where
  a : UInt8
  b : UInt64
  c : Bool
deriving Data

/-- A struct with a nested struct and an array field. -/
structure Outer where
  tag : UInt16
  p : Pt
  xs : Vector UInt32 3
deriving Data

/-- A struct with a linear field is linear. -/
structure Holder where
  r : Except UInt64 UInt64
  n : UInt64
deriving Data

/-- A struct with a proof field, which takes no bytes and has no lens. The struct has no
constructor, since building it needs the proof. -/
structure Bounded where
  v : UInt64
  h : v < 10
deriving Data

-- the instances are built by the builders of `Millipede/Core/Data.lean`
example : (inferInstance : Data Pt) = Data.struct [⟨Pt.x⟩, ⟨Pt.y⟩] := rfl
example : (inferInstance : Data Mixed) = Data.struct [⟨Mixed.a⟩, ⟨Mixed.b⟩, ⟨Mixed.c⟩] := rfl

/-- The field offsets of a struct shape. -/
def offsets : Shape → List Nat
  | .prod fs => Shape.prodOffsets 0 fs
  | _ => []

-- the C layout gives the values that `gcc` gives, and `Tests/Layout.lean` checks the rules
-- against gcc
example : (Data.shape Pt).size = 16 ∧ (Data.shape Pt).align = 8 := by decide
example : (Data.shape Mixed).size = 24 ∧ (Data.shape Mixed).align = 8 := by decide
example : offsets (Data.shape Mixed) = [0, 8, 16] := by decide
/-- `struct Outer { uint16_t tag; struct Pt p; uint32_t xs[3]; }` takes 2 bytes, 6 of padding, 16,
12 and 4 of padding. -/
example : (Data.shape Outer).size = 40 ∧ offsets (Data.shape Outer) = [0, 8, 24] := by decide
/-- The proof field takes no space. -/
example : (Data.shape Bounded).size = 8 := by decide

-- linearity follows the fields
example : Data.linear Pt = false := rfl
example : Data.linear Holder = true := rfl
example : Data.linear Outer = false := rfl

-- a lens has a name, a field number, which is the position and fixes the offset, a projection
-- and an update
example : Pt.y.lens.name = "y" ∧ Pt.y.lens.index = 1 := ⟨rfl, rfl⟩
example : Outer.xs.lens.index = 2 := rfl
example (p : Pt) : Pt.x.lens.get p = p.x := by simp
example (p : Pt) (v : UInt64) : Pt.x.lens.set p v = { p with x := v } := by simp
example (p : Pt) (v : UInt64) : (Pt.y.lens.set p v).y = v ∧ (Pt.y.lens.set p v).x = p.x := by
  simp
-- the constructor builds from its arguments in field order
example : Pt.ctor.build (.cons 1 (.cons 2 .nil)) = ⟨1, 2⟩ := rfl
example : Pt.ctor.kind = .struct := rfl

/-! ## Enums -/

/-- Three constructors, two with a payload. -/
inductive Cmd where
  | stop
  | add (n : UInt64)
  | mul (n : UInt64)
deriving Data, DecidableEq, Repr

/-- A two-constructor enum whose payloads are a struct and a linear `Result`. -/
inductive Msg where
  | point (p : Pt)
  | answer (r : Except UInt64 UInt64)
deriving Data

example : (Data.shape Cmd).size = 16 ∧ (Data.shape Cmd).align = 8 := by decide
example : Data.linear Cmd = false := rfl
example : Data.linear Msg = true := rfl

-- a constructor has the kind `variant i` and builds from its payload, which is the unit literal
-- when there is no field
example : Cmd.add.ctor.kind = .variant 1 := rfl
example : Cmd.stop.ctor.build (.cons () .nil) = .stop := rfl
example : Cmd.mul.ctor.build (.cons 3 .nil) = .mul 3 := rfl

-- with three or more constructors there is a chain of splits; `split0` tests `stop` and hands
-- back the value otherwise, `split1` tests `add` likewise, and the last split `split2` tests `mul`
-- with the rest `Unit`; a two-constructor enum has one split, which hands back the other payload
example (n : UInt64) : Cmd.split0.split (.add n) = .inr (.add n) := by simp
example : Cmd.split0.split .stop = .inl () := by simp
example (n : UInt64) : Cmd.split1.split (.add n) = .inl n := by simp
example (n : UInt64) : Cmd.split1.split (.mul n) = .inr (.mul n) := by simp
example (n : UInt64) : Cmd.split2.split (.mul n) = .inl n := by simp
example (n : UInt64) : Cmd.split2.split (.add n) = .inr () := by simp
example : Msg.split0.split (.point ⟨1, 2⟩) = .inl ⟨1, 2⟩ := by simp

/-- Every value reaches exactly the arm of its constructor in the chain, with its payload
recovered, so a `match` built from the chain has one arm per constructor. -/
theorem cmd_chain (c : Cmd) :
    (match Cmd.split0.split c with
      | .inl _ => Cmd.stop
      | .inr d => match Cmd.split1.split d with
        | .inl n => Cmd.add n
        | .inr d => match Cmd.split2.split d with
          | .inl n => Cmd.mul n
          | .inr _ => Cmd.mul 0) = c := by
  cases c <;> simp

-- every derived lens, constructor and split carries a certificate of its laws, so `compile`
-- accepts programs built from them
example : Pt.x.lens.law.isSome = true := rfl
example : Pt.y.lens.law.isSome = true := rfl
example : Pt.ctor.law.isSome = true := rfl
example : Cmd.stop.ctor.law.isSome = true := rfl
example : Cmd.add.ctor.law.isSome = true := rfl
example : Cmd.mul.ctor.law.isSome = true := rfl
example : Cmd.split0.law.isSome = true := rfl
example : Cmd.split1.law.isSome = true := rfl
example : Cmd.split2.law.isSome = true := rfl
example : Msg.point.ctor.law.isSome = true := rfl
example : Msg.answer.ctor.law.isSome = true := rfl
example : Msg.split0.law.isSome = true := rfl

/-! ## Used by `mp def` -/

mp def area (p : Pt) : UInt64 := p.x * p.y

example : area = fun p => pure (p.x * p.y) := rfl

mp def eval (acc : UInt64) (c : Cmd) : UInt64 :=
  match c with
  | .stop => acc
  | .add n => acc + n
  | .mul n => acc * n

example : (eval 5 (.add 3)).run = 8 := rfl
example : (eval 5 (.mul 3)).run = 15 := rfl
example : (eval 5 .stop).run = 5 := rfl

/-! ## Rejections -/

-- a structure or enum with type parameters is derived for every parameter, but a
-- universe-polymorphic one is refused
/-- error: deriving Data: `Millipede.Tests.Derive.Box` has indices or universe parameters; object types are `Type`s with parameters -/
#guard_msgs in
inductive Box.{u} (α : Type u) where
  | a (v : α)
  | b
deriving Data

/-- error: deriving Data: constructor `Millipede.Tests.Derive.Two.both` has 2 fields; an enum constructor has at most one (wrap several fields in a structure) -/
#guard_msgs in
inductive Two where
  | none
  | both (a b : UInt64)
deriving Data

/-- error: deriving Data: `Millipede.Tests.Derive.One` has a single constructor; declare it as a `structure` -/
#guard_msgs in
inductive One where
  | only (a : UInt64)
deriving Data

/--
error: deriving Data: the field of `Millipede.Tests.Derive.Lst.cons` has type
  Lst
which has no `Data` instance (recursive types are not supported; use indices into an arena)
-/
#guard_msgs in
inductive Lst where
  | nil
  | cons (tail : Lst)
deriving Data

/--
error: deriving Data: field `n` has type
  Nat
which has no `Data` instance (recursive types are not supported; use indices into an arena)
-/
#guard_msgs in
structure Unbounded where
  n : Nat
deriving Data

end Millipede.Tests.Derive
