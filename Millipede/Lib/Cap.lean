import Millipede.Lib.Linear
import Millipede.Meta.Derive

/-!
# Capability tokens

A token of class `c` is a value of type `Cap c`, and holding one gives a function the authority
to call the externs of that class. `Cap c` is a struct with a single `LinTok` field, so a token
takes no bytes and must be used exactly once. Its Lean constructor is private to this module,
which makes the type sealed, so `mp def` refuses to build one anywhere else.

`Cap.mint c` builds a token. Its result is sealed, so `mp def` refuses it outside this module,
except in the `init` wrapper that `mp program` generates, which mints one token of each class
that `init` takes. `Cap.drop c` consumes a token, which can then no longer be passed to an
extern. A class and its extern symbols are declared with `mp capability`.
-/

namespace Millipede.Lib

/-- A capability token of class `c`, sealed and linear, of size zero. -/
structure Cap (c : String) where
  private mk ::
  tok : LinTok
deriving Data

/-- The value of an access to an empty `Slots (Cap c)` cell, which only the Core model reads, and
only when the access's obligation fails. Programs cannot name it. -/
instance {c : String} : Inhabited (Cap c) := ⟨⟨⟨⟩⟩⟩

/-- A token has no bytes. -/
@[simp] theorem Cap.size (c : String) : (Data.shape (Cap c)).size = 0 := by
  have h : Data.shape (Cap c) = Data.shape (Cap "") := rfl
  rw [h]; decide

/-- A token is linear. -/
@[simp] theorem Cap.linear (c : String) : Data.linear (Cap c) = true := rfl

/-- Mint a token of class `c`. Only the `init` wrapper of `mp program` may apply it. The layout of
a token does not depend on its class, so its law is the one for the class `""`, transported. -/
def Cap.mint (c : String) : Ctor [] ⟨Cap c⟩ :=
  ⟨"Cap.mint", .struct, fun _ => ⟨⟨⟩⟩, some ⟨Flat.CtorLaw.struct _ rfl _ (by
      have h1 : Data.shape (Cap c) = Data.shape (Cap "") := rfl
      have h2 : Flat.planOf [] ⟨Cap c⟩ .struct = Flat.planOf [] ⟨Cap ""⟩ .struct := rfl
      rw [h1, h2]; decide) (by
    intro _ _ _; exact ⟨⟨by show (slice _ _ 0).length = 0; simp [slice], trivial⟩, trivial⟩)⟩,
    none⟩

/-- Consume a token of class `c`. -/
def Cap.drop (c : String) : Ctor [⟨Cap c⟩] Ty.unit :=
  ⟨"Cap.drop", .struct, fun _ => (), some ⟨Flat.CtorLaw.unit _ _ _⟩, none⟩

end Millipede.Lib
