import Millipede.Core.Data

/-!
# Linear tokens

`LinTok` is a linear type of size zero. Its shape is `ghost`, so it takes no bytes and the
compiler erases it, and `Data.linear` is `true`. A struct with a `LinTok` field is linear, so
`deriving Data` makes it a type whose values must be used exactly once, at no run-time cost.

The arena keys of `Millipede/Lib/Pool.lean` are such structs. `{ idx : UInt64, tok : LinTok }`
takes 8 bytes and is linear. A linear struct can be consumed only by a constructor that takes it
as an argument, and the library declares one, `Key.burn : Ctor [Key] Unit`, next to the key type.
It keeps that constructor `private`, together with the minting constructor and the struct's own
constructor, which makes the struct sealed, so that outside the library keys can be neither
forged nor dropped.
-/

namespace Millipede

/-- The zero-size linear token. -/
structure LinTok where
  mk ::

instance : Inhabited LinTok := ⟨⟨⟩⟩

/-- The instance of shape `ghost`, which is linear. The empty byte string represents the token. -/
instance : Data LinTok where
  shape := .ghost
  linear := true
  repr _ _ := True
  encode _ := ⟨[], rfl⟩
  encode_repr _ := trivial

instance : Data.Determinate LinTok := ⟨fun _ _ _ _ _ => rfl⟩

@[simp] theorem LinTok.size : (Data.shape LinTok).size = 0 := rfl
@[simp] theorem LinTok.linear : Data.linear LinTok = true := rfl

end Millipede
