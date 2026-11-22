import Millipede.Target.X64.Encode
import Millipede.Target.Machine

/-!
# The 32-bit little-endian field and `natBytes`

The rel32 or disp32 field that the encoder writes equals the 4-byte field that a `pc32`
relocation patches.
-/

namespace Millipede.X64

/-- The rel32 field and the relocation's field agree. -/
theorem le32_toUInt32 (w : UInt64) : le32 w.toUInt32 = natBytes 4 w.toNat := by
  simp only [le32, natBytes_toNat_succ]; simp only [natBytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> simp [Nat.shiftRight_eq_div_pow] <;> omega

end Millipede.X64
