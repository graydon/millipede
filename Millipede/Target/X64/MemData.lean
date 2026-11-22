import Millipede.Target.X64.Laws
import Millipede.Compile.Lin
import Millipede.Target.SelMem

/-!
# Lin's memory in the x64 data region

A Lin program with a data region of `M` bytes keeps its memory, a total byte map, in the `M`
machine bytes from the address `D` of the symbol `mp_mem`, so Lin address `x < M` is machine
address `D + x`. The relation `DataRel D M m h` says this and that the region is readable and
writable, and it is shared with arm64. This module shows that x64's `load`, `load8`, `store` and
`store8` of an in-bounds access agree with Lin's `load` and `store` when the region is below
`2^47`, where every address is canonical.
-/

namespace Millipede.X64

open Flat (Heap)

open Sel

/-! ## The machine's accesses -/

/-- An address below `2^47` is canonical. -/
theorem canonical_lt {a : UInt64} (h : a.toNat < 2 ^ 47) : canonical a = true := by
  have : a >>> 47 = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight]
    simp only [UInt64.toNat_zero]
    have : (47 : UInt64).toNat % 64 = 47 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt h
  simp [canonical, this]

/-- The machine load of width `w`. -/
def loadW (m : Memory) (a : UInt64) : Flat.Width → Option UInt64
  | .w8 => load8 m a
  | .w64 => load64 m a

/-- An in-bounds load from a data region below `2^47` gives Lin's value. -/
theorem load_data {D : UInt64} {M : Nat} {m : Memory} {h : Heap} (hR : DataRel D M m h)
    (hDM : D.toNat + M ≤ 2 ^ 47) (w : Flat.Width) (a : UInt64) (hb : a.toNat + w.bytes ≤ M) :
    loadW m (D + a) w = some (h.load w a) := by
  have hDa : (D + a).toNat = D.toNat + a.toNat := by rw [UInt64.toNat_add]; simp; omega
  have hrd := readWord_data hR (by omega) w a hb
  cases w <;> simp only [Flat.Width.bytes] at hb hrd
  · simp only [loadW, load8, canonical_lt (show (D + a).toNat < 2 ^ 47 by omega), ite_true, hrd]
  · have h7 : (D + a + 7).toNat = D.toNat + a.toNat + 7 := by
      rw [UInt64.toNat_add, hDa]; simp; omega
    simp only [loadW, load64, canonical_lt (show (D + a).toNat < 2 ^ 47 by omega),
      canonical_lt (show (D + a + 7).toNat < 2 ^ 47 by omega), Bool.and_self, ite_true, hrd]

/-- The machine store of width `w`. -/
def storeW (m : Memory) (a v : UInt64) : Flat.Width → Option Memory
  | .w8 => store8 m a v
  | .w64 => store64 m a v

/-- An in-bounds store to a data region below `2^47` succeeds and keeps the relation with Lin's
heap after Lin's store. It changes only the bytes `[D + a, D + a + w.bytes)` and keeps the
permissions. -/
theorem store_data {D : UInt64} {M : Nat} {m : Memory} {h : Heap} (hR : DataRel D M m h)
    (hDM : D.toNat + M ≤ 2 ^ 47) (w : Flat.Width) (a v : UInt64) (hb : a.toNat + w.bytes ≤ M) :
    ∃ m', storeW m (D + a) v w = some m' ∧ DataRel D M m' (h.store w a v) ∧
      Memory.Frame m m' ∧
      ∀ y, ¬ Memory.InRange (D + a) (w.bytes) y → m'.bytes y = m.bytes y := by
  have hDa : (D + a).toNat = D.toNat + a.toNat := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨m', hw, hrest⟩ := writeWord_data hR (by omega) w a v hb
  refine ⟨m', ?_, hrest⟩
  cases w <;> simp only [Flat.Width.bytes] at hb hw
  · simp only [storeW, store8, canonical_lt (show (D + a).toNat < 2 ^ 47 by omega), ite_true, hw]
  · have h7 : (D + a + 7).toNat = D.toNat + a.toNat + 7 := by
      rw [UInt64.toNat_add, hDa]; simp; omega
    simp only [storeW, store64, canonical_lt (show (D + a).toNat < 2 ^ 47 by omega),
      canonical_lt (show (D + a + 7).toNat < 2 ^ 47 by omega), Bool.and_self, ite_true, hw]

end Millipede.X64
