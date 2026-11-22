/-!
# Little-endian bytes

This file defines the little-endian byte encoding of numbers, which the layout, the memory
lowering, the machine models, relocations and the ELF writer share. `natBytes n x` is the low `n`
bytes of `x`, least significant first. `natOfBytes bs` is the number that the bytes denote, and
the two are inverse. `decodeLE bs` is the word that up to 8 bytes denote.
-/

namespace Millipede

/-- The low `n` bytes of `x`, least significant first. -/
def natBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => UInt8.ofNat (x % 256) :: natBytes n (x / 256)

@[simp] theorem natBytes_length (n x : Nat) : (natBytes n x).length = n := by
  induction n generalizing x <;> simp [natBytes, *]

/-- `natBytes n` is injective below `256 ^ n`. -/
theorem natBytes_inj {n x y : Nat} (hx : x < 256 ^ n) (hy : y < 256 ^ n)
    (h : natBytes n x = natBytes n y) : x = y := by
  induction n generalizing x y with
  | zero => simp at hx hy; omega
  | succ n ih =>
    simp only [natBytes, List.cons.injEq] at h
    have h0 : x % 256 = y % 256 := by
      have := congrArg UInt8.toNat h.1
      simpa [UInt8.toNat_ofNat] using this
    have h1 : x / 256 = y / 256 :=
      ih (Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ, Nat.mul_comm] at hx; exact hx))
        (Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ, Nat.mul_comm] at hy; exact hy)) h.2
    omega

/-- The bytes of a word are its low byte followed by the bytes of the word shifted right by 8. -/
theorem natBytes_toNat_succ (w : UInt64) (n : Nat) :
    natBytes (n + 1) w.toNat = w.toUInt8 :: natBytes n (w >>> 8).toNat := by
  simp only [natBytes, List.cons.injEq]
  constructor
  · apply UInt8.toNat_inj.mp; simp [UInt64.toNat_toUInt8]
  · congr 1; simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-- The eight bytes of a word. -/
theorem natBytes8_eq (x : UInt64) : natBytes 8 x.toNat =
    [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8, (x >>> 32).toUInt8,
     (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8] := by
  simp only [natBytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply UInt8.toNat_inj.mp; simp [UInt64.toNat_toUInt8,
      UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul] <;> omega)

/-- The number a little-endian byte list denotes. -/
def natOfBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * natOfBytes bs

theorem natOfBytes_lt : ∀ bs : List UInt8, natOfBytes bs < 256 ^ bs.length
  | [] => Nat.zero_lt_one
  | b :: bs => by
    have := natOfBytes_lt bs
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [natOfBytes, List.length_cons, Nat.pow_succ]
    have : 256 * natOfBytes bs + 256 ≤ 256 ^ bs.length * 256 := by
      rw [Nat.mul_comm (256 ^ bs.length)]; omega
    omega

theorem natOfBytes_natBytes : ∀ (n x : Nat), natOfBytes (natBytes n x) = x % 256 ^ n
  | 0, x => by simp [natBytes, natOfBytes, Nat.mod_one]
  | n + 1, x => by
    simp only [natBytes, natOfBytes, natOfBytes_natBytes n (x / 256)]
    have h1 : (UInt8.ofNat (x % 256)).toNat = x % 256 := by
      simp
    rw [h1, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

/-- The little-endian bytes of the number a byte list denotes are the list. -/
theorem natBytes_natOfBytes : ∀ bs : List UInt8, natBytes bs.length (natOfBytes bs) = bs
  | [] => rfl
  | b :: bs => by
    simp only [List.length_cons, natBytes, natOfBytes]
    have hb : b.toNat < 256 := b.toNat_lt
    rw [show (b.toNat + 256 * natOfBytes bs) % 256 = b.toNat by omega,
      show (b.toNat + 256 * natOfBytes bs) / 256 = natOfBytes bs by omega, natBytes_natOfBytes bs]
    simp

/-- The little-endian decoding of up to 8 bytes into a word, where bytes beyond the eighth are
shifted out. -/
def decodeLE (bs : List UInt8) : UInt64 :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.toUInt64) 0

theorem decodeLE_cons (b : UInt8) (bs : List UInt8) :
    decodeLE (b :: bs) = (decodeLE bs <<< 8) ||| b.toUInt64 := rfl

/-- Decoding up to 8 bytes gives their little-endian number, without overflow. -/
theorem decodeLE_toNat : ∀ bs : List UInt8, bs.length ≤ 8 → (decodeLE bs).toNat = natOfBytes bs
  | [], _ => rfl
  | b :: bs, h => by
    have ih := decodeLE_toNat bs (by simp at h; omega)
    have hlt := natOfBytes_lt bs
    have hle : 256 ^ bs.length ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by simp at h; omega)
    have hb : b.toNat < 256 := b.toNat_lt
    have h7 : (256 : Nat) ^ 7 * 256 = 2 ^ 64 := by decide
    have e1 : (decodeLE bs <<< 8).toNat = natOfBytes bs <<< 8 := by
      rw [UInt64.toNat_shiftLeft, ih, show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.shiftLeft_eq]
      refine Nat.mod_eq_of_lt ?_
      have : natOfBytes bs * 2 ^ 8 < 256 ^ 7 * 256 :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_of_lt_of_le hlt hle) (by decide)
      omega
    rw [decodeLE_cons, UInt64.toNat_or, e1, UInt8.toNat_toUInt64,
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega : b.toNat < 2 ^ 8), Nat.shiftLeft_eq]
    simp only [natOfBytes]
    have : (2 : Nat) ^ 8 = 256 := rfl
    rw [this]; omega

/-- Decoding the 8 little-endian bytes of a word gives the word. -/
theorem decodeLE_natBytes8 (x : UInt64) : decodeLE (natBytes 8 x.toNat) = x := by
  apply UInt64.toNat_inj.mp
  rw [decodeLE_toNat _ (by simp), natOfBytes_natBytes, Nat.mod_eq_of_lt x.toNat_lt]

end Millipede
