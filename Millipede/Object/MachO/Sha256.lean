/-!
# SHA-256

`Sha256.hash bs` is the SHA-256 digest of a list of bytes, as FIPS 180-4 defines it. The Mach-O
code signature holds the digest of each 4 KiB page of the file, and the loader model recomputes
them, so the hash is part of the format's specification. It is a plain function over `List UInt8`
and `UInt32`, by structural recursion on explicit counts: `blocks` takes the number of 64-byte
blocks, `schedule` the number of message words still to produce, and `rounds` walks the list of
round constants. Tests/MachO.lean compares it with `sha256sum`.
-/

namespace Millipede.MachO.Sha256

/-- The working variables `a` to `h`. -/
structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32
deriving Repr, DecidableEq

/-- The initial hash value, the first 32 bits of the fractional parts of the square roots of the
first eight primes. -/
def init : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- The 64 round constants, the first 32 bits of the fractional parts of the cube roots of the
first 64 primes. -/
def K : List UInt32 :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Rotation right by `n` bits, `0 < n < 32`. -/
def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- The big-endian word of four bytes, missing bytes read as zero. -/
def word (bs : List UInt8) : UInt32 :=
  (bs.getD 0 0).toUInt32 <<< 24 ||| (bs.getD 1 0).toUInt32 <<< 16 |||
    (bs.getD 2 0).toUInt32 <<< 8 ||| (bs.getD 3 0).toUInt32

/-- The first `n` big-endian words of the bytes. -/
def words : Nat → List UInt8 → List UInt32
  | 0, _ => []
  | n + 1, bs => word bs :: words n (bs.drop 4)

/-- The next message word after a window `W[t-16] … W[t-1]`. -/
def nextWord (w : List UInt32) : UInt32 :=
  smallSigma1 (w.getD 14 0) + w.getD 9 0 + smallSigma0 (w.getD 1 0) + w.getD 0 0

/-- `n` words of the message schedule, starting from the window of the last 16. -/
def schedule : Nat → List UInt32 → List UInt32
  | 0, _ => []
  | n + 1, w => w.getD 0 0 :: schedule n (w.drop 1 ++ [nextWord w])

/-- One round of the compression function. -/
def round (s : State) (k w : UInt32) : State :=
  let t1 := s.h + bigSigma1 s.e + ((s.e &&& s.f) ^^^ (~~~s.e &&& s.g)) + k + w
  let t2 := bigSigma0 s.a + ((s.a &&& s.b) ^^^ (s.a &&& s.c) ^^^ (s.b &&& s.c))
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- The rounds, one per pair of constant and message word. -/
def rounds : List UInt32 → List UInt32 → State → State
  | k :: ks, w :: ws, s => rounds ks ws (round s k w)
  | _, _, s => s

/-- Adds two states word by word. -/
def State.add (x y : State) : State :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d, x.e + y.e, x.f + y.f, x.g + y.g, x.h + y.h⟩

/-- Processes one 64-byte block. -/
def compress (s : State) (block : List UInt8) : State :=
  s.add (rounds K (schedule 64 (words 16 block)) s)

/-- Processes `n` blocks of 64 bytes. -/
def blocks : Nat → List UInt8 → State → State
  | 0, _, s => s
  | n + 1, bs, s => blocks n (bs.drop 64) (compress s (bs.take 64))

/-- The big-endian bytes of the low `k` bytes of `n`. -/
def beBytes (k n : Nat) : List UInt8 := (List.range k).reverse.map fun i => UInt8.ofNat (n / 256 ^ i)

/-- The message with its padding: a one bit, zeros, and the bit length as 64 bits big-endian. -/
def padded (bs : List UInt8) : List UInt8 :=
  bs ++ [0x80] ++ List.replicate ((64 - (bs.length + 9) % 64) % 64) 0 ++ beBytes 8 (8 * bs.length)

/-- The four big-endian bytes of a word. -/
def wordBytes (x : UInt32) : List UInt8 :=
  [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- The 32-byte SHA-256 digest. -/
def hash (bs : List UInt8) : List UInt8 :=
  let m := padded bs
  let s := blocks (m.length / 64) m init
  wordBytes s.a ++ wordBytes s.b ++ wordBytes s.c ++ wordBytes s.d ++ wordBytes s.e ++
    wordBytes s.f ++ wordBytes s.g ++ wordBytes s.h

@[simp] theorem hash_length (bs : List UInt8) : (hash bs).length = 32 := by
  simp [hash, wordBytes]

end Millipede.MachO.Sha256
