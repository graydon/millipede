import Millipede.Compile.Flat
import Millipede.Target.Machine

/-!
# Memory facts shared by every instruction selection

The facts in this module are stated over `Memory.read`, `write`, `readWord` and `writeWord`,
which every ISA's loads and stores reduce to. x64 adds a canonical-address check and arm64 an
`sp`-alignment check, and each ISA proves that its accesses to the stack region equal these.

The module covers the bytes at an address, the stack region `Region m lo N` of `8 N` readable and
writable bytes from `lo` below `2^47`, its words `word m lo k` at addresses `wa lo k`, and the
fact that a word store changes exactly that word and no byte below the region. It then relates
Lin's byte memory to the machine's data region through `DataRel`, so that an in-bounds read or
write of the data region is Lin's read or write. Last come the remainder identity
`x - x / y * y = x % y`, by which both ISAs compute a remainder, and lemmas about frames.
-/

namespace Millipede.Sel

open Flat (Heap)

theorem add_ofNat_zero (a : UInt64) : a + UInt64.ofNat 0 = a := UInt64.add_zero a

theorem add_one_ofNat (a : UInt64) (i : Nat) :
    a + 1 + UInt64.ofNat i = a + UInt64.ofNat (i + 1) := by
  rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm 1]; rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  simp [UInt64.toNat_ofNat']; omega

/-! ## Bytes -/

/-- The bytes at `a, a+1, …, a+n-1`, in the shape `Memory.read` produces. -/
def bytesFrom (m : Memory) (a : UInt64) : Nat → List UInt8
  | 0 => []
  | n + 1 => m.bytes a :: bytesFrom m (a + 1) n

theorem read_eq (m : Memory) : ∀ (n : Nat) (a : UInt64),
    (∀ i, i < n → m.readable (a + UInt64.ofNat i) = true) → m.read a n = some (bytesFrom m a n)
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    simp only [add_ofNat_zero] at h0
    simp only [Memory.read, h0, ite_true, bytesFrom]
    rw [read_eq m n (a + 1) (fun i hi => by rw [add_one_ofNat]; exact h (i + 1) (by omega))]
    rfl

theorem write_some : ∀ (bs : List UInt8) (m : Memory) (a : UInt64),
    (∀ i, i < bs.length → m.writable (a + UInt64.ofNat i) = true) → ∃ m', m.write a bs = some m'
  | [], m, _, _ => ⟨m, rfl⟩
  | b :: bs, m, a, h => by
    have h0 := h 0 (by simp)
    simp only [add_ofNat_zero] at h0
    simp only [Memory.write, h0, ite_true]
    exact write_some bs _ _ fun i hi => by
      rw [Memory.set_writable, add_one_ofNat]; exact h (i + 1) (by simp; omega)

/-- A store leaves bytes outside its range unchanged. -/
theorem write_bytes_out : ∀ (bs : List UInt8) (m m' : Memory) (a b : UInt64),
    m.write a bs = some m' → (∀ i, i < bs.length → a + UInt64.ofNat i ≠ b) → m'.bytes b = m.bytes b
  | [], m, m', _, _, h, _ => by cases h; rfl
  | c :: bs, m, m', a, b, h, hb => by
    simp only [Memory.write] at h
    split at h
    · rw [write_bytes_out bs _ _ _ _ h (fun i hi => by
        rw [add_one_ofNat]; exact hb (i + 1) (by simp; omega))]
      have := hb 0 (by simp)
      simp only [add_ofNat_zero] at this
      simp [Memory.set, Ne.symm this]
    · cases h

/-- A store writes its bytes, provided its range does not wrap onto itself. -/
theorem write_bytes_in : ∀ (bs : List UInt8) (m m' : Memory) (a : UInt64),
    bs.length < 2 ^ 64 → m.write a bs = some m' → bytesFrom m' a bs.length = bs
  | [], _, _, _, _, _ => rfl
  | c :: bs, m, m', a, hl, h => by
    simp only [Memory.write] at h
    split at h
    · simp only [List.length_cons, bytesFrom]
      rw [write_bytes_in bs _ _ _ (by simp at hl; omega) h]
      rw [write_bytes_out bs _ _ _ _ h (fun i hi => ?_)]
      · simp [Memory.set]
      · rw [add_one_ofNat]
        intro he
        have := congrArg UInt64.toNat he
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at this
        simp at hl
        omega
    · cases h

theorem bytesFrom_congr (m m' : Memory) : ∀ (n : Nat) (a : UInt64),
    (∀ i, i < n → m'.bytes (a + UInt64.ofNat i) = m.bytes (a + UInt64.ofNat i)) →
    bytesFrom m' a n = bytesFrom m a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    simp only [add_ofNat_zero] at h0
    simp only [bytesFrom, h0]
    rw [bytesFrom_congr m m' n (a + 1) (fun i hi => by rw [add_one_ofNat]; exact h (i + 1) (by omega))]

/-! ## The stack region -/

/-- The stack region is `8 * N` readable and writable bytes from `lo`, below `2^47`, which is
above both Linux stack tops. -/
structure Region (m : Memory) (lo N : Nat) : Prop where
  rw : ∀ i, i < 8 * N → m.readable (UInt64.ofNat (lo + i)) = true ∧
    m.writable (UInt64.ofNat (lo + i)) = true
  top : lo + 8 * N ≤ 2 ^ 47

/-- The address of stack word `k`. -/
def wa (lo k : Nat) : UInt64 := UInt64.ofNat (lo + 8 * k)

theorem wa_add (lo k i : Nat) : wa lo k + UInt64.ofNat i = UInt64.ofNat (lo + 8 * k + i) := by
  simp [wa, UInt64.ofNat_add]

/-- Distinct addresses below `2^64`. -/
theorem ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    UInt64.ofNat a ≠ UInt64.ofNat b := by
  intro e
  have := congrArg UInt64.toNat e
  simp only [UInt64.toNat_ofNat'] at this
  omega

theorem wa_pred {lo k : Nat} (hk : 0 < k) : wa lo k - 8 = wa lo (k - 1) := by
  apply UInt64.toNat_inj.mp
  simp only [wa, UInt64.toNat_sub, UInt64.toNat_ofNat']
  simp; omega

theorem wa_succ (lo k : Nat) : wa lo k + 8 = wa lo (k + 1) := by
  rw [show (8 : UInt64) = UInt64.ofNat 8 from rfl, wa_add]; simp [wa, Nat.mul_add, Nat.add_assoc]

/-- `wa lo k + 8 n` is word `k + n`. -/
theorem wa_add_words (lo k n : Nat) : wa lo k + UInt64.ofNat (8 * n) = wa lo (k + n) := by
  rw [wa_add]; simp [wa, Nat.mul_add, Nat.add_assoc]

/-- `wa lo k - 8 n` is word `k - n`. -/
theorem wa_sub_words {lo k n : Nat} (h : n ≤ k) (hk : lo + 8 * k < 2 ^ 64) :
    wa lo k - UInt64.ofNat (8 * n) = wa lo (k - n) := by
  apply UInt64.toNat_inj.mp
  simp only [wa, UInt64.toNat_sub, UInt64.toNat_ofNat']
  simp; omega

/-- The word at stack index `k`. -/
def word (m : Memory) (lo k : Nat) : UInt64 := decodeLE (bytesFrom m (wa lo k) 8)

/-- A word load from stack word `k` succeeds and returns the word. -/
theorem readWord_wa {m : Memory} {lo N k : Nat} (hR : Region m lo N) (hk : k < N) :
    m.readWord (wa lo k) 8 = some (word m lo k) := by
  have hr : ∀ i, i < 8 → m.readable (wa lo k + UInt64.ofNat i) = true := by
    intro i hi
    rw [wa_add, Nat.add_assoc]; exact (hR.rw (8 * k + i) (by omega)).1
  simp only [Memory.readWord, read_eq m 8 _ hr]
  rfl

theorem region_frame {m m' : Memory} {lo N : Nat} (hR : Region m lo N) (hF : Memory.Frame m m') :
    Region m' lo N := by
  refine ⟨fun i hi => ?_, hR.top⟩
  have := hR.rw i hi
  simp only [Memory.readable, Memory.writable, Memory.permAt, Memory.page, hF.1, hF.2.1]
  exact this

/-- A word store to stack word `k` succeeds and changes exactly that word. -/
theorem writeWord_wa {m : Memory} {lo N k : Nat} (hR : Region m lo N) (hk : k < N) (v : UInt64) :
    ∃ m', m.writeWord (wa lo k) 8 v = some m' ∧ Region m' lo N ∧ Memory.Frame m m' ∧
      word m' lo k = v ∧ ∀ j, j < N → j ≠ k → word m' lo j = word m lo j := by
  have hw : ∀ i, i < (natBytes 8 v.toNat).length → m.writable (wa lo k + UInt64.ofNat i) = true := by
    intro i hi
    rw [natBytes_length] at hi
    rw [wa_add, Nat.add_assoc]; exact (hR.rw (8 * k + i) (by omega)).2
  obtain ⟨m', hm'⟩ := write_some _ m _ hw
  have hF := Memory.write_frame _ _ _ _ hm'
  refine ⟨m', hm', region_frame hR hF, hF, ?_, fun j hj hjk => ?_⟩
  · simp only [word]
    have := write_bytes_in _ _ _ _ (by rw [natBytes_length]; omega) hm'
    rw [natBytes_length] at this
    rw [this, decodeLE_natBytes8]
  · simp only [word]
    congr 1
    apply bytesFrom_congr
    intro i hi
    apply write_bytes_out _ _ _ _ _ hm'
    intro i' hi'
    rw [natBytes_length] at hi'
    rw [wa_add, wa_add]
    have := hR.top
    apply ofNat_ne (by omega) (by omega)
    omega

/-- A word store writes its little-endian bytes. -/
theorem writeWord_wa_bytes {m m' : Memory} {lo N k : Nat} (hR : Region m lo N) (hk : k < N)
    {v : UInt64} (hs : m.writeWord (wa lo k) 8 v = some m') :
    bytesFrom m' (wa lo k) 8 = natBytes 8 v.toNat := by
  have := write_bytes_in _ _ _ _ (by rw [natBytes_length]; omega) hs
  rwa [natBytes_length] at this

/-- Every byte below address `lo`, the start of the stack region, is unchanged. -/
def LowSame (lo : Nat) (m m' : Memory) : Prop := ∀ a : UInt64, a.toNat < lo → m'.bytes a = m.bytes a

theorem LowSame.refl (lo : Nat) (m : Memory) : LowSame lo m m := fun _ _ => rfl

theorem LowSame.trans {lo : Nat} {m₁ m₂ m₃ : Memory} (h₁ : LowSame lo m₁ m₂)
    (h₂ : LowSame lo m₂ m₃) : LowSame lo m₁ m₃ := fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem LowSame.of_eq {lo : Nat} {m m' : Memory} (h : m' = m) : LowSame lo m m' := by
  subst h; exact LowSame.refl lo _

/-- A word store to the region leaves every byte below it unchanged. -/
theorem writeWord_wa_low {m m' : Memory} {lo N k : Nat} {v : UInt64} (hR : Region m lo N)
    (hk : k < N) (hs : m.writeWord (wa lo k) 8 v = some m') : LowSame lo m m' := by
  intro b hb
  apply Memory.writeWord_outside hs
  have htop := hR.top
  have hw : (wa lo k).toNat = lo + 8 * k := by simp only [wa, UInt64.toNat_ofNat']; omega
  simp only [Memory.InRange, UInt64.toNat_sub, hw]
  have : (2 ^ 64 - (lo + 8 * k) + b.toNat) % 2 ^ 64 = 2 ^ 64 - (lo + 8 * k) + b.toNat := by
    apply Nat.mod_eq_of_lt; omega
  omega

/-- A word of the region depends only on its eight bytes. -/
theorem word_congr {m m' : Memory} {lo k : Nat}
    (h : ∀ i, i < 8 → m'.bytes (wa lo k + UInt64.ofNat i) = m.bytes (wa lo k + UInt64.ofNat i)) :
    word m' lo k = word m lo k := by
  simp only [word]; rw [bytesFrom_congr m m' 8 _ h]

/-- Writing at most one byte onto a stack word whose bytes are zero, as a one-byte `read` does,
makes the word that byte zero-extended, or 0 when nothing was written. It changes no other word
and no byte below the region, and keeps the region. -/
theorem byte_word {m m' : Memory} {lo N k : Nat} (hR : Region m lo N) (hk : k < N)
    (hz : bytesFrom m (wa lo k) 8 = natBytes 8 0) {l : List UInt8} (hl : l.length ≤ 1)
    (hw : m.write (wa lo k) l = some m') :
    Region m' lo N ∧ Memory.Frame m m' ∧ word m' lo k = (l.headD 0).toUInt64 ∧
      (∀ j, j < N → j ≠ k → word m' lo j = word m lo j) ∧ LowSame lo m m' := by
  have hF := Memory.write_frame _ _ _ _ hw
  have htop := hR.top
  have hout : ∀ b : UInt64, b ≠ wa lo k → m'.bytes b = m.bytes b := by
    intro b hb
    apply write_bytes_out _ _ _ _ _ hw
    intro i hi
    have : i = 0 := by omega
    subst this; simpa [add_ofNat_zero] using Ne.symm hb
  refine ⟨⟨fun i hi => ?_, hR.top⟩, hF, ?_, fun j hj hjk => ?_, fun b hb => ?_⟩
  · have := hR.rw i hi
    simp only [Memory.readable, Memory.writable, Memory.permAt, Memory.page, hF.1, hF.2.1]
    exact this
  · have htail : bytesFrom m' (wa lo k + 1) 7 = (natBytes 8 0).tail := by
      have e : bytesFrom m (wa lo k) 8 = m.bytes (wa lo k) :: bytesFrom m (wa lo k + 1) 7 := rfl
      rw [hz] at e
      have e2 := (List.cons.inj e).2
      show _ = natBytes 7 0
      rw [e2]
      apply bytesFrom_congr
      intro i hi
      apply hout
      rw [add_one_ofNat, wa_add]
      simp only [wa]
      exact ofNat_ne (by omega) (by omega) (by omega)
    have hhead : m'.bytes (wa lo k) = l.headD (m.bytes (wa lo k)) := by
      match l, hl, hw with
      | [], _, hw => cases hw; rfl
      | [b], _, hw =>
        have := write_bytes_in [b] _ _ _ (by simp) hw
        simpa [bytesFrom] using this
    have h0 : m.bytes (wa lo k) = 0 := by
      have e : bytesFrom m (wa lo k) 8 = m.bytes (wa lo k) :: bytesFrom m (wa lo k + 1) 7 := rfl
      rw [hz] at e
      have := (List.cons.inj e).1
      simpa [natBytes] using this.symm
    simp only [word]
    show decodeLE (m'.bytes (wa lo k) :: bytesFrom m' (wa lo k + 1) 7) = _
    rw [htail, hhead, h0]
    simp [natBytes, decodeLE]
  · simp only [word]
    congr 1
    apply bytesFrom_congr
    intro i hi
    apply hout
    rw [wa_add]
    simp only [wa]
    exact ofNat_ne (by omega) (by omega) (by omega)
  · apply hout
    intro e
    have := congrArg UInt64.toNat e
    simp only [wa, UInt64.toNat_ofNat'] at this
    omega

/-- One output buffer of capacity `c` receives one list of bytes. -/
theorem fitOut_single (c : Nat) (bs : List (List UInt8)) :
    fitOut [c] bs = [(fitOut [c] bs).headD []] := by
  cases bs <;> rfl

/-! ## Division -/

theorem udiv_ofNat (x y : UInt64) : UInt64.ofNat (x.toNat / y.toNat) = x / y := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.toNat_lt)

/-- The remainder from the quotient, as x64's selected code and arm64's `msub` compute it. -/
theorem umod_eq (x y : UInt64) : x - x / y * y = x % y := by
  have h1 : (x / y * y).toNat = x.toNat / y.toNat * y.toNat := by
    rw [UInt64.toNat_mul, UInt64.toNat_div]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) x.toNat_lt)
  have h2 : x / y * y ≤ x := by
    rw [UInt64.le_iff_toNat_le, h1]; exact Nat.div_mul_le_self _ _
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ h2, h1, UInt64.toNat_mod]
  have := Nat.mod_add_div x.toNat y.toNat
  rw [Nat.mul_comm] at this
  omega

/-! ## Lin's byte memory in the data region -/

/-- The bytes of a Lin heap at `a, a+1, …, a+n-1`. -/
def hbytes (h : Heap) (a : UInt64) (n : Nat) : List UInt8 :=
  (List.range n).map fun i => h (a + UInt64.ofNat i)

/-- Write bytes sequentially from `a` into a Lin heap. -/
def hwrite : Heap → UInt64 → List UInt8 → Heap
  | h, _, [] => h
  | h, a, b :: bs => hwrite (h.store8 a b) (a + 1) bs

/-- `hwrite` is Flat's `Heap.writeBytes`, which writes an extern's output into a memory
buffer. -/
theorem hwrite_eq : ∀ (h : Heap) (a : UInt64) (bs : List UInt8), hwrite h a bs = h.writeBytes a bs
  | _, _, [] => rfl
  | h, a, b :: bs => hwrite_eq (h.store8 a b) (a + 1) bs

/-- Lin's load is the little-endian decoding of the bytes it covers. -/
theorem heap_load_eq (h : Heap) (w : Flat.Width) (a : UInt64) :
    h.load w a = decodeLE (hbytes h a (w.bytes)) := by
  cases w <;> simp [Heap.load, hbytes, Flat.Width.bytes, decodeLE, List.foldr_map]

/-- The little-endian bytes of a word, byte by byte. -/
theorem natBytes8_shifts (v : UInt64) :
    natBytes 8 v.toNat = (List.range 8).map fun i => (v >>> (8 * UInt64.ofNat i)).toUInt8 := by
  simp only [natBytes_toNat_succ]
  simp only [natBytes, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.cons.injEq, and_true, UInt64.reduceOfNat, UInt64.reduceMul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first
    | trivial
    | apply UInt8.toNat_inj.mp
      simp [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
        Nat.div_div_eq_div_mul]

theorem foldl_store8 (v : UInt64) (a : UInt64) : ∀ (k : Nat) (h : Heap),
    (List.range' k (8 - k)).foldl (fun h i =>
      h.store8 (a + UInt64.ofNat i) (v >>> (8 * UInt64.ofNat i)).toUInt8) h =
    hwrite h (a + UInt64.ofNat k)
      ((List.range' k (8 - k)).map fun i => (v >>> (8 * UInt64.ofNat i)).toUInt8)
  | k, h => by
    by_cases hk : k < 8
    · obtain ⟨n, hn⟩ : ∃ n, 8 - k = n + 1 := ⟨7 - k, by omega⟩
      rw [hn, List.range'_succ, List.foldl_cons, List.map_cons, hwrite]
      have := foldl_store8 v a (k + 1) (h.store8 (a + UInt64.ofNat k)
        (v >>> (8 * UInt64.ofNat k)).toUInt8)
      rw [show 8 - (k + 1) = n by omega] at this
      rw [this, UInt64.ofNat_add, UInt64.add_assoc]; rfl
    · rw [show 8 - k = 0 by omega]; rfl
termination_by k => 8 - k

/-- Lin's store is the sequential write of the little-endian bytes. -/
theorem heap_store_eq (h : Heap) (w : Flat.Width) (a v : UInt64) :
    h.store w a v = hwrite h a (natBytes (w.bytes) v.toNat) := by
  cases w with
  | w8 => rw [Flat.Width.bytes, natBytes_toNat_succ]; rfl
  | w64 =>
    have := foldl_store8 v a 0 h
    simp only [Nat.sub_zero, (show UInt64.ofNat 0 = 0 from rfl), UInt64.add_zero] at this
    rw [Flat.Width.bytes, natBytes8_shifts, List.range_eq_range']
    exact this

/-- The data region relation says the `M` machine bytes from `D` are readable and writable and
hold the Lin heap's bytes `0 … M-1`. -/
def DataRel (D : UInt64) (M : Nat) (m : Memory) (h : Heap) : Prop :=
  ∀ i, i < M → m.readable (D + UInt64.ofNat i) = true ∧ m.writable (D + UInt64.ofNat i) = true ∧
    m.bytes (D + UInt64.ofNat i) = h (UInt64.ofNat i)

/-- An address in a range `[b, b + n)` that does not wrap is below `b + n`. -/
theorem inRange_lt {b y : UInt64} {n : Nat} (hb : b.toNat + n ≤ 2 ^ 64) (h : Memory.InRange b n y) :
    y.toNat < b.toNat + n := by
  simp only [Memory.InRange, UInt64.toNat_sub] at h
  have := y.toNat_lt; have := b.toNat_lt
  by_cases hyb : b.toNat ≤ y.toNat
  · rw [show 2 ^ 64 - b.toNat + y.toNat = 2 ^ 64 + (y.toNat - b.toNat) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at h; omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h; omega

/-- A write to `[D + a, D + a + n)` inside the `M` bytes of the data region at `D`, which lies
below `lo`, leaves every byte from `lo` up unchanged. -/
theorem high_of_out {m m' : Memory} {D a : UInt64} {n M lo : Nat} (hDlo : D.toNat + M ≤ lo)
    (hb : a.toNat + n ≤ M) (hout : ∀ y, ¬ Memory.InRange (D + a) n y → m'.bytes y = m.bytes y) :
    ∀ y : UInt64, lo ≤ y.toNat → m'.bytes y = m.bytes y := by
  intro y hy
  have hy' := y.toNat_lt
  rw [hout y fun hin => ?_]
  have h := inRange_lt (by rw [UInt64.toNat_add]; have := D.toNat_lt; omega) hin
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)] at h; omega

/-- An in-bounds read of the data region gives Lin's bytes. -/
theorem read_data {D : UInt64} {M : Nat} {m : Memory} {h : Heap} (hR : DataRel D M m h)
    (hM : M < 2 ^ 64) : ∀ (n : Nat) (a : UInt64), a.toNat + n ≤ M →
    m.read (D + a) n = some (hbytes h a n)
  | 0, _, _ => rfl
  | n + 1, a, hb => by
    have e0 : D + a = D + UInt64.ofNat a.toNat := by rw [UInt64.ofNat_toNat]
    obtain ⟨hr, -, hby⟩ := hR a.toNat (by omega)
    rw [← e0] at hr hby
    have ha : a.toNat + 1 < 2 ^ 64 := by omega
    have e1 : D + a + 1 = D + (a + 1) := UInt64.add_assoc _ _ _
    have h1 : (a + 1).toNat = a.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    simp only [Memory.read, hr, ite_true]
    rw [e1, read_data hR hM n (a + 1) (by omega)]
    simp only [Option.map_some, hby, hbytes, List.range_succ_eq_map, List.map_cons,
      List.map_map, Option.some.injEq, List.cons.injEq]
    refine ⟨by rw [UInt64.ofNat_toNat, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero],
      List.map_congr_left fun i _ => ?_⟩
    simp only [Function.comp_apply]
    rw [add_one_ofNat]

/-- An in-bounds write to the data region succeeds and keeps the relation with Lin's heap after
the same write. It changes only the bytes written and keeps the permissions. -/
theorem write_data {D : UInt64} {M : Nat} {m : Memory} {h : Heap} (hR : DataRel D M m h)
    (hDM : D.toNat + M < 2 ^ 64) : ∀ (bs : List UInt8) (a : UInt64), a.toNat + bs.length ≤ M →
    ∃ m', m.write (D + a) bs = some m' ∧ DataRel D M m' (hwrite h a bs) ∧
      Memory.Frame m m' ∧ ∀ y, ¬ Memory.InRange (D + a) bs.length y → m'.bytes y = m.bytes y
  | [], _, _ => ⟨m, rfl, hR, Memory.Frame.refl _, fun _ _ => rfl⟩
  | b :: bs, a, hb => by
    simp only [List.length_cons] at hb
    have e0 : D + a = D + UInt64.ofNat a.toNat := by rw [UInt64.ofNat_toNat]
    obtain ⟨-, hw, -⟩ := hR a.toNat (by omega)
    rw [← e0] at hw
    have hR1 : DataRel D M (m.set (D + a) b) (h.store8 a b) := by
      intro i hi
      obtain ⟨r1, w1, b1⟩ := hR i hi
      refine ⟨r1, w1, ?_⟩
      simp only [Memory.set, Heap.store8]
      by_cases hia : UInt64.ofNat i = a
      · subst hia; simp
      · have : D + UInt64.ofNat i ≠ D + a := fun e => hia ((UInt64.add_right_inj D).mp e)
        simp [this, hia, b1]
    have e1 : D + a + 1 = D + (a + 1) := UInt64.add_assoc _ _ _
    have h1 : (a + 1).toNat = a.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    obtain ⟨m', hm', hR', hF, hout⟩ := write_data hR1 hDM bs (a + 1) (by omega)
    refine ⟨m', ?_, hR', ?_, fun y hy => ?_⟩
    · simp only [Memory.write, hw, ite_true]; rw [e1]; exact hm'
    · exact Memory.Frame.trans (m₂ := m.set (D + a) b) ⟨rfl, rfl, fun a' ha' => by
        simp only [Memory.set]; split
        · subst_vars; rw [hw] at ha'; cases ha'
        · rfl⟩ hF
    · have hy' : ¬ Memory.InRange (D + (a + 1)) bs.length y := by
        intro hr; apply hy
        simp only [Memory.InRange, List.length_cons] at hr ⊢
        have e : y - (D + a) = (y - (D + (a + 1))) + 1 := by grind
        rw [e, UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
      have hne : y ≠ D + a := by intro e; subst e; apply hy; simp [Memory.InRange]
      rw [hout y hy']; simp [Memory.set, hne]

/-- The relation depends only on the region's bytes and the permissions, so it survives stores
that keep the permissions and leave the region's bytes unchanged. -/
theorem dataRel_congr {D : UInt64} {M : Nat} {m m' : Memory} {h : Heap} (hR : DataRel D M m h)
    (hF : Memory.Frame m m') (hb : ∀ i, i < M → m'.bytes (D + UInt64.ofNat i) =
      m.bytes (D + UInt64.ofNat i)) : DataRel D M m' h := by
  intro i hi
  obtain ⟨r, w, b⟩ := hR i hi
  refine ⟨?_, ?_, by rw [hb i hi, b]⟩
  · simp only [Memory.readable, Memory.permAt, Memory.page, hF.1, hF.2.1]; exact r
  · simp only [Memory.writable, Memory.permAt, Memory.page, hF.1, hF.2.1]; exact w

/-- An in-bounds word load from the data region gives Lin's value. -/
theorem readWord_data {D : UInt64} {M : Nat} {m : Memory} {h : Heap} (hR : DataRel D M m h)
    (hM : M < 2 ^ 64) (w : Flat.Width) (a : UInt64) (hb : a.toNat + w.bytes ≤ M) :
    m.readWord (D + a) w.bytes = some (h.load w a) := by
  rw [Memory.readWord, read_data hR hM _ a hb, heap_load_eq]; rfl

/-- An in-bounds word store to the data region succeeds and keeps the relation with Lin's heap
after Lin's store. It changes only the bytes `[D + a, D + a + w.bytes)` and keeps the
permissions. -/
theorem writeWord_data {D : UInt64} {M : Nat} {m : Memory} {h : Heap} (hR : DataRel D M m h)
    (hDM : D.toNat + M < 2 ^ 64) (w : Flat.Width) (a v : UInt64) (hb : a.toNat + w.bytes ≤ M) :
    ∃ m', m.writeWord (D + a) w.bytes v = some m' ∧ DataRel D M m' (h.store w a v) ∧
      Memory.Frame m m' ∧
      ∀ y, ¬ Memory.InRange (D + a) (w.bytes) y → m'.bytes y = m.bytes y := by
  obtain ⟨m', hw, hR', hF, hout⟩ := write_data hR hDM (natBytes (w.bytes) v.toNat) a
    (by rw [natBytes_length]; exact hb)
  rw [natBytes_length] at hout
  exact ⟨m', hw, by rw [heap_store_eq]; exact hR', hF, hout⟩

/-! ## Frames -/

/-- `Frame.writes` at one location. -/
theorem writes_apply : ∀ (vs : List UInt64) (f : Flat.Frame) (d y : Nat),
    Flat.Frame.writes f d vs y = if d ≤ y ∧ y < d + vs.length then vs.getD (y - d) 0 else f y
  | [], f, d, y => by simp [Flat.Frame.writes]; omega
  | v :: vs, f, d, y => by
    simp only [Flat.Frame.writes, writes_apply vs _ (d + 1) y, List.length_cons]
    by_cases h1 : d + 1 ≤ y ∧ y < d + 1 + vs.length
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
      rw [show y - d = (y - (d + 1)) + 1 by omega]
      simp
    · rw [ite_eq_right h1]
      by_cases h2 : y = d
      · subst h2; simp [Flat.Frame.set]
      · simp only [Flat.Frame.set, h2, ite_false]
        rw [ite_eq_right (by omega)]

end Millipede.Sel
