/-!
# Shapes

A `Shape` is a closed description of how a value is laid out in memory. Sizes and alignments are
in bytes and are computed by structural recursion, following the C rules for naturally aligned
fields. The shapes are the following:

* `word w` is a `w`-bit scalar, whose size and alignment are both `w.bytes`.
* `prod fs` is a C struct of the fields `fs`. Each field is placed at the first offset aligned to
  its alignment, the struct's alignment is the largest field alignment or 1 when there are no
  fields, and its size is the end of the last field rounded up to that alignment. An empty
  struct has size 0, as in GNU C.
* `sum vs` is a C `struct { tag; union { vs } }`. The tag is at offset 0, one byte wide for up to
  256 variants, and the payload follows at `payloadOffset vs`, the tag size rounded up to the
  largest variant alignment. The size is the payload offset plus the largest variant size,
  rounded up to the larger of the tag's and the variants' alignments.
* `array n s` is `n` elements of shape `s` with stride `s.size`, which is always a multiple of
  `s.align`.
* `slots n s` has the same layout as `array n s`. Its cells carry no tags, so which cells are full
  is known only to proofs.
* `ghost` has no run-time representation, with size 0 and alignment 1, so ghost fields do not
  change the layout of a struct.

`Shape.Val s` is the memory contents of a value of shape `s`, a byte list of length `s.size`.
`Shape.words` is a width in 64-bit words, one per scalar and one tag word per sum. The cost model
charges it for each copy of a value, and the static stack bound counts it for each bound value,
but values in memory use the byte layout. The end of the file proves the layout facts that the
memory lowering needs, which are the bounds, alignment and disjointness of fields, elements and
sum payloads.
-/

namespace Millipede

/-- The width of a scalar machine word. -/
inductive Width where
  | w8 | w16 | w32 | w64
deriving Repr, DecidableEq, Inhabited

/-- The bytes of a scalar of this width. -/
def Width.bytes : Width → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8

/-- The bits of a scalar of this width. -/
def Width.bits (w : Width) : Nat := 8 * w.bytes

/-- `n` rounded up to a multiple of `a`, for `a > 0`; `alignUp n 0 = 0`. -/
def alignUp (n a : Nat) : Nat := (n + (a - 1)) / a * a

/-- The tag width of a sum with `n` variants, the narrowest of 8, 16, 32 and 64 bits that holds
every index below `n`. -/
def tagWidth (n : Nat) : Width :=
  if n ≤ 2 ^ 8 then .w8 else if n ≤ 2 ^ 16 then .w16 else if n ≤ 2 ^ 32 then .w32 else .w64

/-- A closed description of a value's memory layout. -/
inductive Shape where
  /-- one scalar of width `w` -/
  | word (w : Width)
  /-- a C struct, with the fields one after another, each naturally aligned -/
  | prod (fs : List Shape)
  /-- a tagged union, with a tag followed by the payload of the selected variant -/
  | sum (vs : List Shape)
  /-- `n` elements -/
  | array (n : Nat) (s : Shape)
  /-- `n` cells, each empty or full, with no tags -/
  | slots (n : Nat) (s : Shape)
  /-- no run-time representation -/
  | ghost
deriving Repr, Inhabited

mutual
/-- Decides the equality of shapes. -/
def Shape.eqb : Shape → Shape → Bool
  | .word w, .word w' => w == w'
  | .prod fs, .prod fs' => Shape.eqbL fs fs'
  | .sum vs, .sum vs' => Shape.eqbL vs vs'
  | .array n s, .array n' s' => n == n' && Shape.eqb s s'
  | .slots n s, .slots n' s' => n == n' && Shape.eqb s s'
  | .ghost, .ghost => true
  | _, _ => false
/-- Decides the equality of lists of shapes. -/
def Shape.eqbL : List Shape → List Shape → Bool
  | [], [] => true
  | a :: as, b :: bs => Shape.eqb a b && Shape.eqbL as bs
  | _, _ => false
end

mutual
theorem Shape.eqb_spec : (a b : Shape) → Shape.eqb a b = true → a = b
  | .word w, .word w', h => by simp only [Shape.eqb, beq_iff_eq] at h; rw [h]
  | .prod fs, .prod fs', h => by simp only [Shape.eqb] at h; rw [Shape.eqbL_spec fs fs' h]
  | .sum vs, .sum vs', h => by simp only [Shape.eqb] at h; rw [Shape.eqbL_spec vs vs' h]
  | .array n s, .array n' s', h => by
    simp only [Shape.eqb, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, Shape.eqb_spec s s' h.2]
  | .slots n s, .slots n' s', h => by
    simp only [Shape.eqb, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, Shape.eqb_spec s s' h.2]
  | .ghost, .ghost, _ => rfl
  | .word _, .prod _, h | .word _, .sum _, h | .word _, .array _ _, h | .word _, .slots _ _, h
  | .word _, .ghost, h | .prod _, .word _, h | .prod _, .sum _, h | .prod _, .array _ _, h
  | .prod _, .slots _ _, h | .prod _, .ghost, h | .sum _, .word _, h | .sum _, .prod _, h
  | .sum _, .array _ _, h | .sum _, .slots _ _, h | .sum _, .ghost, h | .array _ _, .word _, h
  | .array _ _, .prod _, h | .array _ _, .sum _, h | .array _ _, .slots _ _, h
  | .array _ _, .ghost, h | .slots _ _, .word _, h | .slots _ _, .prod _, h
  | .slots _ _, .sum _, h | .slots _ _, .array _ _, h | .slots _ _, .ghost, h
  | .ghost, .word _, h | .ghost, .prod _, h | .ghost, .sum _, h | .ghost, .array _ _, h
  | .ghost, .slots _ _, h => by simp [Shape.eqb] at h
theorem Shape.eqbL_spec : (as bs : List Shape) → Shape.eqbL as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Shape.eqbL, Bool.and_eq_true] at h
    rw [Shape.eqb_spec a b h.1, Shape.eqbL_spec as bs h.2]
  | [], _ :: _, h => by simp [Shape.eqbL] at h
  | _ :: _, [], h => by simp [Shape.eqbL] at h
end

/-- The 64-bit word shape. -/
abbrev Shape.u64 : Shape := .word .w64

mutual
/-- The size in bytes by the C layout rules, tail padding included. -/
def Shape.size : Shape → Nat
  | .word w => w.bytes
  | .prod fs => alignUp (Shape.prodEnd 0 fs) (Shape.alignMax fs)
  | .sum vs => alignUp (alignUp (tagWidth vs.length).bytes (Shape.alignMax vs) + Shape.sizeMax vs)
      (max (tagWidth vs.length).bytes (Shape.alignMax vs))
  | .array n s => n * s.size
  | .slots n s => n * s.size
  | .ghost => 0
/-- The alignment in bytes, a power of two that is at least 1. -/
def Shape.align : Shape → Nat
  | .word w => w.bytes
  | .prod fs => Shape.alignMax fs
  | .sum vs => max (tagWidth vs.length).bytes (Shape.alignMax vs)
  | .array _ s => s.align
  | .slots _ s => s.align
  | .ghost => 1
/-- The end offset of the fields `fs` laid out from offset `off`, before tail padding. -/
def Shape.prodEnd : Nat → List Shape → Nat
  | off, [] => off
  | off, s :: ss => Shape.prodEnd (alignUp off s.align + s.size) ss
/-- The largest alignment in a list, or 1 for the empty list. -/
def Shape.alignMax : List Shape → Nat
  | [] => 1
  | s :: ss => max s.align (Shape.alignMax ss)
/-- The largest size in a list, or 0 for the empty list. -/
def Shape.sizeMax : List Shape → Nat
  | [] => 0
  | s :: ss => max s.size (Shape.sizeMax ss)
end

mutual
/-- The width in 64-bit words, one per scalar and one tag word per sum, which is the cost model's
unit for copying a value. -/
def Shape.words : Shape → Nat
  | .word _ => 1
  | .prod fs => Shape.wordsSum fs
  | .sum vs => 1 + Shape.wordsMax vs
  | .array n s => n * s.words
  | .slots n s => n * s.words
  | .ghost => 0
/-- The sum of `Shape.words` over a list. -/
def Shape.wordsSum : List Shape → Nat
  | [] => 0
  | s :: ss => s.words + Shape.wordsSum ss
/-- The maximum of `Shape.words` over a list, or 0 for the empty list. -/
def Shape.wordsMax : List Shape → Nat
  | [] => 0
  | s :: ss => max s.words (Shape.wordsMax ss)
end

/-- The memory contents of a value of shape `s`, exactly `s.size` bytes. -/
abbrev Shape.Val (s : Shape) : Type := {bs : List UInt8 // bs.length = s.size}

/-- The offsets of the fields `fs` laid out from offset `off`. -/
def Shape.prodOffsets : Nat → List Shape → List Nat
  | _, [] => []
  | off, s :: ss => alignUp off s.align :: Shape.prodOffsets (alignUp off s.align + s.size) ss

/-- The offset of field `i` of the struct `prod fs`, or 0 when `i` is out of range. -/
def Shape.fieldOffset (fs : List Shape) (i : Nat) : Nat := (Shape.prodOffsets 0 fs).getD i 0

/-- The offset of element or cell `i` of `array n s` or `slots n s`. -/
def Shape.elemOffset (s : Shape) (i : Nat) : Nat := i * s.size

/-- The bytes of the tag of `sum vs`. -/
def Shape.tagBytes (vs : List Shape) : Nat := (tagWidth vs.length).bytes

/-- The offset of the payload of `sum vs`. -/
def Shape.payloadOffset (vs : List Shape) : Nat := alignUp (Shape.tagBytes vs) (Shape.alignMax vs)

/-- The bytes `off … off+len-1` of `bs`. -/
def slice (bs : List UInt8) (off len : Nat) : List UInt8 := (bs.drop off).take len

/-! ## Arithmetic of `alignUp` -/

theorem le_alignUp (n a : Nat) (h : 0 < a) : n ≤ alignUp n a := by
  have := Nat.div_add_mod (n + (a - 1)) a
  have := Nat.mod_lt (n + (a - 1)) h
  unfold alignUp; rw [Nat.mul_comm]; omega

theorem dvd_alignUp (n a : Nat) : a ∣ alignUp n a := Nat.dvd_mul_left _ _

theorem alignUp_of_dvd {n a : Nat} (h : a ∣ n) (ha : 0 < a) : alignUp n a = n := by
  obtain ⟨k, rfl⟩ := h
  unfold alignUp
  rw [show a * k + (a - 1) = (a - 1) + k * a by rw [Nat.mul_comm]; omega,
    Nat.add_mul_div_right _ _ ha, Nat.div_eq_of_lt (by omega), Nat.mul_comm]; simp

theorem alignUp_zero (a : Nat) : alignUp 0 a = 0 := by
  unfold alignUp; rcases a with _ | a
  · simp
  · simp [Nat.div_eq_of_lt (Nat.lt_succ_self a)]

/-! ## Alignment is a positive power of two dividing the size -/

theorem Width.bytes_pow2 (w : Width) : ∃ k, w.bytes = 2 ^ k := by
  cases w
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

theorem max_pow2 (a b : Nat) : max (2 ^ a) (2 ^ b) = 2 ^ max a b := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.pow_le_pow_right (by decide) h)]
  · rw [Nat.max_eq_left h, Nat.max_eq_left (Nat.pow_le_pow_right (by decide) h)]

mutual
theorem Shape.align_pow2 : (s : Shape) → ∃ k, s.align = 2 ^ k
  | .word w => w.bytes_pow2
  | .prod fs => Shape.alignMax_pow2 fs
  | .sum vs => by
      obtain ⟨i, hi⟩ := (tagWidth vs.length).bytes_pow2
      obtain ⟨j, hj⟩ := Shape.alignMax_pow2 vs
      exact ⟨max i j, by simp only [Shape.align]; rw [hi, hj, max_pow2]⟩
  | .array _ s => Shape.align_pow2 s
  | .slots _ s => Shape.align_pow2 s
  | .ghost => ⟨0, rfl⟩
theorem Shape.alignMax_pow2 : (fs : List Shape) → ∃ k, Shape.alignMax fs = 2 ^ k
  | [] => ⟨0, rfl⟩
  | s :: ss => by
      obtain ⟨i, hi⟩ := Shape.align_pow2 s
      obtain ⟨j, hj⟩ := Shape.alignMax_pow2 ss
      exact ⟨max i j, by simp only [Shape.alignMax]; rw [hi, hj, max_pow2]⟩
end

theorem Shape.align_pos (s : Shape) : 0 < s.align := by
  obtain ⟨k, hk⟩ := s.align_pow2; rw [hk]; exact Nat.two_pow_pos k

theorem Shape.alignMax_pos (fs : List Shape) : 0 < Shape.alignMax fs := by
  obtain ⟨k, hk⟩ := Shape.alignMax_pow2 fs; rw [hk]; exact Nat.two_pow_pos k

theorem Shape.size_le_sizeMax {s : Shape} {fs : List Shape} (h : s ∈ fs) :
    s.size ≤ Shape.sizeMax fs := by
  induction fs with
  | nil => cases h
  | cons t ts ih =>
    simp only [Shape.sizeMax]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- Every size is a multiple of the alignment, so arrays need no inter-element padding. -/
theorem Shape.align_dvd_size : (s : Shape) → s.align ∣ s.size
  | .word _ => Nat.dvd_refl _
  | .prod _ => dvd_alignUp _ _
  | .sum _ => dvd_alignUp _ _
  | .array _ s => Nat.dvd_trans (Shape.align_dvd_size s) (Nat.dvd_mul_left _ _)
  | .slots _ s => Nat.dvd_trans (Shape.align_dvd_size s) (Nat.dvd_mul_left _ _)
  | .ghost => Nat.dvd_zero _

/-! ## Struct fields: bounds, alignment, non-overlap -/

theorem Shape.le_prodEnd (off : Nat) (fs : List Shape) : off ≤ Shape.prodEnd off fs := by
  induction fs generalizing off with
  | nil => exact Nat.le_refl _
  | cons s ss ih =>
    exact Nat.le_trans (Nat.le_trans (le_alignUp off _ s.align_pos) (Nat.le_add_right _ _))
      (ih _)

@[simp] theorem Shape.prodOffsets_length (off : Nat) (fs : List Shape) :
    (Shape.prodOffsets off fs).length = fs.length := by
  induction fs generalizing off <;> simp [Shape.prodOffsets, *]

theorem Shape.prodOffsets_ge (off : Nat) (fs : List Shape) (i : Nat)
    (hi : i < (Shape.prodOffsets off fs).length) : off ≤ (Shape.prodOffsets off fs)[i] := by
  induction fs generalizing off i with
  | nil => simp [Shape.prodOffsets] at hi
  | cons s ss ih =>
    cases i with
    | zero => exact le_alignUp off _ s.align_pos
    | succ i =>
      simp only [Shape.prodOffsets, List.getElem_cons_succ]
      exact Nat.le_trans (Nat.le_trans (le_alignUp off _ s.align_pos) (Nat.le_add_right _ _))
        (ih _ i _)

theorem Shape.prodOffsets_end (off : Nat) (fs : List Shape) (i : Nat)
    (hi : i < (Shape.prodOffsets off fs).length) :
    (Shape.prodOffsets off fs)[i] + (fs[i]'(by simpa using hi)).size ≤ Shape.prodEnd off fs := by
  induction fs generalizing off i with
  | nil => simp [Shape.prodOffsets] at hi
  | cons s ss ih =>
    cases i with
    | zero => exact Shape.le_prodEnd _ ss
    | succ i =>
      simp only [Shape.prodOffsets, List.getElem_cons_succ, Shape.prodEnd]
      exact ih _ i _

theorem Shape.prodOffsets_disjoint (off : Nat) (fs : List Shape) (i j : Nat) (hij : i < j)
    (hj : j < (Shape.prodOffsets off fs).length) :
    (Shape.prodOffsets off fs)[i] + (fs[i]'(by simp at hj; omega)).size ≤
      (Shape.prodOffsets off fs)[j] := by
  induction fs generalizing off i j with
  | nil => simp [Shape.prodOffsets] at hj
  | cons s ss ih =>
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        simp only [Shape.prodOffsets, List.getElem_cons_succ, List.getElem_cons_zero]
        exact Shape.prodOffsets_ge _ ss j _
      | succ i =>
        simp only [Shape.prodOffsets, List.getElem_cons_succ]
        exact ih _ i j (by omega) _

theorem Shape.fieldOffset_eq (fs : List Shape) (i : Nat) (hi : i < fs.length) :
    Shape.fieldOffset fs i = (Shape.prodOffsets 0 fs)[i]'(by simpa using hi) := by
  simp [Shape.fieldOffset, List.getD_eq_getElem?_getD, hi]

/-- Field `i` lies inside the struct. -/
theorem Shape.fieldOffset_add_size_le (fs : List Shape) (i : Nat) (hi : i < fs.length) :
    Shape.fieldOffset fs i + (fs[i]).size ≤ (Shape.prod fs).size := by
  rw [Shape.fieldOffset_eq fs i hi]
  exact Nat.le_trans (Shape.prodOffsets_end 0 fs i (by simpa using hi))
    (le_alignUp _ _ (Shape.alignMax_pos fs))

/-- Distinct fields do not overlap, since field `i` ends before a later field `j` starts. -/
theorem Shape.fieldOffset_disjoint (fs : List Shape) (i j : Nat) (hij : i < j)
    (hj : j < fs.length) :
    Shape.fieldOffset fs i + (fs[i]'(by omega)).size ≤ Shape.fieldOffset fs j := by
  rw [Shape.fieldOffset_eq fs i (by omega), Shape.fieldOffset_eq fs j hj]
  exact Shape.prodOffsets_disjoint 0 fs i j hij _

/-! ## Array elements and slots cells -/

/-- Element `i < n` lies inside `array n s`. -/
theorem Shape.elemOffset_add_size_le (n : Nat) (s : Shape) (i : Nat) (hi : i < n) :
    s.elemOffset i + s.size ≤ (Shape.array n s).size := by
  simp only [Shape.elemOffset, Shape.size]
  rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi

/-- Cell `i < n` lies inside `slots n s`. -/
theorem Shape.cellOffset_add_size_le (n : Nat) (s : Shape) (i : Nat) (hi : i < n) :
    s.elemOffset i + s.size ≤ (Shape.slots n s).size :=
  Shape.elemOffset_add_size_le n s i hi

/-! ## Sums: tag and payload -/

theorem Shape.tagBytes_le_payloadOffset (vs : List Shape) :
    Shape.tagBytes vs ≤ Shape.payloadOffset vs :=
  le_alignUp _ _ (Shape.alignMax_pos vs)

/-- The payload of any variant lies inside the sum. -/
theorem Shape.payload_add_size_le (vs : List Shape) (v : Shape) (h : v ∈ vs) :
    Shape.payloadOffset vs + v.size ≤ (Shape.sum vs).size := by
  simp only [Shape.size]
  refine Nat.le_trans ?_ (le_alignUp _ _ (Nat.lt_of_lt_of_le (Shape.alignMax_pos vs)
    (Nat.le_max_right _ _)))
  exact Nat.add_le_add_left (Shape.size_le_sizeMax h) _

/-- The tag holds every variant index. -/
theorem tagWidth_fits (n i : Nat) (hi : i < n) (hn : n ≤ 2 ^ 64) :
    i < 2 ^ (tagWidth n).bits := by
  unfold tagWidth Width.bits
  split
  · simp [Width.bytes]; omega
  · split
    · simp [Width.bytes]; omega
    · split
      · simp [Width.bytes]; omega
      · simp [Width.bytes]; omega

/-! ## Slices -/

@[simp] theorem slice_length (bs : List UInt8) (off len : Nat) :
    (slice bs off len).length = min len (bs.length - off) := by
  simp [slice]

theorem slice_length_of_le {bs : List UInt8} {off len : Nat} (h : off + len ≤ bs.length) :
    (slice bs off len).length = len := by
  simp; omega

/-- Slicing exactly at a known part of a concatenation. -/
theorem slice_append_mid (pre mid post : List UInt8) :
    slice (pre ++ mid ++ post) pre.length mid.length = mid := by
  simp [slice]

theorem slice_append_mid' {pre mid post : List UInt8} {off len : Nat} (h : pre.length = off)
    (hm : mid.length = len) : slice (pre ++ mid ++ post) off len = mid := by
  subst h hm; exact slice_append_mid pre mid post

end Millipede
