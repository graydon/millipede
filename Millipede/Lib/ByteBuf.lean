import Millipede.Lib.Bump
import Millipede.Lib.Slice

/-!
# A byte buffer for I/O

`Buf16` is `Bump U8 16`, whose bytes are `Slots` cells with ghost occupancy, so no slice of it can
be taken and it cannot be handed to an extern. `ByteBuf cap` is the form of a byte buffer for
I/O, one definition for every capacity `cap < 2 ^ 64`. It holds an array of `cap` bytes and the
number `len` of bytes held, with the invariant `len ≤ cap`. Its contents are slices of the array,
used in place. The bytes held are `&b.bytes[0..b.len]`, and the free space is
`&mut b.bytes[b.len..cap]`. A function cannot return a reference, so these slices are written
inline where they are used.

The functions of this module are the common uses. `writeTo` passes the bytes held to `write` as a
shared slice, and `readFrom` calls `read` into the free space as a mutable slice and appends the
bytes read. `reverse` reverses the bytes held in place with `Slice.reverse`, and `append` copies
as many bytes of a slice as fit into the free space with `Slice.copy`. `push!` appends a byte and
`clear` forgets the bytes held. An instance is an application such as `ByteBuf 16`, and a call
`ByteBuf.readFrom (&mut b) 0` infers the capacity.

The contracts say that `new` satisfies the invariant and that `push!`, `clear`, `readFrom`,
`reverse` and `append` keep it, whatever the oracle answers, since a count above the free space is
not appended. `push!` appends, `reverse` reverses the bytes held, and `append` appends
`min src.len (cap - len)` bytes of its slice. The obligations, which say that the slices fit the
array, are discharged under the invariant. Slices are described in doc/design/memory.md.
-/

namespace Millipede.Lib

open Millipede Std.WP

set_option experimental.vcgen true

/-- `write(fd, buf, len)` from a byte slice. -/
mp extern "write" ByteBuf.sysWrite (fd : UInt64) (buf : &[U8]) : UInt64

/-- `read(fd, buf, cap)` into a mutable byte slice, which returns the count read or `-errno`. -/
mp extern "read" ByteBuf.sysRead (fd : UInt64) (buf : &mut [U8]) : UInt64

/-- A byte buffer of `cap` bytes for I/O, with the bytes and the number held. -/
structure ByteBuf (cap : Nat) where
  bytes : Arr UInt8 cap
  len : UInt64
deriving Data

section
variable (cap : Nat) (hcap : cap < 2 ^ 64)
include hcap

/-- The invariant, which says that at most `cap` bytes are held. -/
def ByteBuf.Inv (b : ByteBuf cap) : Prop := b.len.toNat ≤ cap

/-- The empty buffer. -/
mp def ByteBuf.new ensures ByteBuf.Inv cap result : ByteBuf cap :=
  { bytes := Vector.replicate cap 0, len := 0 }

/-- Append a byte. The obligation `len < cap` replaces a check. -/
mp def ByteBuf.push! (b : &mut ByteBuf cap) (v : UInt8) requires b.len.toNat < cap
    ensures ByteBuf.Inv cap b' ∧ b'.len.toNat = b.len.toNat + 1 ∧
      b'.bytes = vset b.bytes b.len.toNat v : Unit := do
  let i := b.len
  b.bytes[i]! := v
  b.len := i +! 1
  ()

/-- Forget the bytes held. -/
mp def ByteBuf.clear (b : &mut ByteBuf cap) ensures ByteBuf.Inv cap b' ∧ b'.len = 0 : Unit := do
  b.len := 0
  ()

/-- `write` the bytes held, the shared slice `&b.bytes[0..b.len]` passed as a pointer and a
length. It returns the count written, or `-errno`. -/
mp def ByteBuf.writeTo (b : &ByteBuf cap) (fd : UInt64) requires ByteBuf.Inv cap b : UInt64 :=
  let n := b.len
  ByteBuf.sysWrite fd (&b.bytes[0..n])

/-- `read` into the free space, the mutable slice `&mut b.bytes[b.len..cap]`, and append the bytes
read. It returns the extern's result, which is the count or `-errno`. A count above the free
space is an error and appends nothing, so the invariant holds whatever the oracle answers. -/
mp def ByteBuf.readFrom (b : &mut ByteBuf cap) (fd : UInt64) requires ByteBuf.Inv cap b
    ensures ByteBuf.Inv cap b' : UInt64 := do
  let n := b.len
  let r := ByteBuf.sysRead fd (&mut b.bytes[n..cap])
  if r <= cap -! n then
    b.len := n +! r
    r
  else r

/-- Reverse the bytes held in place, by `Slice.reverse` on the slice `&mut b.bytes[0..b.len]`. The
length is kept and byte `j` becomes byte `len-1-j`. -/
mp def ByteBuf.reverse (b : &mut ByteBuf cap) requires ByteBuf.Inv cap b
    ensures b'.len = b.len ∧ ∀ j < cap, vget b'.bytes j 0 =
      if j < b.len.toNat then vget b.bytes (b.len.toNat - 1 - j) 0 else vget b.bytes j 0 : Unit :=
  let n := b.len
  let _ := Slice.reverse (&mut b.bytes[0..n])
  ()

/-- Append as many bytes of a slice as fit, copied by `Slice.copy` into the free space
`&mut b.bytes[b.len..cap]`. It returns the count appended, `min src.len (cap - len)`, and the
bytes of `src` follow the bytes held. -/
mp def ByteBuf.append (b : &mut ByteBuf cap) (src : &[UInt8; cap]) requires ByteBuf.Inv cap b
    ensures ByteBuf.Inv cap b' ∧ result.toNat = min src.len.toNat (cap - b.len.toNat) ∧
      b'.len.toNat = b.len.toNat + result.toNat ∧ ∀ j < cap, vget b'.bytes j 0 =
        if b.len.toNat ≤ j ∧ j < b'.len.toNat then (src.cell (j - b.len.toNat)).getD 0
        else vget b.bytes j 0 : UInt64 := do
  let n := b.len
  let free := cap -! n
  let c := if src.len < free then src.len else free
  let _ := Slice.copy (&mut b.bytes[n..cap]) (&src)
  b.len := n +! c
  c

end

/-- Element `j` of an array after a view of it was written back. -/
theorem ByteBuf.vget_vunview {n : Nat} (v : Vector UInt8 n) (lo len : Nat) (s : Slots UInt8 n)
    (j : Nat) (hj : j < n) : vget (vunview v lo len s) j 0 =
      if lo ≤ j ∧ j - lo < len then (s.cell (j - lo)).getD (vget v j 0) else vget v j 0 := by
  simp [vget, vunview, hj]

section
variable (cap : Nat) (hcap : cap < 2 ^ 64)
include hcap

mp prove ByteBuf.reverse.spec := by
  intro b
  vcgen [ByteBuf.reverse]
  case vc1 h => simp only [ByteBuf.Inv] at h; simp only [UInt64.sub_zero, vview_isFull]; grind
  case vc2 h _ _ _ hs =>
    intro j hj
    simp only [ByteBuf.Inv, UInt64.sub_zero] at h hs ⊢
    rw [ByteBuf.vget_vunview _ _ _ _ _ hj, Nat.sub_zero, hs j hj]
    by_cases hl : j < b.len.toNat
    · simp [hl, vview_cell, vget, show b.len.toNat - 1 - j < cap by omega,
        show b.len.toNat - 1 - j < b.len.toNat by omega]
    · simp [hl]

/-- The free space `cap - len` as a word. -/
theorem ByteBuf.toNat_free (b : ByteBuf cap) (h : b.len.toNat ≤ cap) :
    (UInt64.ofNat cap - b.len).toNat = cap - b.len.toNat := by
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hcap]; omega),
    UInt64.toNat_ofNat_of_lt' hcap]

/-- `append`'s postcondition, for a count `c` and the copied view `x`. -/
theorem ByteBuf.append_post (b : ByteBuf cap) (src x : Slots UInt8 cap) (sl c : UInt64)
    (h : b.len.toNat ≤ cap) (hf : ∀ k < sl.toNat, src.isFull k = true)
    (hc : c.toNat = min sl.toNat (cap - b.len.toNat))
    (hx : ∀ k < cap, x.cell k = if k < cap - b.len.toNat ∧ k < sl.toNat then src.cell k
      else (vview b.bytes b.len.toNat (cap - b.len.toNat)).cell k) :
    ByteBuf.Inv cap ⟨vunview b.bytes b.len.toNat (cap - b.len.toNat) x, b.len + c⟩ ∧
      c.toNat = min sl.toNat (cap - b.len.toNat) ∧ (b.len + c).toNat = b.len.toNat + c.toNat ∧
      ∀ j < cap, vget (vunview b.bytes b.len.toNat (cap - b.len.toNat) x) j 0 =
        if b.len.toNat ≤ j ∧ j < (b.len + c).toNat then (src.cell (j - b.len.toNat)).getD 0
        else vget b.bytes j 0 := by
  have hl : (b.len + c).toNat = b.len.toNat + c.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by simp only [ByteBuf.Inv, hl]; omega, hc, hl, fun j hj => ?_⟩
  rw [ByteBuf.vget_vunview _ _ _ _ _ hj, hl]
  by_cases hin : b.len.toNat ≤ j ∧ j - b.len.toNat < cap - b.len.toNat
  · rw [ite_eq_left hin, hx _ (by omega)]
    by_cases hs : j - b.len.toNat < sl.toNat
    · rw [ite_eq_left ⟨hin.2, hs⟩, ite_eq_left ⟨hin.1, by omega⟩]
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hf _ hs)
      simp [hv]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), vview_cell]
      simp [vget, hj, show b.len.toNat + (j - b.len.toNat) = j by omega, hin.2,
        show j - b.len.toNat < cap by omega]
  · rw [ite_eq_right hin, ite_eq_right (by omega)]

mp prove ByteBuf.append.spec := by
  intro b src sl
  vcgen [ByteBuf.append]
  all_goals obtain ⟨h, hsl, hf⟩ := ‹ByteBuf.Inv cap b ∧ _›; simp only [ByteBuf.Inv] at h
  all_goals simp only [UInt64.lt_iff_toNat_lt, ByteBuf.toNat_free cap hcap b h] at *
  all_goals try exact ⟨⟨by omega, fun k hk => by simp; omega⟩, hsl, hf⟩
  · exact ByteBuf.append_post cap hcap b src _ sl sl h hf (by omega) ‹_›
  · have := ByteBuf.append_post cap hcap b src _ sl (UInt64.ofNat cap - b.len) h hf
      (by rw [ByteBuf.toNat_free cap hcap b h]; omega) ‹_›
    rwa [ByteBuf.toNat_free cap hcap b h] at this

end

end Millipede.Lib
