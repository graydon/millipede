import Millipede.Target.Abi

/-!
# Linked images

An `Image` is what the linker produces and what a format writer serialises. It holds the loadable
segments, each with an address, initialised bytes, a size in memory with zero fill, and
permissions, together with the entry point and the stack size. Executables are static and make raw
system calls, so an image has no imports or exports.

`Image.init abi img` is the machine state in which the program starts. Its memory holds the
segments' bytes and zeros elsewhere, page permissions come from the segments, and a read-write
stack of `stackSize` bytes, rounded up to pages, lies directly below `abi.stackTop`. The registers
are the ABI's entry registers with `sp = abi.stackTop`, and the world is empty. Every format's
loader model must produce exactly this state from the bytes its writer produced.

`Image.valid abi img` is the check that every writer must perform. It requires the segments to be
page-aligned, non-empty, sorted, on disjoint pages, below the stack and never both writable and
executable, and the stack to be non-empty and page-aligned. `Image.init_wxorx` proves that the
initial memory of a valid image is W^X, so code never changes.
-/

namespace Millipede

/-- A loadable segment, which holds `bytes` at `vaddr` followed by zeros up to `memSize` bytes. -/
structure Segment where
  vaddr : UInt64
  bytes : List UInt8
  memSize : Nat
  perm : Perm
deriving DecidableEq, Repr, Inhabited

/-- A linked, loadable program. -/
structure Image where
  segments : List Segment
  entry : UInt64
  /-- the bytes of stack the program needs, which is the proved bound rounded as the backend
  chooses -/
  stackSize : Nat
deriving DecidableEq, Repr, Inhabited

namespace Segment

/-- The segment's memory range contains address `a`. -/
def contains (sg : Segment) (a : UInt64) : Bool :=
  sg.vaddr.toNat ≤ a.toNat && a.toNat < sg.vaddr.toNat + sg.memSize

/-- The byte at `a`, which is zero past `bytes`. -/
def byteAt (sg : Segment) (a : UInt64) : UInt8 :=
  sg.bytes.getD (a.toNat - sg.vaddr.toNat) 0

/-- The first page that the segment touches. -/
def firstPage (pageBits : Nat) (sg : Segment) : Nat := sg.vaddr.toNat / 2 ^ pageBits

/-- The last page that the segment touches, which is meaningful when `memSize > 0`. -/
def lastPage (pageBits : Nat) (sg : Segment) : Nat :=
  (sg.vaddr.toNat + sg.memSize - 1) / 2 ^ pageBits

/-- The segment touches page `p`. -/
def coversPage (pageBits : Nat) (sg : Segment) (p : Nat) : Bool :=
  0 < sg.memSize && sg.firstPage pageBits ≤ p && p ≤ sg.lastPage pageBits

end Segment

namespace Image

/-- The byte at `a`, taken from the first segment that contains it, and zero when there is none. -/
def segByte : List Segment → UInt64 → UInt8
  | [], _ => 0
  | sg :: sgs, a => if sg.contains a then sg.byteAt a else segByte sgs a

/-- The permissions of page `p`, taken from the first segment that touches it, if any. -/
def segPerm (pageBits : Nat) : List Segment → Nat → Option Perm
  | [], _ => none
  | sg :: sgs, p => if sg.coversPage pageBits p then some sg.perm else segPerm pageBits sgs p

/-- The number of stack pages. -/
def stackPages (pageBits : Nat) (img : Image) : Nat :=
  (img.stackSize + 2 ^ pageBits - 1) / 2 ^ pageBits

/-- Page `p` is a stack page, one of the `stackPages` pages directly below `stackTop`. -/
def isStackPage (pageBits : Nat) (stackTop : UInt64) (img : Image) (p : Nat) : Bool :=
  stackTop.toNat / 2 ^ pageBits - img.stackPages pageBits ≤ p &&
    p < stackTop.toNat / 2 ^ pageBits

/-- The byte at `a` in the initial memory. -/
def byteAt (img : Image) (a : UInt64) : UInt8 := segByte img.segments a

/-- The permissions of page `p` in the initial memory, which are the segment's, else read-write on
stack pages, else unmapped. -/
def pagePerm (pageBits : Nat) (stackTop : UInt64) (img : Image) (p : Nat) : Perm :=
  match segPerm pageBits img.segments p with
  | some pm => pm
  | none => if img.isStackPage pageBits stackTop p then Perm.rw else Perm.none

/-- The initial memory. -/
def mem (pageBits : Nat) (stackTop : UInt64) (img : Image) : Memory where
  pageBits := pageBits
  bytes := img.byteAt
  perm := img.pagePerm pageBits stackTop

/-- The machine state at process entry. -/
def init {isa : Isa} (abi : Abi isa) (img : Image) : MState isa.Regs where
  regs := abi.entryRegs img.entry abi.stackTop
  mem := img.mem abi.pageBits abi.stackTop
  world := World.init

/-- The checks on one segment, which require it to be non-empty and page-aligned, its bytes to fit,
its permissions not to be both writable and executable, and its end to be at or below `limit`. -/
def segOk (pageBits : Nat) (limit : Nat) (sg : Segment) : Bool :=
  0 < sg.memSize && sg.bytes.length ≤ sg.memSize && sg.vaddr.toNat % 2 ^ pageBits == 0 &&
    !(sg.perm.w && sg.perm.x) && sg.vaddr.toNat + sg.memSize ≤ limit

/-- Segments are sorted by address and occupy disjoint pages. -/
def sortedDisjoint (pageBits : Nat) : List Segment → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a.lastPage pageBits < b.firstPage pageBits &&
      sortedDisjoint pageBits (b :: rest)

/-- The validity check that writers perform before serialising. -/
def valid {isa : Isa} (abi : Abi isa) (img : Image) : Bool :=
  let P := 2 ^ abi.pageBits
  let top := abi.stackTop.toNat / P
  let n := img.stackPages abi.pageBits
  0 < img.stackSize && abi.stackTop.toNat % P == 0 && n ≤ top &&
    img.segments.all (segOk abi.pageBits ((top - n) * P)) &&
    sortedDisjoint abi.pageBits img.segments

theorem segPerm_mem {pageBits : Nat} : ∀ {sgs : List Segment} {p : Nat} {pm : Perm},
    segPerm pageBits sgs p = some pm → ∃ sg ∈ sgs, sg.perm = pm
  | [], _, _, h => by cases h
  | sg :: sgs, p, pm, h => by
    simp only [segPerm] at h
    split at h
    · cases h; exact ⟨sg, List.mem_cons_self, rfl⟩
    · obtain ⟨sg', hm, he⟩ := segPerm_mem h
      exact ⟨sg', List.mem_cons_of_mem _ hm, he⟩

/-- A valid image starts with W^X memory, in which no page is both writable and executable. -/
theorem init_wxorx {isa : Isa} (abi : Abi isa) (img : Image) (h : img.valid abi = true) :
    (img.init abi).mem.WxorX := by
  intro p ⟨hw, hx⟩
  change (img.pagePerm abi.pageBits abi.stackTop p).w = true at hw
  change (img.pagePerm abi.pageBits abi.stackTop p).x = true at hx
  unfold pagePerm at hw hx
  cases hpm : segPerm abi.pageBits img.segments p with
  | none =>
    rw [hpm] at hw hx
    by_cases hs : img.isStackPage abi.pageBits abi.stackTop p = true
    · simp [hs, Perm.rw] at hx
    · simp [hs, Perm.none] at hx
  | some pm =>
    rw [hpm] at hw hx
    obtain ⟨sg, hm, rfl⟩ := segPerm_mem hpm
    simp only [valid, Bool.and_eq_true, List.all_eq_true] at h
    have := h.1.2 sg hm
    simp only [segOk, Bool.and_eq_true, Bool.not_eq_true'] at this
    simp [hw, hx] at this

end Image

end Millipede
