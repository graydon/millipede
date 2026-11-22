import Millipede.Extern.Oracle
import Millipede.Core.LE

/-!
# Machine memory and machine state

Memory is a map from 64-bit addresses to bytes with permissions to read, write and execute for
each page. Addresses wrap modulo 2⁶⁴, and an ISA that faults on some addresses, as x64 does on
non-canonical ones, checks that itself. The page size is `2 ^ pageBits` bytes, fixed for each
memory by the ABI's loader model.

A data read needs read permission on every byte. Instruction fetch returns the longest run of
executable bytes at the address up to a maximum length, so decoding never sees a byte that is not
executable. A store needs write permission on every byte and changes nothing else, and
permissions never change, so under W^X code is never modified.

`MState Regs` is the machine state every ISA shares. It holds the ISA's registers, which include
the program counter, the memory, and the extern `World` of events so far and a halted flag. A
system call changes only registers and the world.
-/

namespace Millipede

/-- Page permissions. -/
structure Perm where
  r : Bool
  w : Bool
  x : Bool
deriving DecidableEq, Repr, Inhabited

namespace Perm
/-- Unmapped. -/
def none : Perm := ⟨false, false, false⟩
/-- Read-only data. -/
def r_ : Perm := ⟨true, false, false⟩
/-- Read-write data, including the stack. -/
def rw : Perm := ⟨true, true, false⟩
/-- Code. -/
def rx : Perm := ⟨true, false, true⟩
end Perm

/-- Byte-addressed memory with per-page permissions. Page `p` covers addresses
`[p * 2^pageBits, (p+1) * 2^pageBits)`. -/
structure Memory where
  pageBits : Nat
  bytes : UInt64 → UInt8
  perm : Nat → Perm

namespace Memory

/-- The page number of an address. -/
def page (m : Memory) (a : UInt64) : Nat := a.toNat / 2 ^ m.pageBits

/-- The permissions of the page holding `a`. -/
def permAt (m : Memory) (a : UInt64) : Perm := m.perm (m.page a)

def readable (m : Memory) (a : UInt64) : Bool := (m.permAt a).r
def writable (m : Memory) (a : UInt64) : Bool := (m.permAt a).w
def executable (m : Memory) (a : UInt64) : Bool := (m.permAt a).x

/-- Overwrites one byte without checking permissions, which `write` does. -/
def set (m : Memory) (a : UInt64) (b : UInt8) : Memory :=
  { m with bytes := fun a' => if a' = a then b else m.bytes a' }

/-- Reads `n` bytes from `a` on, with wrapping addresses, and gives `none` unless every byte is
readable. -/
def read (m : Memory) (a : UInt64) : Nat → Option (List UInt8)
  | 0 => some []
  | n + 1 => if m.readable a then (m.read (a + 1) n).map (m.bytes a :: ·) else none

/-- Instruction fetch, which returns the executable bytes at `a`, at most `n` of them, and stops
at the first byte that is not executable. -/
def fetch (m : Memory) (a : UInt64) : Nat → List UInt8
  | 0 => []
  | n + 1 => if m.executable a then m.bytes a :: m.fetch (a + 1) n else []

/-- Stores bytes from `a` on, with wrapping addresses, and gives `none` unless every byte is
writable. -/
def write : Memory → UInt64 → List UInt8 → Option Memory
  | m, _, [] => some m
  | m, a, b :: bs => if m.writable a then (m.set a b).write (a + 1) bs else none

/-- The bytes `bs` are stored at `a` in executable memory. -/
def CodeAt (m : Memory) : UInt64 → List UInt8 → Prop
  | _, [] => True
  | a, b :: bs => m.executable a = true ∧ m.bytes a = b ∧ m.CodeAt (a + 1) bs

/-- No page is both writable and executable. -/
def WxorX (m : Memory) : Prop := ∀ p, ¬ ((m.perm p).w = true ∧ (m.perm p).x = true)

/-- `m'` arises from `m` by stores, so it has the same page size and permissions, and every
byte that is not writable is unchanged. -/
def Frame (m m' : Memory) : Prop :=
  m'.pageBits = m.pageBits ∧ m'.perm = m.perm ∧
    ∀ a, m.writable a = false → m'.bytes a = m.bytes a

end Memory

namespace Memory

/-- Reads an `n`-byte little-endian word, zero-extended. -/
def readWord (m : Memory) (a : UInt64) (n : Nat) : Option UInt64 :=
  (m.read a n).map decodeLE

/-- Writes the low `n` bytes of `w`, little-endian. -/
def writeWord (m : Memory) (a : UInt64) (n : Nat) (w : UInt64) : Option Memory :=
  m.write a (natBytes n w.toNat)

/-! ### Laws of memory -/

@[simp] theorem set_pageBits (m : Memory) (a : UInt64) (b : UInt8) :
    (m.set a b).pageBits = m.pageBits := rfl
@[simp] theorem set_perm (m : Memory) (a : UInt64) (b : UInt8) :
    (m.set a b).perm = m.perm := rfl
@[simp] theorem set_writable (m : Memory) (a : UInt64) (b : UInt8) :
    (m.set a b).writable = m.writable := rfl

theorem Frame.refl (m : Memory) : Frame m m := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {m₁ m₂ m₃ : Memory} (h₁ : Frame m₁ m₂) (h₂ : Frame m₂ m₃) :
    Frame m₁ m₃ := by
  obtain ⟨p₁, q₁, r₁⟩ := h₁
  obtain ⟨p₂, q₂, r₂⟩ := h₂
  refine ⟨p₂.trans p₁, q₂.trans q₁, fun a ha => ?_⟩
  have ha' : m₂.writable a = false := by
    simp only [writable, permAt, page, p₁, q₁]; exact ha
  rw [r₂ a ha', r₁ a ha]

/-- A successful store touches only writable bytes and keeps the page size and permissions. -/
theorem write_frame : ∀ (bs : List UInt8) (m m' : Memory) (a : UInt64),
    m.write a bs = some m' → Frame m m'
  | [], m, m', a, h => by cases h; exact Frame.refl m
  | b :: bs, m, m', a, h => by
    simp only [write] at h
    split at h
    · rename_i hw
      refine Frame.trans (m₂ := m.set a b) ⟨rfl, rfl, fun a' ha' => ?_⟩ (write_frame bs _ _ _ h)
      simp only [set]
      split
      · subst_vars; rw [hw] at ha'; cases ha'
      · rfl
    · cases h

/-- Every byte a successful store covers is writable. -/
theorem write_writable : ∀ (bs : List UInt8) (m m' : Memory) (a : UInt64),
    m.write a bs = some m' → ∀ i, i < bs.length → m.writable (a + UInt64.ofNat i) = true
  | [], _, _, _, _, i, hi => by simp at hi
  | b :: bs, m, m', a, h, i, hi => by
    simp only [write] at h
    split at h
    · rename_i hw
      cases i with
      | zero => simpa using hw
      | succ i =>
        have := write_writable bs _ _ _ h i (by simp at hi; omega)
        rw [set_writable] at this
        have e : a + 1 + UInt64.ofNat i = a + UInt64.ofNat (i + 1) := by
          rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm 1]; rfl
        rwa [e] at this
    · cases h

/-- Every byte a successful read covers is readable. -/
theorem read_readable : ∀ (n : Nat) (m : Memory) (a : UInt64) (bs : List UInt8),
    m.read a n = some bs → ∀ i, i < n → m.readable (a + UInt64.ofNat i) = true
  | 0, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, m, a, bs, h, i, hi => by
    simp only [read] at h
    split at h
    · rename_i hr
      cases i with
      | zero => simpa using hr
      | succ i =>
        cases hrd : m.read (a + 1) n with
        | none => rw [hrd] at h; cases h
        | some bs' =>
          have := read_readable n m (a + 1) bs' hrd i (by omega)
          have e : a + 1 + UInt64.ofNat i = a + UInt64.ofNat (i + 1) := by
            rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm 1]; rfl
          rwa [e] at this
    · cases h

/-- A read returns exactly `n` bytes. -/
theorem read_length : ∀ (n : Nat) (m : Memory) (a : UInt64) (bs : List UInt8),
    m.read a n = some bs → bs.length = n
  | 0, _, _, _, h => by cases h; rfl
  | n + 1, m, a, bs, h => by
    simp only [read] at h
    split at h
    · cases hrd : m.read (a + 1) n with
      | none => rw [hrd] at h; cases h
      | some bs' =>
        rw [hrd] at h; cases h
        simp [read_length n m (a + 1) bs' hrd]
    · cases h

/-- Every fetched byte comes from an executable address. -/
theorem fetch_executable : ∀ (n : Nat) (m : Memory) (a : UInt64) (i : Nat),
    i < (m.fetch a n).length → m.executable (a + UInt64.ofNat i) = true
  | 0, _, _, i, hi => by simp [fetch] at hi
  | n + 1, m, a, i, hi => by
    simp only [fetch] at hi
    split at hi
    · rename_i hx
      cases i with
      | zero => simpa using hx
      | succ i =>
        have := fetch_executable n m (a + 1) i (by simp at hi; omega)
        have e : a + 1 + UInt64.ofNat i = a + UInt64.ofNat (i + 1) := by
          rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm 1]; rfl
        rwa [e] at this
    · simp at hi

/-- At most `n` bytes are fetched. -/
theorem fetch_length_le : ∀ (n : Nat) (m : Memory) (a : UInt64), (m.fetch a n).length ≤ n
  | 0, _, _ => by simp [fetch]
  | n + 1, m, a => by
    simp only [fetch]
    split
    · simp only [List.length_cons]; have := fetch_length_le n m (a + 1); omega
    · simp

/-- Fetching where code `bs` sits returns `bs` followed by whatever follows it. -/
theorem fetch_codeAt : ∀ (bs : List UInt8) (m : Memory) (a : UInt64) (n : Nat),
    m.CodeAt a bs → bs.length ≤ n →
    m.fetch a n = bs ++ m.fetch (a + UInt64.ofNat bs.length) (n - bs.length)
  | [], m, a, n, _, _ => by simp
  | b :: bs, m, a, n, h, hn => by
    obtain ⟨hx, hb, hrest⟩ := h
    cases n with
    | zero => simp at hn
    | succ n =>
      simp only [fetch, hx, ite_true, hb, List.cons_append, List.cons.injEq, true_and]
      rw [fetch_codeAt bs m (a + 1) n hrest (by simp at hn; omega)]
      have e : a + 1 + UInt64.ofNat bs.length = a + UInt64.ofNat (b :: bs).length := by
        simp only [List.length_cons]
        rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm 1]; rfl
      rw [e]; simp

/-- Under W^X, stores leave instruction fetch unchanged, so code does not change. -/
theorem Frame.fetch_eq {m m' : Memory} (hwx : m.WxorX) (h : Frame m m') :
    ∀ (n : Nat) (a : UInt64), m'.fetch a n = m.fetch a n
  | 0, _ => rfl
  | n + 1, a => by
    obtain ⟨hp, hq, hb⟩ := h
    have hx : m'.executable a = m.executable a := by
      simp [executable, permAt, page, hp, hq]
    simp only [fetch, hx]
    split
    · rename_i hxa
      have hw : m.writable a = false := by
        cases hwa : m.writable a with
        | false => rfl
        | true => exact absurd ⟨hwa, hxa⟩ (hwx (m.page a))
      rw [hb a hw, Frame.fetch_eq hwx ⟨hp, hq, hb⟩ n (a + 1)]
    · rfl

/-- Address `a` lies in the `n`-byte range starting at `b`, with addresses wrapping modulo
`2^64`. -/
def InRange (b : UInt64) (n : Nat) (a : UInt64) : Prop := (a - b).toNat < n

/-- A store changes only the bytes it covers. -/
theorem write_outside : ∀ (bs : List UInt8) (m m' : Memory) (a b : UInt64),
    m.write a bs = some m' → ¬ InRange a bs.length b → m'.bytes b = m.bytes b
  | [], m, m', _, _, h, _ => by cases h; rfl
  | c :: bs, m, m', a, b, h, hb => by
    simp only [write] at h
    split at h
    · have hb' : ¬ InRange (a + 1) bs.length b := by
        intro hr; apply hb
        simp only [InRange, List.length_cons] at hr ⊢
        have e : b - a = (b - (a + 1)) + 1 := by
          grind
        rw [e, UInt64.toNat_add]
        simp only [UInt64.toNat_one]
        omega
      rw [write_outside bs _ _ _ _ h hb']
      have hne : b ≠ a := by
        intro e; subst e; apply hb; simp [InRange]
      simp [set, hne]
    · cases h

/-- A word store changes memory only by stores. -/
theorem writeWord_frame {m m' : Memory} {a : UInt64} {n : Nat} {v : UInt64}
    (h : m.writeWord a n v = some m') : Frame m m' :=
  write_frame _ _ _ _ h

/-- A word store changes only the `n` bytes it covers. -/
theorem writeWord_outside {m m' : Memory} {a : UInt64} {n : Nat} {v : UInt64}
    (h : m.writeWord a n v = some m') {b : UInt64} (hb : ¬ InRange a n b) :
    m'.bytes b = m.bytes b :=
  write_outside _ _ _ _ _ h (by rw [natBytes_length]; exact hb)

/-- A prefix of the fetched bytes lies, executable, in memory. -/
theorem codeAt_of_fetch : ∀ (p q : List UInt8) (m : Memory) (a : UInt64) (k : Nat),
    m.fetch a k = p ++ q → m.CodeAt a p
  | [], _, _, _, _, _ => trivial
  | b :: p, q, m, a, k, h => by
    cases k with
    | zero => simp [fetch] at h
    | succ k =>
      simp only [fetch] at h
      split at h
      · rename_i hx
        simp only [List.cons_append, List.cons.injEq] at h
        exact ⟨hx, h.1, codeAt_of_fetch p q m (a + 1) k h.2⟩
      · simp at h

theorem Frame.wxorx {m m' : Memory} (h : Frame m m') (hwx : m.WxorX) : m'.WxorX := by
  intro p; rw [h.2.1]; exact hwx p

/-- Writes several byte strings, each at its address, as an extern writes its output buffers.
It fails if any byte is not writable, and ignores extra addresses or strings. -/
def writeAll (m : Memory) : List UInt64 → List (List UInt8) → Option Memory
  | a :: as, bs :: bss => (m.write a bs).bind fun m' => m'.writeAll as bss
  | _, _ => some m

theorem writeAll_frame : ∀ (as : List UInt64) (bss : List (List UInt8)) (m m' : Memory),
    m.writeAll as bss = some m' → Frame m m'
  | [], _, m, m', h => by cases h; exact Frame.refl m
  | _ :: _, [], m, m', h => by cases h; exact Frame.refl m
  | a :: as, bs :: bss, m, m', h => by
    simp only [writeAll] at h
    cases hw : m.write a bs with
    | none => rw [hw] at h; cases h
    | some m₁ =>
      rw [hw, Option.bind_some] at h
      exact (write_frame bs m m₁ a hw).trans (writeAll_frame as bss m₁ m' h)

end Memory

/-- The machine state shared by every ISA: the registers, which include the program counter,
the memory, and the extern world of the trace so far and a halted flag. -/
structure MState (Regs : Type) where
  regs : Regs
  mem : Memory
  world : World

/-- What every machine step must respect: memory changes only by stores, and the trace only
grows. -/
def MState.Respects {Regs : Type} (s s' : MState Regs) : Prop :=
  Memory.Frame s.mem s'.mem ∧ s.world.events <+: s'.world.events

theorem MState.Respects.refl {Regs : Type} (s : MState Regs) : s.Respects s :=
  ⟨Memory.Frame.refl _, List.prefix_refl _⟩

theorem MState.Respects.trans {Regs : Type} {s₁ s₂ s₃ : MState Regs}
    (h₁ : s₁.Respects s₂) (h₂ : s₂.Respects s₃) : s₁.Respects s₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

end Millipede
