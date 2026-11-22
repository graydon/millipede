import Millipede.Target.Machine

/-!
# ISA models

An `Isa` is an instruction type, a register file, an encoder and decoder, and the semantics of
one decoded instruction. The machine step `Isa.step` is defined here once for every ISA. It
fetches at most `maxLen` executable bytes at `pc`, decodes them, and executes the instruction. The
machine is stuck when decoding fails or execution faults, as on a division by zero, a
non-canonical address, a load from unreadable memory or a store to unwritable memory. The
system-call instruction is executed by calling the `trap` argument of `exec`, which the ABI
supplies, so the ISA does not know which system calls exist.

`exec` is a function, so execution is deterministic by construction. Each ISA proves the other
laws, the fields of `Isa.Laws`:

* Decoding an encoded instruction followed by any bytes gives it back with its length, and an
  encoding is non-empty and at most `maxLen` bytes long.
* A decoded instruction never claims more bytes than it was given.
* If `trap` only stores to writable memory and extends the trace, so does `exec`.
* The frame law. Each ISA names the parts of its register file as locations that cover the whole
  file, so that every location unchanged means the registers unchanged. An instruction other
  than the system-call instruction keeps every location outside `regWrites i`, every memory byte
  outside the ranges `memWrites i len regs` computed from the registers before it, and the world.
  After the system-call instruction, memory and the world are exactly what the handler left.

An encoder returns `none` for an instruction it cannot encode, such as one with an immediate out
of range, and the assembler then refuses the program.
-/

namespace Millipede

/-- An instruction-set model. -/
structure Isa where
  /-- The modelled instruction subset. -/
  Instr : Type
  /-- The register file, including the program counter and the flags. -/
  Regs : Type
  pc : Regs → UInt64
  /-- The stack pointer, by which stack depth is measured. -/
  sp : Regs → UInt64
  /-- The length of the longest encoding, 15 on x64 and 4 on arm64. -/
  maxLen : Nat
  encode : Instr → Option (List UInt8)
  /-- Decodes a prefix of the bytes, giving the instruction and how many bytes it used. -/
  decode : List UInt8 → Option (Instr × Nat)
  /-- Executes one instruction of the given length, from which it computes the fall-through
  `pc`. `trap` performs the system call. -/
  exec : (MState Regs → Option (MState Regs)) → Instr → Nat → MState Regs →
    Option (MState Regs)
  /-- The names of the parts of the register file, such as general registers, `pc` and the
  flags. -/
  Loc : Type
  /-- The value of a register location, with the flags read as a word. -/
  get : Regs → Loc → UInt64
  /-- The register locations an instruction may write, `pc` included. -/
  regWrites : Instr → List Loc
  /-- The memory ranges `(start, length)` an instruction of the given length may write, as a
  function of the registers before it. -/
  memWrites : Instr → Nat → Regs → List (UInt64 × Nat)
  /-- Whether an instruction is the system-call instruction, whose effect is the ABI's
  handler. -/
  isTrap : Instr → Bool

namespace Isa

variable (isa : Isa)

/-- Fetches and decodes the instruction at `pc`. Only executable bytes are ever decoded. -/
def fetchDecode (s : MState isa.Regs) : Option (isa.Instr × Nat) :=
  isa.decode (s.mem.fetch (isa.pc s.regs) isa.maxLen)

/-- One machine step, which fetches, decodes and executes an instruction. `none` means the
machine is stuck. -/
def step (trap : MState isa.Regs → Option (MState isa.Regs)) (s : MState isa.Regs) :
    Option (MState isa.Regs) :=
  match isa.fetchDecode s with
  | some (i, n) => isa.exec trap i n s
  | none => none

/-- The laws every ISA model proves. -/
structure Laws : Prop where
  decode_encode : ∀ (i : isa.Instr) (bs rest : List UInt8), isa.encode i = some bs →
    isa.decode (bs ++ rest) = some (i, bs.length)
  encode_length : ∀ (i : isa.Instr) (bs : List UInt8), isa.encode i = some bs →
    0 < bs.length ∧ bs.length ≤ isa.maxLen
  decode_length : ∀ (bs : List UInt8) (i : isa.Instr) (n : Nat), isa.decode bs = some (i, n) →
    0 < n ∧ n ≤ bs.length
  exec_respects : ∀ (trap : MState isa.Regs → Option (MState isa.Regs)) (i : isa.Instr)
    (n : Nat) (s s' : MState isa.Regs),
    (∀ t t', trap t = some t' → t.Respects t') →
    isa.exec trap i n s = some s' → s.Respects s'
  /-- The locations name the whole register file. -/
  get_ext : ∀ r r' : isa.Regs, (∀ l, isa.get r l = isa.get r' l) → r = r'
  /-- Only the named register locations change. -/
  exec_regs : ∀ (trap : MState isa.Regs → Option (MState isa.Regs)) (i : isa.Instr)
    (n : Nat) (s s' : MState isa.Regs), isa.isTrap i = false →
    isa.exec trap i n s = some s' → ∀ l, l ∉ isa.regWrites i → isa.get s'.regs l = isa.get s.regs l
  /-- Only the bytes in the named ranges change. -/
  exec_bytes : ∀ (trap : MState isa.Regs → Option (MState isa.Regs)) (i : isa.Instr)
    (n : Nat) (s s' : MState isa.Regs), isa.isTrap i = false →
    isa.exec trap i n s = some s' →
    ∀ a, (∀ w ∈ isa.memWrites i n s.regs, ¬ Memory.InRange w.1 w.2 a) →
      s'.mem.bytes a = s.mem.bytes a
  /-- An instruction other than the system call does not touch the world. -/
  exec_world : ∀ (trap : MState isa.Regs → Option (MState isa.Regs)) (i : isa.Instr)
    (n : Nat) (s s' : MState isa.Regs), isa.isTrap i = false →
    isa.exec trap i n s = some s' → s'.world = s.world
  /-- After the system-call instruction, memory and the world are the handler's. -/
  exec_trap : ∀ (trap : MState isa.Regs → Option (MState isa.Regs)) (i : isa.Instr)
    (n : Nat) (s s' : MState isa.Regs), isa.isTrap i = true →
    isa.exec trap i n s = some s' → ∃ t, trap s = some t ∧ s'.mem = t.mem ∧ s'.world = t.world

variable {isa}

/-- If the encoding of `i` sits, executable, at `pc`, the machine decodes `i`. -/
theorem fetchDecode_codeAt (hl : isa.Laws) {i : isa.Instr} {bs : List UInt8}
    {s : MState isa.Regs} (he : isa.encode i = some bs)
    (hc : s.mem.CodeAt (isa.pc s.regs) bs) : isa.fetchDecode s = some (i, bs.length) := by
  unfold fetchDecode
  rw [Memory.fetch_codeAt bs s.mem _ _ hc (hl.encode_length i bs he).2]
  exact hl.decode_encode i bs _ he

/-- A machine step respects memory permissions and only extends the trace. -/
theorem step_respects (hl : isa.Laws) {trap : MState isa.Regs → Option (MState isa.Regs)}
    (ht : ∀ t t', trap t = some t' → t.Respects t') {s s' : MState isa.Regs}
    (h : isa.step trap s = some s') : s.Respects s' := by
  unfold step at h
  split at h
  · exact hl.exec_respects trap _ _ s s' ht h
  · cases h

end Isa

end Millipede
