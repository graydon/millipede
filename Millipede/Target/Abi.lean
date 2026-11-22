import Millipede.Target.Isa

/-!
# ABI models

An `Abi isa` fixes the following for one platform on one ISA:

* The system-call convention. `sysCall` reads the requested call from the state and says whether
  it returns. The call number selects the extern symbol, word arguments come from registers, and
  the contents of input buffers are read from memory, so they must be readable. `sysOut` gives
  the addresses of the call's output buffers, one for each output capacity, where the handler
  writes the bytes the oracle supplies, truncated to the capacity. `sysRet` writes the result word
  and overwrites the registers the convention overwrites. An unknown call number, an unreadable
  input buffer or an unwritable output byte makes the machine stuck.
* The registers at process entry, `entryRegs entry sp`.
* Where the operating system puts the stack, below `stackTop`, the initial `sp`. Address-space
  randomisation is not modelled, and compiled code never observes addresses.
* The page size `2 ^ pageBits` used for layout, and the stack alignment at calls.

A process exits by the `exit` system call, which does not return. `World.call` records its event
and sets `halted`, after which the machine stutters.

`Abi.linux` models Linux on any ISA. The system calls Millipede uses, `read`, `write` and `exit`,
take the same arguments on every architecture, and only the registers of the number and the
arguments and the call numbers differ. On x64 the number is in `rax`, the arguments in
`rdi rsi rdx` and the result in `rax`, with the numbers 0, 1 and 60 from
`arch/x86/entry/syscalls/syscall_64.tbl`. On arm64 they are `x8`, `x0 x1 x2` and `x0`, with the
numbers 63, 64 and 93 from `include/uapi/asm-generic/unistd.h`. The system-call instruction itself
belongs to the ISA.

`Abi.trap ω` is the system-call handler given to `Isa.exec`. It changes only the registers and the
world, through `World.call`, so the oracle answers system calls exactly as it answers source-level
extern calls.
-/

namespace Millipede

/-- A platform ABI on an ISA. -/
structure Abi (isa : Isa) where
  /-- The base-2 logarithm of the page size used for layout, 12 on Linux x64. -/
  pageBits : Nat
  /-- The initial stack pointer, below which the stack lies. -/
  stackTop : UInt64
  /-- The stack alignment required at calls, in bytes, which is 16 on both targets. -/
  stackAlign : Nat
  /-- The registers at process entry, given the entry point and the initial stack pointer. -/
  entryRegs : (entry sp : UInt64) → isa.Regs
  /-- The system call the state requests, and whether it does not return. -/
  sysCall : MState isa.Regs → Option (Call × Bool)
  /-- The addresses of the requested call's output buffers, in order. -/
  sysOut : MState isa.Regs → List UInt64 := fun _ => []
  /-- Writes the result word into the registers and overwrites what the convention overwrites.
  It does not advance `pc`, which the ISA's `exec` does. -/
  sysRet : UInt64 → isa.Regs → isa.Regs

namespace Abi

variable {isa : Isa} (abi : Abi isa)

/-- The system-call handler, which performs the requested call against the oracle. The bytes
of the reply go to the output buffers, at most each buffer's capacity, the result word goes to
the registers, and the world records the event unless it has halted. -/
def trap (ω : Oracle) (s : MState isa.Regs) : Option (MState isa.Regs) :=
  match abi.sysCall s with
  | some (c, nr) =>
    let r := s.world.ask ω c nr
    (s.mem.writeAll (abi.sysOut s) (fitOut c.outCaps r.1.bytesOut)).map fun m =>
      { s with mem := m, regs := abi.sysRet r.1.result s.regs, world := r.2 }
  | none => none

/-- A system call only stores to writable memory and only extends the trace. -/
theorem trap_respects (ω : Oracle) (s s' : MState isa.Regs) (h : abi.trap ω s = some s') :
    s.Respects s' := by
  unfold trap at h
  split at h
  · obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨Memory.writeAll_frame _ _ _ _ hm, ?_⟩
    show s.world.events <+: (s.world.ask ω _ _).2.events
    rw [World.ask_snd]; exact World.call_prefix ω _ _ _
  · cases h

/-- A machine step with this ABI's system calls respects memory and extends the trace. -/
theorem step_respects (hl : isa.Laws) (ω : Oracle) {s s' : MState isa.Regs}
    (h : isa.step (abi.trap ω) s = some s') : s.Respects s' :=
  Isa.step_respects hl (abi.trap_respects ω) h

end Abi

/-! ## Linux -/

/-- The Linux system-call numbers of one architecture. -/
structure LinuxNums where
  read : UInt64
  write : UInt64
  exit : UInt64
deriving DecidableEq, Repr

/-- The x86-64 numbers: `read` 0, `write` 1, `exit` 60. -/
def LinuxNums.x64 : LinuxNums := ⟨0, 1, 60⟩

/-- The AArch64 numbers, from the generic table: `read` 63, `write` 64, `exit` 93. -/
def LinuxNums.a64 : LinuxNums := ⟨63, 64, 93⟩

/-- Where an ISA's Linux system-call convention keeps the call number, the arguments and the
result. -/
structure LinuxRegs (isa : Isa) where
  /-- The call number, in `rax` on x64 and `x8` on arm64. -/
  nr : isa.Regs → UInt64
  /-- Argument `i`, in `rdi rsi rdx r10 r8 r9` on x64 and `x0` to `x5` on arm64. -/
  arg : Nat → isa.Regs → UInt64
  /-- Writes the result, to `rax` on x64 and `x0` on arm64. -/
  setRet : UInt64 → isa.Regs → isa.Regs

/-- The Linux process and system-call model on an ISA. `exit(code)` does not return,
`write(fd, buf, n)` reads its `n` bytes from `buf`, which must be readable, and `read(fd, buf, n)`
writes at most `n` bytes the oracle supplies to `buf`. Any other call number makes the machine
stuck. -/
def Abi.linux {isa : Isa} (pageBits : Nat) (stackTop : UInt64)
    (entryRegs : (entry sp : UInt64) → isa.Regs) (n : LinuxNums) (R : LinuxRegs isa) : Abi isa where
  pageBits := pageBits
  stackTop := stackTop
  stackAlign := 16
  entryRegs := entryRegs
  sysCall s :=
    let r := s.regs
    if R.nr r = n.exit then some (⟨"exit", [R.arg 0 r], [], []⟩, true)
    else if R.nr r = n.write then
      (s.mem.read (R.arg 1 r) (R.arg 2 r).toNat).map fun bs =>
        (⟨"write", [R.arg 0 r], [bs], []⟩, false)
    else if R.nr r = n.read then some (⟨"read", [R.arg 0 r], [], [(R.arg 2 r).toNat]⟩, false)
    else none
  sysOut s := if R.nr s.regs = n.read then [R.arg 1 s.regs] else []
  sysRet := R.setRet

/-- The AArch64 Linux stack top of the model, `2^39 - 2^16`, which is below the end of the
smallest common user address space of 39 bits and aligned to 64 KiB. As on x64, address
randomisation is not modelled, and compiled code never observes addresses. -/
def Abi.a64LinuxStackTop : UInt64 := 0x7fffff0000

end Millipede
