import Millipede.Target.X64.Laws
import Millipede.Target.Isa

/-!
# x64 as an `Isa`

`X64.isa` packages the x64 model as an `Isa`, with `rip` as the program counter, `rsp` as the
stack pointer, instructions of at most 15 bytes, the encoder `some ∘ encode` because every
instruction of the subset is encodable, the decoder and `exec`, and the register locations and
write sets of the frame law. `X64.laws` proves the generic laws for it, the frame law included.
-/

namespace Millipede.X64

/-- The x64 ISA model. -/
def isa : Isa where
  Instr := Instr
  Regs := Regs
  pc r := r.rip
  sp r := r.gpr .rsp
  maxLen := 15
  encode i := some (encode i)
  decode := decode
  exec := exec
  Loc := XLoc
  get := XLoc.get
  regWrites := Instr.regWrites
  memWrites := Instr.memWrites
  isTrap := Instr.isTrap

/-- The x64 model satisfies the ISA laws. -/
theorem laws : isa.Laws where
  decode_encode i bs rest h := by
    cases h; exact decode_encode i rest
  encode_length i bs h := by
    cases h; exact encode_length i
  decode_length _ _ _ h := decode_length h
  exec_respects trap i n s s' ht h := exec_respects trap i n s s' ht h
  get_ext _ _ h := regs_ext h
  exec_regs _ _ _ _ _ hi h := exec_regs hi h
  exec_bytes _ _ _ _ _ hi h := exec_bytes hi h
  exec_world _ _ _ _ _ hi h := exec_world (ne_syscall hi) h
  exec_trap _ _ _ _ _ hi h := exec_trap hi h

end Millipede.X64
