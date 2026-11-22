import Millipede.Target.A64.Laws
import Millipede.Target.Isa

/-!
# arm64 as an ISA

`isa` packages the arm64 model as an instance of the shared ISA interface. Its instructions are
`Instr`, its register file is `Regs` with `sp` as register 31, and every instruction is 4 bytes
long. It encodes an encodable instruction as `bytes i` and refuses the others, decodes
with `decode`, executes with `exec`, and gives the frame law over the register locations `ALoc`.
The theorem `laws` proves the laws of the interface for this model.
-/

namespace Millipede.A64

/-- The arm64 ISA model. -/
def isa : Isa where
  Instr := Instr
  Regs := Regs
  pc r := r.pc
  sp r := r.x 31
  maxLen := 4
  encode i := if i.valid then some (bytes i) else none
  decode := decode
  exec := exec
  Loc := ALoc
  get := ALoc.get
  regWrites := Instr.regWrites
  memWrites := Instr.memWrites
  isTrap := Instr.isTrap

theorem isa_encode {i : Instr} {bs : List UInt8} (h : isa.encode i = some bs) :
    i.valid = true ∧ bs = bytes i := by
  simp only [isa] at h
  split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

/-- The arm64 model satisfies the laws of the ISA interface. -/
theorem laws : isa.Laws where
  decode_encode i bs rest h := by
    obtain ⟨hv, rfl⟩ := isa_encode h
    exact (bytes_length (i : Instr)) ▸ decode_encode hv rest
  encode_length i bs h := by
    obtain ⟨-, rfl⟩ := isa_encode h
    exact (bytes_length (i : Instr)) ▸ ⟨by decide, by decide⟩
  decode_length _ _ _ h := decode_length h
  exec_respects trap i n s s' ht h := exec_respects trap i n s s' ht h
  get_ext _ _ h := regs_ext h
  exec_regs _ _ n _ _ hi h := exec_regs (n := n) hi h
  exec_bytes _ _ n _ _ hi h := exec_bytes (n := n) hi h
  exec_world _ _ n _ _ hi h := exec_world (n := n) hi h
  exec_trap _ _ n _ _ hi h := exec_trap (n := n) hi h

end Millipede.A64
