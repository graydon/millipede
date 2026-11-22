import Millipede.Target.X64.Exec

/-!
# The laws of the x64 ISA model

This module proves that the x64 encoder and decoder agree and that execution respects memory
permissions and changes only what an instruction names. `decode_encode` says that decoding the
encoding of any instruction, followed by any bytes, gives back the instruction and its length.
`decode_spec` says the decoder accepts only canonical encodings, so a decoded instruction is
exactly the encoding of what was decoded, and every encoding is 1 to 15 bytes long. The byte-field
lemmas are proved bit by bit or, for the ModRM byte, by evaluating all 256 cases in the kernel.

`exec` is a function, so execution is deterministic by construction. `exec_respects` says memory
changes only by stores to writable memory and the trace only grows, provided the system-call
handler does the same. The frame lemmas say which registers, flags and memory an instruction may
change and that a straight-line instruction falls through to `rip + len`. The end of the file
states the frame law of `Isa.Laws` over the register locations `XLoc`, which cover the whole
register file.
-/

namespace Millipede.X64

/-! ## Byte fields -/

/-- A REX prefix is recognised as one. -/
@[simp] theorem isRex_rex (w r x b : Bool) : isRex (rex w r x b) = true := by
  revert w r x b; decide

/-- The REX bits are read back. -/
@[simp] theorem rexOf_rex (w r x b : Bool) : rexOf (rex w r x b) = ⟨w, r, x, b⟩ := by
  revert w r x b; decide

/-- 32-bit little-endian values are read back. -/
@[simp] theorem get32_le32 (x : UInt32) (rest : List UInt8) :
    get32 (le32 x ++ rest) = some (x, rest) := by
  simp only [le32, get32, List.cons_append, List.nil_append, Option.some.injEq, Prod.mk.injEq,
    and_true]
  apply UInt32.eq_of_toBitVec_eq
  ext i hi
  simp
  simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_umod, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, show (256#32).toNat = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  obtain h | h | h | h : i < 8 ∨ 8 ≤ i ∧ i < 16 ∨ 16 ≤ i ∧ i < 24 ∨ 24 ≤ i ∧ i < 32 := by omega
  all_goals simp (disch := omega) only [decide_eq_true, decide_eq_false, Nat.sub_add_cancel,
    Bool.true_and, Bool.false_and, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false]

/-- 64-bit little-endian values are read back. -/
@[simp] theorem get64_le64 (x : UInt64) (rest : List UInt8) :
    get64 (le64 x ++ rest) = some (x, rest) := by
  simp only [le64, get64, List.cons_append, List.nil_append, Option.some.injEq, Prod.mk.injEq,
    and_true]
  apply UInt64.eq_of_toBitVec_eq
  ext i hi
  simp
  simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_umod, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, show (256#64).toNat = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  obtain h | h | h | h | h | h | h | h : i < 8 ∨ 8 ≤ i ∧ i < 16 ∨ 16 ≤ i ∧ i < 24 ∨
    24 ≤ i ∧ i < 32 ∨ 32 ≤ i ∧ i < 40 ∨ 40 ≤ i ∧ i < 48 ∨ 48 ≤ i ∧ i < 56 ∨ 56 ≤ i ∧ i < 64 := by
    omega
  all_goals simp (disch := omega) only [decide_eq_true, decide_eq_false, Nat.sub_add_cancel,
    Bool.true_and, Bool.false_and, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false]

/-- The three fields of a ModRM byte are read back, for each of the 256 field values. -/
theorem modrm_fields : ∀ i, i < 4 → ∀ j, j < 8 → ∀ k, k < 8 →
    modrm (UInt8.ofNat i) (UInt8.ofNat j) (UInt8.ofNat k) >>> 6 = UInt8.ofNat i ∧
    (modrm (UInt8.ofNat i) (UInt8.ofNat j) (UInt8.ofNat k) >>> 3) &&& 7 = UInt8.ofNat j ∧
    modrm (UInt8.ofNat i) (UInt8.ofNat j) (UInt8.ofNat k) &&& 7 = UInt8.ofNat k := by
  decide

theorem modrm_fields' (md reg rm : UInt8) (h1 : md < 4) (h2 : reg < 8) (h3 : rm < 8) :
    modrm md reg rm >>> 6 = md ∧ (modrm md reg rm >>> 3) &&& 7 = reg ∧ modrm md reg rm &&& 7 = rm := by
  simpa using modrm_fields md.toNat (by simpa [UInt8.lt_iff_toNat_lt] using h1) reg.toNat
    (by simpa [UInt8.lt_iff_toNat_lt] using h2) rm.toNat (by simpa [UInt8.lt_iff_toNat_lt] using h3)

theorem modrm_mod (md reg rm : UInt8) (h1 : md < 4) (h2 : reg < 8) (h3 : rm < 8) :
    modrm md reg rm >>> 6 = md := (modrm_fields' md reg rm h1 h2 h3).1
theorem modrm_reg (md reg rm : UInt8) (h1 : md < 4) (h2 : reg < 8) (h3 : rm < 8) :
    (modrm md reg rm >>> 3) &&& 7 = reg := (modrm_fields' md reg rm h1 h2 h3).2.1
theorem modrm_rm (md reg rm : UInt8) (h1 : md < 4) (h2 : reg < 8) (h3 : rm < 8) :
    modrm md reg rm &&& 7 = rm := (modrm_fields' md reg rm h1 h2 h3).2.2

/-- A register operand is read back, for any 3-bit `reg` field and any `REX.X`. -/
theorem parseModRM_reg (reg : UInt8) (r : Reg) (x : Bool) (rest : List UInt8) (h : reg < 8) :
    parseModRM x (RM.reg r).hi (encModRM reg (.reg r) ++ rest) = some (reg, .reg r, rest) := by
  have := r.lo_lt
  simp [encModRM, parseModRM, RM.hi, modrm_mod, modrm_reg, modrm_rm, h, this]

/-- A memory operand, with its SIB byte and displacement, is read back, for any 3-bit `reg`
field. -/
theorem parseModRM_mem (reg : UInt8) (m : Mem) (rest : List UInt8) (h : reg < 8) :
    parseModRM (RM.mem m).xhi (RM.mem m).hi (encModRM reg (.mem m) ++ rest) =
      some (reg, .mem m, rest) := by
  rcases m with ⟨b, d⟩ | d | ⟨b, ⟨i, hi⟩, d⟩
  · have := b.lo_lt
    by_cases h4 : b.lo = 4
    · have e : Reg.ofBits b.hi 4 = b := by rw [← h4]; simp
      have e1 : ((0x24 : UInt8) >>> 3) &&& 7 = 4 := by decide
      have e2 : (0x24 : UInt8) &&& 7 = 4 := by decide
      have e3 : Reg.ofBits false 4 = .rsp := rfl
      simp [encModRM, parseModRM, sibMem, RM.hi, RM.xhi, modrm_mod, modrm_reg, modrm_rm, h, h4, e,
        e1, e2, e3]
    · simp [encModRM, parseModRM, RM.hi, modrm_mod, modrm_reg, modrm_rm, h, this, h4]
  · simp [encModRM, parseModRM, modrm_mod, modrm_reg, h]
  · have := b.lo_lt
    have := i.lo_lt
    simp [encModRM, parseModRM, sibMem, RM.hi, RM.xhi, modrm_mod, modrm_reg, modrm_rm, *]

attribute [local simp] parseModRM_reg parseModRM_mem Reg.lo_lt Alu.digit_lt Shift.digit_lt

/-- `store8` is read back: with a REX prefix exactly when the byte register, the base or the
index needs one. -/
theorem parse_store8 (m : Mem) (s : Reg) (rest : List UInt8) :
    parse (encode (.store8 m s) ++ rest) = some (.store8 m s) := by
  simp only [encode]
  split
  · simp [parse, parseBody]
  · rename_i hn
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
    obtain ⟨⟨hs, hb⟩, hx⟩ := hn
    have hsh : s.hi = false := by simp [Reg.needsRex8] at hs; exact hs.1
    have e : Reg.ofBits false s.lo = s := by rw [← hsh]; simp
    have := parseModRM_mem s.lo m rest s.lo_lt
    rw [hx, hb] at this
    have hr : isRex 0x88 = false := by decide
    simp [parse, parseBody, hr, Rex.none, this, e]

/-- `store8I` is read back: with a REX prefix exactly when the base or the index needs one. -/
theorem parse_store8I (m : Mem) (v : UInt8) (rest : List UInt8) :
    parse (encode (.store8I m v) ++ rest) = some (.store8I m v) := by
  simp only [encode]
  split
  · simp [parse, parseBody]
  · rename_i hn
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
    obtain ⟨hb, hx⟩ := hn
    have := parseModRM_mem 0 m ([v] ++ rest) (by decide)
    rw [hx, hb] at this
    have hr : isRex 0xC6 = false := by decide
    simp only [List.singleton_append] at this
    simp [parse, parseBody, hr, Rex.none, this]

/-- The lenient parser recovers every instruction from its encoding, whatever follows it.
Instructions whose opcode byte carries a register or condition are checked for each register or
condition, and the rest symbolically with `parseModRM_reg` and `parseModRM_mem` as conditional
simp lemmas. -/
theorem parse_encode (i : Instr) (rest : List UInt8) : parse (encode i ++ rest) = some i := by
  cases i
  case store8 m s => exact parse_store8 m s rest
  case store8I m v => exact parse_store8I m v rest
  case setcc c d => cases c <;> cases d <;> rfl
  case movRI d _ | push d | pop d => cases d <;> simp [encode, parse, isRex, parseBody, rex] <;> rfl
  case jcc c _ => cases c <;> simp +decide [Cond.code, encode, parse, parseBody] <;> rfl
  case aluRR op _ _ =>
    cases op <;> simp +decide [encode, encW, parse, parseBody, parseModRMReg, Alu.rr, Alu.ofRR]
  all_goals simp +decide [encode, encW, parse, parseBody, parseModRMMem, parseModRMReg]

/-! ## The codec laws -/

/-- Decoding inverts encoding, for every instruction and any trailing bytes. -/
theorem decode_encode (i : Instr) (rest : List UInt8) :
    decode (encode i ++ rest) = some (i, (encode i).length) := by
  simp [decode, parse_encode]

/-- Only canonical encodings decode, so the decoded bytes are exactly the encoding of the
decoded instruction. -/
theorem decode_spec {bs : List UInt8} {i : Instr} {n : Nat} (h : decode bs = some (i, n)) :
    n = (encode i).length ∧ bs = encode i ++ bs.drop n := by
  unfold decode at h
  split at h
  · rename_i i' _
    split at h
    · rename_i ht
      cases h
      refine ⟨rfl, ?_⟩
      conv => lhs; rw [← List.take_append_drop (encode i).length bs]
      rw [ht]
    · cases h
  · cases h

/-- A ModRM encoding, with its SIB byte and displacement, is 1 to 6 bytes long. -/
theorem encModRM_length (reg : UInt8) (rm : RM) :
    1 ≤ (encModRM reg rm).length ∧ (encModRM reg rm).length ≤ 6 := by
  rcases rm with r | (⟨b, d⟩ | d | ⟨b, i, d⟩) <;> simp [encModRM, le32]
  split <;> simp

/-- Every encoding is 1 to 15 bytes long. -/
theorem encode_length (i : Instr) : 0 < (encode i).length ∧ (encode i).length ≤ 15 := by
  cases i <;> simp [encode, encW, le32, le64] <;>
    first
    | (have := encModRM_length; grind)
    | (split <;> simp)

/-- A decoded instruction uses at least one and at most the available bytes. -/
theorem decode_length {bs : List UInt8} {i : Instr} {n : Nat} (h : decode bs = some (i, n)) :
    0 < n ∧ n ≤ bs.length := by
  obtain ⟨hn, hb⟩ := decode_spec h
  refine ⟨hn ▸ (encode_length i).1, ?_⟩
  rw [hb, List.length_append]; omega

/-! ## Memory access -/

theorem store64_frame {m m' : Memory} {a v : UInt64} (h : store64 m a v = some m') :
    Memory.Frame m m' := by
  unfold store64 at h
  split at h
  · exact Memory.writeWord_frame h
  · cases h

theorem store8_frame {m m' : Memory} {a v : UInt64} (h : store8 m a v = some m') :
    Memory.Frame m m' := by
  unfold store8 at h
  split at h
  · exact Memory.writeWord_frame h
  · cases h

/-! ## Execution -/

/-- Execution respects memory permissions and only extends the trace, given a system-call
handler that does the same. -/
theorem exec_respects (trap : State → Option State) (i : Instr) (n : Nat) (s s' : State)
    (ht : ∀ t t', trap t = some t' → t.Respects t') (h : exec trap i n s = some s') :
    s.Respects s' := by
  cases i <;> simp only [exec, State.withRegs, State.jump, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, Option.some.injEq] at h
  all_goals (repeat' split at h)
  all_goals first
    | (obtain ⟨_, hm, rfl⟩ := h; exact ⟨store64_frame hm, List.prefix_refl _⟩)
    | (obtain ⟨_, hm, rfl⟩ := h; exact ⟨store8_frame hm, List.prefix_refl _⟩)
    | (obtain ⟨_, hm, rfl⟩ := h; exact (ht _ _ hm : s.Respects _))
    | (obtain ⟨_, _, rfl⟩ := h; exact ⟨Memory.Frame.refl _, List.prefix_refl _⟩)
    | (subst h; exact ⟨Memory.Frame.refl _, List.prefix_refl _⟩)
    | (cases h <;> exact ⟨Memory.Frame.refl _, List.prefix_refl _⟩)

/-! ## Frame lemmas -/

/-- The general-purpose registers an instruction may write, apart from those `syscall` writes,
whose effect the ABI defines. -/
def Instr.writes : Instr → List Reg
  | .movRR d _ | .movRI d _ | .load d _ | .load8 d _ | .lea d _ | .imul d _ | .shiftCL _ d | .setcc _ d
  | .movzx d _ => [d]
  | .aluRR op d _ | .aluRI op d _ => if op.writes then [d] else []
  | .div _ => [.rax, .rdx]
  | .call _ | .ret | .push _ => [.rsp]
  | .pop r => [.rsp, r]
  | .store _ _ | .store8 _ _ | .storeI _ _ | .store8I _ _ | .jcc _ _ | .jmp _ | .syscall => []

/-- Whether the instruction stores to memory. -/
def Instr.stores : Instr → Bool
  | .store _ _ | .store8 _ _ | .storeI _ _ | .store8I _ _ | .call _ | .push _ => true
  | _ => false

/-- Whether the instruction may change the flags. -/
def Instr.setsFlags : Instr → Bool
  | .aluRR _ _ _ | .aluRI _ _ _ | .imul _ _ | .shiftCL _ _ => true
  | _ => false

/-- Whether the instruction transfers control other than by falling through. -/
def Instr.branches : Instr → Bool
  | .jcc _ _ | .jmp _ | .call _ | .ret => true
  | _ => false

/-- Unfolds one successful `exec` into equations about the new state. -/
local macro "exec_cases" h:ident : tactic => `(tactic| (
  simp only [exec, State.withRegs, State.jump, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, Option.some.injEq] at $h:ident
  repeat' split at $h:ident
  all_goals first
    | (obtain ⟨_, _, e⟩ := $h:ident; subst e)
    | subst $h:ident
    | cases $h:ident))

/-- An instruction other than `syscall` changes no general-purpose register outside
`i.writes`. -/
theorem exec_gpr {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i ≠ .syscall) (h : exec trap i n s = some s') :
    ∀ r, r ∉ i.writes → s'.regs.gpr r = s.regs.gpr r := by
  intro r hr
  cases i <;> exec_cases h <;> simp_all [Instr.writes, Regs.set]

/-- An instruction other than `syscall` does not touch the world. -/
theorem exec_world {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i ≠ .syscall) (h : exec trap i n s = some s') : s'.world = s.world := by
  cases i <;> exec_cases h <;> simp_all

/-- Among instructions other than `syscall`, whose effect the ABI defines, only `store`, `call`
and `push` change memory. -/
theorem exec_mem {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i ≠ .syscall) (hs : i.stores = false) (h : exec trap i n s = some s') :
    s'.mem = s.mem := by
  cases i <;> simp only [Instr.stores, Bool.true_eq_false] at hs <;> exec_cases h <;> simp_all

/-- Only the ALU operations, `imul` and the shifts change the flags. -/
theorem exec_flags {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i ≠ .syscall) (hs : i.setsFlags = false) (h : exec trap i n s = some s') :
    s'.regs.flags = s.regs.flags := by
  cases i <;> simp only [Instr.setsFlags, Bool.true_eq_false] at hs <;> exec_cases h <;> simp_all

/-- Every instruction that does not branch, `syscall` included, continues at `rip + len`. -/
theorem exec_rip {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hb : i.branches = false) (h : exec trap i n s = some s') :
    s'.regs.rip = s.regs.rip + UInt64.ofNat n := by
  cases i <;> simp only [Instr.branches, Bool.true_eq_false] at hb <;> exec_cases h <;> simp_all

end Millipede.X64

/-! ## The frame law of `Isa.Laws`

The locations `XLoc` of the register file are the 16 general registers, `rip` and the flags,
read as the word `Flags.bits`, and `regs_ext` shows they cover the whole register file.
`Instr.regWrites` names the locations an instruction writes, which are always `rip`, the registers
of `Instr.writes` and the flags if it sets them. `Instr.memWrites` names the byte ranges it stores
to, computed from the registers before it. `exec_regs`, `exec_bytes`, `exec_world` and
`exec_trap` together are the frame law. -/

namespace Millipede.X64

/-- The flags as a word: `cf + 2 zf + 4 sf + 8 of`. -/
def Flags.bits (f : Flags) : UInt64 :=
  (if f.cf then 1 else 0) + (if f.zf then 2 else 0) + (if f.sf then 4 else 0) +
    (if f.of then 8 else 0)

theorem Flags.bits_inj {f g : Flags} (h : f.bits = g.bits) : f = g := by
  obtain ⟨a, b, c, d⟩ := f
  obtain ⟨a', b', c', d'⟩ := g
  revert h
  cases a <;> cases b <;> cases c <;> cases d <;> cases a' <;> cases b' <;> cases c' <;>
    cases d' <;> decide

/-- The locations of the x64 register file. -/
inductive XLoc where
  | gpr (r : Reg)
  | rip
  | flags
deriving DecidableEq, Repr

/-- Reads a location. -/
def XLoc.get (r : Regs) : XLoc → UInt64
  | .gpr x => r.gpr x
  | .rip => r.rip
  | .flags => r.flags.bits

/-- Two register files that agree at every location are equal. -/
theorem regs_ext {r r' : Regs} (h : ∀ l, XLoc.get r l = XLoc.get r' l) : r = r' := by
  obtain ⟨g, p, f⟩ := r
  obtain ⟨g', p', f'⟩ := r'
  have hg : g = g' := funext fun x => h (.gpr x)
  have hp : p = p' := h .rip
  have hf : f = f' := Flags.bits_inj (h .flags)
  subst hg hp hf; rfl

/-- The locations an instruction may write, which are `rip`, its `writes`, and the flags if it
sets them. -/
def Instr.regWrites (i : Instr) : List XLoc :=
  .rip :: (i.writes.map XLoc.gpr ++ if i.setsFlags then [XLoc.flags] else [])

/-- The memory ranges an instruction of length `n` may store to, given the registers before it. -/
def Instr.memWrites (i : Instr) (n : Nat) (r : Regs) : List (UInt64 × Nat) :=
  match i with
  | .store m _ => [(m.addr r (r.rip + UInt64.ofNat n), 8)]
  | .store8 m _ => [(m.addr r (r.rip + UInt64.ofNat n), 1)]
  | .storeI m _ => [(m.addr r (r.rip + UInt64.ofNat n), 8)]
  | .store8I m _ => [(m.addr r (r.rip + UInt64.ofNat n), 1)]
  | .call _ | .push _ => [(r.gpr .rsp - 8, 8)]
  | _ => []

/-- Whether the instruction is the system-call instruction. -/
def Instr.isTrap : Instr → Bool
  | .syscall => true
  | _ => false

theorem store64_bytes {m m' : Memory} {a v : UInt64} (h : store64 m a v = some m') {b : UInt64}
    (hb : ¬ Memory.InRange a 8 b) : m'.bytes b = m.bytes b := by
  unfold store64 at h
  split at h
  · exact Memory.writeWord_outside h hb
  · cases h

theorem store8_bytes {m m' : Memory} {a v : UInt64} (h : store8 m a v = some m') {b : UInt64}
    (hb : ¬ Memory.InRange a 1 b) : m'.bytes b = m.bytes b := by
  unfold store8 at h
  split at h
  · exact Memory.writeWord_outside h hb
  · cases h

theorem ne_syscall {i : Instr} (h : i.isTrap = false) : i ≠ .syscall := by
  rintro rfl; cases h

/-- An instruction other than the trap changes no location outside `Instr.regWrites`. -/
theorem exec_regs {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i.isTrap = false) (h : exec trap i n s = some s') :
    ∀ l, l ∉ i.regWrites → XLoc.get s'.regs l = XLoc.get s.regs l := by
  intro l hl
  cases l with
  | gpr r =>
    exact exec_gpr (ne_syscall hi) h r fun hr => hl (by simp [Instr.regWrites, hr])
  | rip => exact absurd (by simp [Instr.regWrites]) hl
  | flags =>
    cases hf : i.setsFlags
    · show s'.regs.flags.bits = s.regs.flags.bits
      rw [exec_flags (ne_syscall hi) hf h]
    · exact absurd (by simp [Instr.regWrites, hf]) hl

/-- An instruction other than the trap changes only the bytes in `memWrites`. -/
theorem exec_bytes {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i.isTrap = false) (h : exec trap i n s = some s') (a : UInt64)
    (ha : ∀ w ∈ i.memWrites n s.regs, ¬ Memory.InRange w.1 w.2 a) :
    s'.mem.bytes a = s.mem.bytes a := by
  cases hst : i.stores
  · rw [exec_mem (ne_syscall hi) hst h]
  · cases i <;> simp only [Instr.stores, Bool.false_eq_true] at hst <;>
      simp only [Instr.memWrites, List.mem_singleton, forall_eq] at ha <;>
      simp only [exec, Option.map_eq_some_iff] at h <;>
      obtain ⟨_, hm, rfl⟩ := h <;>
      first | exact store64_bytes hm ha | exact store8_bytes hm ha

/-- The system call's memory and world are the handler's. -/
theorem exec_trap {trap : State → Option State} {i : Instr} {n : Nat} {s s' : State}
    (hi : i.isTrap = true) (h : exec trap i n s = some s') :
    ∃ t, trap s = some t ∧ s'.mem = t.mem ∧ s'.world = t.world := by
  cases i <;> simp only [Instr.isTrap, Bool.false_eq_true] at hi
  simp only [exec, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t, ht, rfl, rfl⟩

end Millipede.X64
