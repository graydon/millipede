import Millipede.Target.A64.Encode
import Std.Tactic.BVDecide

/-!
# The arm64 decoder and the codec laws

`decode bs` reads the first four bytes of `bs` as a little-endian word and decodes it in two
stages. First `parse` dispatches on the opcode bits, with one fixed mask and pattern per
instruction class, and reads the operand fields. The parser is lenient, so it ignores bits that
the canonical form fixes but that do not select the class, such as the shift amount of a
shifted-register operand or the `N` bit of `ubfm`. Then `decodeWord` re-encodes the parsed
instruction and accepts it only if it is encodable and the word is exactly its encoding.

Only canonical encodings of the subset therefore decode, and every other word decodes to `none`,
where the machine is stuck. The laws say that decoding inverts encoding for every encodable
instruction and that a decoded instruction is four bytes long and is the encoding of an encodable
instruction. The field lemmas are proved with `bv_decide`.
-/

namespace Millipede.A64

/-- Whether `w` matches the fixed bits `p` under the mask `m`. -/
def Matches (w m p : BitVec 32) : Bool := w &&& m == p

/-- Bits `[pos, pos + n)` of a word. -/
abbrev get (w : BitVec 32) (pos n : Nat) : BitVec n := w.extractLsb' pos n

/-- A load when bit 22 is set and a store otherwise, of the size in bits 30 and 31. -/
def ldst (w : BitVec 32) (a : Addr) : Instr :=
  if w.getLsbD 22 = true then .ldr (Size.ofBits (get w 30 2)) (get w 0 5) a
  else .str (Size.ofBits (get w 30 2)) (get w 0 5) a

/-- The lenient parser, which reads an instruction of the class that the opcode bits select. -/
def parse (w : BitVec 32) : Option Instr :=
  let sf := w.getLsbD 31
  let d := get w 0 5
  let n := get w 5 5
  let m := get w 16 5
  if Matches w 0x1F800000 0x12800000 then
    some (.mov (MovOp.ofBits (get w 29 2)) sf d (get w 5 16) (get w 21 2))
  else if Matches w 0x1F800000 0x11000000 then
    some (.addImm sf (w.getLsbD 30) (w.getLsbD 29) d n (get w 10 12) (w.getLsbD 22))
  else if Matches w 0x1F200000 0x0B000000 then
    some (.addReg sf (w.getLsbD 30) (w.getLsbD 29) d n m)
  else if Matches w 0x1F000000 0x0A000000 then
    some (.logReg (LogOp.ofBits (get w 29 2)) sf d n m)
  else if Matches w 0x7FE00000 0x1B000000 then
    some (.madd sf (w.getLsbD 15) d n m (get w 10 5))
  else if Matches w 0x7FE0F800 0x1AC00800 then
    some (.div sf (w.getLsbD 10) d n m)
  else if Matches w 0x7FE0F000 0x1AC02000 then
    some (.shiftV (ShiftOp.ofBits (get w 10 2)) sf d n m)
  else if Matches w 0x1F800000 0x13000000 then
    some (.bfm (!w.getLsbD 30) sf d n (get w 16 6) (get w 10 6))
  else if Matches w 0x3FE00000 0x1A800000 then
    some (.csel (CselOp.ofBits (get w 30 1 ++ get w 10 1)) sf d n m (Cond.ofBits (get w 12 4)))
  else if Matches w 0x3F000000 0x39000000 then some (ldst w (.uimm n (get w 10 12)))
  else if Matches w 0x3F200C00 0x38000000 then some (ldst w (.simm n (get w 12 9)))
  else if Matches w 0x3F200C00 0x38200800 then some (ldst w (.reg n m))
  else if Matches w 0x1F000000 0x10000000 then
    some (.adr sf d (get w 5 19 ++ get w 29 2))
  else if Matches w 0x7C000000 0x14000000 then
    some (.b sf (get w 0 26))
  else if Matches w 0xFF000010 0x54000000 then
    some (.bcond (Cond.ofBits (get w 0 4)) (get w 5 19))
  else if Matches w 0x7E000000 0x34000000 then
    some (.cbz sf (w.getLsbD 24) d (get w 5 19))
  else if Matches w 0xFFFFFC1F 0xD65F0000 then some (.ret n)
  else if Matches w 0xFFE0001F 0xD4000001 then some (.svc (get w 5 16))
  else none

/-- Decode a word, which is accepted only if it is the canonical encoding of an encodable
instruction. -/
def decodeWord (w : BitVec 32) : Option Instr :=
  (parse w).bind fun i => if i.valid && encode i == w then some i else none

/-- The little-endian word of four bytes. -/
def word4 (b0 b1 b2 b3 : UInt8) : BitVec 32 := BitVec.ofNat 32 (natOfBytes [b0, b1, b2, b3])

/-- The decoder, which returns the instruction in the first four bytes and its length 4. -/
def decode : List UInt8 → Option (Instr × Nat)
  | b0 :: b1 :: b2 :: b3 :: _ => (decodeWord (word4 b0 b1 b2 b3)).map (·, 4)
  | _ => none

/-! ## The codec laws -/

theorem ite_skip {α : Type} {c : Bool} {a b x : α} (hc : c = false) (h : b = x) :
    (if c = true then a else b) = x := by simp [hc, h]
theorem ite_take {α : Type} {c : Bool} {a b x : α} (hc : c = true) (h : a = x) :
    (if c = true then a else b) = x := by simp [hc, h]

/-- Step through the dispatch of `parse`, refuting the classes the word does not belong to and
entering its own, then compare the fields by `bv_decide`. -/
scoped macro "a64_parse_tac" : tactic => `(tactic| (
  simp only [parse, ldst];
  repeat (first
    | refine ite_skip (by simp only [Matches, encode, Addr.enc, bit, fld]; bv_decide) ?_
    | refine ite_take (by simp only [Matches, encode, Addr.enc, bit, fld]; bv_decide) ?_
    | rw [Option.some.injEq]);
  simp only [encode, Addr.enc, bit, fld, get, Option.some.injEq, Instr.mov.injEq,
    Instr.addImm.injEq, Instr.addReg.injEq, Instr.logReg.injEq, Instr.madd.injEq,
    Instr.div.injEq, Instr.shiftV.injEq, Instr.bfm.injEq, Instr.csel.injEq, Instr.ldr.injEq,
    Instr.str.injEq, Instr.adr.injEq, Instr.b.injEq, Instr.bcond.injEq, Instr.cbz.injEq,
    Instr.ret.injEq, Instr.svc.injEq, Addr.uimm.injEq,
    Addr.simm.injEq, Addr.reg.injEq, LogOp.ofBits_eq_iff, ShiftOp.ofBits_eq_iff,
    CselOp.ofBits_eq_iff, Size.ofBits_eq_iff, Cond.ofBits_eq_iff, MovOp.ofBits_eq_iff, reduceCtorEq, and_false, or_false];
  all_goals (try and_intros);
  all_goals bv_decide))

/-- The parser recovers every instruction from its encoding. -/
theorem parse_encode (i : Instr) : parse (encode i) = some i := by
  cases i
  case mov op _ _ _ _ => cases op <;> a64_parse_tac
  case ldr a | str a => cases a <;> a64_parse_tac
  all_goals a64_parse_tac

/-- Decoding a word inverts encoding, for every encodable instruction. -/
theorem decodeWord_encode {i : Instr} (h : i.valid = true) : decodeWord (encode i) = some i := by
  simp [decodeWord, parse_encode, h]

/-- The four bytes of an instruction read back as its word. -/
theorem word4_bytes (i : Instr) :
    ∃ b0 b1 b2 b3, bytes i = [b0, b1, b2, b3] ∧ word4 b0 b1 b2 b3 = encode i := by
  refine ⟨(bytes i)[0]!, (bytes i)[1]!, (bytes i)[2]!, (bytes i)[3]!, ?_, ?_⟩
  · simp [bytes, natBytes]
  · have e : [(bytes i)[0]!, (bytes i)[1]!, (bytes i)[2]!, (bytes i)[3]!] = bytes i := by
      simp [bytes, natBytes]
    rw [word4, e, bytes, natOfBytes_natBytes]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (encode i).isLt]

/-- Decoding inverts encoding, for every encodable instruction and any trailing bytes. -/
theorem decode_encode {i : Instr} (h : i.valid = true) (rest : List UInt8) :
    decode (bytes i ++ rest) = some (i, 4) := by
  obtain ⟨b0, b1, b2, b3, hb, hw⟩ := word4_bytes i
  rw [hb]; simp [decode, hw, decodeWord_encode h]

/-- Only canonical encodings decode, so a decoded instruction is encodable, four bytes long and
its encoding begins the bytes it was read from. -/
theorem decode_spec {bs : List UInt8} {i : Instr} {n : Nat} (h : decode bs = some (i, n)) :
    n = 4 ∧ i.valid = true ∧ bs = bytes i ++ bs.drop 4 := by
  match bs, h with
  | b0 :: b1 :: b2 :: b3 :: rest, h =>
    simp only [decode, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨i', hd, rfl, rfl⟩ := h
    simp only [decodeWord, Option.bind_eq_some_iff] at hd
    obtain ⟨_, _, hc⟩ := hd
    split at hc
    · rename_i hv
      cases hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hv
      refine ⟨rfl, hv.1, ?_⟩
      have : bytes i' = [b0, b1, b2, b3] := by
        rw [bytes, hv.2, word4, BitVec.toNat_ofNat]
        have := natBytes_natOfBytes [b0, b1, b2, b3]
        simp only [List.length_cons, List.length_nil] at this
        rw [Nat.mod_eq_of_lt (by have := natOfBytes_lt [b0, b1, b2, b3]; simpa using this)]
        exact this
      simp [this]
    · cases hc

/-- A decoded instruction uses four of the available bytes. -/
theorem decode_length {bs : List UInt8} {i : Instr} {n : Nat} (h : decode bs = some (i, n)) :
    0 < n ∧ n ≤ bs.length := by
  obtain ⟨rfl, -, hb⟩ := decode_spec h
  rw [hb, List.length_append, bytes_length]; omega

end Millipede.A64
