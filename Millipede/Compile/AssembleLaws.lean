import Millipede.Compile.Assemble

/-!
# The assembler law

An architecture's assembler `Asm.Assembler A` is correct when it satisfies `Assembler.Laws`, five
facts about one instruction:

- `isa`, the ISA's own laws, by which decoding an encoding gives the instruction back;
- `size`, that the bytes `asmSI` produces have the size `A.size` that the layout assumed;
- `sec`, that its relocations patch `.text`;
- `resolve_size`, that a resolved instruction encodes to that size as well;
- `spec`, that once its relocations are applied, for any placement `base` of `.text` and symbol
  assignment `σ` that agree with the local labels the assembler was given, the instruction's bytes
  are the encoding of the instruction resolved at its address.

From these laws `assemble_text` follows for every program. If `assemble asm P = .ok obj`, the
`.text` section is placed at `base` without wrapping around the address space, and the relocations
apply, then for every function `f` of `P` the patched section contains, at `f`'s offset, exactly
`f.bytes σ (base + offset)`, the encoding of `f`'s code resolved at its address. This is what
`Asm.Prog.Loaded` asks of a loaded program. Decoding the patched section at any instruction of
`f`, and in particular at any local label, therefore yields that instruction, resolved.

See doc/design/compiler.md.
-/

namespace Millipede.Asm

/-! ## Relocations and bytes -/

theorem applyRelocs_append (σ : String → Option UInt64) (base : UInt64) (sec : Nat) :
    ∀ (r₁ r₂ : List Reloc) (bs : List UInt8),
      applyRelocs σ base sec (r₁ ++ r₂) bs =
        (applyRelocs σ base sec r₁ bs).bind (applyRelocs σ base sec r₂)
  | [], _, _ => rfl
  | r :: r₁, r₂, bs => by
    simp only [List.cons_append, applyRelocs]
    split
    · split
      · rfl
      · split
        · rfl
        · exact applyRelocs_append σ base sec r₁ r₂ _
    · exact applyRelocs_append σ base sec r₁ r₂ _

/-- Relocations applied in two batches. -/
theorem applyRelocs_append_some {σ : String → Option UInt64} {base : UInt64} {sec : Nat}
    {r₁ r₂ : List Reloc} {bs X : List UInt8}
    (h : applyRelocs σ base sec (r₁ ++ r₂) bs = some X) :
    ∃ Y, applyRelocs σ base sec r₁ bs = some Y ∧ applyRelocs σ base sec r₂ Y = some X := by
  rw [applyRelocs_append] at h
  cases h₁ : applyRelocs σ base sec r₁ bs <;> simp_all

/-- Relocations that patch other sections leave a section unchanged. -/
theorem applyRelocs_other (σ : String → Option UInt64) (base : UInt64) (sec : Nat) :
    ∀ (rs : List Reloc) (bs : List UInt8), (∀ r ∈ rs, r.sec ≠ sec) →
      applyRelocs σ base sec rs bs = some bs
  | [], _, _ => rfl
  | r :: rs, bs, h => by
    simp only [applyRelocs, h r List.mem_cons_self, ↓reduceIte]
    exact applyRelocs_other σ base sec rs bs fun r' hr => h r' (List.mem_cons_of_mem _ hr)

theorem toNat_add_ofNat {b : UInt64} {n : Nat} (h : b.toNat + n < 2 ^ 64) :
    (b + UInt64.ofNat n).toNat = b.toNat + n := by
  simp [UInt64.toNat_add]; omega

/-! ## Resolution and encoding -/

theorem resolveAt_cons_some {A : Arch} {ρ : Ref → Option UInt64}
    {a : UInt64} {i : A.SInstr} {is : List A.SInstr} {i' : A.isa.Instr}
    {is' : List A.isa.Instr} (h₁ : A.resolve ρ a i = some i')
    (h₂ : resolveAt A ρ (a + UInt64.ofNat (A.size i)) is = some is') :
    resolveAt A ρ a (i :: is) = some (i' :: is') := by
  simp only [resolveAt, h₁, h₂]

theorem resolveAt_cons_inv {A : Arch} {ρ : Ref → Option UInt64}
    {a : UInt64} {i : A.SInstr} {is : List A.SInstr} {ins : List A.isa.Instr}
    (h : resolveAt A ρ a (i :: is) = some ins) :
    ∃ i' is', A.resolve ρ a i = some i' ∧
      resolveAt A ρ (a + UInt64.ofNat (A.size i)) is = some is' ∧ ins = i' :: is' := by
  simp only [resolveAt] at h
  split at h
  · rename_i i' is' h₁ h₂
    cases h
    exact ⟨i', is', h₁, h₂, rfl⟩
  · cases h

theorem encodeAll_cons_inv {isa : Isa} {i : isa.Instr} {is : List isa.Instr} {bs : List UInt8}
    (h : encodeAll isa (i :: is) = some bs) :
    ∃ e es, isa.encode i = some e ∧ encodeAll isa is = some es ∧ bs = e ++ es := by
  simp only [encodeAll] at h
  split at h
  · cases h; exact ⟨_, _, ‹_›, ‹_›, rfl⟩
  · cases h

theorem encodeAll_cons {isa : Isa} {i : isa.Instr} {is : List isa.Instr} {e es : List UInt8}
    (h₁ : isa.encode i = some e) (h₂ : encodeAll isa is = some es) :
    encodeAll isa (i :: is) = some (e ++ es) := by
  simp only [encodeAll, h₁, h₂]

/-! ## Layout lemmas -/

section
variable {A : Arch}

theorem seqSize_append : ∀ (a b : List A.SInstr), seqSize A (a ++ b) = seqSize A a + seqSize A b
  | [], _ => by simp [seqSize]
  | i :: a, b => by simp only [List.cons_append, seqSize, seqSize_append a b]; omega

theorem blocksOff_le : ∀ (bs : List (List A.SInstr)) (l : Nat),
    blocksOff A bs l ≤ seqSize A bs.flatten
  | _, 0 => by simp [blocksOff]
  | [], _ + 1 => by simp [blocksOff]
  | b :: bs, l + 1 => by
    simp only [blocksOff, List.flatten_cons, seqSize_append]
    have := blocksOff_le bs l; omega

theorem labelOff_le (f : Fn A) (l : Nat) : f.labelOff l ≤ seqSize A f.code := by
  simp only [Fn.labelOff, Fn.code, seqSize_append]
  have := blocksOff_le f.blocks l; omega

/-- A label's offset is the size of the code before it. -/
theorem blocksOff_eq : ∀ (bs : List (List A.SInstr)) (l : Nat), l ≤ bs.length →
    blocksOff A bs l = seqSize A (bs.take l).flatten
  | _, 0, _ => by simp [blocksOff, seqSize]
  | [], _ + 1, h => by simp at h
  | b :: bs, l + 1, h => by
    simp only [blocksOff, List.take_succ_cons, List.flatten_cons, seqSize_append]
    rw [blocksOff_eq bs l (by simp at h; omega)]

theorem seqSize_take_append : ∀ (a b : List A.SInstr) (k : Nat),
    seqSize A ((a ++ b).take (a.length + k)) = seqSize A a + seqSize A (b.take k)
  | [], b, k => by simp [seqSize]
  | i :: a, b, k => by
    simp only [List.cons_append, List.length_cons, Nat.add_right_comm _ 1 k,
      List.take_succ_cons, seqSize, seqSize_take_append a b k]; omega

end

/-! ## The laws of an assembler -/

section
variable (σ : String → Option UInt64) (base : UInt64) (N : Nat)
  (ρ : Ref → Option UInt64) (lab : Nat → Option Nat)

/-- The facts that the assembler's resolution of local labels shares with the Asm resolution.
Labels that the assembler knows at section offset `t` resolve to `base + t`, symbols resolve by
`σ`, and the section of `N` bytes from `base` does not wrap around the address space. -/
structure Agree : Prop where
  sym : ∀ s, ρ (.sym s) = σ s
  label : ∀ l t, lab l = some t → ρ (.label l) = some (base + UInt64.ofNat t) ∧ t ≤ N
  wrap : base.toNat + N < 2 ^ 64
end

/-- The laws of an architecture's assembler, which the module documentation describes. -/
structure Assembler.Laws {A : Arch} (asm : Assembler A) : Prop where
  isa : A.isa.Laws
  size : ∀ lab off si bs rs, asm.asmSI lab off si = .ok (bs, rs) → bs.length = A.size si
  sec : ∀ lab off si bs rs, asm.asmSI lab off si = .ok (bs, rs) → ∀ r ∈ rs, r.sec = textSec
  resolve_size : ∀ ρ a si i e, A.resolve ρ a si = some i → A.isa.encode i = some e →
    e.length = A.size si
  spec : ∀ {σ base N ρ lab}, Agree σ base N ρ lab → ∀ {off si bs rs},
    asm.asmSI lab off si = .ok (bs, rs) → ∀ (pre post : List UInt8) {X : List UInt8},
    pre.length = off → off + A.size si ≤ N →
    applyRelocs σ base textSec rs (pre ++ bs ++ post) = some X →
    ∃ i e, A.resolve ρ (base + UInt64.ofNat off) si = some i ∧ A.isa.encode i = some e ∧
      X = pre ++ e ++ post

variable {A : Arch} {asm : Assembler A}

/-! ## Sequences and functions -/

/-- Inversion for `asmSeq` on a non-empty sequence. -/
theorem asmSeq_cons_inv {lab : Nat → Option Nat} {off : Nat} {i : A.SInstr} {is : List A.SInstr}
    {bs : List UInt8} {rs : List Reloc} (h : asmSeq asm lab off (i :: is) = .ok (bs, rs)) :
    ∃ b₁ r₁ bs' r₂, asm.asmSI lab off i = .ok (b₁, r₁) ∧
      asmSeq asm lab (off + A.size i) is = .ok (bs', r₂) ∧ bs = b₁ ++ bs' ∧ rs = r₁ ++ r₂ := by
  simp only [asmSeq, bind, Except.bind] at h
  split at h
  · cases h
  split at h
  · cases h
  cases h; exact ⟨_, _, _, _, ‹_›, ‹_›, rfl, rfl⟩

/-- Inversion for `asmFns` on a non-empty list. -/
theorem asmFns_cons_inv {off : Nat} {f : Fn A} {fs : List (Fn A)}
    {bs : List UInt8} {rs : List Reloc} {ss : List Symbol}
    (h : asmFns asm off (f :: fs) = .ok (bs, rs, ss)) :
    ∃ bf rf bs' rs' ss', asmSeq asm (fnLabels f off) off f.code = .ok (bf, rf) ∧
      asmFns asm (off + bf.length) fs = .ok (bs', rs', ss') ∧ bs = bf ++ bs' ∧ rs = rf ++ rs' ∧
      ss = ⟨f.name, textSec, off, true⟩ :: ss' := by
  simp only [asmFns, bind, Except.bind] at h
  split at h
  · cases h
  split at h
  · cases h
  cases h; exact ⟨_, _, _, _, _, ‹_›, ‹_›, rfl, rfl, rfl⟩

theorem asmSeq_length (hl : asm.Laws) {lab : Nat → Option Nat} :
    ∀ (is : List A.SInstr) (off : Nat) (bs : List UInt8) (rs : List Reloc),
      asmSeq asm lab off is = .ok (bs, rs) → bs.length = seqSize A is
  | [], _, bs, rs, h => by cases h; rfl
  | i :: is, off, bs, rs, h => by
    obtain ⟨b₁, r₁, bs', r₂, hp, hq, rfl, rfl⟩ := asmSeq_cons_inv h
    simp only [List.length_append, hl.size _ _ _ _ _ hp, asmSeq_length hl is _ _ _ hq, seqSize]

theorem asmSeq_relocs (hl : asm.Laws) {lab : Nat → Option Nat} : ∀ (is : List A.SInstr)
    (off : Nat) (bs : List UInt8) (rs : List Reloc), asmSeq asm lab off is = .ok (bs, rs) →
    ∀ r ∈ rs, r.sec = textSec
  | [], _, _, _, h => by cases h; simp
  | i :: is, off, bs, rs, h => by
    obtain ⟨b₁, r₁, bs', r₂, hp, hq, rfl, rfl⟩ := asmSeq_cons_inv h
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hl.sec _ _ _ _ _ hp r hr
    · exact asmSeq_relocs hl is _ _ _ hq r hr

theorem asmFns_relocs (hl : asm.Laws) : ∀ (fs : List (Fn A)) (off : Nat) (bs : List UInt8)
    (rs : List Reloc) (ss : List Symbol), asmFns asm off fs = .ok (bs, rs, ss) →
    ∀ r ∈ rs, r.sec = textSec
  | [], _, _, _, _, h => by cases h; simp
  | f :: fs, off, bs, rs, ss, h => by
    obtain ⟨bf, rf, bs', rs', ss', hp, hq, rfl, rfl, rfl⟩ := asmFns_cons_inv h
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact asmSeq_relocs hl _ _ _ _ hp r hr
    · exact asmFns_relocs hl fs _ _ _ _ hq r hr

/-- After its relocations, the bytes of a sequence are its resolved code, encoded. -/
theorem asmSeq_spec (hl : asm.Laws) {σ : String → Option UInt64} {base : UInt64} {N : Nat}
    {ρ : Ref → Option UInt64} {lab : Nat → Option Nat} (hA : Agree σ base N ρ lab) :
    ∀ (is : List A.SInstr) (off : Nat) (bs : List UInt8) (rs : List Reloc),
      asmSeq asm lab off is = .ok (bs, rs) → ∀ (pre post : List UInt8) (X : List UInt8),
      pre.length = off → off + bs.length ≤ N →
      applyRelocs σ base textSec rs (pre ++ bs ++ post) = some X →
      ∃ ins code, resolveAt A ρ (base + UInt64.ofNat off) is = some ins ∧
        encodeAll A.isa ins = some code ∧ X = pre ++ code ++ post
  | [], off, bs, rs, h, pre, post, X, _, _, hX => by
    cases h
    simp only [applyRelocs, List.append_nil, Option.some.injEq] at hX
    exact ⟨[], [], rfl, rfl, by rw [← hX]; simp⟩
  | i :: is, off, bs, rs, h, pre, post, X, hpre, hN, hX => by
    obtain ⟨b₁, r₁, bs', r₂, hp, hq, rfl, rfl⟩ := asmSeq_cons_inv h
    have hsz := hl.size _ _ _ _ _ hp
    simp only [List.length_append, hsz] at hN
    rw [show pre ++ (b₁ ++ bs') ++ post = pre ++ b₁ ++ (bs' ++ post) by simp] at hX
    obtain ⟨Y, h₁, hX⟩ := applyRelocs_append_some hX
    obtain ⟨i', e, hi', he, rfl⟩ := hl.spec hA hp pre (bs' ++ post) hpre (by omega) h₁
    have hlen : (pre ++ e).length = off + A.size i := by
      simp only [List.length_append, hpre, hl.resolve_size _ _ _ _ _ hi' he]
    obtain ⟨ins', code', hins', hc', hX'⟩ := asmSeq_spec hl hA is _ bs' r₂ hq (pre ++ e) post X
      hlen (by omega) (by simpa using hX)
    refine ⟨i' :: ins', e ++ code', ?_, encodeAll_cons he hc', by rw [hX']; simp⟩
    have ha : base + UInt64.ofNat off + UInt64.ofNat (A.size i) =
        base + UInt64.ofNat (off + A.size i) := by
      rw [UInt64.ofNat_add, UInt64.add_assoc]
    exact resolveAt_cons_some hi' (by rw [ha]; exact hins')

/-- Resolved code has the layout's size, instruction by instruction. -/
theorem resolveAt_size (hl : asm.Laws) {ρ : Ref → Option UInt64} :
    ∀ (is : List A.SInstr) (a : UInt64) (ins : List A.isa.Instr) (code : List UInt8),
      resolveAt A ρ a is = some ins → encodeAll A.isa ins = some code →
      code.length = seqSize A is ∧ ins.length = is.length
  | [], _, ins, code, h, hc => by cases h; cases hc; exact ⟨rfl, rfl⟩
  | i :: is, a, ins, code, h, hc => by
    obtain ⟨i', is', h₁, h₂, rfl⟩ := resolveAt_cons_inv h
    obtain ⟨e, es, he, hes, rfl⟩ := encodeAll_cons_inv hc
    have := resolveAt_size hl is _ is' es h₂ hes
    simp only [List.length_append, List.length_cons, seqSize, hl.resolve_size _ _ _ _ _ h₁ he,
      this.1, this.2, and_self]

/-- The code of the first `k` resolved instructions has the size of the first `k` symbolic
ones, and instruction `k` follows it. -/
theorem resolveAt_split (hl : asm.Laws) {ρ : Ref → Option UInt64} :
    ∀ (is : List A.SInstr) (a : UInt64) (ins : List A.isa.Instr) (code : List UInt8),
      resolveAt A ρ a is = some ins → encodeAll A.isa ins = some code →
      ∀ k (hk : k < ins.length), ∃ pre e post, A.isa.encode ins[k] = some e ∧
        code = pre ++ e ++ post ∧ pre.length = seqSize A (is.take k)
  | [], _, ins, code, h, _, k, hk => by cases h; simp at hk
  | i :: is, a, ins, code, h, hc, k, hk => by
    obtain ⟨i', is', h₁, h₂, rfl⟩ := resolveAt_cons_inv h
    obtain ⟨e, es, he, hes, rfl⟩ := encodeAll_cons_inv hc
    cases k with
    | zero => exact ⟨[], e, es, he, rfl, by simp [seqSize]⟩
    | succ k =>
      obtain ⟨pre, e', post, he', rfl, hpre⟩ :=
        resolveAt_split hl is _ is' es h₂ hes k (by simp at hk; omega)
      refine ⟨e ++ pre, e', post, he', by simp, ?_⟩
      simp only [List.length_append, hpre, List.take_succ_cons, seqSize,
        hl.resolve_size _ _ _ _ _ h₁ he]

/-- After the relocations, each function's bytes are its resolved code. -/
theorem asmFns_spec (hl : asm.Laws) {σ : String → Option UInt64} {base : UInt64} {N : Nat}
    (hw : base.toNat + N < 2 ^ 64) :
    ∀ (fs : List (Fn A)) (off : Nat) (bs : List UInt8) (rs : List Reloc)
      (ss : List Symbol), asmFns asm off fs = .ok (bs, rs, ss) →
      ∀ (pre post X : List UInt8), pre.length = off → off + bs.length ≤ N →
      applyRelocs σ base textSec rs (pre ++ bs ++ post) = some X →
      (∃ C, X = pre ++ C ++ post ∧ C.length = bs.length) ∧
      ∀ f ∈ fs, ∃ o code, (⟨f.name, textSec, o, true⟩ : Symbol) ∈ ss ∧
        f.bytes σ (base + UInt64.ofNat o) = some code ∧ code <+: X.drop o
  | [], off, bs, rs, ss, h, pre, post, X, _, _, hX => by
    cases h
    simp only [applyRelocs, List.append_nil, Option.some.injEq] at hX
    exact ⟨⟨[], by simp [hX], rfl⟩, by simp⟩
  | f :: fs, off, bs, rs, ss, h, pre, post, X, hpre, hN, hX => by
    obtain ⟨bf, rf, bs', rs', ss', hp, hq, rfl, rfl, rfl⟩ := asmFns_cons_inv h
    simp only [List.length_append] at hN
    have hlenf := asmSeq_length hl _ _ _ _ hp
    have hA : Agree σ base N (f.refAddr σ (base + UInt64.ofNat off)) (fnLabels f off) := by
      refine ⟨fun _ => rfl, fun l t ht => ?_, hw⟩
      simp only [fnLabels] at ht
      split at ht
      · rename_i hl'
        cases ht
        have := labelOff_le f l
        refine ⟨?_, by omega⟩
        simp only [Fn.refAddr, hl', ↓reduceIte, UInt64.ofNat_add, UInt64.add_assoc]
      · cases ht
    rw [show pre ++ (bf ++ bs') ++ post = pre ++ bf ++ (bs' ++ post) by simp] at hX
    obtain ⟨Y, h₁, hX⟩ := applyRelocs_append_some hX
    obtain ⟨ins, code, hins, hcode, rfl⟩ :=
      asmSeq_spec hl hA _ _ _ _ hp pre (bs' ++ post) Y hpre (by omega) h₁
    have hsz := (resolveAt_size hl _ _ _ _ hins hcode).1
    obtain ⟨⟨C, hC, hCl⟩, hrest⟩ := asmFns_spec hl hw fs _ bs' rs' ss' hq
      (pre ++ code) post X (by simp [hpre, hsz, hlenf])
      (by simp [hlenf]; omega) (by simpa using hX)
    have hbytes : f.bytes σ (base + UInt64.ofNat off) = some code := by
      simp only [Fn.bytes, Fn.resolve]
      rw [hins]; exact hcode
    refine ⟨⟨code ++ C, by simp [hC], by simp [hCl, hsz, hlenf]⟩, ?_⟩
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨off, _, List.mem_cons_self, hbytes, by rw [hC, ← hpre]; simp⟩
    · obtain ⟨o, code, hs, hb, hpfx⟩ := hrest g hg
      exact ⟨o, code, List.mem_cons_of_mem _ hs, hb, hpfx⟩

/-! ## The whole object -/

/-- Inversion for `assemble`. The object is built from the assembled functions, data and bss, and
the sections fit. -/
theorem assemble_inv {P : Prog A} {obj : Obj} (h : assemble asm P = .ok obj) :
    ∃ text relocs fsyms, asmFns asm 0 P.funs = .ok (text, relocs, fsyms) ∧ text.length < 2 ^ 31 ∧
      obj = ⟨[⟨".text", .text, 16, text, 0⟩, ⟨".rodata", .rodata, 8, (asmData 0 P.data).1, 0⟩,
        ⟨".bss", .bss, 16, [], (asmBss 0 P.bss).1⟩],
        fsyms ++ (asmData 0 P.data).2 ++ (asmBss 0 P.bss).2, relocs⟩ := by
  simp only [assemble, bind, Except.bind] at h
  split at h
  · cases h
  rename_i q hq
  simp only [pure, Except.pure] at h
  split at h
  · split at h
    · cases h; exact ⟨_, _, _, hq, ‹_ ∧ _›.1, rfl⟩
    · cases h
  · cases h

/-- The assembler law. For any placement `base` of `.text` that does not wrap around the address
space and any symbol assignment `σ`, once the relocations are applied, the bytes at each
function's symbol are exactly that function's code resolved at that address. -/
theorem assemble_text (hl : asm.Laws) {P : Prog A} {obj : Obj} (h : assemble asm P = .ok obj) :
    ∃ text, obj.sections[textSec]? = some ⟨".text", .text, 16, text, 0⟩ ∧ text.length < 2 ^ 31 ∧
      ∀ (σ : String → Option UInt64) (base : UInt64) (X : List UInt8),
        base.toNat + text.length < 2 ^ 64 → applyRelocs σ base textSec obj.relocs text = some X →
        X.length = text.length ∧
        ∀ f ∈ P.funs, ∃ o code, (⟨f.name, textSec, o, true⟩ : Symbol) ∈ obj.symbols ∧
          f.bytes σ (base + UInt64.ofNat o) = some code ∧ code <+: X.drop o := by
  obtain ⟨text, relocs, fsyms, hq, hlen, rfl⟩ := assemble_inv h
  refine ⟨text, rfl, hlen, fun σ base X hw hX => ?_⟩
  obtain ⟨⟨C, hC, hCl⟩, hf⟩ := asmFns_spec hl hw P.funs 0 text relocs fsyms hq [] [] X rfl
    (by omega) (by simpa using hX)
  refine ⟨by simp [hC, hCl], fun f hfm => ?_⟩
  obtain ⟨o, code, hs, hb, hp⟩ := hf f hfm
  exact ⟨o, code, List.mem_append_left _ (List.mem_append_left _ hs), hb, hp⟩

/-- After relocation, decoding `.text` at the offset from `f`'s symbol of instruction `k` of `f`
yields that instruction, resolved at its address. -/
theorem assemble_decode (hl : asm.Laws) {P : Prog A} {obj : Obj} (h : assemble asm P = .ok obj) :
    ∃ text, obj.sections[textSec]? = some ⟨".text", .text, 16, text, 0⟩ ∧
      ∀ (σ : String → Option UInt64) (base : UInt64) (X : List UInt8),
        base.toNat + text.length < 2 ^ 64 → applyRelocs σ base textSec obj.relocs text = some X →
        ∀ f ∈ P.funs, ∃ (o : Nat) (ins : List A.isa.Instr),
          (⟨f.name, textSec, o, true⟩ : Symbol) ∈ obj.symbols ∧
          f.resolve σ (base + UInt64.ofNat o) = some ins ∧ ins.length = f.code.length ∧
          ∀ k (hk : k < ins.length), ∃ e, A.isa.encode ins[k] = some e ∧
            A.isa.decode (X.drop (o + seqSize A (f.code.take k))) = some (ins[k], e.length) := by
  obtain ⟨text, hsec, _, hlaw⟩ := assemble_text hl h
  refine ⟨text, hsec, fun σ base X hw hX f hf => ?_⟩
  obtain ⟨o, code, hs, hb, hp⟩ := (hlaw σ base X hw hX).2 f hf
  simp only [Fn.bytes] at hb
  cases hr : f.resolve σ (base + UInt64.ofNat o) with
  | none => rw [hr] at hb; cases hb
  | some ins =>
    rw [hr] at hb
    refine ⟨o, ins, hs, hr, (resolveAt_size hl _ _ _ _ hr hb).2, fun k hk => ?_⟩
    obtain ⟨pre, e, post, he, rfl, hpre⟩ := resolveAt_split hl _ _ _ _ hr hb k hk
    obtain ⟨t, ht⟩ := hp
    refine ⟨e, he, ?_⟩
    rw [← hpre, ← List.drop_drop, ← ht]
    simp only [List.append_assoc, List.drop_left]
    exact hl.isa.decode_encode _ _ _ he

end Millipede.Asm
