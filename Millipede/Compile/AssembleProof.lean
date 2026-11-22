import Millipede.Compile.AssembleLaws
import Millipede.Target.X64.Select
import Millipede.Target.X64.Le32

/-!
# The x64 assembler and its law

`X64.asm : Asm.Assembler X64.arch` is the x64 part of the generic assembler, and
`X64.assemble := Asm.assemble X64.asm`. References to local labels are resolved here as rel32
distances between two section offsets, and a distance out of reach is an error. References to
symbols, which are other functions and data items, become relocations. The field is left as zeros
and a `pc32` relocation with addend `-4` is emitted for it, because a rel32 field ends its
instruction, so `S - 4 - P` is the distance from the next instruction to `S`.

`X64.asmLaws : X64.asm.Laws` proves the laws for one instruction, so the generic assembler theorems
hold for x64. The module also proves that the x64 encoder is total.

See doc/design/compiler.md.
-/

namespace Millipede.X64

open Asm (textSec Agree toNat_add_ofNat)

/-- A pc32 relocation for the 4-byte field that ends at section offset `fieldEnd`. -/
def pcReloc (fieldEnd : Nat) (s : String) : Reloc :=
  ⟨textSec, fieldEnd - 4, .pc32, s, -4⟩

/-- The distance from section offset `next` to the target of local label `l`, if it is in
reach. -/
def localRel (lab : Nat → Option Nat) (l : Nat) (next : Nat) : Except String UInt32 :=
  match lab l with
  | none => .error "assemble: unknown label"
  | some t =>
    match rel32 (UInt64.ofNat t) (UInt64.ofNat next) with
    | some r => .ok r
    | none => .error "assemble: branch out of range"

/-- Assembles one symbolic instruction at section offset `off`, with local labels at the section
offsets `lab l`. The result is the instruction to encode, with its symbol fields zero, and its
relocations. -/
def asmSI (lab : Nat → Option Nat) (off : Nat) : SI → Except String (Instr × List Reloc)
  | .op i => .ok (i, [])
  | .jmp (.label l) => (localRel lab l (off + 5)).map fun r => (.jmp r, [])
  | .jmp (.sym s) => .ok (.jmp 0, [pcReloc (off + 5) s])
  | .jcc c (.label l) => (localRel lab l (off + 6)).map fun r => (.jcc c r, [])
  | .jcc c (.sym s) => .ok (.jcc c 0, [pcReloc (off + 6) s])
  | .call (.label l) => (localRel lab l (off + 5)).map fun r => (.call r, [])
  | .call (.sym s) => .ok (.call 0, [pcReloc (off + 5) s])
  | .lea d (.label l) =>
    (localRel lab l (off + SI.size (.lea d (.label l)))).map fun r => (.lea d (.rip r), [])
  | .lea d (.sym s) => .ok (.lea d (.rip 0), [pcReloc (off + SI.size (.lea d (.sym s))) s])

theorem ofInt_toUInt32 (v : Int) : UInt32.ofInt v = (UInt64.ofInt v).toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.ofInt, UInt64.ofInt, UInt64.toNat_toUInt32, UInt32.toNat_ofNat',
    UInt64.toNat_ofNat']
  have h1 : 0 ≤ v % 2^64 := Int.emod_nonneg _ (by decide)
  have h2 : v % 2^64 < 2^64 := Int.emod_lt_of_pos _ (by decide)
  have h3 : 0 ≤ v % 2^32 := Int.emod_nonneg _ (by decide)
  have h3' : v % 2^32 < 2^32 := Int.emod_lt_of_pos _ (by decide)
  have h4 : (v % 2^64) % 2^32 = v % 2^32 := Int.emod_emod_of_dvd v (by decide)
  omega

/- The lemma `le32_toUInt32`, by which the rel32 field agrees with the relocation's field, is in
`Millipede/Target/X64/Le32.lean` with the other encoding lemmas. -/

theorem le32_ofInt (v : Int) : le32 (UInt32.ofInt v) = natBytes 4 (UInt64.ofInt v).toNat := by
  rw [ofInt_toUInt32, le32_toUInt32]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  simp [UInt64.toNat_ofNat']; omega

/-! ## Instruction shapes -/

theorem lea_shape (d : Reg) (x : UInt32) :
    encode (.lea d (.rip x)) = [rex true d.hi false false, 0x8D, modrm 0 d.lo 5] ++ le32 x := by
  simp [encode, encW, encModRM, RM.hi, RM.xhi]

theorem SI.size_lea' (d : Reg) (r : Asm.Ref) : SI.size (.lea d r) = 7 := by
  simp [SI.size, encode, encW, encModRM, le32]

theorem asmSI_size {lab : Nat → Option Nat} {off : Nat} {si : SI} {ins : Instr}
    {rs : List Reloc} (h : asmSI lab off si = .ok (ins, rs)) :
    (encode ins).length = SI.size si := by
  rcases si with i | (l|s) | ⟨c, l|s⟩ | (l|s) | ⟨d, l|s⟩ <;>
    simp only [asmSI, localRel, Except.map] at h <;> (repeat' split at h) <;>
    simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp [encode, encW, encModRM, le32, SI.size]

/-- A resolved instruction has the size the layout assumed. -/
theorem resolve_size {ρ : Asm.Ref → Option UInt64} {a : UInt64} {si : SI} {i : Instr}
    (h : SI.resolve ρ a si = some i) : (encode i).length = SI.size si := by
  rcases si with i | r | ⟨c, r⟩ | r | ⟨d, r⟩ <;> simp only [SI.resolve] at h
  · cases h; rfl
  all_goals
    cases hr : ρ r <;> rw [hr] at h <;> simp only [Option.bind_none, Option.bind_some,
      reduceCtorEq] at h
    cases hx : rel32 _ _ <;> rw [hx] at h <;> simp only [Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at h
    subst h; simp [encode, encW, encModRM, le32, SI.size]

/-! ## One instruction -/

section
variable {σ : String → Option UInt64} {base : UInt64} {N : Nat}
  {ρ : Asm.Ref → Option UInt64} {lab : Nat → Option Nat}


theorem rel32_shift (hA : Agree σ base N ρ lab) {t n : Nat} (ht : t ≤ N) (hn : n ≤ N) :
    rel32 (base + UInt64.ofNat t) (base + UInt64.ofNat n) =
      rel32 (UInt64.ofNat t) (UInt64.ofNat n) := by
  have := hA.wrap
  unfold rel32
  rw [toNat_add_ofNat (show base.toNat + t < 2 ^ 64 by omega),
    toNat_add_ofNat (show base.toNat + n < 2 ^ 64 by omega),
    toNat_ofNat_lt (show t < 2 ^ 64 by omega), toNat_ofNat_lt (show n < 2 ^ 64 by omega)]
  have e : ((base.toNat + t : Nat) : Int) - ((base.toNat + n : Nat) : Int) = (t : Int) - (n : Int)
    := by omega
  simp only [e]

/-- For a symbol reference, the relocation patches the field to give the resolved instruction. -/
theorem sym_case (hA : Agree σ base N ρ lab) (hdr : List UInt8) (mk : UInt32 → Instr)
    (hmk : ∀ x, encode (mk x) = hdr ++ le32 x) (s : String) (pre post : List UInt8)
    (off : Nat) (hpre : pre.length = off) (hN : off + hdr.length + 4 ≤ N) {X : List UInt8}
    (h : applyRelocs σ base textSec [pcReloc (off + hdr.length + 4) s]
      (pre ++ encode (mk 0) ++ post) = some X) :
    ∃ i, ((ρ (.sym s)).bind fun t =>
        (rel32 t (base + UInt64.ofNat off + UInt64.ofNat (hdr.length + 4))).map mk) = some i ∧
      X = pre ++ encode i ++ post := by
  have hw := hA.wrap
  simp only [applyRelocs, pcReloc, textSec, ite_true] at h
  rw [hA.sym s]
  cases hs : σ s with
  | none => rw [hs] at h; cases h
  | some S =>
    rw [hs] at h
    dsimp only at h
    cases hv : RelocKind.patch .pc32 S (base + UInt64.ofNat (off + hdr.length + 4 - 4)) (-4)
        (((pre ++ encode (mk 0) ++ post).drop (off + hdr.length + 4 - 4)).take RelocKind.pc32.width) with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h
      simp only [Option.some.injEq] at h
      simp only [RelocKind.patch] at hv
      split at hv
      · rename_i hr
        cases hv
        subst h
        have hfield : off + hdr.length + 4 - 4 = (pre ++ hdr).length := by simp; omega
        rw [hfield, hmk, show pre ++ (hdr ++ le32 0) ++ post = (pre ++ hdr) ++ le32 0 ++ post by
          simp, patchBytes_mid _ _ _ _ (by simp [le32, natBytes_length])]
        rw [hfield] at hr
        have e1 : (base + UInt64.ofNat (pre ++ hdr).length).toNat = base.toNat + off + hdr.length
          := by rw [toNat_add_ofNat] <;> simp <;> omega
        have e2 : (base + UInt64.ofNat off + UInt64.ofNat (hdr.length + 4)).toNat =
            base.toNat + off + hdr.length + 4 := by
          rw [UInt64.add_assoc, ← UInt64.ofNat_add, toNat_add_ofNat] <;> omega
        rw [e1] at hr
        refine ⟨mk (UInt32.ofInt ((S.toNat : Int) - (base.toNat + off + hdr.length + 4 : Nat))),
          ?_, ?_⟩
        · simp only [Option.bind_some]
          unfold rel32
          rw [e2]
          have e3 : (pre ++ hdr).length = off + hdr.length := by simp; omega
          dsimp only
          split
          · rfl
          · rename_i hn; exact absurd (by push_cast at hr ⊢; omega) hn
        · rw [hmk, le32_ofInt]
          simp only [List.append_assoc]
          congr 6
          rw [e1]; push_cast; omega
      · cases hv

theorem localRel_ok (hA : Agree σ base N ρ lab) {l n : Nat} {r : UInt32} (hn : n ≤ N)
    (h : localRel lab l n = .ok r) : (ρ (.label l)).bind (fun t => rel32 t (base + UInt64.ofNat n)) =
      some r := by
  simp only [localRel] at h
  split at h
  · cases h
  · rename_i t ht
    obtain ⟨hρ, htN⟩ := hA.label l t ht
    rw [hρ, Option.bind_some, rel32_shift hA htN hn]
    split at h
    · rename_i r' hr; cases h; exact hr
    · cases h

theorem lea_length (d : Reg) (x : UInt32) : (encode (.lea d (.rip x))).length = 7 := by
  simp [encode, encW, encModRM, le32]

theorem except_map_eq_ok {ε α β : Type} {f : α → β} {x : Except ε α} {y : β}
    (h : x.map f = .ok y) : ∃ a, x = .ok a ∧ f a = y := by
  cases x <;> simp_all [Except.map]

/-- For a label reference, the field that `localRel` computes resolves the instruction at its
address. -/
theorem label_case (hA : Agree σ base N ρ lab) {l off L : Nat} (mk : UInt32 → Instr)
    {r : UInt32} (hL : off + L ≤ N) (hr : localRel lab l (off + L) = .ok r) :
    ((ρ (.label l)).bind fun t =>
      (rel32 t (base + UInt64.ofNat off + UInt64.ofNat L)).map mk) = some (mk r) := by
  have := localRel_ok hA hL hr
  rw [UInt64.add_assoc, ← UInt64.ofNat_add]
  cases hρ : ρ (.label l) <;> rw [hρ] at this <;> simp_all

/-- After its relocations are applied, the bytes of one instruction are the encoding of the
instruction resolved at its address. -/
theorem asmSI_spec (hA : Agree σ base N ρ lab) {off : Nat} {si : SI} {ins : Instr}
    {rs : List Reloc} (h : asmSI lab off si = .ok (ins, rs)) (pre post : List UInt8)
    (hpre : pre.length = off) (hN : off + SI.size si ≤ N) {X : List UInt8}
    (hX : applyRelocs σ base textSec rs (pre ++ encode ins ++ post) = some X) :
    ∃ i, SI.resolve ρ (base + UInt64.ofNat off) si = some i ∧ X = pre ++ encode i ++ post := by
  have hw := hA.wrap
  cases si
  case op i =>
    simp only [asmSI, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [applyRelocs, Option.some.injEq] at hX
    exact ⟨_, rfl, hX.symm⟩
  all_goals rename_i r; cases r
  case jmp.sym s =>
    cases h
    exact sym_case hA [0xE9] Instr.jmp (fun _ => rfl) s pre post off hpre
      (by simp [SI.size] at hN; omega) hX
  case jcc.sym c s =>
    cases h
    exact sym_case hA [0x0F, 0x80 + c.code] (Instr.jcc c) (fun _ => rfl) s pre post off hpre
      (by simp [SI.size] at hN; omega) hX
  case call.sym s =>
    cases h
    exact sym_case hA [0xE8] Instr.call (fun _ => rfl) s pre post off hpre
      (by simp [SI.size] at hN; omega) hX
  case lea.sym d s =>
    cases h
    rw [SI.size_lea'] at hN
    have := sym_case hA [rex true d.hi false false, 0x8D, modrm 0 d.lo 5]
      (fun x => Instr.lea d (.rip x)) (lea_shape d) s pre post off hpre (by simp; omega)
      (by simpa [SI.size_lea'] using hX)
    simpa [SI.resolve, lea_length] using this
  all_goals
    obtain ⟨r, hr, he⟩ := except_map_eq_ok h
    cases he
    simp only [applyRelocs, Option.some.injEq] at hX
    refine ⟨_, ?_, hX.symm⟩
  case lea.label d l =>
    rw [SI.size_lea'] at hN hr
    simpa [SI.resolve, lea_length] using label_case hA _ (by omega) hr
  all_goals exact label_case hA _ (by simp [SI.size] at hN; omega) hr
end


/-! ## The instance -/

/-- The x64 part of the assembler, which gives an instruction's encoding and its relocations. -/
def asm : Asm.Assembler arch where
  asmSI lab off si := (asmSI lab off si).map fun r => (encode r.1, r.2)

/-- The x64 assembler. -/
abbrev assemble (P : Asm.Prog arch) : Except String Obj := Asm.assemble asm P

theorem asm_inv {lab : Nat → Option Nat} {off : Nat} {si : SI} {bs : List UInt8}
    {rs : List Reloc} (h : asm.asmSI lab off si = .ok (bs, rs)) :
    ∃ ins, asmSI lab off si = .ok (ins, rs) ∧ bs = encode ins := by
  obtain ⟨⟨ins, rs'⟩, h1, h2⟩ := except_map_eq_ok h
  cases h2
  exact ⟨ins, h1, rfl⟩

theorem asmSI_relocs {lab : Nat → Option Nat} {off : Nat} {si : SI} {ins : Instr}
    {rs : List Reloc} (h : asmSI lab off si = .ok (ins, rs)) : ∀ r ∈ rs, r.sec = textSec := by
  rcases si with i | (l|s) | ⟨c, l|s⟩ | (l|s) | ⟨d, l|s⟩ <;>
    simp only [asmSI, localRel, Except.map] at h <;> (repeat' split at h) <;>
    simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp [pcReloc]

/-- The x64 assembler satisfies the assembler laws. -/
theorem asmLaws : asm.Laws where
  isa := laws
  size _ _ _ _ _ h := by
    obtain ⟨ins, h', rfl⟩ := asm_inv h; exact asmSI_size h'
  sec _ _ _ _ _ h := by
    obtain ⟨ins, h', -⟩ := asm_inv h; exact asmSI_relocs h'
  resolve_size _ _ _ _ _ h he := by cases he; exact resolve_size h
  spec hA _ _ _ _ h pre post _ hpre hN hX := by
    obtain ⟨ins, h', rfl⟩ := asm_inv h
    obtain ⟨i, hi, rfl⟩ := asmSI_spec hA h' pre post hpre hN hX
    exact ⟨i, _, hi, rfl, rfl⟩

/-! ## The total encoder -/

theorem encodeAll_eq : ∀ (is : List Instr), Asm.encodeAll isa is = some (is.flatMap encode)
  | [] => rfl
  | i :: is => by
    simp only [Asm.encodeAll, List.flatMap_cons]
    rw [encodeAll_eq is]; rfl

end Millipede.X64
