import Millipede.Top.Sound
import Millipede.Target.A64.SelectProof
import Millipede.Target.SelInit
import Millipede.RegAlloc.A64RegSound

/-!
# Soundness of the compiler on arm64 Linux

The composition of the passes is proved once for every lawful backend in `Top/Sound.lean`. This
file proves the laws of the arm64 backend, which are the ELF round trip, the loader's start, and
the simulation and instruction budget of the selected code at its register locations. From them
follows `compile_sound_arm64`, the statement `CompileSound.Statement compile arm64Linux` without
hypotheses.
-/

namespace Millipede

namespace A64

open Sel (wa)

/-- The loader's start on arm64, which says that the initial state of a linked image satisfies
`A64.Init`. Function symbols are 4-aligned because every instruction is 4 bytes, the bottom of the
stack region is 16-byte aligned, and its size is a multiple of 64 KiB, so its number of words is
even. -/
theorem init_of_link {k c : Nat} {P : Lin.Prog} {A : Asm.Prog arch} {obj : Obj} {img : Image}
    {D : Sel.Selector arch} (hs : Sel.select D P = .ok A) (ha : Asm.assemble asm A = .ok obj)
    (hk : Link.link (Compile.linkConfigA64W k c P) [obj] = .ok img) :
    ∃ σ lo N, Init P A σ lo N k c (img.init linux) := by
  have st := Sel.link_start asm_laws ha hk linux rfl rfl (show 3 ≤ 16 by decide)
    (show Abi.a64LinuxStackTop.toNat ≤ 2 ^ 47 by decide)
  obtain ⟨-, hml, _, hfk⟩ := Sel.select_spec hs
  have hsz : (Compile.linkConfigA64W k c P).stackSize = P.stackBytes (φ.words k c) := rfl
  have hpg : linux.pageBits = 16 := rfl
  refine ⟨_, _, _, ⟨st.world, st.wx, st.loaded, st.region, ?_, fun f hf a h => ?_, st.top.symm,
    ?_, ?_, fun fn hfn x hx => ?_, hsz ▸ st.size, st.bss, st.below⟩⟩
  · -- the entry function
    obtain ⟨fn, hfn⟩ : ∃ fn, P.funs[P.main]? = some fn := ⟨_, List.getElem?_eq_getElem hml⟩
    obtain ⟨f, hf, hsf⟩ := hfk P.main fn hfn
    exact ⟨f, hf, st.entry f (List.mem_of_getElem? hf) hsf.name⟩
  · -- function symbols are 4-aligned
    have := Asm.link_fn_dvd asm_laws (k := 4) (fun _ => Nat.dvd_refl 4) (by decide) ha hk f hf a h
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mod]
    exact Nat.mod_eq_zero_of_dvd this
  · -- `lo` is 16-byte aligned
    have := st.lo_page
    rw [hpg] at this
    omega
  · -- `N` is even
    rw [st.words, hpg]
    show 2 ^ 13 * _ % 2 = 0
    omega
  · -- `main`'s frame is zero
    have h1 := Lin.frameBytes_le (φ.words k c) P P.main
    have h2 : P.frameBytes (φ.words k c) P.main = fsize (Sel.frameW k c fn.frame) := by
      simp [Lin.Prog.frameBytes, hfn, φ, FrameModel.words]
    have h3 : P.stackBytes (φ.words k c) = (Lin.needs (φ.words k c) P.funs).getD P.main 0 := rfl
    have := st.size
    have := (fsize_eq (Sel.frameW k c fn.frame)).symm
    exact st.zero _ (by omega)

end A64

/-- The Lin pass of the arm64 backend, as a lock-step refinement at the register locations the
selection uses. -/
def Compile.a64Prep_lock (o : Compile.Options) (P : Lin.Prog) :
    RegAlloc.Lock P (Compile.a64Prep o P)
      (RegAlloc.A64Reg.kcUsed (Compile.a64K o) (Compile.a64C o) (Compile.a64Prep o P) o.memBase).1
      (RegAlloc.A64Reg.kcUsed (Compile.a64K o) (Compile.a64C o) (Compile.a64Prep o P) o.memBase).2 :=
  Compile.prep_lock o _ _ _ _ (fun _ h => RegAlloc.A64Reg.kcUsed_of_ok h) rfl P

open RegAlloc.A64Reg in
/-- The arm64 backend's laws, which are the ELF round trip, the loader's start, in which the
location registers are zero, and the simulation and cost of the selected code at the register
locations actually used. -/
theorem a64Backend_laws (o : Compile.Options) : (a64Backend o).Laws where
  load_write img bs hw := (Elf.a64Linux_laws A64.linux).load_write img bs hw
  run {p fp A obj img} hl hH hA hbud ho hlk ω := by
    let L := Compile.a64Prep_lock o (Lin.linearize fp p.memBytes)
    let kc := kcUsed (Compile.a64K o) (Compile.a64C o) (Compile.a64Prep o (Lin.linearize fp p.memBytes)) o.memBase
    have hk : kc.1 ≤ 10 ∧ kc.2 ≤ 14 := by
      obtain ⟨h1, h2⟩ := kcUsed_le (Compile.a64K o) (Compile.a64C o)
        (Compile.a64Prep o (Lin.linearize fp p.memBytes)) o.memBase
      have e1 : Compile.a64K o ≤ 10 := by unfold Compile.a64K; split <;> omega
      have e2 : Compile.a64C o ≤ 14 := by unfold Compile.a64C; split <;> omega
      exact ⟨Nat.le_trans h1 e1, Nat.le_trans h2 e2⟩
    have hA' := select_ok (k := kc.1) (c := kc.2) (mb := o.memBase) hA
    obtain ⟨σ, lo, N, hI⟩ := A64.init_of_link hA' ho hlk
    have hwf := L.wf (Lin.lower_linearize_wf hl p.memBytes)
    have hI' : Init kc.1 kc.2 _ A σ lo N (img.init A64.linux) := ⟨hI, fun x hx => init_zero img hk hx⟩
    have hlaws : (pkg kc.1 kc.2 o.memBase _ A σ lo N).Laws :=
      Sel.pkg_laws A64.asm_laws hA' hwf (cases hk hA hwf hI.bound) (fun _ h => h.1.world)
        (fun _ h => by
          show (Sel.wa lo N - (_ : A64.State).regs.x 31).toNat ≤ _; rw [h.1.sp]; simp)
        (by simp only [counts, A64.entryLen, A64.entryIs, List.length_cons]; omega) (entry_ok kc.1 kc.2 o.memBase hk _ A σ lo N hA hI.bound)
    obtain ⟨h1, h2, h3⟩ := Sel.select_lower_sound (S' := pkg kc.1 kc.2 o.memBase _ A σ lo N) A64.κ A64.laws hl hH
      L hlaws hI' ω
    refine ⟨h1, h2, ?_, Sel.select_lower_cost (S' := pkg kc.1 kc.2 o.memBase _ A σ lo N) hl hH L hlaws hbud hI' ω⟩
    intro n s hn
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hn
    show ((img.init A64.linux).regs.x 31 - t.1.regs.x 31).toNat ≤ _
    rw [hI.sp]
    exact Nat.le_trans (h3 n t ht) (L.stackBytes _)

/-- The compiler is sound for arm64 Linux, with no hypotheses. This is the statement of
`Millipede.compile_sound` at `arm64Linux`, the instance of `compile_sound_of_backend` at
`a64Backend`. -/
theorem compile_sound_arm64 : CompileSound.Statement compile arm64Linux :=
  compile_sound_of_backend a64Backend (a64Backend_laws {}) rfl

/-- `compile_sound` and `compile_sound_arm64` for every setting of the options, including register
allocation turned off. -/
theorem compileWith_sound (o : Compile.Options) :
    CompileSound.Statement (compileWith o) x64Linux ∧
      CompileSound.Statement (compileWith o) arm64Linux :=
  ⟨compileWith_sound_of_backend o (x64Backend o) (x64Backend_laws o) rfl,
    compileWith_sound_of_backend o (a64Backend o) (a64Backend_laws o) rfl⟩

end Millipede
