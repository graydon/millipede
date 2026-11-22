import Millipede.RegAlloc.A64RegCall
import Millipede.Target.SelInit

/-!
# arm64 with register locations: the loader's start and `main`'s entry

The start state `Init` is the loader's start with the location registers `x19, …` zero, which
holds because Linux and the loader model start with every register but `sp` zero. This module
also defines the simulation package `pkg` of the register selector and proves `entry_ok`, which
says that `main`'s entry sequence establishes the relation at the convention `conv k c`. Together
with the cases of the selector, these make the arm64 backend lawful.
-/
namespace Millipede.RegAlloc.A64Reg

open Millipede.A64 (State)

/-- The loader's start with the registers of the locations zero. -/
def Init (k c : Nat) (P : Lin.Prog) (A : Asm.Prog A64.arch) (σ : String → Option UInt64)
    (lo N : Nat) (m : State) : Prop :=
  A64.Init P A σ lo N k c m ∧ ∀ x, x < k + c → m.regs.x (loc k x) = 0

/-- The simulation package of the register selector. -/
abbrev pkg (k c : Nat) (mb : Bool) (P : Lin.Prog) (A : Asm.Prog A64.arch) (σ : String → Option UInt64)
    (lo N : Nat) : Sel.SimPkg (A := A64.arch) A64.linux P :=
  Sel.pkg A64.linux (conv k c mb) P A σ lo N (Live.flex P) (Init k c P A σ lo N) (counts k c mb (Live.of P))

/-- The loader model starts with every register but `sp` zero. -/
theorem init_zero (img : Image) {k c x : Nat} (hk : k ≤ 10 ∧ c ≤ 14) (hx : x < k + c) :
    (img.init A64.linux).regs.x (loc k x) = 0 := by
  have : loc k x ≠ 31 := loc_ne31 hk hx
  simp only [Image.init, A64.linux, Abi.linux]
  exact ite_eq_right_iff.2 fun h => absurd h this

/-- `main`'s entry sequence establishes the relation with register locations, because `main`'s
register locations start zero and the loader zeroes its frame words. -/
theorem entry_ok (k c : Nat) (mb : Bool) (hk : k ≤ 10 ∧ c ≤ 14) (P : Lin.Prog) (A : Asm.Prog A64.arch)
    (σ : String → Option UInt64) (lo N : Nat) (hsel : select k c P mb = .ok A)
    (hB : P.stackBytes (A64.φ.words k c) ≤ 8 * N) (ω : Oracle) (m₀ : State) (cy : Nat)
    (hI0 : Init k c P A σ lo N m₀) :
    ∃ m₁, (Sel.M (A := A64.arch) A64.linux).run ω (m₀, cy) ((counts k c mb (Live.of P)).entry P) =
        some (m₁, cy + (counts k c mb (Live.of P)).entry P) ∧
      (∃ fn f a j, Sel.MatchAt (conv k c mb) P A σ lo N P.init m₁ fn f a j) ∧
      Sel.RunAll (A := A64.arch) A64.linux ω (Sel.SpBound (conv k c mb) P lo N) (m₀, cy)
        ((counts k c mb (Live.of P)).entry P) := by
  obtain ⟨hI, hz⟩ := hI0
  obtain ⟨-, hml, _, hk'⟩ := Sel.select_spec (select_ok hsel)
  obtain ⟨fn, hfn⟩ : ∃ fn, P.funs[P.main]? = some fn := ⟨_, List.getElem?_eq_getElem hml⟩
  obtain ⟨f, hf, hsf⟩ := hk' P.main fn hfn
  obtain ⟨f', hf', hσ⟩ := hI.entry
  rw [hf] at hf'; cases hf'
  have hmem : f ∈ A.funs := List.mem_of_getElem? hf
  obtain ⟨a, ha, ⟨is, code, hr, hen, hcode⟩, _⟩ := Sel.fn_code A64.asm_laws hI.loaded hmem
  rw [hσ] at ha; cases ha
  rw [hsf.entry] at hr
  have hD0 := Sel.dataOk_init (Sel.select_bss (select_ok hsel)) hI.bss hI.below (P := P) (lo := lo)
  obtain ⟨Dm, hDm, -, -⟩ := hD0
  obtain ⟨⟨hsm, -⟩, -⟩ := fnOk_iff.1 hsf.ok
  obtain ⟨W, hW⟩ : ∃ W, Sel.frameW k c fn.frame = W := ⟨_, rfl⟩
  have hWF : W ≤ fn.frame := hW ▸ Sel.frameW_le k c fn.frame
  have hfit : A64.fw W ≤ N := by
    have h1 := Lin.frameBytes_le (A64.φ.words k c) P P.main
    simp only [Lin.Prog.frameBytes, hfn] at h1
    have h2 := hB
    simp only [Lin.Prog.stackBytes] at h2
    have : (A64.φ.words k c).frame fn.frame = A64.fsize W := by
      simp [FrameModel.words, A64.φ, hW]
    rw [A64.fsize_eq] at this; omega
  have hgt := A64.fw_gt W
  have htop := hI.region.top
  have ha4 : m₀.regs.pc % 4 = 0 := hI.aligned f hmem _ hσ
  obtain ⟨t, hrun, hlen, hsp, hpc, hw, hF, hwx, hlow, hR', -, hrest, hall, hregs, h29⟩ :=
    A64.run_entryB (ω := ω) (mb := mb) cy (F := W) (by unfold A64.maxFrame at hsm ⊢; omega) hfit
      (Nat.le_refl _) hI.region hI.sp hI.lo16 hI.even
      (by rw [hI.world]; rfl) ha4 hI.wx (show f.refAddr σ m₀.regs.pc (.sym Sel.memSym) = some Dm from hDm)
      (by rw [← hW]; exact hr) hen hcode
  have hj2 : (N - A64.fw W) % 2 = 0 := by
    have := hI.even; have := A64.fw_even W; omega
  have hM : Sel.MatchAt (conv k c mb) P A σ lo N P.init t fn f m₀.regs.pc (N - A64.fw W) := by
    refine ⟨hw.trans hI.world, rfl, hwx, Sel.loaded_frame hI.loaded hI.wx hF, hR', hfn, hf, hσ,
      ⟨ha4, hI.lo16, hj2⟩, Nat.zero_le _, ?_, hsp, ?_, ?_, rfl,
      Sel.dataOk_keep (by omega) (Sel.dataOk_init (Sel.select_bss (select_ok hsel)) hI.bss hI.below) hF hlow,
      hI.aligned, fun hmb D hD => by rw [h29, if_pos hmb]; rw [hDm] at hD; exact Option.some.inj hD⟩
    · show t.regs.pc = m₀.regs.pc + UInt64.ofNat (f.labelOff 0)
      rw [hpc, hlen, Asm.Fn.labelOff, hsf.entry]
      cases mb <;> simp [Asm.blocksOff, selector, A64.seqSize_si, A64.ops, List.length_map,
        A64.symAddr, hW] <;> omega
    · show _ ∧ _
      rw [show Sel.calleeFrame P P.init.fn = fn.frame from Sel.calleeFrame_eq hfn]
      refine ⟨by show N - A64.fw W + A64.fw (Sel.frameW k c fn.frame) = N; rw [hW]; omega,
        fun x hx => ?_⟩
      show (if x < k + c then t.regs.x (loc k x) else _) = 0
      split
      · rename_i hxk
        rw [hregs _ (loc_ne31 hk hxk) (loc_ne hk hxk (by decide)) (loc_ne29 hk hxk), hz x hxk]
      · rename_i hxk
        have := Sel.slot_lt_frameW (c := c) hx (by simp at hxk; omega)
        rw [hW] at this
        have hz' := hI.zero fn hfn (x - c) (by rw [hW]; omega); rw [hW] at hz'
        show Sel.word t.mem lo (N - A64.fw W + x - c) = 0
        rw [show N - A64.fw W + x - c = N - A64.fw W + (x - c) by omega,
          hrest _ (by omega) (by omega), hz']
    · simp only [Lin.State.depth, Lin.Prog.init, List.map_nil, List.sum_nil,
        Lin.Prog.frameBytes, hfn]
      show 8 * (N - A64.fw W) + (A64.fsize (Sel.frameW k c fn.frame) + 0) = 8 * N + 0
      rw [hW, A64.fsize_eq]; omega
  have sb : ∀ x : State, ∀ i, N - A64.fw W ≤ i → i ≤ N → x.regs.x 31 = Sel.wa lo i →
      Sel.SpBound (conv k c mb) P lo N x := fun x i h1 h2 h3 => Sel.spBound_of_match hM h1 h2 h3
  have hcf : (counts k c mb (Live.of P)).entry P = is.length := by
    show A64.entryLen (Sel.frameW k c (Sel.calleeFrame P P.main)) + _ = _
    rw [Sel.calleeFrame_eq hfn, hW]; exact hlen.symm
  rw [hcf]
  exact ⟨t, hrun, ⟨_, _, _, _, hM⟩, Sel.RunAll.mono (fun (x : State)
    (h : x.regs.x 31 = Sel.wa lo N ∨ x.regs.x 31 = Sel.wa lo (N - A64.fw W)) => h.elim
    (sb x N (by omega) (Nat.le_refl _)) (sb x _ (Nat.le_refl _) (by omega))) hall⟩

end Millipede.RegAlloc.A64Reg
