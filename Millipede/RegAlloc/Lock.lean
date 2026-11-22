import Millipede.Compile.Lin

/-!
# Lock-step refinements of Lin programs

A lock-step refinement `Lock P P' k c` is a relation of Lin states under which `P'` takes one step
for each step of `P` with the same world and clock. It also preserves the reactor boundary, makes
the stack bound no larger when `P'`'s frames are counted in the words of a selection with `k`
preserved and `c` caller-saved register locations (`Sel.frameW`, a caller-saved location has no
word), and keeps well-formedness. The Lin-to-Lin passes before selection, which are the checked
register allocation and the identity, are lock-step refinements, and the shared proof of
selection takes one as a parameter.
-/

namespace Millipede.Sel

/-! ## Frame words -/

/-- The stack words of a frame of `F` locations with `k` preserved and `c` caller-saved register
locations. Location `x < k` has the save word `x`, a caller-saved location `k ≤ x < k + c` has
none, and a slot `x ≥ k + c` is word `x - c`. -/
def frameW (k c F : Nat) : Nat := min F k + (F - (k + c))

theorem frameW_zero (k F : Nat) : frameW k 0 F = F := by unfold frameW; omega

theorem frameW_le (k c F : Nat) : frameW k c F ≤ F := by unfold frameW; omega

/-- A slot's word lies in its frame. -/
theorem slot_lt_frameW {k c F x : Nat} (hx : x < F) (hk : k + c ≤ x) : x - c < frameW k c F := by
  unfold frameW; omega

/-- A save word lies in its frame. -/
theorem save_lt_frameW {k c F x : Nat} (hx : x < min k F) : x < frameW k c F := by
  unfold frameW; omega

theorem frameW_mono (k c : Nat) {a b : Nat} (h : a ≤ b) : frameW k c a ≤ frameW k c b := by
  unfold frameW; omega

/-- A frame model composed with the frame words: a frame of `F` locations takes `φ` of its words. -/
def _root_.Millipede.FrameModel.words (φ : FrameModel) (k c : Nat) : FrameModel :=
  ⟨fun F => φ.frame (frameW k c F), fun h => φ.mono (frameW_mono k c h)⟩

theorem _root_.Millipede.FrameModel.words_le (φ : FrameModel) (k c F : Nat) : (φ.words k c).frame F ≤ φ.frame F :=
  φ.mono (frameW_le k c F)

@[simp] theorem _root_.Millipede.FrameModel.words_zero (φ : FrameModel) (k : Nat) : φ.words k 0 = φ := by
  cases φ; simp [FrameModel.words, frameW_zero]

/-- `callMax` is monotone in the callees' needs. -/
theorem callMax_mono {acc₁ acc₂ : List Nat} (h : ∀ i, acc₁.getD i 0 ≤ acc₂.getD i 0) :
    ∀ code, Lin.callMax acc₁ code ≤ Lin.callMax acc₂ code := by
  intro code; induction code with
  | nil => simp [Lin.callMax]
  | cons i is ih =>
    cases i with
    | call g _ _ => have := h g; simp only [Lin.callMax]; omega
    | _ => simpa only [Lin.callMax] using ih

/-- `needsFrom` is monotone in the frame model and the needs before it. -/
theorem needsFrom_mono {φ₁ φ₂ : FrameModel} (h : ∀ F, φ₁.frame F ≤ φ₂.frame F) :
    ∀ (fs : List Lin.Fn) (acc₁ acc₂ : List Nat), acc₁.length = acc₂.length →
      (∀ i, acc₁.getD i 0 ≤ acc₂.getD i 0) →
      ∀ i, (Lin.needsFrom φ₁ acc₁ fs).getD i 0 ≤ (Lin.needsFrom φ₂ acc₂ fs).getD i 0 := by
  intro fs; induction fs with
  | nil => intro _ _ _ h; exact h
  | cons f fs ih =>
    intro acc₁ acc₂ hl ha
    apply ih
    · simp [hl]
    · intro i
      have h1 := h f.frame
      have h2 := callMax_mono ha f.code
      clear h ih
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
      split <;> split <;> simp_all [Lin.fnNeed, List.getElem?_singleton]
      · have := ha i; simp_all
      · split <;> simp; omega


/-- A frame model that charges no frame more makes the stack bound no larger. -/
theorem stackBytes_mono {φ₁ φ₂ : FrameModel} (h : ∀ F, φ₁.frame F ≤ φ₂.frame F) (P : Lin.Prog) :
    P.stackBytes φ₁ ≤ P.stackBytes φ₂ :=
  needsFrom_mono h P.funs [] [] rfl (fun _ => Nat.le_refl _) P.main

theorem stackBytes_words_le (φ : FrameModel) (k c : Nat) (P : Lin.Prog) :
    P.stackBytes (φ.words k c) ≤ P.stackBytes φ :=
  stackBytes_mono (FrameModel.words_le φ k c) P

end Millipede.Sel

namespace Millipede.RegAlloc

open Lin (Prog)

/-! ## Lock-step refinements -/

/-- A lock-step refinement of Lin program `P` by `P'`. It is a relation of states that holds
initially and is preserved by every step, one target step per source step, with equal worlds and
clocks. It maps a reactor-step boundary, which is the reactor loop's `jz` on a non-zero constant
with an empty stack, to one, and keeps well-formedness. It makes the stack bound no larger when
`P'`'s frames are counted in the words of a selection with `k` preserved and `c` caller-saved
register locations (`Sel.frameW`). -/
structure Lock (P P' : Prog) (k c : Nat) where
  R : Lin.State → Lin.State → Prop
  init : R P.init P'.init
  step : ∀ {κ ω s t s'}, R s t → Lin.step κ P ω s = some s' →
    ∃ t', Lin.step κ P' ω t = some t' ∧ R s' t'
  world : ∀ {s t}, R s t → t.world = s.world
  clock : ∀ {s t}, R s t → t.clock = s.clock
  boundary : ∀ {s t}, R s t → s.stack = [] →
    (∃ fn l, P.funs[s.fn]? = some fn ∧ fn.code[s.pc]? = some (.jz (.imm 1) l)) →
    t.stack = [] ∧ ∃ fn l, P'.funs[t.fn]? = some fn ∧ fn.code[t.pc]? = some (.jz (.imm 1) l)
  stackBytes : ∀ φ, P'.stackBytes (φ.words k c) ≤ P.stackBytes φ
  wf : P.Wf → P'.Wf

/-- A self-simulation of `P` up to dead locations, which is a reflexive and transitive relation of
the states of `P` under which `P` steps in lock-step and which keeps the function, position and
world. Selection relates the machine to some state so related to the Lin state, so the machine
may leave a location that is dead at that point unsaved or destroyed. -/
structure Flex (P : Prog) where
  R : Lin.State → Lin.State → Prop
  refl : ∀ s, R s s
  trans : ∀ {a b c}, R a b → R b c → R a c
  step : ∀ {κ ω s t s'}, R s t → Lin.step κ P ω s = some s' →
    ∃ t', Lin.step κ P ω t = some t' ∧ R s' t'
  same : ∀ {s t}, R s t → t.fn = s.fn ∧ t.pc = s.pc ∧ t.world = s.world

namespace Lock

variable {Q Q' : Prog} {k c : Nat} (L : Lock Q Q' k c)

/-- The identity refinement. -/
def id (Q : Prog) (k c : Nat) : Lock Q Q k c where
  R := Eq
  init := rfl
  step {_ _ _ _ _} h hs := ⟨_, h ▸ hs, rfl⟩
  world h := h ▸ rfl
  clock h := h ▸ rfl
  boundary h h1 h2 := h ▸ ⟨h1, h2⟩
  stackBytes φ := Sel.stackBytes_words_le φ k c Q
  wf h := h

/-- A refinement whose frames fit in the words of `(k, c)` fits in those of any `(k', c')` that
give no frame more words. -/
def weaken (L : Lock Q Q' k c) {k' c' : Nat} (h : ∀ F, Sel.frameW k' c' F ≤ Sel.frameW k c F) :
    Lock Q Q' k' c' where
  R := L.R
  init := L.init
  step := L.step
  world := L.world
  clock := L.clock
  boundary := L.boundary
  stackBytes φ := Nat.le_trans (Sel.stackBytes_mono (φ₁ := φ.words k' c') (φ₂ := φ.words k c)
    (fun F => φ.mono (h F)) Q') (L.stackBytes φ)
  wf := L.wf

/-- A refinement counted in whole frames (`(k, 0)`: every location a word) fits every selection. -/
def anyKC {k₀ : Nat} (L : Lock Q Q' k₀ 0) (k c : Nat) : Lock Q Q' k c :=
  weaken L fun F => by simp only [Sel.frameW_zero]; exact Sel.frameW_le k c F

/-- Related states stay related along runs, in which the target takes exactly as many steps. -/
theorem run {κ : CostModel} {ω : Oracle} :
    ∀ (n : Nat) {s t s' : Lin.State}, L.R s t → (Lin.sem κ Q).run ω s n = some s' →
      ∃ t', (Lin.sem κ Q').run ω t n = some t' ∧ L.R s' t'
  | 0, _, _, _, hR, h => by cases h; exact ⟨_, rfl, hR⟩
  | n + 1, s, t, s', hR, h => by
    rw [Sem.run_succ] at h
    cases hs : Lin.step κ Q ω s with
    | none => simp [hs] at h
    | some s₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨t₁, ht, hR₁⟩ := L.step hR hs
      obtain ⟨t', h', hR'⟩ := run n hR₁ h
      exact ⟨t', by rw [Sem.run_succ]; show (Lin.step κ Q' ω t).bind _ = _; rw [ht]; exact h', hR'⟩

/-- The refinement as a forward simulation with factor `1`, one step for each step. -/
def sim (κ : CostModel) (ω : Oracle) : FwdSim (Lin.sem κ Q) (Lin.sem κ Q') ω where
  Idx := Unit
  lt _ _ := False
  wf := ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩
  R _ s t := L.R s t
  factor := 1
  events_eq {_ s t} h := by show s.world.events = t.world.events; rw [L.world h]
  step {_ s t s'} hR hs := by
    obtain ⟨t', ht, hR'⟩ := L.step hR hs
    refine ⟨(), t', 1, Sem.run_one ht, hR', Or.inl Nat.one_pos, ?_⟩
    show t'.clock + 1 * s.clock ≤ t.clock + 1 * s'.clock
    rw [L.clock hR', L.clock hR]; omega

theorem neverStuck (L : Lock Q Q' k c) (κ : CostModel) (ω : Oracle) (hs : (Lin.sem κ Q).NeverStuck ω Q.init) :
    (Lin.sem κ Q').NeverStuck ω Q'.init :=
  (L.sim κ ω).neverStuck (i := ()) L.init hs

theorem traceEq (L : Lock Q Q' k c) (κ : CostModel) (ω : Oracle) (hs : (Lin.sem κ Q).NeverStuck ω Q.init) :
    TraceEq ((Lin.sem κ Q).traceAt ω Q.init) ((Lin.sem κ Q').traceAt ω Q'.init) :=
  (L.sim κ ω).traceEq (Lin.sem_mono κ Q') (i := ()) L.init hs

end Lock

end Millipede.RegAlloc
