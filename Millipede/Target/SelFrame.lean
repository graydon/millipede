import Millipede.Target.SelSim
import Millipede.Target.SelDriver

/-!
# The frame relation

Every backend keeps each Lin activation in a frame of stack words. The running frame's slots
start at the word `j` that the stack pointer names, the return address of the suspended caller
is in word `j + F`, where `F` is the number of slots, and the caller's frame starts further up
by a number of words that depends on the backend. A `Conv` records that number for a caller and
for the bottom activation, `main`, together with the offset of the return address after a call
block's label, the stack-depth offset `dtop` and alignment invariants. On x64, `call` pushes the
return address above the callee's slots, so the caller's frame starts `F + 1` words up. On arm64,
the callee's entry saves `x30` in word `F` of its own frame, which is rounded up to 16 bytes.

Location `x < k` of the running activation is a machine register, and every other location is
its stack word. Registers are saved through the frame word: the caller of a function with `G`
slots saves its registers `x < min k G` in the callee's frame words `x`, which the callee does
not use because those locations are its registers, and the callee's return restores them. So
`Frames` carries a register view down the stack. The running activation's view is the machine's
registers, and a suspended activation's is the save words of the nearest deeper activation large
enough, or else the registers.

This module defines the relation `MatchAt` between a running Lin state and a machine state, with
its parts `LocsOk`, `callerView`, `RetOk`, `Frames` and `DataOk`, and the stack bound `SpBound`.
It proves once for every backend how the relation survives a step in the running frame, a call
(`matchAt_call`) and a return (`matchAt_ret`), and that a block of straight-line code reaching
the next label is matched (`sim_straight`).
-/

namespace Millipede.Sel

open Flat (Operand)

/-- A backend's frame convention, which says where each activation's frame, return address and
register locations are. -/
structure Conv (A : Asm.Arch) where
  /-- The frame model of the stack bound. -/
  φ : FrameModel
  /-- The words from the start of an activation with `F` slots to its caller's activation. -/
  next : Nat → Nat
  /-- The words of the bottom activation, `main`, with `F` slots. -/
  last : Nat → Nat
  /-- The bytes from the label of a call block to its return address, for the call
  `call g args d` at position `pc` of function `i` of the program. It depends on the position
  because a call block saves only the registers live after the call. -/
  retOff : Lin.Prog → Nat → Nat → Nat → List Operand → Nat → Nat
  /-- The offset in `8 j + depth = 8 N + dtop`, at the running frame word `j`. -/
  dtop : Nat
  /-- Extra invariants of the running function's address, the region base and the frame word. -/
  ok : UInt64 → Nat → Nat → Prop
  /-- An invariant of every function symbol's address, such as 4-byte alignment on arm64. -/
  fnAddr : UInt64 → Prop
  /-- The number of register locations. Location `x < k` of the running activation is a machine
  register, and with `k = 0` every location is a frame slot. -/
  k : Nat := 0
  /-- The value of register location `x` in a register file. -/
  reg : A.isa.Regs → Nat → UInt64 := fun _ _ => 0
  /-- The number of caller-saved register locations, `k … k+c-1`. They are registers of the
  running activation that a call destroys, so a suspended activation's are unconstrained, and
  they have no frame word. -/
  c : Nat := 0
  /-- The clobber set of each instruction: the locations its code destroys, which no value live
  after it may occupy unless it defines them (`RegAlloc.Live.clobOk`). -/
  kill : Lin.Instr → Nat → Bool := fun _ _ => false
  /-- An invariant of the registers in every related state, given the symbol map: on arm64 with
  `Options.memBase`, that `x29` holds the data region's address. -/
  regOk : (String → Option UInt64) → A.isa.Regs → Prop := fun _ _ => True
  next_gt : ∀ F, frameW k c F < next F
  last_ge : ∀ F, frameW k c F ≤ last F

/-- An instruction that falls through, keeps the stack pointer and keeps the register invariant
`C.regOk`. -/
def StraightC {A : Asm.Arch} (C : Conv A) (abi : Abi A.isa) (ω : Oracle) (i : A.isa.Instr) : Prop :=
  Straight abi ω i ∧ ∀ σ (s s' : MState A.isa.Regs), A.isa.exec (abi.trap ω) i (ilen i) s = some s' →
    C.regOk σ s.regs → C.regOk σ s'.regs

/-- Straight-line code of such instructions keeps `C.regOk`. -/
theorem runIs_regOk {A : Asm.Arch} {C : Conv A} {abi : Abi A.isa} {ω : Oracle} {σ : String → Option UInt64} :
    ∀ {is : List A.isa.Instr} {s s' : MState A.isa.Regs}, (∀ i ∈ is, StraightC C abi ω i) →
      runIs abi ω is s = some s' → C.regOk σ s.regs → C.regOk σ s'.regs
  | [], _, _, _, h, hB => by cases h; exact hB
  | i :: is, s, s', hs, h, hB => by
    simp only [runIs] at h
    split at h
    · cases h
    · cases hx : A.isa.exec (abi.trap ω) i (ilen i) s with
      | none => rw [hx] at h; cases h
      | some s₁ =>
        rw [hx, Option.bind_some] at h
        exact runIs_regOk (fun j hj => hs j (List.mem_cons_of_mem _ hj)) h
          ((hs i List.mem_cons_self).2 σ s s₁ hx hB)

/-- Under a convention whose register invariant always holds, a straight instruction keeps it. -/
theorem StraightC.of_true {A : Asm.Arch} {C : Conv A} {abi : Abi A.isa} {ω : Oracle}
    (hC : ∀ σ r, C.regOk σ r) {i : A.isa.Instr} (h : Straight abi ω i) : StraightC C abi ω i :=
  ⟨h, fun σ _ s' _ _ => hC σ s'.regs⟩

/-- A register view: the value of each register location. -/
abbrev RegView := Nat → UInt64

/-- The view with location `x` set to `v`. -/
def RegView.set (rv : RegView) (x : Nat) (v : UInt64) : RegView := fun y => if y = x then v else rv y

section Rel
variable {A : Asm.Arch} (C : Conv A) (P : Lin.Prog) (AP : Asm.Prog A) (σ : String → Option UInt64)
  (lo N : Nat)

/-- Slots `0 … F-1` of a frame are the stack words `j, j+1, …`. -/
def SlotsOk (m : Memory) (j F : Nat) (fr : Flat.Frame) : Prop :=
  ∀ x, x < F → word m lo (j + x) = fr x

/-- Word `k` holds the return address of the call to `g` that suspended activation `a`, which is
`retOff` bytes after the label of its call block. -/
def RetOk (m : Memory) (a : Lin.Act) (g k : Nat) : Prop :=
  ∃ (fa : Lin.Fn) (args : List Operand) (f : Asm.Fn A) (addr : UInt64),
    P.funs[a.fn]? = some fa ∧ 0 < a.pc ∧ fa.code[a.pc - 1]? = some (.call g args a.dst) ∧
    AP.funs[a.fn]? = some f ∧ σ f.name = some addr ∧
    word m lo k = addr + UInt64.ofNat (f.labelOff (a.pc - 1) + C.retOff P a.fn (a.pc - 1) g args a.dst)

/-- Locations `0 … F-1` of a frame at word `j` hold `fr`, with location `x < k + c` read in the
register view `rv` and every other location in its stack word `j + x - c`. -/
def LocsOk (k c : Nat) (rv : RegView) (m : Memory) (j F : Nat) (fr : Flat.Frame) : Prop :=
  ∀ x, x < F → (if x < k + c then rv x else word m lo (j + x - c)) = fr x

/-- The register view of the caller of an activation of `G` slots at word `j` with view `rv`.
The registers `x < min k G`, which the call saved, are read from the callee's frame words `x`. -/
def callerView (k : Nat) (m : Memory) (j G : Nat) (rv : RegView) : RegView :=
  fun x => if x < min k G then word m lo (j + x) else rv x

/-- The machine stack holds the Lin activations, with the running frame at word `j`, the return
address at `j + F`, the caller's frame at `j + next F` and so on, and `main`'s frame ending at
word `N`. Each activation's locations `x < k` are read in its register view `rv`. The caller of
an activation of `G` slots sees the words `x < min k G` of that activation's frame, where the
call saved its registers, so a suspended activation's register location `x` is in frame word `x`
of the nearest deeper activation whose frame exceeds `x`, or else still in the register. A
suspended activation's caller-saved locations `k ≤ x < k + c` are read in a view that is free
there, since a call destroys those registers and no value is live in them across it. -/
def Frames (m : Memory) : Nat → Flat.Frame → List Lin.Act → Nat → RegView → Prop
  | g, fr, [], j, rv => j + C.last (calleeFrame P g) = N ∧
      LocsOk lo C.k C.c rv m j (calleeFrame P g) fr
  | g, fr, a :: st, j, rv => LocsOk lo C.k C.c rv m j (calleeFrame P g) fr ∧
      RetOk C P AP σ lo m a g (j + frameW C.k C.c (calleeFrame P g)) ∧
      ∃ rv' : RegView, (∀ x, x < C.k → rv' x = callerView lo C.k m j (calleeFrame P g) rv x) ∧
        Frames m a.fn a.frame st (j + C.next (calleeFrame P g)) rv'

/-- The data region `mp_mem` is at some address `D` below the stack region and holds Lin's
memory. -/
def DataOk (m : Memory) (h : Flat.Heap) : Prop :=
  ∃ D : UInt64, σ memSym = some D ∧ D.toNat + P.mem ≤ lo ∧ DataRel D P.mem m h

/-- The relation between a running Lin state and a machine state. Its witnesses are the Lin
function `fn`, its Asm function `f` at address `a`, and the stack word `j` of its frame. -/
structure MatchAt (s : Lin.State) (m : MState A.isa.Regs) (fn : Lin.Fn) (f : Asm.Fn A)
    (a : UInt64) (j : Nat) : Prop where
  world : m.world = s.world
  run : s.world.halted = false
  wx : m.mem.WxorX
  loaded : AP.Loaded σ m.mem
  region : Region m.mem lo N
  hfn : P.funs[s.fn]? = some fn
  hf : AP.funs[s.fn]? = some f
  addr : σ f.name = some a
  ok : C.ok a lo j
  pc : s.pc ≤ fn.code.length
  rip : A.isa.pc m.regs = a + UInt64.ofNat (f.labelOff s.pc)
  sp : A.isa.sp m.regs = wa lo j
  frames : Frames C P AP σ lo N m.mem s.fn s.frame s.stack j (C.reg m.regs)
  depth : 8 * j + s.depth C.φ P = 8 * N + C.dtop
  chain : Lin.Chain C.φ P s.fn s.stack
  data : DataOk P σ lo m.mem s.mem
  syms : ∀ g ∈ AP.funs, ∀ b, σ g.name = some b → C.fnAddr b
  regOk : C.regOk σ m.regs

/-- `sp` is within the static stack bound below the top of the stack region. -/
def SpBound (x : MState A.isa.Regs) : Prop := (wa lo N - A.isa.sp x.regs).toNat ≤ P.stackBytes C.φ

end Rel

variable {A : Asm.Arch} {C : Conv A} {P : Lin.Prog} {AP : Asm.Prog A}
  {σ : String → Option UInt64} {lo N : Nat}

theorem calleeFrame_eq {g : Nat} {fn : Lin.Fn} (h : P.funs[g]? = some fn) : calleeFrame P g = fn.frame := by
  simp [calleeFrame, h]

/-- `LocsOk` depends on the view only below `k + c`. -/
theorem locsOk_view {k c : Nat} {rv rv' : RegView} {m : Memory} {j F : Nat} {fr : Flat.Frame}
    (hv : ∀ x, x < k + c → rv' x = rv x) (h : LocsOk lo k c rv m j F fr) :
    LocsOk lo k c rv' m j F fr := by
  intro x hx
  have := h x hx
  by_cases hxk : x < k + c <;> simp only [hxk, ite_true, ite_false] at this ⊢
  · rw [hv x hxk]; exact this
  · exact this

/-- `LocsOk` depends on memory only through the words of the slot locations. -/
theorem locsOk_congr {k c : Nat} {rv : RegView} {m m' : Memory} {j F : Nat} {fr : Flat.Frame}
    (hc : ∀ x, x < F → k + c ≤ x → word m' lo (j + x - c) = word m lo (j + x - c))
    (h : LocsOk lo k c rv m j F fr) : LocsOk lo k c rv m' j F fr := by
  intro x hx
  have := h x hx
  by_cases hxk : x < k + c <;> simp only [hxk, ite_true, ite_false] at this ⊢
  · exact this
  · rw [hc x hx (by omega)]; exact this

theorem retOk_congr {m m' : Memory} {a : Lin.Act} {g i : Nat}
    (hc : word m' lo i = word m lo i) (h : RetOk C P AP σ lo m a g i) : RetOk C P AP σ lo m' a g i := by
  obtain ⟨fa, args, f, addr, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨fa, args, f, addr, h1, h2, h3, h4, h5, by rw [hc]; exact h6⟩

theorem frames_le {m : Memory} : ∀ (st : List Lin.Act) (g : Nat) (fr : Flat.Frame) (j : Nat)
    (rv : RegView), Frames C P AP σ lo N m g fr st j rv →
      j + frameW C.k C.c (calleeFrame P g) ≤ N ∧ (st ≠ [] → j + C.next (calleeFrame P g) ≤ N)
  | [], g, _, _, _, h => by
    have := h.1; have := C.last_ge (calleeFrame P g); exact ⟨by omega, fun h => absurd rfl h⟩
  | a :: st, g, _, _, _, ⟨_, _, _, _, h⟩ => by
    have := (frames_le st a.fn a.frame _ _ h).1
    have := C.next_gt (calleeFrame P g)
    exact ⟨by omega, fun _ => by omega⟩

/-- `Frames` depends on memory only through the words from `j` up to `N`. -/
theorem frames_congr {m m' : Memory} : ∀ (st : List Lin.Act) (g : Nat) (fr : Flat.Frame) (j : Nat)
    (rv : RegView), (∀ i, j ≤ i → i < N → word m' lo i = word m lo i) →
    Frames C P AP σ lo N m g fr st j rv → Frames C P AP σ lo N m' g fr st j rv
  | [], g, _, _, _, hc, h => by
    have := h.1; have := C.last_ge (calleeFrame P g)
    exact ⟨h.1, locsOk_congr (fun x hx hk => by
      have := slot_lt_frameW (c := C.c) hx hk; exact hc _ (by omega) (by omega)) h.2⟩
  | a :: st, g, _, j, rv, hc, ⟨h1, h2, rv₀, h3, h4⟩ => by
    have hle := (frames_le st a.fn a.frame _ _ h4).1
    have := C.next_gt (calleeFrame P g)
    refine ⟨locsOk_congr (fun x hx hk => by
      have := slot_lt_frameW (c := C.c) hx hk; exact hc _ (by omega) (by omega)) h1,
      retOk_congr (hc _ (by omega) (by omega)) h2, rv₀, fun x hx => ?_,
      frames_congr st a.fn a.frame _ _ (fun i hi hi' => hc i (by omega) hi') h4⟩
    rw [h3 x hx]; simp only [callerView]
    split
    · exact (hc _ (by omega) (by have := save_lt_frameW (c := C.c) ‹_›; omega)).symm
    · rfl

theorem frames_locs {m : Memory} {g : Nat} {fr : Flat.Frame} {st : List Lin.Act} {j : Nat}
    {rv : RegView} (h : Frames C P AP σ lo N m g fr st j rv) :
    LocsOk lo C.k C.c rv m j (calleeFrame P g) fr := by
  cases st with
  | nil => exact h.2
  | cons _ _ => exact h.1

/-- A slot store or a register write in the running frame keeps `Frames` with the new frame,
provided the frame's save words `x < min k F`, every word above the frame and the preserved
registers of the locations beyond the frame are unchanged. -/
theorem frames_update {m m' : Memory} {g : Nat} {fr fr' : Flat.Frame} {st : List Lin.Act}
    {j : Nat} {rv rv' : RegView} (h : Frames C P AP σ lo N m g fr st j rv)
    (hL : LocsOk lo C.k C.c rv' m' j (calleeFrame P g) fr')
    (hsave : ∀ x, x < min C.k (calleeFrame P g) → word m' lo (j + x) = word m lo (j + x))
    (hc : ∀ i, j + frameW C.k C.c (calleeFrame P g) ≤ i → i < N → word m' lo i = word m lo i)
    (hreg : ∀ x, calleeFrame P g ≤ x → x < C.k → rv' x = rv x) :
    Frames C P AP σ lo N m' g fr' st j rv' := by
  cases st with
  | nil => exact ⟨h.1, hL⟩
  | cons a st =>
    obtain ⟨-, h2, rv₀, h3, h4⟩ := h
    have := C.next_gt (calleeFrame P g)
    have hle := (frames_le st a.fn a.frame _ _ h4).1
    refine ⟨hL, retOk_congr (hc _ (by omega) (by omega)) h2, rv₀, fun x hx => ?_,
      frames_congr st a.fn a.frame _ _ (fun i hi hi' => hc i (by omega) hi') h4⟩
    rw [h3 x hx]; simp only [callerView]
    by_cases hs : x < min C.k (calleeFrame P g)
    · rw [ite_eq_left hs, ite_eq_left hs, hsave x hs]
    · rw [ite_eq_right hs, ite_eq_right hs, hreg x (by omega) hx]

/-- A call pushes the callee onto `Frames`. The caller, function `g` with frame `fr` and view
`rv`, calls a function of `G` slots whose frame is at `j' = j - next G`. After the call sequence
the callee's locations hold `fr'` in the view `rv'`, the return address is in word `j' + G`,
every word from `j` on is unchanged, the caller's registers `x < min k G` are in the callee's
words `j' + x`, and its other registers are unchanged. The suspended activation's frame `fc` is
`fr` except at the caller's locations `x < min k G`, where it is whatever the save word holds,
since a register that is dead after the call is not saved. -/
theorem frames_call {m m' : Memory} {g g' : Nat} {fr fc fr' : Flat.Frame} {st : List Lin.Act}
    {j j' : Nat} {rv rv' : RegView} {act : Lin.Act} (h : Frames C P AP σ lo N m g fr st j rv)
    (hact : act.fn = g ∧ act.frame = fc) (hj : j' + C.next (calleeFrame P g') = j)
    (hL : LocsOk lo C.k C.c rv' m' j' (calleeFrame P g') fr')
    (hra : RetOk C P AP σ lo m' act g' (j' + frameW C.k C.c (calleeFrame P g')))
    (hkeep : ∀ i, j ≤ i → i < N → word m' lo i = word m lo i)
    (hsave : ∀ x, x < min C.k (calleeFrame P g') →
      word m' lo (j' + x) = if x < calleeFrame P g then fc x else rv x)
    (hfc : ∀ x, x < calleeFrame P g → min C.k (calleeFrame P g') ≤ x → fc x = fr x)
    (hreg : ∀ x, min C.k (calleeFrame P g') ≤ x → x < C.k → rv' x = rv x) :
    Frames C P AP σ lo N m' g' fr' (act :: st) j' rv' := by
  obtain ⟨h1, h2⟩ := hact
  refine ⟨hL, hra, fun x => if x < C.k then callerView lo C.k m' j' (calleeFrame P g') rv' x
    else rv x, fun x hx => by simp only [ite_eq_left hx], ?_⟩
  rw [h1, h2, hj]
  have hF := frames_congr st _ _ _ _ hkeep h
  have hl := frames_locs hF
  refine frames_update hF (fun x hx => ?_) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun x hx hxk => ?_)
  · have hlx := hl x hx
    by_cases hxk : x < C.k
    · rw [ite_eq_left (Nat.lt_of_lt_of_le hxk (Nat.le_add_right _ _))] at hlx ⊢
      rw [ite_eq_left hxk]
      simp only [callerView]
      split
      · rw [hsave x ‹_›, ite_eq_left hx]
      · rw [hreg x (by omega) hxk, hlx, hfc x hx (by omega)]
    · rw [hfc x hx (by omega), ← hlx]
      by_cases hxK : x < C.k + C.c
      · rw [ite_eq_left hxK, ite_eq_left hxK, ite_eq_right hxk]
      · rw [ite_eq_right hxK, ite_eq_right hxK]
  · simp only [ite_eq_left hxk, callerView]
    split
    · rw [hsave x ‹_›, ite_eq_right (by omega)]
    · exact hreg x (by omega) hxk

/-- The suspended caller's frame after a call that saved its location `x < min k G` only when
`keep x`. An unsaved location reads its save word `j' + x`, which the call did not write. -/
def savedFrame (lo k G : Nat) (keep : Nat → Bool) (mem : Memory) (j' : Nat) (fr : Flat.Frame) :
    Flat.Frame :=
  fun x => if x < min k G ∧ keep x = false then word mem lo (j' + x) else fr x

/-- A return pops the callee from `Frames`: the caller's activation is related in a view that
agrees below `k` with `callerView`, the saved words for `x < min k G` and the callee's registers
above. -/
theorem frames_ret {m : Memory} {g : Nat} {fr : Flat.Frame} {act : Lin.Act} {st : List Lin.Act}
    {j : Nat} {rv : RegView} (h : Frames C P AP σ lo N m g fr (act :: st) j rv) :
    ∃ rv₀ : RegView, (∀ x, x < C.k → rv₀ x = callerView lo C.k m j (calleeFrame P g) rv x) ∧
      Frames C P AP σ lo N m act.fn act.frame st (j + C.next (calleeFrame P g)) rv₀ :=
  h.2.2

/-- The suspended caller of the running activation holds its frame in its locations, in a view
that agrees below `k` with `callerView`. -/
theorem frames_caller {m : Memory} {g : Nat} {fr : Flat.Frame} {act : Lin.Act} {st : List Lin.Act}
    {j : Nat} {rv : RegView} (h : Frames C P AP σ lo N m g fr (act :: st) j rv) :
    ∃ rv₀ : RegView, (∀ x, x < C.k → rv₀ x = callerView lo C.k m j (calleeFrame P g) rv x) ∧
      LocsOk lo C.k C.c rv₀ m (j + C.next (calleeFrame P g)) (calleeFrame P act.fn) act.frame :=
  let ⟨rv₀, h1, h2⟩ := frames_ret h
  ⟨rv₀, h1, frames_locs h2⟩

/-- The data region survives machine steps that keep the permissions and every byte below the
stack region. -/
theorem dataOk_keep {m m' : Memory} {h : Flat.Heap} (hlo : lo ≤ 2 ^ 47) (hD : DataOk P σ lo m h)
    (hF : Memory.Frame m m') (hl : LowSame lo m m') : DataOk P σ lo m' h := by
  obtain ⟨D, hσ, hle, hR⟩ := hD
  refine ⟨D, hσ, hle, dataRel_congr hR hF fun i hi => hl _ ?_⟩
  have := D.toNat_lt
  rw [UInt64.toNat_add]; simp only [UInt64.toNat_ofNat'] at this ⊢
  have h1 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.mod_eq_of_lt (by omega)]; omega

/-- At the start, the zero-initialised data region `mp_mem` holds Lin's memory of zeros. -/
theorem dataOk_init {m : Memory} (hbss : AP.bss = [(memSym, P.mem)]) (hB : AP.BssAt σ m)
    (hbelow : ∀ b ∈ AP.bss, ∀ D, σ b.1 = some D → D.toNat + b.2 ≤ lo) :
    DataOk P σ lo m (fun _ => 0) := by
  have hb : (memSym, P.mem) ∈ AP.bss := by simp [hbss]
  obtain ⟨D, hD, hz⟩ := hB _ hb
  exact ⟨D, hD, hbelow _ hb D hD, fun i hi => hz i hi⟩

section Match
variable {s s' : Lin.State} {m m' : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64}
  {j : Nat}

/-- A related machine state has not halted. -/
theorem MatchAt.halted (hM : MatchAt C P AP σ lo N s m fn f a j) : m.world.halted = false := by
  rw [hM.world]; exact hM.run

/-- The running frame's locations hold its Lin frame, in registers below `k` and in stack words
above. -/
theorem MatchAt.locs (hM : MatchAt C P AP σ lo N s m fn f a j) :
    LocsOk lo C.k C.c (C.reg m.regs) m.mem j fn.frame s.frame :=
  calleeFrame_eq hM.hfn ▸ frames_locs hM.frames

/-- The running frame lies in the region. -/
theorem MatchAt.room (hM : MatchAt C P AP σ lo N s m fn f a j) : j + frameW C.k C.c fn.frame ≤ N :=
  calleeFrame_eq hM.hfn ▸ (frames_le _ _ _ _ _ hM.frames).1

/-- At a related state, the frame word `j` is within the region, and the stack below the top
fits the static bound. -/
theorem matchAt_room (hM : MatchAt C P AP σ lo N s m fn f a j) :
    j ≤ N ∧ 8 * (N - j) ≤ P.stackBytes C.φ := by
  have h1 := (frames_le _ _ _ _ _ hM.frames).1
  have h2 := Lin.depth_le_of_chain C.φ P s hM.chain
  have h3 := hM.depth
  omega

/-- A state whose `sp` is word `i` of the region, at or above a related frame, is within the
bound. -/
theorem spBound_of_match (hM : MatchAt C P AP σ lo N s m fn f a j) {x : MState A.isa.Regs}
    {i : Nat} (hi : j ≤ i) (hiN : i ≤ N) (h : A.isa.sp x.regs = wa lo i) : SpBound C P lo N x := by
  have := matchAt_room hM
  have htop := hM.region.top
  unfold SpBound; rw [h]
  have : lo + 8 * i ≤ lo + 8 * N := by omega
  simp only [wa, UInt64.toNat_sub, UInt64.toNat_ofNat']
  simp; omega

theorem spBound_of_keep (hM : MatchAt C P AP σ lo N s m fn f a j) {x : MState A.isa.Regs}
    (h : A.isa.sp x.regs = A.isa.sp m.regs) : SpBound C P lo N x :=
  spBound_of_match hM (Nat.le_refl _) (matchAt_room hM).1 (h.trans hM.sp)

/-- A step that stays in the running activation re-establishes the relation when the running
frame's locations hold the new frame and the frame's save words, every word above the frame and
the registers of the locations beyond it are unchanged. -/
theorem matchAt_local (hM : MatchAt C P AP σ lo N s m fn f a j)
    (hfn : s'.fn = s.fn) (hst : s'.stack = s.stack) (hw : m'.world = s'.world)
    (hh : s'.world.halted = false) (hwx : m'.mem.WxorX) (hF : Memory.Frame m.mem m'.mem)
    (hR : Region m'.mem lo N) (hpc : s'.pc ≤ fn.code.length)
    (hrip : A.isa.pc m'.regs = a + UInt64.ofNat (f.labelOff s'.pc))
    (hsp : A.isa.sp m'.regs = wa lo j)
    (hS : LocsOk lo C.k C.c (C.reg m'.regs) m'.mem j fn.frame s'.frame)
    (hsave : ∀ x, x < min C.k fn.frame → word m'.mem lo (j + x) = word m.mem lo (j + x))
    (hc : ∀ k, j + frameW C.k C.c fn.frame ≤ k → k < N → word m'.mem lo k = word m.mem lo k)
    (hreg : ∀ x, fn.frame ≤ x → x < C.k → C.reg m'.regs x = C.reg m.regs x)
    (hD : DataOk P σ lo m'.mem s'.mem) (hB : C.regOk σ m'.regs) :
    MatchAt C P AP σ lo N s' m' fn f a j := by
  have hfr := calleeFrame_eq hM.hfn
  have hdepth : s'.depth C.φ P = s.depth C.φ P := by simp [Lin.State.depth, hfn, hst]
  refine ⟨hw, hh, hwx, loaded_frame hM.loaded hM.wx hF, hR, hfn ▸ hM.hfn, hfn ▸ hM.hf, hM.addr,
    hM.ok, hpc, hrip, hsp, ?_, by rw [hdepth]; exact hM.depth, by rw [hfn, hst]; exact hM.chain, hD, hM.syms, hB⟩
  rw [hfn, hst]
  exact frames_update hM.frames (hfr ▸ hS) (hfr ▸ hsave) (hfr ▸ hc) (hfr ▸ hreg)

/-- A step that changes neither memory, the frame, the world, `sp` nor a location's register
re-establishes the relation at the new `pc`. -/
theorem matchAt_keep (hM : MatchAt C P AP σ lo N s m fn f a j)
    (hfn : s'.fn = s.fn) (hst : s'.stack = s.stack) (hfr : s'.frame = s.frame)
    (hmemL : s'.mem = s.mem) (hwL : s'.world = s.world) (hmem : m'.mem = m.mem)
    (hw : m'.world = m.world) (hsp : A.isa.sp m'.regs = A.isa.sp m.regs)
    (hpc : s'.pc ≤ fn.code.length) (hrip : A.isa.pc m'.regs = a + UInt64.ofNat (f.labelOff s'.pc))
    (hreg : ∀ x, x < C.k + C.c → C.reg m'.regs x = C.reg m.regs x) (hB : C.regOk σ m'.regs) :
    MatchAt C P AP σ lo N s' m' fn f a j :=
  matchAt_local hM hfn hst (hw.trans (hM.world.trans hwL.symm)) (hwL ▸ hM.run) (hmem ▸ hM.wx)
    (hmem ▸ Memory.Frame.refl _) (hmem ▸ hM.region) hpc hrip (hsp.trans hM.sp)
    (hmem ▸ hfr ▸ locsOk_view hreg hM.locs) (fun _ _ => by rw [hmem]) (fun _ _ _ => by rw [hmem])
    (fun x _ hx => hreg x (by omega)) (hmem ▸ hmemL ▸ hM.data) hB

/-- A `tick` has an empty block, so the relation holds at the next position with no machine
step. -/
theorem matchAt_tick (hM : MatchAt C P AP σ lo N s m fn f a j) {κ : CostModel} {ω : Oracle}
    {t : Flat.Tick} (hi : fn.code[s.pc]? = some (.tick t)) (hblk : f.blocks[s.pc]? = some []) :
    MatchAt C P AP σ lo N (Lin.exec κ ω fn (.tick t) s |>.getD s) m fn f a j := by
  have hlt := pc_lt hi
  refine matchAt_keep hM rfl rfl rfl rfl rfl rfl rfl rfl (by show s.pc + 1 ≤ _; omega) ?_
    (fun _ _ => rfl) hM.regOk
  rw [hM.rip, show ((Lin.exec κ ω fn (.tick t) s).getD s).pc = s.pc + 1 from rfl,
    labelOff_succ f hblk]; rfl

/-- A write to the data region that leaves every byte from `lo` up unchanged keeps the stack
words, and the data region then holds the new Lin heap. -/
theorem MatchAt.data_write (hM : MatchAt C P AP σ lo N s m fn f a j) {mem' : Memory} {D : UInt64}
    {h' : Flat.Heap} (hD : σ memSym = some D) (hR' : DataRel D P.mem mem' h')
    (hhi : ∀ y : UInt64, lo ≤ y.toNat → mem'.bytes y = m.mem.bytes y) :
    (∀ k, k < N → word mem' lo k = word m.mem lo k) ∧ DataOk P σ lo mem' h' := by
  obtain ⟨D', h1, h2, -⟩ := hM.data
  rw [hD] at h1; cases h1
  have htop := hM.region.top
  refine ⟨fun k hk => word_congr fun i hi => hhi _ ?_, D, hD, h2, hR'⟩
  rw [wa_add]; simp only [UInt64.toNat_ofNat']; omega

/-- The static stack bound leaves room for a callee's frame below the running one. -/
theorem MatchAt.room_call (hM : MatchAt C P AP σ lo N s m fn f a j)
    (hB : P.stackBytes C.φ ≤ 8 * N) {g : Nat} {args : List Operand} {d : Nat}
    (hi : fn.code[s.pc]? = some (.call g args d)) (hg : g < s.fn) {gf : Lin.Fn}
    (hgf : P.funs[g]? = some gf) : C.φ.frame gf.frame + C.dtop ≤ 8 * j := by
  have h1 := Lin.chain_le C.φ P s.stack s.fn hM.chain
  have h2 := Lin.need_call C.φ P s.fn fn hM.hfn g args d (List.mem_of_getElem? hi) hg
  have h3 := Lin.frameBytes_le C.φ P g
  have h4 := hM.depth
  simp only [Lin.Prog.frameBytes, hgf] at h3
  simp only [Lin.State.depth] at h4
  omega

/-- The relation at a callee's entry, for any number `k` of register locations. After a call
block and the callee's entry sequence, the callee's frame at word `j'` holds a frame `cf` in its
locations, the word above it holds the return address, and every word from `j` on is unchanged.
The caller's registers `x < min k G` that `keep` names, which include every one beyond the
caller's frame, are in the callee's frame words `x`, and its other location registers are
unchanged. The suspended caller's frame is then `savedFrame`. -/
theorem matchAt_call (hM : MatchAt C P AP σ lo N s m fn f a j) {g : Nat} {args : List Operand}
    {d : Nat} (hi : fn.code[s.pc]? = some (.call g args d)) (hg : g < s.fn) {gf : Lin.Fn}
    (hgf : P.funs[g]? = some gf) {fg : Asm.Fn A} (hfg : AP.funs[g]? = some fg) {ag : UInt64}
    (hag : σ fg.name = some ag) {j' : Nat} (hj : j' + C.next gf.frame = j)
    (hφ : C.φ.frame gf.frame = 8 * C.next gf.frame) (hw : m'.world = m.world)
    (hF : Memory.Frame m.mem m'.mem) (hlow : LowSame lo m.mem m'.mem) (hR : Region m'.mem lo N)
    (hok : C.ok ag lo j') (hpc : A.isa.pc m'.regs = ag + UInt64.ofNat (fg.labelOff 0))
    (hsp : A.isa.sp m'.regs = wa lo j')
    {cf : Flat.Frame} (hL : LocsOk lo C.k C.c (C.reg m'.regs) m'.mem j' gf.frame cf)
    (hra : word m'.mem lo (j' + frameW C.k C.c gf.frame) =
      a + UInt64.ofNat (f.labelOff s.pc + C.retOff P s.fn s.pc g args d))
    (hkeep : ∀ k, j ≤ k → k < N → word m'.mem lo k = word m.mem lo k) {keep : Nat → Bool}
    (hkF : ∀ x, fn.frame ≤ x → keep x = true)
    (hsave : ∀ x, x < min C.k gf.frame → keep x = true → word m'.mem lo (j' + x) = C.reg m.regs x)
    (hreg : ∀ x, min C.k gf.frame ≤ x → x < C.k → C.reg m'.regs x = C.reg m.regs x)
    (hB : C.regOk σ m'.regs) :
    MatchAt C P AP σ lo N ⟨g, 0, cf,
      ⟨s.fn, s.pc + 1, savedFrame lo C.k gf.frame keep m'.mem j' s.frame, d⟩ :: s.stack, s.mem,
      s.world, s.clock⟩ m' gf fg ag j' := by
  have hfr := calleeFrame_eq (P := P) hgf
  have hfn := calleeFrame_eq (P := P) hM.hfn
  have hlocs := hM.locs
  refine ⟨hw.trans hM.world, hM.run, hF.wxorx hM.wx, loaded_frame hM.loaded hM.wx hF, hR, hgf,
    hfg, hag, hok, Nat.zero_le _, hpc, hsp,
    frames_call hM.frames ⟨rfl, rfl⟩ (by rw [hfr]; exact hj) (hfr ▸ hL)
      ⟨fn, args, f, a, hM.hfn, Nat.succ_pos _, by simpa using hi, hM.hf, hM.addr,
        by rw [hfr]; simpa using hra⟩ hkeep (fun x hx => ?_) (fun x hx hx' => ?_)
      (hfr ▸ hreg), ?_,
    ⟨Lin.need_call C.φ P s.fn fn hM.hfn g args d (List.mem_of_getElem? hi) hg, hM.chain⟩,
    dataOk_keep (by have := hR.top; omega) hM.data hF hlow, hM.syms, hB⟩
  · rw [hfr] at hx; rw [hfn]
    simp only [savedFrame]
    cases hk : keep x
    · have hxF : x < fn.frame := by
        by_cases h : fn.frame ≤ x
        · rw [hkF x h] at hk; cases hk
        · omega
      rw [ite_eq_left hxF, ite_eq_left ⟨hx, rfl⟩]
    · rw [hsave x hx hk]
      split
      · rw [ite_eq_right (by simp [hk])]
        have := hlocs x ‹_›; rwa [ite_eq_left (by omega)] at this
      · rfl
  · rw [hfr] at hx'; simp only [savedFrame]; rw [ite_eq_right (by omega)]
  · have hd := hM.depth
    simp only [Lin.State.depth, List.map_cons, List.sum_cons, Lin.Prog.frameBytes, hgf] at hd ⊢
    omega

/-- The caller of the running activation has a function, a call at the position before its
return position, a return address in the word above the running frame, and room for its frame
in the region. -/
theorem MatchAt.caller (hM : MatchAt C P AP σ lo N s m fn f a j) {act : Lin.Act}
    {st : List Lin.Act} (hst : s.stack = act :: st) :
    ∃ (fa : Lin.Fn) (args : List Operand) (fc : Asm.Fn A) (addr : UInt64),
      P.funs[act.fn]? = some fa ∧ AP.funs[act.fn]? = some fc ∧ σ fc.name = some addr ∧
      0 < act.pc ∧ fa.code[act.pc - 1]? = some (.call s.fn args act.dst) ∧
      word m.mem lo (j + frameW C.k C.c fn.frame) =
        addr + UInt64.ofNat (fc.labelOff (act.pc - 1) + C.retOff P act.fn (act.pc - 1) s.fn args act.dst) ∧
      j + C.next fn.frame + frameW C.k C.c fa.frame ≤ N := by
  have hFr := hM.frames
  rw [hst] at hFr
  obtain ⟨-, ⟨fa, args, fc, addr, hfa, hpc0, hcall, hfc, hσ, hra⟩, _, -, hFr'⟩ := hFr
  have := (frames_le _ _ _ _ _ hFr').1
  rw [calleeFrame_eq hM.hfn] at hra this
  rw [calleeFrame_eq hfa] at this
  exact ⟨fa, args, fc, addr, hfa, hfc, hσ, hpc0, hcall, hra, this⟩

/-- The relation back in the caller, for any number `k` of register locations. After a return
sequence and the caller's result stores, the caller's frame at `j' = j + next F` holds `fr'` in
its locations, read in the registers. Its save words and every word above it are unchanged, and
the registers of the locations beyond its frame hold what `callerView` gives, as the callee's
restores left them. -/
theorem matchAt_ret (hM : MatchAt C P AP σ lo N s m fn f a j) {act : Lin.Act}
    {st : List Lin.Act} (hst : s.stack = act :: st) {fa : Lin.Fn} (hfa : P.funs[act.fn]? = some fa)
    {fc : Asm.Fn A} (hfc : AP.funs[act.fn]? = some fc) {addr : UInt64}
    (haddr : σ fc.name = some addr) (hpcL : act.pc ≤ fa.code.length) {j' : Nat}
    (hj : j' = j + C.next fn.frame) (hφ : C.φ.frame fn.frame = 8 * C.next fn.frame)
    (hw : m'.world = m.world) (hF : Memory.Frame m.mem m'.mem) (hlow : LowSame lo m.mem m'.mem)
    (hR : Region m'.mem lo N) (hok : C.ok addr lo j')
    (hpc : A.isa.pc m'.regs = addr + UInt64.ofNat (fc.labelOff act.pc))
    (hsp : A.isa.sp m'.regs = wa lo j') {fr' : Flat.Frame}
    (hL : LocsOk lo C.k C.c (C.reg m'.regs) m'.mem j' fa.frame fr')
    (hsave : ∀ x, x < min C.k fa.frame → word m'.mem lo (j' + x) = word m.mem lo (j' + x))
    (hc : ∀ i, j' + frameW C.k C.c fa.frame ≤ i → i < N → word m'.mem lo i = word m.mem lo i)
    (hreg : ∀ x, fa.frame ≤ x → x < C.k →
      C.reg m'.regs x = callerView lo C.k m.mem j fn.frame (C.reg m.regs) x)
    (hB : C.regOk σ m'.regs) :
    MatchAt C P AP σ lo N ⟨act.fn, act.pc, fr', st, s.mem, s.world, s.clock⟩ m' fa fc addr j' := by
  have hFr := hM.frames
  rw [hst] at hFr
  have hfr := calleeFrame_eq (P := P) hfa
  obtain ⟨rv₀, hv₀, hFr'⟩ := frames_ret hFr
  rw [calleeFrame_eq hM.hfn] at hFr' hv₀
  rw [← hj] at hFr'
  refine ⟨hw.trans hM.world, hM.run, hF.wxorx hM.wx, loaded_frame hM.loaded hM.wx hF, hR, hfa,
    hfc, haddr, hok, hpcL, hpc, hsp,
    frames_update hFr' (hfr ▸ hL) (hfr ▸ hsave) (hfr ▸ hc)
      (fun x h1 h2 => by rw [hfr] at h1; exact (hreg x h1 h2).trans (hv₀ x h2).symm), ?_,
    by have := hM.chain; rw [hst] at this; exact this.2,
    dataOk_keep (by have := hR.top; omega) hM.data hF hlow, hM.syms, hB⟩
  have hd := hM.depth
  simp only [Lin.State.depth, hst, List.map_cons, List.sum_cons, Lin.Prog.frameBytes,
    hM.hfn] at hd ⊢
  omega

end Match

/-! ## The instruction at the running position -/

section Ctx
variable {D : Selector A}

/-- Everything known about the instruction at the running position of a program selected by
`Sel.select D`. -/
structure Ctx (D : Selector A) (P : Lin.Prog) (AP : Asm.Prog A) (σ : String → Option UInt64)
    (s : Lin.State) (m : MState A.isa.Regs) (fn : Lin.Fn) (f : Asm.Fn A) (a : UInt64)
    (ins : Lin.Instr) (b : List A.SInstr) : Prop where
  sel : SelFn D P s.fn fn f AP.data
  blk : f.blocks[s.pc]? = some b
  instr : ∃ d, D.instr P s.fn s.pc fn ins = .ok (b, d) ∧ ∀ x ∈ d, x ∈ AP.data
  code : SeqAt m.mem (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b
  wf : ins.Wf P s.fn fn.frame fn.code.length
  fwf : fn.Wf P s.fn
  mem : f ∈ AP.funs
  nblocks : f.blocks.length = fn.code.length

theorem ctx_of {asm : Asm.Assembler A} (hl : asm.Laws) (hsel : select D P = .ok AP) (hwf : P.Wf)
    {s : Lin.State} {m : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A} {a : UInt64} {j : Nat}
    (hM : MatchAt C P AP σ lo N s m fn f a j) {ins : Lin.Instr} (hi : fn.code[s.pc]? = some ins) :
    ∃ b, Ctx D P AP σ s m fn f a ins b := by
  obtain ⟨_, _, _, hk⟩ := select_spec hsel
  obtain ⟨f', hf', hsf⟩ := hk s.fn fn hM.hfn
  rw [hM.hf] at hf'; cases hf'
  obtain ⟨d, hc, hd⟩ := hsf.code
  obtain ⟨hnb, hk'⟩ := selCode_spec fn.code 0 f.blocks d hc
  obtain ⟨b, d', hb, hsi, hd'⟩ := hk' s.pc ins hi
  have hmem : f ∈ AP.funs := List.mem_of_getElem? hM.hf
  obtain ⟨a', ha', _, hblk⟩ := fn_code hl hM.loaded hmem
  rw [hM.addr] at ha'; cases ha'
  exact ⟨b, ⟨hsf, hb, ⟨d', by simpa using hsi, fun x hx => hd x (hd' x hx)⟩,
    hblk s.pc b hb, (hwf.2 s.fn fn hM.hfn).2 ins (List.mem_of_getElem? hi), hwf.2 s.fn fn hM.hfn,
    hmem, hnb⟩⟩

/-- For any position `p` of a selected and loaded function `g`, the block that `select`
produced for it is in memory at its label. -/
theorem block_at {asm : Asm.Assembler A} (hl : asm.Laws) (hsel : select D P = .ok AP) {m : Memory}
    (hL : AP.Loaded σ m) {g p : Nat} {fa : Lin.Fn} {fc : Asm.Fn A} {addr : UInt64}
    (hfa : P.funs[g]? = some fa) (hfc : AP.funs[g]? = some fc) (hσ : σ fc.name = some addr)
    {ins : Lin.Instr} (hi : fa.code[p]? = some ins) :
    ∃ b d, fc.blocks[p]? = some b ∧ D.instr P g p fa ins = .ok (b, d) ∧
      SeqAt m (fc.refAddr σ addr) (addr + UInt64.ofNat (fc.labelOff p)) b ∧ SelFn D P g fa fc AP.data := by
  obtain ⟨_, _, _, hk⟩ := select_spec hsel
  obtain ⟨f', hf', hsf⟩ := hk g fa hfa
  rw [hfc] at hf'; cases hf'
  obtain ⟨d, hc, -⟩ := hsf.code
  obtain ⟨-, hk'⟩ := selCode_spec fa.code 0 fc.blocks d hc
  obtain ⟨b, d', hb, hsi, -⟩ := hk' p ins hi
  obtain ⟨a', ha', _, hblk⟩ := fn_code hl hL (List.mem_of_getElem? hfc)
  rw [hσ] at ha'; cases ha'
  exact ⟨b, d', hb, by simpa using hsi, hblk p b hb, hsf⟩

end Ctx

/-! ## Straight-line blocks -/

/-- A block of straight-line code that runs from a related state to a state whose locations hold
the next Lin state's frame, with the words above the frame and the data region as required, is
matched. The machine reaches the next label in a related state and keeps `sp` throughout. -/
theorem sim_straight {asm : Asm.Assembler A} (hl : asm.Laws) (hil : A.isa.Laws) {abi : Abi A.isa}
    {ω : Oracle} {s s' : Lin.State} {m m' : MState A.isa.Regs} {fn : Lin.Fn} {f : Asm.Fn A}
    {a : UInt64} {j : Nat} (hM : MatchAt C P AP σ lo N s m fn f a j) {b : List A.SInstr}
    (hblk : f.blocks[s.pc]? = some b) (hlt : s.pc < fn.code.length)
    {is : List A.isa.Instr} {code : List UInt8}
    (hr : Asm.resolveAt A (f.refAddr σ a) (a + UInt64.ofNat (f.labelOff s.pc)) b = some is)
    (he : Asm.encodeAll A.isa is = some code)
    (hcode : m.mem.CodeAt (a + UInt64.ofNat (f.labelOff s.pc)) code)
    (hs : ∀ i ∈ is, StraightC C abi ω i) (hrun : runIs abi ω is m = some m')
    (hw : m'.world = s'.world) (hh : s'.world.halted = false) (hfn : s'.fn = s.fn)
    (hst : s'.stack = s.stack) (hpc : s'.pc = s.pc + 1)
    (hS : LocsOk lo C.k C.c (C.reg m'.regs) m'.mem j fn.frame s'.frame)
    (hsave : ∀ x, x < min C.k fn.frame → word m'.mem lo (j + x) = word m.mem lo (j + x))
    (hc : ∀ k, j + frameW C.k C.c fn.frame ≤ k → k < N → word m'.mem lo k = word m.mem lo k)
    (hreg : ∀ x, fn.frame ≤ x → x < C.k → C.reg m'.regs x = C.reg m.regs x)
    (hD : DataOk P σ lo m'.mem s'.mem) (c : Nat) :
    (M abi).run ω (m, c) is.length = some (m', c + is.length) ∧
      MatchAt C P AP σ lo N s' m' fn f a j ∧
      RunAll abi ω (fun x => A.isa.sp x.regs = A.isa.sp m.regs) (m, c) is.length := by
  obtain ⟨hrun', hF, hwx', hpc', hall⟩ :=
    run_straight (abi := abi) hil c hM.wx he (by rw [hM.rip]; exact hcode) (fun i h => (hs i h).1) hrun
  have hsp : A.isa.sp m'.regs = A.isa.sp m.regs := hall _ (Nat.le_refl _) _ hrun'
  refine ⟨hrun', matchAt_local hM hfn hst hw hh hwx' hF (region_frame hM.region hF)
    (by rw [hpc]; omega) ?_ (hsp.trans hM.sp) hS hsave hc hreg hD (runIs_regOk hs hrun hM.regOk), hall⟩
  rw [hpc', hM.rip, hpc]; exact next_pc hl hblk hr he

end Millipede.Sel
