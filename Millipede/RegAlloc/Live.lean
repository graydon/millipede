import Millipede.RegAlloc.Sound

/-!
# Validated live sets of an allocated program

The selectors need to know which locations hold a value that is still needed at each position of
the allocated Lin program, because a location that is dead after a call needs no save and one that
is dead after an instruction may be destroyed by it. The live sets give, for each function and
position, the live locations. They are computed by running the allocator's untrusted liveness on
the allocated program, and validated by the allocation checker itself, which checks the program
against itself with the map `{(x, x) | x ∈ live}` at each position.

That check is exactly the consistency of backward dataflow. An operand read at a position is live
there, what is live at a successor is live before the instruction or defined by it, every call's
arguments serve the callee's entry set, the returned operands are live at `ret`, and at a join
every predecessor carries the join's set. No second checker or soundness proof is needed, because
`step_sim` turns the accepted check into a lock-step simulation of the program by itself. Its
relation says only that the live locations agree, in the running frame at its position and in each
suspended frame at its return position for every list of results.

`Live.of P` is the checked sets, or `none` when the check fails, in which case every location
counts as live. `Live.flex P` is the self-simulation, and `keepCall` is the save set of a call
site. A register location is saved when it is live after the call and is not one of the call's
results, when the caller's frame does not reach it because it belongs to a deeper activation, or
when it is an argument, since the call sequence reads arguments back from the save words. A call
writes only the callee's locations live at its entry (`R_call`).
-/

namespace Millipede.RegAlloc

open Flat (Operand Frame)
open Lin (Instr Prog)

/-- The live locations of each position of each function. -/
abbrev LiveSets := List (List (List Nat))

/-- The live set at position `pc` of function `i`, which is `[]` when absent. -/
def liveAt (lv : LiveSets) (i pc : Nat) : List Nat := (lv.getD i []).getD pc []

/-- The live sets as location maps of the program to itself, with `(x, x)` for each live `x`. -/
def idMaps (lv : LiveSets) : List (List LocMap) := lv.map (·.map (·.map fun x => (x, x)))

theorem mapOf_idMaps (lv : LiveSets) (i pc : Nat) :
    mapOf (idMaps lv) i pc = (liveAt lv i pc).map fun x => (x, x) := by
  simp only [mapOf, idMaps, liveAt, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases lv[i]? <;> simp only [Option.map_none, Option.getD_none, List.getElem?_nil,
    Option.map_some, Option.getD_some, List.getElem?_map, List.map_nil]
  rename_i l
  cases l[pc]? <;> rfl

namespace Live

/-- The untrusted live sets of a program, from the allocator's liveness of each function in index
order, since a call uses the argument positions live at its callee's entry. -/
def compute (P : Prog) : LiveSets := Id.run do
  let mut res : Array (List (List Nat)) := #[]
  for fn in P.funs do
    let entry := fun g => ((res[g]?).map fun l => l.headD []).getD []
    let code := fn.code.toArray
    let infos := (Array.range code.size).map fun pc => Alloc.info P fn entry pc code[pc]!
    res := res.push (Alloc.liveness infos).toList
  return res.toList

/-- The validated live sets, which are `compute P` if the checker accepts it against `P` itself. -/
def of (P : Prog) : Option LiveSets :=
  let c := compute P
  if check P P (idMaps c) then some c else none

/-- Whether location `x` is live at position `pc` of function `i`, which always holds without live
sets. -/
def liveIn (lvo : Option LiveSets) (i pc x : Nat) : Bool :=
  match lvo with
  | none => true
  | some lv => (liveAt lv i pc).contains x

/-- The save set of a call `call g args d` with `n` results at position `pc` of function `i`, whose
frame has `F` slots. Location `x` is kept when the caller's frame does not reach it, when it is
live after the call and not a result, or when it is an argument. -/
def keepCall (lvo : Option LiveSets) (i pc F d n : Nat) (args : List Operand) (x : Nat) : Bool :=
  lvo.isNone || decide (F ≤ x) || (liveIn lvo i (pc + 1) x && !(decide (d ≤ x) && decide (x < d + n))) ||
    args.contains (.slot x)

/-- The save set of the call `call g args d` at position `pc` of function `i` of `P`, as the
selectors use it, with the caller's frame and the callee's number of results. -/
def callKeep (lvo : Option LiveSets) (P : Prog) (i pc g d : Nat) (args : List Operand) :
    Nat → Bool :=
  keepCall lvo i pc (Sel.calleeFrame P i) d (retLen P g) args

/-- The locations instruction `ins` defines: its destination, or a call's result locations. -/
def defs (P : Prog) : Instr → Nat → Bool
  | .mov x _ => (· == x)
  | .bin _ x _ _ => (· == x)
  | .load _ x _ _ => (· == x)
  | .ext _ _ x _ => (· == x)
  | .call g _ d => fun y => decide (d ≤ y) && decide (y < d + retLen P g)
  | _ => fun _ => false

/-- The clobber check: no location live after an instruction is one that the instruction's code
destroys, `kill ins x`, unless the instruction defines it. "After" is position `pc + 1` of the same
function, which for a call is its return position, so a location a call destroys is not live
across the call. It fails without live sets, in which every location counts as live. -/
def clobOk (kill : Instr → Nat → Bool) (lvo : Option LiveSets) (P : Prog) : Bool :=
  match lvo with
  | none => false
  | some lv => all2 (fun i fn _ => all2 (fun pc ins _ =>
      (liveAt lv i (pc + 1)).all fun x => !kill ins x || defs P ins x) 0 fn.code fn.code) 0 P.funs P.funs

theorem clobOk_spec {kill : Instr → Nat → Bool} {lv : LiveSets} {P : Prog}
    (h : clobOk kill (some lv) P = true) {i pc x : Nat} {fn : Lin.Fn} {ins : Instr}
    (hfn : P.funs[i]? = some fn) (hi : fn.code[pc]? = some ins) (hx : x ∈ liveAt lv i (pc + 1))
    (hk : kill ins x = true) : defs P ins x = true := by
  obtain ⟨-, h1⟩ := all2_spec h
  obtain ⟨_, -, h2⟩ := h1 i fn hfn
  obtain ⟨-, h3⟩ := all2_spec h2
  obtain ⟨_, -, h4⟩ := h3 pc ins hi
  simp only [Nat.zero_add, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h4
  rcases h4 x hx with h | h
  · rw [hk] at h; cases h
  · exact h

/-- The relation of states that agree on their live locations, which is equality without live
sets. -/
def R (P : Prog) : Lin.State → Lin.State → Prop :=
  match of P with
  | some lv => Rel P (idMaps lv)
  | none => Eq

theorem agree_refl (L : List Nat) (f : Frame) : Agree (L.map fun x => (x, x)) f f := by
  intro p hp; simp only [List.mem_map] at hp; obtain ⟨x, -, rfl⟩ := hp; rfl

theorem agree_trans {L : List Nat} {f g h : Frame} (h1 : Agree (L.map fun x => (x, x)) f g)
    (h2 : Agree (L.map fun x => (x, x)) g h) : Agree (L.map fun x => (x, x)) f h := by
  intro p hp
  have e1 := h1 p hp; have e2 := h2 p hp
  simp only [List.mem_map] at hp; obtain ⟨x, -, rfl⟩ := hp
  exact e2.trans e1

theorem stackRel_refl (P : Prog) (lv : LiveSets) : ∀ (g : Nat) (st : List Lin.Act),
    StackRel P (idMaps lv) g st st
  | _, [] => trivial
  | _, a :: st => ⟨rfl, rfl, fun _ _ => by rw [mapOf_idMaps]; exact agree_refl _ _,
      stackRel_refl P lv a.fn st⟩

theorem stackRel_trans (P : Prog) (lv : LiveSets) : ∀ (g : Nat) (s₁ s₂ s₃ : List Lin.Act),
    StackRel P (idMaps lv) g s₁ s₂ → StackRel P (idMaps lv) g s₂ s₃ → StackRel P (idMaps lv) g s₁ s₃
  | _, [], [], [], _, _ => trivial
  | _, a :: s₁, b :: s₂, c :: s₃, ⟨hf, hp, hA, hS⟩, ⟨hf', hp', hA', hS'⟩ => by
    refine ⟨hf'.trans hf, hp'.trans hp, fun vs hl => ?_, ?_⟩
    · have h1 := hA vs hl; have h2 := hA' vs hl
      rw [hf, hp] at h2; rw [mapOf_idMaps] at h1 h2 ⊢; exact agree_trans h1 h2
    · rw [hf] at hS'; exact stackRel_trans P lv a.fn s₁ s₂ s₃ hS hS'
  | _, [], _ :: _, _, h, _ => h.elim
  | _, _ :: _, [], _, h, _ => h.elim
  | _, [], [], _ :: _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, h => h.elim

theorem rel_refl (P : Prog) (lv : LiveSets) (s : Lin.State) : Rel P (idMaps lv) s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, by rw [mapOf_idMaps]; exact agree_refl _ _, stackRel_refl P lv _ _⟩

theorem rel_trans (P : Prog) (lv : LiveSets) {a b c : Lin.State} (h1 : Rel P (idMaps lv) a b)
    (h2 : Rel P (idMaps lv) b c) : Rel P (idMaps lv) a c := by
  have hfr := h2.frame; have hst := h2.stack
  have hf1 := h1.frame
  rw [h1.fn] at hst; rw [h1.fn, h1.pc] at hfr
  rw [mapOf_idMaps] at hfr hf1
  exact ⟨h2.fn.trans h1.fn, h2.pc.trans h1.pc, h2.mem.trans h1.mem, h2.world.trans h1.world,
    h2.clock.trans h1.clock, by rw [mapOf_idMaps]; exact agree_trans hf1 hfr,
    stackRel_trans P lv _ _ _ _ h1.stack hst⟩

theorem of_check {P : Prog} {lv : LiveSets} (h : of P = some lv) : check P P (idMaps lv) = true := by
  dsimp only [of] at h; split at h
  · cases h; assumption
  · cases h

/-- The self-simulation of a program up to dead locations. -/
def flex (P : Prog) : Flex P where
  R := R P
  refl s := by
    cases h : of P <;> simp only [R, h]
    exact rel_refl P _ s
  trans {a b c} h1 h2 := by
    cases h : of P <;> simp only [R, h] at h1 h2 ⊢
    · exact h1.trans h2
    · exact rel_trans P _ h1 h2
  step {κ ω s t s'} hR hs := by
    cases h : of P <;> simp only [R, h] at hR ⊢
    · subst hR; exact ⟨s', hs, rfl⟩
    · exact step_sim (checked_of (of_check h)) hR hs
  same {s t} hR := by
    cases h : of P <;> simp only [R, h] at hR
    · subst hR; exact ⟨rfl, rfl, rfl⟩
    · exact ⟨hR.fn, hR.pc, hR.world⟩

/-- A state whose running frame has changed only at locations dead at its position is related to
the original. -/
theorem R_frame (P : Prog) {lv : LiveSets} (hlv : of P = some lv) (s : Lin.State) {fr : Frame}
    (h : ∀ x ∈ liveAt lv s.fn s.pc, fr x = s.frame x) : R P s { s with frame := fr } := by
  simp only [R, hlv]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, stackRel_refl P lv _ _⟩
  rw [mapOf_idMaps]
  intro p hp
  simp only [List.mem_map] at hp; obtain ⟨x, hx, rfl⟩ := hp
  exact h x hx

/-- After an instruction that passed the clobber check, a frame that differs from the next state's
only at locations the instruction destroys and does not define is related to it. -/
theorem R_kill (P : Prog) {kill : Instr → Nat → Bool} (hc : clobOk kill (of P) P = true)
    {i pc : Nat} {fn : Lin.Fn} {ins : Instr} (hfn : P.funs[i]? = some fn)
    (hi : fn.code[pc]? = some ins) {fr fr' : Frame} {st : List Lin.Act} {mem : Flat.Heap}
    {w : World} {clk : Nat} (h : ∀ x, kill ins x = false ∨ defs P ins x = true → fr' x = fr x) :
    R P ⟨i, pc + 1, fr, st, mem, w, clk⟩ ⟨i, pc + 1, fr', st, mem, w, clk⟩ := by
  cases hlv : of P with
  | none => rw [hlv] at hc; cases hc
  | some lv =>
    rw [hlv] at hc
    refine R_frame P hlv ⟨i, pc + 1, fr, st, mem, w, clk⟩ fun x hx => h x ?_
    cases hk : kill ins x
    · exact Or.inl rfl
    · exact Or.inr (clobOk_spec hc hfn hi hx hk)

/-- The callee's entry state whose frame has changed only at locations dead at the callee's
entry, and whose suspended caller's frame has changed only at locations the call does not keep,
is related to the true one, so a call need not write those callee locations or save those caller
locations. -/
theorem R_call (P : Prog) {g i pc d F : Nat} {args : List Operand} {cf cf' fr fr' : Frame}
    {st : List Lin.Act} {mem : Flat.Heap} {w : World} {clk : Nat}
    (hc : ∀ x, liveIn (of P) g 0 x = true → cf' x = cf x)
    (h : ∀ x, keepCall (of P) i pc F d (retLen P g) args x = true → fr' x = fr x) :
    R P ⟨g, 0, cf, ⟨i, pc + 1, fr, d⟩ :: st, mem, w, clk⟩
      ⟨g, 0, cf', ⟨i, pc + 1, fr', d⟩ :: st, mem, w, clk⟩ := by
  cases hlv : of P with
  | none =>
    have : fr' = fr := funext fun x => h x (by simp [keepCall, liveIn, hlv])
    have hcf : cf' = cf := funext fun x => hc x (by simp [liveIn, hlv])
    subst this hcf; simp only [R, hlv]
  | some lv =>
    simp only [R, hlv]
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ⟨rfl, rfl, fun vs hl => ?_, stackRel_refl P lv _ _⟩⟩
    · rw [mapOf_idMaps]
      intro p hp
      simp only [List.mem_map] at hp; obtain ⟨x, hx, rfl⟩ := hp
      exact hc x (by simp [liveIn, hlv, hx])
    rw [mapOf_idMaps]
    intro p hp
    simp only [List.mem_map] at hp; obtain ⟨x, hx, rfl⟩ := hp
    show Frame.writes fr' d vs x = Frame.writes fr d vs x
    rw [Sel.writes_apply, Sel.writes_apply]
    split
    · rfl
    · rename_i hn
      refine h x ?_
      simp only [keepCall, liveIn, hlv, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        Bool.and_eq_false_iff, decide_eq_false_iff_not, List.contains_iff_mem, hx, true_and]
      exact Or.inl (Or.inr (by rw [← hl] at *; omega))

end Live

end Millipede.RegAlloc
