import Millipede.Compile.Lin
import Millipede.Target.PMove

/-!
# The arguments of a call sequence

Both register selectors pass the arguments of a call to `g`, whose frame has `G` words, as the
padded list `padArgs G args`: the arguments followed by zeros. Argument `x` goes into `g`'s
location `x`. With `k` preserved and `c` caller-saved register locations, the arguments
`k … min (k + c) G - 1` (`cArgs`) go into caller-saved registers. Those whose operand is itself in
a caller-saved register form a parallel move (`cMoves`), which `PMove.seq` sequentialises; the
others are loaded after it. This module holds these definitions and their facts, for any register
type and any map `loc` from locations to registers.

The returned words travel by parallel moves too, between places that are registers or operands
(`Place`): `ret` moves its operands into the result registers (`retMoves`), and the caller moves
the result registers into the result locations (`resMoves`), so an operand may sit in a result
register and a result may stay in the register it arrives in.
-/

namespace Millipede.Sel

open Flat (Operand)

/-- Exactly `n` operands, the arguments followed by immediate zeros. -/
def padArgs (n : Nat) (args : List Operand) : List Operand :=
  (args ++ List.replicate (n - args.length) (Operand.imm 0)).take n

theorem padArgs_length (G : Nat) (args : List Operand) : (padArgs G args).length = G := by
  simp [padArgs]; omega

theorem padArgs_below {G F : Nat} {args : List Operand} (h : Lin.OpsBelow args F) :
    Lin.OpsBelow (padArgs G args) F := by
  intro y hy
  have := List.mem_of_mem_take hy
  rcases List.mem_append.1 this with h1 | h1
  · exact h y h1
  · simp at h1

theorem padArgs_val {G : Nat} {args : List Operand} (_h : args.length ≤ G) (fr : Flat.Frame)
    {x : Nat} (hx : x < G) :
    ((padArgs G args).map (Operand.eval fr)).getD x 0 = (args.map (Operand.eval fr)).getD x 0 := by
  simp only [padArgs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, hx,
    ite_true, List.getElem?_append]
  by_cases hl : x < args.length
  · simp [hl]
  · simp [hl, List.getElem?_replicate]
    split <;> rfl

theorem pad_drop {G n x : Nat} {args : List Operand} (hargs : args.length ≤ G) (hx : n ≤ x)
    (hxG : x < G) (fr : Flat.Frame) :
    (((padArgs G args).drop n).map (Operand.eval fr)).getD (x - n) 0 =
      (args.map (Operand.eval fr)).getD x 0 := by
  rw [← padArgs_val hargs fr hxG]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
    show n + (x - n) = x by omega]

theorem pad_take {G n x : Nat} {args : List Operand} (hargs : args.length ≤ G) (hx : x < n)
    (hnG : n ≤ G) (fr : Flat.Frame) :
    (((padArgs G args).take n).map (Operand.eval fr)).getD x 0 =
      (args.map (Operand.eval fr)).getD x 0 := by
  rw [← padArgs_val hargs fr (show x < G by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, hx, ite_true]

/-- An operand of the padded argument list that is a slot is an argument. -/
theorem slot_of_pad {G n y : Nat} {args : List Operand}
    (h : Operand.slot y ∈ (padArgs G args).take n) : Operand.slot y ∈ args := by
  have h1 := List.mem_of_mem_take (List.mem_of_mem_take h)
  rcases List.mem_append.1 h1 with h2 | h2
  · exact h2
  · simp at h2

theorem slot_of_pad_drop {G n y : Nat} {args : List Operand}
    (h : Operand.slot y ∈ (padArgs G args).drop n) : Operand.slot y ∈ args := by
  have h1 := List.mem_of_mem_take (List.mem_of_mem_drop h)
  rcases List.mem_append.1 h1 with h2 | h2
  · exact h2
  · simp at h2

/-! ## The caller-saved register arguments -/

/-- The caller-saved register arguments of a callee of `G` slots, which are the arguments
`k … min (k + c) G - 1`. -/
def cArgs (k c G : Nat) (args : List Operand) : List Operand :=
  ((padArgs G args).drop k).take (min (k + c) G - k)

theorem cArgs_length {k c G : Nat} {args : List Operand} (hargs : args.length ≤ G) :
    (cArgs k c G args).length = min (k + c) G - k := by
  simp only [cArgs, List.length_take, List.length_drop, padArgs_length]; omega

theorem cArgs_val {k c G : Nat} {args : List Operand} (hargs : args.length ≤ G) (fr : Flat.Frame)
    {i : Nat} (hi : i < (cArgs k c G args).length) :
    ((cArgs k c G args)[i]?.getD (.imm 0)).eval fr = (args.map (Operand.eval fr)).getD (k + i) 0 := by
  rw [cArgs_length hargs] at hi
  rw [← padArgs_val hargs fr (show k + i < G by omega)]
  simp only [cArgs, List.getElem?_take, show i < min (k + c) G - k from hi, ite_true,
    List.getElem?_drop, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (padArgs G args)[k + i]? <;> rfl

theorem cArgs_below {k c G F : Nat} {args : List Operand} (h : Lin.OpsBelow args F) :
    Lin.OpsBelow (cArgs k c G args) F :=
  fun y hy => padArgs_below h y (List.mem_of_mem_drop (List.mem_of_mem_take hy))

theorem cArgs_slot {k c G y : Nat} {args : List Operand} (h : Operand.slot y ∈ cArgs k c G args) :
    Operand.slot y ∈ args :=
  slot_of_pad_drop (List.mem_of_mem_take h)

/-- Whether an operand is in a caller-saved location. -/
def isC (k c : Nat) : Operand → Bool
  | .slot y => decide (k ≤ y) && decide (y < k + c)
  | _ => false

variable {R : Type} [DecidableEq R]

/-- The register of a register operand under the location map `loc`, and `d` for others. -/
def oreg (loc : Nat → R) (d : R) : Operand → R
  | .slot y => loc y
  | _ => d

/-- The moves of the caller-saved register arguments `j, j+1, …` that `ent` names and whose
operand is in a caller-saved location, which form a parallel move. -/
def cMoves (loc : Nat → R) (d : R) (k c : Nat) (ent : Nat → Bool) : Nat → List Operand → List (R × R)
  | _, [] => []
  | j, o :: os => (if ent j && isC k c o then [(loc j, oreg loc d o)] else []) ++
      cMoves loc d k c ent (j + 1) os

variable {loc : Nat → R} {d : R} {k c : Nat}

/-- The moves of the caller-saved register arguments `l, l+1, …` are those of the operands in
caller-saved locations that `ent` names, into their registers. -/
theorem mem_cMoves (ent : Nat → Bool) : ∀ (l : Nat) (os : List Operand) {p : R × R},
    p ∈ cMoves loc d k c ent l os → ∃ i, i < os.length ∧ ent (l + i) = true ∧
      isC k c (os[i]?.getD (.imm 0)) = true ∧ p = (loc (l + i), oreg loc d (os[i]?.getD (.imm 0)))
  | _, [], _, h => by simp [cMoves] at h
  | l, o :: os, p, h => by
    simp only [cMoves, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i hc
        simp only [List.mem_singleton] at h; subst h
        simp only [Bool.and_eq_true] at hc
        exact ⟨0, by simp, by simpa using hc.1, by simpa using hc.2, by simp⟩
      · simp at h
    · obtain ⟨i, hi, h1, h2, rfl⟩ := mem_cMoves ent (l + 1) os h
      exact ⟨i + 1, by simp; omega, by rw [← h1]; congr 1; omega, by simpa using h2,
        by simp [show l + 1 + i = l + (i + 1) by omega]⟩

theorem cMoves_of (ent : Nat → Bool) : ∀ (l : Nat) (os : List Operand) (i : Nat),
    i < os.length → ent (l + i) = true → isC k c (os[i]?.getD (.imm 0)) = true →
    (loc (l + i), oreg loc d (os[i]?.getD (.imm 0))) ∈ cMoves loc d k c ent l os
  | _, [], _, h, _, _ => by simp at h
  | l, o :: os, 0, _, he, hc => by
    simp only [cMoves, List.mem_append]
    left; simp only [Nat.add_zero] at he; simp [he, show isC k c o = true by simpa using hc]
  | l, o :: os, i + 1, hi, he, hc => by
    simp only [cMoves, List.mem_append]
    right
    have := cMoves_of ent (l + 1) os i (by simp at hi; omega) (by rw [← he]; congr 1; omega)
      (by simpa using hc)
    simpa [show l + 1 + i = l + (i + 1) by omega] using this

/-- The moves have distinct destinations when `loc` is injective below `k + c`. -/
theorem cMoves_nodup (hinj : ∀ x y, x < k + c → y < k + c → loc x = loc y → x = y)
    (ent : Nat → Bool) : ∀ (l : Nat) (os : List Operand), l + os.length ≤ k + c →
      ((cMoves loc d k c ent l os).map (·.1)).Nodup
  | _, [], _ => by simp [cMoves]
  | l, o :: os, h => by
    simp only [List.length_cons] at h
    simp only [cMoves, List.map_append, List.nodup_append]
    refine ⟨by split <;> simp, cMoves_nodup hinj ent (l + 1) os (by omega), ?_⟩
    intro a ha b hb e
    split at ha
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha
      subst ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
      obtain ⟨i, hi, -, -, rfl⟩ := mem_cMoves ent (l + 1) os hp
      have := hinj _ _ (by omega) (by omega) e; omega
    · simp at ha

/-- The destinations of the caller-saved argument moves are caller-saved locations below `G` that
`ent` names. -/
theorem cMoves_dst {G : Nat} {args : List Operand} (hargs : args.length ≤ G) (ent : Nat → Bool)
    {p : R × R} (hp : p ∈ cMoves loc d k c ent k (cArgs k c G args)) :
    ∃ x, k ≤ x ∧ x < k + c ∧ x < G ∧ ent x = true ∧ p.1 = loc x := by
  obtain ⟨i, hi, h1, -, rfl⟩ := mem_cMoves ent k _ hp
  rw [cArgs_length hargs] at hi
  exact ⟨k + i, by omega, by omega, by omega, h1, rfl⟩

/-- After the parallel move of the caller-saved arguments, a caller-saved location below `G` that
`ent` names and whose argument is in a caller-saved location holds that argument's register. -/
theorem par_cMoves {V : Type} (hinj : ∀ x y, x < k + c → y < k + c → loc x = loc y → x = y)
    {G : Nat} {args : List Operand} (hargs : args.length ≤ G) (ent : Nat → Bool) (f : R → V)
    {x : Nat} (h1 : k ≤ x) (h3 : x < G) (h4 : ent x = true) {o : Operand}
    (ho : (cArgs k c G args)[x - k]? = some o) (hc : isC k c o = true) (hx : x < k + c) :
    PMove.par f (cMoves loc d k c ent k (cArgs k c G args)) (loc x) = f (oreg loc d o) := by
  have hlen := cArgs_length (k := k) (c := c) hargs
  have hi : x - k < (cArgs k c G args).length := by
    rw [hlen]; have := (List.getElem?_eq_some_iff.1 ho).1; rw [hlen] at this; omega
  have hm := cMoves_of (loc := loc) (d := d) (k := k) (c := c) ent k (cArgs k c G args) (x - k) hi
    (by rw [show k + (x - k) = x by omega]; exact h4) (by rw [ho]; exact hc)
  rw [show k + (x - k) = x by omega, ho, Option.getD_some] at hm
  exact PMove.par_of_mem (cMoves_nodup hinj ent k _ (by rw [hlen]; omega)) f hm

/-! ## Parallel moves between registers and operands -/

/-- Where a parallel move reads or writes: a register, or an operand that is in no register (a
slot or an immediate). -/
abbrev Place (R : Type) := R ⊕ Operand

/-- The place of operand `o` with `kc` register locations: its register for a register location. -/
def place (loc : Nat → R) (kc : Nat) : Operand → Place R
  | .slot y => if y < kc then .inl (loc y) else .inr (.slot y)
  | o => .inr o

/-- The moves of `ret`: operand `l` of `os` into result register `res (i + l)`. -/
def retMoves (res : Nat → R) (pl : Operand → Place R) : Nat → List Operand → List (Place R × Place R)
  | _, [] => []
  | i, o :: os => (.inl (res i), pl o) :: retMoves res pl (i + 1) os

/-- The moves after a call: result register `res (i + l)` into location `d + i + l`, for `l < n`. -/
def resMoves (res : Nat → R) (pl : Operand → Place R) (d : Nat) : Nat → Nat → List (Place R × Place R)
  | _, 0 => []
  | i, n + 1 => (pl (.slot (d + i)), .inl (res i)) :: resMoves res pl d (i + 1) n

theorem mem_retMoves {res : Nat → R} {pl : Operand → Place R} :
    ∀ (i : Nat) (os : List Operand) {p : Place R × Place R}, p ∈ retMoves res pl i os ↔
      ∃ l, l < os.length ∧ p = (.inl (res (i + l)), pl (os[l]?.getD (.imm 0)))
  | _, [], _ => by simp [retMoves]
  | i, o :: os, p => by
    simp only [retMoves, List.mem_cons, mem_retMoves (i + 1) os, List.length_cons]
    constructor
    · rintro (rfl | ⟨l, hl, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · exact ⟨l + 1, by omega, by simp [show i + 1 + l = i + (l + 1) by omega]⟩
    · rintro ⟨l, hl, rfl⟩
      cases l with
      | zero => left; simp
      | succ l => right; exact ⟨l, by omega, by simp [show i + 1 + l = i + (l + 1) by omega]⟩

theorem mem_resMoves {res : Nat → R} {pl : Operand → Place R} {d : Nat} :
    ∀ (i n : Nat) {p : Place R × Place R}, p ∈ resMoves res pl d i n ↔
      ∃ l, l < n ∧ p = (pl (.slot (d + i + l)), .inl (res (i + l)))
  | _, 0, _ => by simp [resMoves]
  | i, n + 1, p => by
    simp only [resMoves, List.mem_cons, mem_resMoves (i + 1) n]
    constructor
    · rintro (rfl | ⟨l, hl, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · exact ⟨l + 1, by omega, by simp [show i + 1 + l = i + (l + 1) by omega, Nat.add_assoc]⟩
    · rintro ⟨l, hl, rfl⟩
      cases l with
      | zero => left; simp
      | succ l => right; exact ⟨l, by omega, by simp [show i + 1 + l = i + (l + 1) by omega, Nat.add_assoc]⟩

theorem retMoves_length {res : Nat → R} {pl : Operand → Place R} :
    ∀ (i : Nat) (os : List Operand), (retMoves res pl i os).length = os.length
  | _, [] => rfl
  | i, _ :: os => by simp [retMoves, retMoves_length (i + 1) os]

theorem resMoves_length {res : Nat → R} {pl : Operand → Place R} {d : Nat} :
    ∀ (i n : Nat), (resMoves res pl d i n).length = n
  | _, 0 => rfl
  | i, n + 1 => by simp [resMoves, resMoves_length (i + 1) n]

/-- The moves of `ret` have distinct destinations when the result registers are distinct. -/
theorem retMoves_nodup {res : Nat → R} (pl : Operand → Place R) :
    ∀ (i : Nat) (os : List Operand), (∀ a b, i ≤ a → a < i + os.length → i ≤ b →
      b < i + os.length → res a = res b → a = b) → ((retMoves res pl i os).map (·.1)).Nodup
  | _, [], _ => by simp [retMoves]
  | i, o :: os, hinj => by
    simp only [retMoves, List.map_cons, List.nodup_cons, List.length_cons] at hinj ⊢
    refine ⟨fun h => ?_, retMoves_nodup pl (i + 1) os fun a b h1 h2 h3 h4 =>
      hinj a b (by omega) (by omega) (by omega) (by omega)⟩
    obtain ⟨p, hp, he⟩ := List.mem_map.1 h
    obtain ⟨l, hl, rfl⟩ := (mem_retMoves _ _).1 hp
    have := hinj _ _ (by omega) (by omega) (Nat.le_refl _) (by omega) (Sum.inl.inj he)
    omega

/-- The moves after a call have distinct destinations when the places of the result locations are
distinct. -/
theorem resMoves_nodup {res : Nat → R} {pl : Operand → Place R} {d : Nat} :
    ∀ (i n : Nat), (∀ a b, i ≤ a → a < i + n → i ≤ b → b < i + n →
      pl (.slot (d + a)) = pl (.slot (d + b)) → a = b) → ((resMoves res pl d i n).map (·.1)).Nodup
  | _, 0, _ => by simp [resMoves]
  | i, n + 1, hinj => by
    simp only [resMoves, List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, resMoves_nodup (i + 1) n fun a b h1 h2 h3 h4 =>
      hinj a b (by omega) (by omega) (by omega) (by omega)⟩
    obtain ⟨p, hp, he⟩ := List.mem_map.1 h
    obtain ⟨l, hl, rfl⟩ := (mem_resMoves _ _).1 hp
    have := hinj (i + 1 + l) i (by omega) (by omega) (Nat.le_refl _) (by omega)
      (by rw [← Nat.add_assoc]; exact he)
    omega

/-- Places of distinct locations are distinct when `loc` is injective below `kc`. -/
theorem place_slot_inj {loc : Nat → R} {kc : Nat} (hinj : ∀ x y, x < kc → y < kc → loc x = loc y → x = y)
    {x y : Nat} (h : place loc kc (.slot x) = place loc kc (.slot y)) : x = y := by
  simp only [place] at h
  split at h <;> split at h
  · exact hinj x y ‹_› ‹_› (Sum.inl.inj h)
  · cases h
  · cases h
  · exact Operand.slot.inj (Sum.inr.inj h)

end Millipede.Sel
