import Millipede.Core.WfSound
import Millipede.Core.Checked

/-!
# The abstract domain of the obligation analyser

An abstract value `AVal Γ` describes one value of a term in the context `Γ` through four parts.
- `w : Itv` says that, if the value is a `U64`, its `toNat` lies in this interval.
- `b : Itv` says the same for a `U8`.
- `t` and `f`, lists of `Cmp Γ`, say for a `Bool` which comparisons hold when it is `true` or
  `false`. They let the analyser refine a branch such as `if i < n then … a[i]! …`.
- `ub : List (UB Γ)` gives, for a `U64`, upper bounds `≤ c₀ + d · y` affine in a variable `y`,
  which describe how a loop's state grows with its counter, as `acc := acc + x` with `x ≤ d`
  does.

The meaning `AVal.sat` is stated for a value of any type, with one conjunct per scalar type under
the hypothesis that the type is that scalar, so it needs no decision on types. A value of type
`U64` that the analyser describes leaves the `U8` and `Bool` parts at their top, which holds of
every value. An abstract environment `AEnv Γ` has one abstract value per variable, by de Bruijn
index with missing ones top, and the comparisons known to hold on the current path. Its meaning is
`AEnv.sat`.

The operations on environments, each with its soundness lemma, are entering a binder with `push`,
leaving one with `AVal.unshift`, forgetting the variables a write may change with `kill`, setting
a variable with `setv`, refining by a comparison that holds with `assume`, and reading atoms with
`atomW` and `atomV`. A literal of a type the analyser does not know is read through its bytes by
`litV`. The obligations are described in doc/design/obligations.md.
-/

namespace Millipede.Analysis

open Millipede

/-- The largest word. -/
abbrev wmax : Nat := 2 ^ 64 - 1

/-! ## Intervals -/

/-- A closed interval of naturals `[lo, hi]`, empty when `hi < lo`. -/
structure Itv where
  lo : Nat
  hi : Nat
deriving DecidableEq, Repr

namespace Itv

/-- `x ∈ [lo, hi]`. -/
def mem (i : Itv) (x : Nat) : Prop := i.lo ≤ x ∧ x ≤ i.hi

/-- Every word. -/
def top : Itv := ⟨0, wmax⟩
/-- Every byte. -/
def top8 : Itv := ⟨0, 255⟩
/-- One point. -/
def pt (n : Nat) : Itv := ⟨n, n⟩
/-- The smallest interval containing both. -/
def join (a b : Itv) : Itv := ⟨min a.lo b.lo, max a.hi b.hi⟩
/-- The intersection. -/
def meet (a b : Itv) : Itv := ⟨max a.lo b.lo, min a.hi b.hi⟩
/-- Inclusion `a ⊆ b` of non-empty intervals. -/
def sub (a b : Itv) : Bool := b.lo ≤ a.lo && a.hi ≤ b.hi

theorem mem_top {x : Nat} (h : x < 2 ^ 64) : top.mem x := ⟨Nat.zero_le _, by show x ≤ 2 ^ 64 - 1; omega⟩
theorem mem_top8 {x : Nat} (h : x < 2 ^ 8) : top8.mem x := ⟨Nat.zero_le _, by show x ≤ 255; omega⟩
theorem mem_pt (n : Nat) : (pt n).mem n := ⟨Nat.le_refl _, Nat.le_refl _⟩
theorem mem_join_l {a b : Itv} {x : Nat} (h : a.mem x) : (join a b).mem x := by
  simp only [mem, join] at *; omega
theorem mem_join_r {a b : Itv} {x : Nat} (h : b.mem x) : (join a b).mem x := by
  simp only [mem, join] at *; omega
theorem mem_meet {a b : Itv} {x : Nat} (ha : a.mem x) (hb : b.mem x) : (meet a b).mem x := by
  simp only [mem, meet] at *; omega
theorem mem_sub {a b : Itv} {x : Nat} (h : a.sub b = true) (ha : a.mem x) : b.mem x := by
  simp only [mem, sub, Bool.and_eq_true, decide_eq_true_eq] at *; omega

end Itv

/-! ## Facts -/

/-- Comparison operators of facts. -/
inductive COp where
  | lt | le | eq | ne
deriving DecidableEq, Repr

/-- The meaning of a comparison on naturals. -/
def COp.eval : COp → Nat → Nat → Prop
  | .lt, x, y => x < y
  | .le, x, y => x ≤ y
  | .eq, x, y => x = y
  | .ne, x, y => x ≠ y

/-- A comparison of two word atoms. -/
structure Cmp (Γ : List Ty) where
  op : COp
  a : Atom Γ .u64
  b : Atom Γ .u64

/-- An upper bound `≤ c0 + d · y`. -/
structure UB (Γ : List Ty) where
  c0 : Nat
  d : Nat
  y : Atom Γ .u64

variable {Γ : List Ty}

/-- The comparison holds. -/
def Cmp.holds (c : Cmp Γ) (env : Env Γ) : Prop :=
  c.op.eval (c.a.denote env).toNat (c.b.denote env).toNat

/-- The bound holds of `x`. -/
def UB.holds (u : UB Γ) (x : Nat) (env : Env Γ) : Prop := x ≤ u.c0 + u.d * (u.y.denote env).toNat

/-! ### Atoms: identity, shifting, mentioning a variable -/

/-- Syntactic equality of word atoms, comparing variables by index. -/
def _root_.Millipede.Atom.beq : Atom Γ .u64 → Atom Γ .u64 → Bool
  | .var m, .var m' => m.idx == m'.idx
  | .lit x, .lit y => x == y
  | _, _ => false

/-- Two variables with the same index have the same type and are the same. -/
theorem _root_.Millipede.Mem.eq_of_idx {t : Ty} {Γ : List Ty} (m : Mem t Γ) :
    ∀ {t' : Ty} (m' : Mem t' Γ), m.idx = m'.idx → t = t' ∧ HEq m m' := by
  induction m with
  | here => intro _ m' h; cases m' with
    | here => exact ⟨rfl, HEq.rfl⟩
    | there => simp [Mem.idx] at h
  | there m ih => intro _ m' h; cases m' with
    | here => simp [Mem.idx] at h
    | there m' =>
      obtain ⟨rfl, hh⟩ := ih m' (by simpa [Mem.idx] using h)
      exact ⟨rfl, by cases hh; rfl⟩

theorem _root_.Millipede.Atom.beq_denote {a b : Atom Γ .u64} (h : a.beq b = true) (env : Env Γ) :
    a.denote env = b.denote env := by
  cases a <;> cases b <;> simp only [Atom.beq, beq_iff_eq, Bool.false_eq_true] at h
  · obtain ⟨-, h⟩ := Mem.eq_of_idx _ _ h; cases h; rfl
  · simp [h, Atom.denote]

/-- Whether an atom is a variable with an index in `ks`. -/
def _root_.Millipede.Atom.hits {t : Ty} (ks : List Nat) : Atom Γ t → Bool
  | .var m => ks.contains m.idx
  | .lit _ => false

/-- Two environments agree off the variables `ks`. -/
def AgreeOff (ks : List Nat) (env env' : Env Γ) : Prop :=
  ∀ {s : Ty} (m : Mem s Γ), m.idx ∉ ks → env'.get m = env.get m

theorem _root_.Millipede.Atom.denote_agree {t : Ty} {ks : List Nat} {env env' : Env Γ} (h : AgreeOff ks env env')
    (a : Atom Γ t) (ha : a.hits ks = false) : a.denote env' = a.denote env := by
  cases a with
  | var m => exact h m (by simpa [Atom.hits] using ha)
  | lit => rfl

/-- The variable one binder further out, or `none` for the binder itself. -/
def _root_.Millipede.Mem.unshift : {t s : Ty} → {Γ : List Ty} → Mem t (s :: Γ) → Option (Mem t Γ)
  | _, _, _, .here => none
  | _, _, _, .there m => some m

/-- The atom one binder further out, or `none` for the binder itself. -/
def _root_.Millipede.Atom.unshift {s t : Ty} : Atom (s :: Γ) t → Option (Atom Γ t)
  | .var m => m.unshift.map .var
  | .lit v => some (.lit v)

theorem _root_.Millipede.Atom.denote_unshift {s t : Ty} {a : Atom (s :: Γ) t} {a' : Atom Γ t}
    (h : a.unshift = some a') (x : s.carrier) (env : Env Γ) :
    a'.denote env = a.denote (.cons x env) := by
  rcases a with m | v
  · cases m <;> simp only [Atom.unshift, Mem.unshift, Option.map_none, Option.map_some,
      Option.some.injEq, reduceCtorEq] at h
    subst h; rfl
  · simp only [Atom.unshift, Option.some.injEq] at h; subst h; rfl

/-! ### Facts under binders and writes -/

def Cmp.shift {s : Ty} (c : Cmp Γ) : Cmp (s :: Γ) := ⟨c.op, c.a.shift, c.b.shift⟩
def UB.shift {s : Ty} (u : UB Γ) : UB (s :: Γ) := ⟨u.c0, u.d, u.y.shift⟩
def Cmp.unshift {s : Ty} (c : Cmp (s :: Γ)) : Option (Cmp Γ) :=
  c.a.unshift.bind fun a => c.b.unshift.map fun b => ⟨c.op, a, b⟩
def UB.unshift {s : Ty} (u : UB (s :: Γ)) : Option (UB Γ) := u.y.unshift.map fun y => ⟨u.c0, u.d, y⟩
def Cmp.hits (ks : List Nat) (c : Cmp Γ) : Bool := c.a.hits ks || c.b.hits ks
def UB.hits (ks : List Nat) (u : UB Γ) : Bool := u.y.hits ks

@[simp] theorem Cmp.holds_shift {s : Ty} (c : Cmp Γ) (x : s.carrier) (env : Env Γ) :
    c.shift.holds (.cons x env) ↔ c.holds env := by
  simp [Cmp.shift, Cmp.holds]

@[simp] theorem UB.holds_shift {s : Ty} (u : UB Γ) (n : Nat) (x : s.carrier) (env : Env Γ) :
    u.shift.holds n (.cons x env) ↔ u.holds n env := by
  simp [UB.shift, UB.holds]

theorem Cmp.holds_unshift {s : Ty} {c : Cmp (s :: Γ)} {c' : Cmp Γ} (h : c.unshift = some c')
    {x : s.carrier} {env : Env Γ} (hc : c.holds (.cons x env)) : c'.holds env := by
  simp only [Cmp.unshift, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  simpa [Cmp.holds, Atom.denote_unshift ha x env, Atom.denote_unshift hb x env] using hc

theorem UB.holds_unshift {s : Ty} {u : UB (s :: Γ)} {u' : UB Γ} (h : u.unshift = some u')
    {n : Nat} {x : s.carrier} {env : Env Γ} (hu : u.holds n (.cons x env)) : u'.holds n env := by
  simp only [UB.unshift, Option.map_eq_some_iff] at h
  obtain ⟨y, hy, rfl⟩ := h
  simpa [UB.holds, Atom.denote_unshift hy x env] using hu

theorem Cmp.holds_agree {ks : List Nat} {env env' : Env Γ} (h : AgreeOff ks env env') {c : Cmp Γ}
    (hc : c.hits ks = false) (hh : c.holds env) : c.holds env' := by
  simp only [Cmp.hits, Bool.or_eq_false_iff] at hc
  simpa [Cmp.holds, Atom.denote_agree h _ hc.1, Atom.denote_agree h _ hc.2] using hh

theorem UB.holds_agree {ks : List Nat} {env env' : Env Γ} (h : AgreeOff ks env env') {u : UB Γ}
    (hu : u.hits ks = false) {n : Nat} (hh : u.holds n env) : u.holds n env' := by
  simpa [UB.holds, Atom.denote_agree h _ hu] using hh

/-! ## Abstract values -/

/-- An abstract value, as the module doc describes. The defaults are top. -/
structure AVal (Γ : List Ty) where
  w : Itv := Itv.top
  b : Itv := Itv.top8
  t : List (Cmp Γ) := []
  f : List (Cmp Γ) := []
  ub : List (UB Γ) := []

/-- The meaning of an abstract value, for a value of any type. -/
def AVal.sat (a : AVal Γ) (env : Env Γ) {t : Ty} (v : t.carrier) : Prop :=
  (∀ h : t = .u64, a.w.mem (cast (congrArg Ty.carrier h) v : UInt64).toNat ∧
    ∀ u ∈ a.ub, u.holds (cast (congrArg Ty.carrier h) v : UInt64).toNat env) ∧
  (∀ h : t = .u8, a.b.mem (cast (congrArg Ty.carrier h) v : UInt8).toNat) ∧
  (∀ h : t = .bool, ((cast (congrArg Ty.carrier h) v : Bool) = true → ∀ c ∈ a.t, c.holds env) ∧
    ((cast (congrArg Ty.carrier h) v : Bool) = false → ∀ c ∈ a.f, c.holds env))

/-- A word described by an interval and bounds. -/
def AVal.ofW (w : Itv) (ub : List (UB Γ) := []) : AVal Γ := { w, ub }
/-- A byte described by an interval. -/
def AVal.ofB (b : Itv) : AVal Γ := { b }
/-- A boolean described by what its two values imply. -/
def AVal.ofBool (t f : List (Cmp Γ)) : AVal Γ := { t, f }

theorem AVal.sat_top (env : Env Γ) {t : Ty} (v : t.carrier) : (({} : AVal Γ)).sat env v := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · subst h; exact ⟨Itv.mem_top (UInt64.toNat_lt _), by simp⟩
  · subst h; exact Itv.mem_top8 (UInt8.toNat_lt _)
  · subst h; simp

theorem AVal.sat_ofW {w : Itv} {ub : List (UB Γ)} {env : Env Γ} {v : UInt64} :
    (AVal.ofW w ub).sat env (t := .u64) v ↔ w.mem v.toNat ∧ ∀ u ∈ ub, u.holds v.toNat env := by
  constructor
  · intro h; simpa [AVal.ofW] using h.1 rfl
  · intro h
    refine ⟨fun _ => by simpa [AVal.ofW] using h, fun hh => ?_, fun hh => ?_⟩
    · exact Itv.mem_top8 (UInt8.toNat_lt _)
    · simp [AVal.ofW]

theorem AVal.sat_ofB {b : Itv} {env : Env Γ} {v : UInt8} :
    (AVal.ofB b).sat env (t := .u8) v ↔ b.mem v.toNat := by
  constructor
  · intro h; simpa [AVal.ofB] using h.2.1 rfl
  · intro h
    refine ⟨fun _ => ⟨Itv.mem_top (UInt64.toNat_lt _), by simp [AVal.ofB]⟩, fun _ => by simpa [AVal.ofB] using h,
      fun _ => by simp [AVal.ofB]⟩

theorem AVal.sat_ofBool {t f : List (Cmp Γ)} {env : Env Γ} {v : Bool} :
    (AVal.ofBool t f).sat env (t := .bool) v ↔
      (v = true → ∀ c ∈ t, c.holds env) ∧ (v = false → ∀ c ∈ f, c.holds env) := by
  constructor
  · intro h; simpa [AVal.ofBool] using h.2.2 rfl
  · intro h
    exact ⟨fun _ => ⟨Itv.mem_top (UInt64.toNat_lt _), by simp [AVal.ofBool]⟩,
      fun _ => Itv.mem_top8 (UInt8.toNat_lt _), fun _ => by simpa [AVal.ofBool] using h⟩

/-- The `U64` part of a description. -/
theorem AVal.sat_w {a : AVal Γ} {env : Env Γ} {v : UInt64} (h : a.sat env (t := .u64) v) :
    a.w.mem v.toNat ∧ ∀ u ∈ a.ub, u.holds v.toNat env := by simpa using h.1 rfl

theorem AVal.sat_b {a : AVal Γ} {env : Env Γ} {v : UInt8} (h : a.sat env (t := .u8) v) :
    a.b.mem v.toNat := by simpa using h.2.1 rfl

theorem AVal.sat_bool {a : AVal Γ} {env : Env Γ} {v : Bool} (h : a.sat env (t := .bool) v) :
    (v = true → ∀ c ∈ a.t, c.holds env) ∧ (v = false → ∀ c ∈ a.f, c.holds env) := by
  simpa using h.2.2 rfl

/-- Only the intervals, with the facts dropped. -/
def AVal.plain {Γ' : List Ty} (a : AVal Γ) : AVal Γ' := { w := a.w, b := a.b }

theorem AVal.sat_plain {Γ' : List Ty} {a : AVal Γ} {env : Env Γ} {env' : Env Γ'} {t : Ty}
    {v : t.carrier} (h : a.sat env v) : (a.plain : AVal Γ').sat env' v :=
  ⟨fun hh => ⟨(h.1 hh).1, by simp [AVal.plain]⟩, h.2.1, fun _ => by simp [AVal.plain]⟩

def AVal.shift {s : Ty} (a : AVal Γ) : AVal (s :: Γ) :=
  { w := a.w, b := a.b, t := a.t.map Cmp.shift, f := a.f.map Cmp.shift, ub := a.ub.map UB.shift }

theorem AVal.sat_shift {s : Ty} {a : AVal Γ} {x : s.carrier} {env : Env Γ} {t : Ty}
    {v : t.carrier} : a.shift.sat (.cons x env) v ↔ a.sat env v := by
  simp [AVal.sat, AVal.shift]

def AVal.unshift {s : Ty} (a : AVal (s :: Γ)) : AVal Γ :=
  { w := a.w, b := a.b, t := a.t.filterMap Cmp.unshift, f := a.f.filterMap Cmp.unshift,
    ub := a.ub.filterMap UB.unshift }

theorem AVal.sat_unshift {s : Ty} {a : AVal (s :: Γ)} {x : s.carrier} {env : Env Γ} {t : Ty}
    {v : t.carrier} (h : a.sat (.cons x env) v) : a.unshift.sat env v := by
  refine ⟨fun hh => ⟨(h.1 hh).1, ?_⟩, h.2.1, fun hh => ⟨fun hv c hc => ?_, fun hv c hc => ?_⟩⟩
  · intro u hu
    simp only [AVal.unshift, List.mem_filterMap] at hu
    obtain ⟨u', hu', he⟩ := hu
    exact UB.holds_unshift he ((h.1 hh).2 u' hu')
  · simp only [AVal.unshift, List.mem_filterMap] at hc
    obtain ⟨c', hc', he⟩ := hc
    exact Cmp.holds_unshift he ((h.2.2 hh).1 hv c' hc')
  · simp only [AVal.unshift, List.mem_filterMap] at hc
    obtain ⟨c', hc', he⟩ := hc
    exact Cmp.holds_unshift he ((h.2.2 hh).2 hv c' hc')

/-- Forget the facts that mention the variables `ks`. -/
def AVal.forget (ks : List Nat) (a : AVal Γ) : AVal Γ :=
  { a with t := a.t.filter (!·.hits ks), f := a.f.filter (!·.hits ks),
           ub := a.ub.filter (!·.hits ks) }

theorem AVal.sat_forget {ks : List Nat} {env env' : Env Γ} (he : AgreeOff ks env env') {a : AVal Γ}
    {t : Ty} {v : t.carrier} (h : a.sat env v) : (a.forget ks).sat env' v := by
  refine ⟨fun hh => ⟨(h.1 hh).1, fun u hu => ?_⟩, h.2.1, fun hh => ⟨fun hv c hc => ?_, fun hv c hc => ?_⟩⟩
  · simp only [AVal.forget, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hu
    exact UB.holds_agree he hu.2 ((h.1 hh).2 u hu.1)
  · simp only [AVal.forget, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
    exact Cmp.holds_agree he hc.2 ((h.2.2 hh).1 hv c hc.1)
  · simp only [AVal.forget, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
    exact Cmp.holds_agree he hc.2 ((h.2.2 hh).2 hv c hc.1)

/-- The least upper bound of two descriptions, with the facts dropped. -/
def AVal.join (a b : AVal Γ) : AVal Γ := { w := a.w.join b.w, b := a.b.join b.b }

theorem AVal.sat_join_l {a b : AVal Γ} {env : Env Γ} {t : Ty} {v : t.carrier} (h : a.sat env v) :
    (a.join b).sat env v :=
  ⟨fun hh => ⟨Itv.mem_join_l (h.1 hh).1, by simp [AVal.join]⟩, fun hh => Itv.mem_join_l (h.2.1 hh),
    fun _ => by simp [AVal.join]⟩

theorem AVal.sat_join_r {a b : AVal Γ} {env : Env Γ} {t : Ty} {v : t.carrier} (h : b.sat env v) :
    (a.join b).sat env v :=
  ⟨fun hh => ⟨Itv.mem_join_r (h.1 hh).1, by simp [AVal.join]⟩, fun hh => Itv.mem_join_r (h.2.1 hh),
    fun _ => by simp [AVal.join]⟩

/-- A literal of any type, read through its bytes, which gives its value for a word or a byte. -/
def litV {t : Ty} (v : t.carrier) : AVal Γ :=
  let n := natOfBytes (Data.encodeBytes v)
  { w := Itv.pt n, b := Itv.pt n }

theorem litV_sat {t : Ty} (v : t.carrier) (env : Env Γ) : (litV v : AVal Γ).sat env v := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · subst h
    refine ⟨?_, by simp [litV]⟩
    simp only [litV, cast_eq]
    show (Itv.pt (natOfBytes (natBytes 8 v.toNat))).mem _
    rw [natOfBytes_natBytes, Nat.mod_eq_of_lt (UInt64.toNat_lt v)]; exact Itv.mem_pt _
  · subst h
    simp only [litV, cast_eq]
    show (Itv.pt (natOfBytes (natBytes 1 v.toNat))).mem _
    rw [natOfBytes_natBytes, Nat.mod_eq_of_lt (UInt8.toNat_lt v)]; exact Itv.mem_pt _
  · subst h; simp [litV]

/-! ## Abstract environments -/

/-- One abstract value per variable, by index with missing ones top, and the comparisons that hold
on the current path. -/
structure AEnv (Γ : List Ty) where
  vs : List (AVal Γ) := []
  ps : List (Cmp Γ) := []

namespace AEnv

/-- The description of variable `k`. -/
def get (A : AEnv Γ) (k : Nat) : AVal Γ := A.vs[k]?.getD {}

/-- The meaning of an abstract environment. -/
def sat (A : AEnv Γ) (env : Env Γ) : Prop :=
  (∀ {t : Ty} (m : Mem t Γ), (A.get m.idx).sat env (env.get m)) ∧ ∀ c ∈ A.ps, c.holds env

/-- Enter a binder described by `a`. -/
def push {s : Ty} (a : AVal (s :: Γ)) (A : AEnv Γ) : AEnv (s :: Γ) :=
  ⟨a :: A.vs.map AVal.shift, A.ps.map Cmp.shift⟩

theorem sat_push {s : Ty} {A : AEnv Γ} {env : Env Γ} {a : AVal (s :: Γ)} {x : s.carrier}
    (hA : A.sat env) (ha : a.sat (.cons x env) x) : (A.push a).sat (.cons x env) := by
  refine ⟨fun m => ?_, fun c hc => ?_⟩
  · cases m with
    | here => simpa [push, get, Mem.idx] using ha
    | there m =>
      have := hA.1 m
      simp only [get, push, Mem.idx, List.getElem?_cons_succ, List.getElem?_map] at this ⊢
      cases h : A.vs[m.idx]? with
      | none => simpa using AVal.sat_top _ _
      | some a' => simpa [h, AVal.sat_shift] using this
  · simp only [push, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    simpa using hA.2 c' hc'

/-- Forget the variables `ks`, which a write may have changed, and every fact that mentions
them. -/
def kill (ks : List Nat) (A : AEnv Γ) : AEnv Γ :=
  ⟨go 0 A.vs, A.ps.filter (!·.hits ks)⟩
where
  go (k : Nat) : List (AVal Γ) → List (AVal Γ)
    | [] => []
    | a :: as => (if ks.contains k then {} else a.forget ks) :: go (k + 1) as

theorem kill_go_get (ks : List Nat) : ∀ (as : List (AVal Γ)) (k i : Nat),
    ((kill.go ks k as)[i]?.getD {}) =
      if ks.contains (k + i) then {} else (as[i]?.getD {}).forget ks
  | [], k, i => by split <;> simp [kill.go, AVal.forget]
  | a :: as, k, 0 => by simp [kill.go]
  | a :: as, k, i + 1 => by
    simp only [kill.go, List.getElem?_cons_succ]
    rw [kill_go_get ks as (k + 1) i, show k + 1 + i = k + (i + 1) by omega]

theorem sat_kill {ks : List Nat} {A : AEnv Γ} {env env' : Env Γ} (hA : A.sat env)
    (he : AgreeOff ks env env') : (A.kill ks).sat env' := by
  refine ⟨fun m => ?_, fun c hc => ?_⟩
  · simp only [get, kill, kill_go_get, Nat.zero_add]
    split
    · exact AVal.sat_top _ _
    · next h =>
      rw [he m (by simpa using h)]
      exact AVal.sat_forget he (hA.1 m)
  · simp only [kill, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
    exact Cmp.holds_agree he hc.2 (hA.2 c hc.1)

/-- Replace element `k` of a list of descriptions, padding with top. -/
def setPad : List (AVal Γ) → Nat → AVal Γ → List (AVal Γ)
  | [], 0, a => [a]
  | [], k + 1, a => {} :: setPad [] k a
  | _ :: as, 0, a => a :: as
  | b :: as, k + 1, a => b :: setPad as k a

theorem setPad_get : ∀ (l : List (AVal Γ)) (k : Nat) (a : AVal Γ) (j : Nat),
    (setPad l k a)[j]?.getD {} = if k = j then a else l[j]?.getD {}
  | [], 0, a, 0 | _ :: _, 0, a, 0 => by simp [setPad]
  | [], 0, a, j + 1 => by simp [setPad]
  | _ :: as, 0, a, j + 1 => by simp [setPad]
  | [], k + 1, a, 0 => by simp [setPad]
  | _ :: as, k + 1, a, 0 => by simp [setPad]
  | [], k + 1, a, j + 1 => by simpa [setPad] using setPad_get [] k a j
  | _ :: as, k + 1, a, j + 1 => by simpa [setPad] using setPad_get as k a j

/-- Set the description of variable `k`. -/
def setv (k : Nat) (a : AVal Γ) (A : AEnv Γ) : AEnv Γ := { A with vs := setPad A.vs k a }

theorem get_setv (A : AEnv Γ) (k : Nat) (a : AVal Γ) (j : Nat) :
    (A.setv k a).get j = if k = j then a else A.get j := setPad_get A.vs k a j

theorem sat_setv {A : AEnv Γ} {env : Env Γ} {s : Ty} (m : Mem s Γ) {a : AVal Γ} (hA : A.sat env)
    (ha : a.sat env (env.get m)) : (A.setv m.idx a).sat env := by
  refine ⟨fun m' => ?_, hA.2⟩
  rw [get_setv]
  split
  · next h =>
    obtain ⟨rfl, hm⟩ := Mem.eq_of_idx m m' h
    cases hm
    exact ha
  · exact hA.1 m'

/-! ### Reading atoms -/

/-- The interval of a word atom. -/
def atomW (A : AEnv Γ) : Atom Γ .u64 → Itv
  | .var m => (A.get m.idx).w
  | .lit v => Itv.pt v.toNat

/-- The upper bounds of a word atom. -/
def atomUB (A : AEnv Γ) : Atom Γ .u64 → List (UB Γ)
  | .var m => (A.get m.idx).ub
  | .lit _ => []

/-- The description of an atom of any type. -/
def atomV {t : Ty} (A : AEnv Γ) : Atom Γ t → AVal Γ
  | .var m => A.get m.idx
  | .lit v => litV v

theorem atomV_sat {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {t : Ty} (a : Atom Γ t) :
    (A.atomV a).sat env (a.denote env) := by
  cases a with
  | var m => exact hA.1 m
  | lit v => exact litV_sat v env

theorem atomW_mem {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) (a : Atom Γ .u64) :
    (A.atomW a).mem (a.denote env).toNat := by
  cases a with
  | var m => exact (AVal.sat_w (hA.1 m)).1
  | lit v => exact Itv.mem_pt _

theorem atomUB_holds {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) (a : Atom Γ .u64) :
    ∀ u ∈ A.atomUB a, u.holds (a.denote env).toNat env := by
  cases a with
  | var m => exact (AVal.sat_w (hA.1 m)).2
  | lit v => simp [atomUB]

/-- Whether comparison `c` is known on the path. -/
def has (A : AEnv Γ) (c : Cmp Γ) : Bool :=
  A.ps.any fun c' => c'.op == c.op && c'.a.beq c.a && c'.b.beq c.b

theorem has_holds {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {c : Cmp Γ} (h : A.has c = true) :
    c.holds env := by
  simp only [has, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨c', hc', ⟨⟨ho, ha⟩, hb⟩⟩ := h
  have := hA.2 c' hc'
  simpa [Cmp.holds, ho, Atom.beq_denote ha, Atom.beq_denote hb] using this

/-! ### Refinement by a comparison -/

/-- Narrow the interval of a word variable to `J`. A literal is left unchanged. -/
def narrow (x : Atom Γ .u64) (J : Itv) (A : AEnv Γ) : AEnv Γ :=
  match x with
  | .var m => A.setv m.idx { A.get m.idx with w := (A.get m.idx).w.meet J }
  | .lit _ => A

theorem sat_narrow {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) (x : Atom Γ .u64) {J : Itv}
    (hJ : J.mem (x.denote env).toNat) : (A.narrow x J).sat env := by
  cases x with
  | lit => exact hA
  | var m =>
    refine sat_setv m hA ⟨fun h => ?_, (hA.1 m).2.1, (hA.1 m).2.2⟩
    cases h
    exact ⟨Itv.mem_meet (AVal.sat_w (hA.1 m)).1 hJ, (AVal.sat_w (hA.1 m)).2⟩

/-- Assume that `c` holds, recording it and narrowing the intervals of its variables. -/
def assume (c : Cmp Γ) (A : AEnv Γ) : AEnv Γ :=
  let A' : AEnv Γ := { A with ps := c :: A.ps }
  match c.op with
  | .lt =>
    let A1 := A'.narrow c.a ⟨0, (A.atomW c.b).hi - 1⟩
    A1.narrow c.b ⟨(A1.atomW c.a).lo + 1, wmax⟩
  | .le =>
    let A1 := A'.narrow c.a ⟨0, (A.atomW c.b).hi⟩
    A1.narrow c.b ⟨(A1.atomW c.a).lo, wmax⟩
  | .eq =>
    let A1 := A'.narrow c.a (A.atomW c.b)
    A1.narrow c.b (A1.atomW c.a)
  | .ne => A'

theorem sat_assume {A : AEnv Γ} {env : Env Γ} (hA : A.sat env) {c : Cmp Γ} (hc : c.holds env) :
    (A.assume c).sat env := by
  have hA' : ({ A with ps := c :: A.ps } : AEnv Γ).sat env :=
    ⟨hA.1, by simpa using ⟨hc, hA.2⟩⟩
  rcases c with ⟨_ | _ | _ | _, a, b⟩ <;> simp only [Cmp.holds, COp.eval] at hc <;>
    simp only [assume]
  all_goals
    have ha := atomW_mem hA a
    have hb := atomW_mem hA b
    have hlt := UInt64.toNat_lt (b.denote env)
    simp only [Itv.mem] at ha hb
  · have h1 := sat_narrow hA' a (J := ⟨0, (A.atomW b).hi - 1⟩) (by simp only [Itv.mem]; omega)
    refine sat_narrow h1 b ?_
    have := atomW_mem h1 a; simp only [Itv.mem, wmax] at this ⊢; omega
  · have h1 := sat_narrow hA' a (J := ⟨0, (A.atomW b).hi⟩) (by simp only [Itv.mem]; omega)
    refine sat_narrow h1 b ?_
    have := atomW_mem h1 a; simp only [Itv.mem, wmax] at this ⊢; omega
  · have h1 := sat_narrow hA' a (J := A.atomW b) (by rw [hc]; exact atomW_mem hA b)
    exact sat_narrow h1 b (by rw [← hc]; exact atomW_mem h1 a)
  · exact hA'

/-- Assume all of `cs`. -/
def assumeAll (cs : List (Cmp Γ)) (A : AEnv Γ) : AEnv Γ := cs.foldl (fun A c => A.assume c) A

theorem sat_assumeAll {env : Env Γ} : ∀ {cs : List (Cmp Γ)} {A : AEnv Γ}, A.sat env →
    (∀ c ∈ cs, c.holds env) → (A.assumeAll cs).sat env
  | [], _, hA, _ => hA
  | c :: cs, _, hA, hc => by
    simp only [assumeAll, List.foldl_cons]
    exact sat_assumeAll (sat_assume hA (hc c (by simp))) (fun c' h => hc c' (by simp [h]))

end AEnv

end Millipede.Analysis
