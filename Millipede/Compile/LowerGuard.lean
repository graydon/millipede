import Millipede.Compile.LowerCase

/-!
# The memory refinement of `guard (valid p)`

A guard is the checked test of a place's obligations. `placeCheck` computes `Place.check` into
`RY`, as the conjunction of the index bounds and, for a pair `p[i], p[j]`, of `i ≠ j`, and the guard
stores that bit as the tag byte of its `Result Unit Unit`. Places with a `Slots` cell or a slice
have no run-time check, because cells have no tags, so `placeCheck` gives `none` for them. The
checker does not admit a guard on such a place, since `Guard.valid` requires `Place.checkable`, and
`compile` refuses a term that has one.

See doc/design/compiler.md.
-/

namespace Millipede.Flat

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

theorem bword_and (a b : Bool) : (bword a &&& bword b) = bword (a && b) := by
  cases a <;> cases b <;> decide

/-- The word bound test: `x < n` on words is `x.toNat < n` when `n` fits a word. -/
theorem ult_bword (x : UInt64) {n : Nat} (hn : n < UInt64.size) :
    (if x < UInt64.ofNat n then (1 : UInt64) else 0) = bword (decide (x.toNat < n)) := by
  have e : (x < UInt64.ofNat n) ↔ x.toNat < n := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]
  by_cases h : x.toNat < n
  · simp [bword, h, e.mpr h]
  · simp [bword, h, show ¬ x < UInt64.ofNat n from fun h' => h (e.mp h')]

theorem ne_bword (x y : UInt64) :
    (if x = y then (0 : UInt64) else 1) = bword (decide (x.toNat ≠ y.toNat)) := by
  by_cases h : x = y
  · simp [bword, h]
  · have : x.toNat ≠ y.toNat := fun e => h (UInt64.toNat_inj.mp e)
    simp [bword, h, this]

/-- The slice bound `lo + len ≤ n` as two word tests that cannot overflow, `lo ≤ n` and
`len ≤ n - lo`. -/
theorem range_bword (b : Bool) (lo len : UInt64) {n : Nat} (hn : n < UInt64.size) :
    (bword b &&& (if lo ≤ UInt64.ofNat n then (1 : UInt64) else 0)) &&&
        (if len ≤ UInt64.ofNat n - lo then (1 : UInt64) else 0) =
      bword (b && decide (lo.toNat + len.toNat ≤ n)) := by
  have hn' : (UInt64.ofNat n).toNat = n := by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]
  by_cases h1 : lo.toNat ≤ n
  · have e1 : lo ≤ UInt64.ofNat n := by rw [UInt64.le_iff_toNat_le, hn']; exact h1
    have e2 : (UInt64.ofNat n - lo).toNat = n - lo.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ e1, hn']
    by_cases h2 : len.toNat ≤ n - lo.toNat
    · have e3 : len ≤ UInt64.ofNat n - lo := by rw [UInt64.le_iff_toNat_le, e2]; exact h2
      simp only [e1, e3, ↓reduceIte, show lo.toNat + len.toNat ≤ n by omega, decide_true,
        Bool.and_true]
      cases b <;> decide
    · have e3 : ¬ len ≤ UInt64.ofNat n - lo := by rw [UInt64.le_iff_toNat_le, e2]; exact h2
      simp only [e1, e3, ↓reduceIte, show ¬ lo.toNat + len.toNat ≤ n by omega, decide_false,
        Bool.and_false]
      cases b <;> decide
  · have e1 : ¬ lo ≤ UInt64.ofNat n := by rw [UInt64.le_iff_toNat_le, hn']; exact h1
    simp only [e1, ↓reduceIte, show ¬ lo.toNat + len.toNat ≤ n by omega, decide_false,
      Bool.and_false]
    cases b <;> cases (decide (len ≤ UInt64.ofNat n - lo)) <;> simp [bword]

/-- One bound test `i < n`, combined with `RY` by a bitwise and. -/
theorem checkLt_runs {Γ : List Ty} (i : Atom Γ .u64) {ρ : List Loc} {S : List SI}
    {W : List Bool} {bp n nn : Nat} {env : Env Γ}
    {f : Frame} {h : Heap} {b : Bool} (hn : n < UInt64.size) (hf : f BP = UInt64.ofNat bp)
    (hY : f RY = bword b) (henv : MEnvRel h bp env ρ S) (hfe : FEnvRel f env ρ)
    (hl : Lay bp nn Γ ρ S W)
    (hnh : ∀ m, i = .var m → (S.getD m.idx default).hole = none) (hnL : bp + nn ≤ L)
    (hnU : bp + nn ≤ UInt64.size) :
    ∃ f', Runs κ ω L (.seq (atomWord i ρ RX) (.seq (.bin .ult RX (.slot RX) (.imm (UInt64.ofNat n)))
        (.bin .band RY (.slot RY) (.slot RX)))) f h f' h ∧ f' BP = f BP ∧
      f' RY = bword (b && decide ((i.denote env).toNat < n)) ∧ ∀ x, x ≠ RX → x ≠ RY → f' x = f x := by
  refine ⟨_, Runs.seq (atomWord_u64 i RX hf henv hfe hl hnh hnL hnU) (Runs.seq (Runs.bin _ _ _ _ _ _)
    (Runs.bin _ _ _ _ _ _)), ?_, ?_, ?_⟩
  · simp [Frame.set]
  · simp only [Frame.set_same, eval_slot, eval_imm, BinOp.eval]
    rw [Frame.set_ne _ _ (by decide), Frame.set_ne _ _ (by decide), hY, ult_bword _ hn, bword_and]
  · intro x h1 h2; simp [Frame.set, h1, h2]

/-- The run-time check of a place computes `Place.check` into `RY` and leaves memory unchanged. -/
theorem placeCheck_runs {Γ : List Ty} {ρ : List Loc} {S : List SI} {W : List Bool} {bp nn : Nat}
    {env : Env Γ} {h : Heap}
    (henv : MEnvRel h bp env ρ S) (hl : Lay bp nn Γ ρ S W) (hnL : bp + nn ≤ L)
    (hnU : bp + nn ≤ UInt64.size) :
    ∀ {t : Ty} (p : Place Γ t) (c : Stmt) (f : Frame), f BP = UInt64.ofNat bp → FEnvRel f env ρ →
      placeCheck p ρ = some c → p.IdxNH S →
      ∃ f', Runs κ ω L c f h f' h ∧ f' BP = f BP ∧ f' RY = bword (p.check env) := by
  intro t p
  induction p with
  | var m =>
    intro c f hf _ hc _
    simp only [placeCheck, Option.some.injEq] at hc; subst hc
    exact ⟨_, Runs.mov _ _ _ _, by simp [Frame.set], by simp [Place.check, bword]⟩
  | field p l ih =>
    intro c f hf hfe hc hnh
    exact ih c f hf hfe hc hnh
  | @index t n _ p i ih =>
    intro c f hf hfe hc hnh
    simp only [placeCheck] at hc
    split at hc
    · rename_i hn
      obtain ⟨c₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hc
      obtain ⟨f₁, hr₁, hb₁, hy₁⟩ := ih c₀ f hf hfe h₀ hnh.1
      obtain ⟨f₂, hr₂, hb₂, hy₂, _⟩ := checkLt_runs (κ := κ) (ω := ω) i hn (hb₁.trans hf) hy₁ henv
        (hfe.keep hr₁.keep) hl hnh.2 hnL hnU
      exact ⟨f₂, Runs.seq hr₁ hr₂, hb₂.trans hb₁, by rw [hy₂]; rfl⟩
    · cases hc
  | slot p i ih => intro c f _ _ hc; simp [placeCheck] at hc
  | @range t n p lo len ih =>
    intro c f hf hfe hc hnh
    simp only [placeCheck] at hc
    split at hc
    · rename_i hn
      obtain ⟨c₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hc
      obtain ⟨f₁, hr₁, hb₁, hy₁⟩ := ih c₀ f hf hfe h₀ hnh.1
      have hfe₁ := hfe.keep hr₁.keep
      have hr₂ := atomWord_u64 (κ := κ) (ω := ω) lo RX (hb₁.trans hf) henv hfe₁ hl hnh.2.1 hnL hnU
      let f₂ := f₁.set RX (lo.denote env)
      have hr₃ := Runs.bin (κ := κ) (ω := ω) (L := L) .ule RT (.slot RX) (.imm (UInt64.ofNat n)) f₂ h
      let f₃ := f₂.set RT (BinOp.ule.eval ((Operand.slot RX).eval f₂)
        ((Operand.imm (UInt64.ofNat n)).eval f₂))
      have hr₄ := Runs.bin (κ := κ) (ω := ω) (L := L) .band RY (.slot RY) (.slot RT) f₃ h
      let f₄ := f₃.set RY (BinOp.band.eval ((Operand.slot RY).eval f₃) ((Operand.slot RT).eval f₃))
      have hr₅ := Runs.bin (κ := κ) (ω := ω) (L := L) .sub RX (.imm (UInt64.ofNat n)) (.slot RX) f₄ h
      let f₅ := f₄.set RX (BinOp.sub.eval ((Operand.imm (UInt64.ofNat n)).eval f₄)
        ((Operand.slot RX).eval f₄))
      have hb₅ : f₅ BP = UInt64.ofNat bp := by simp [f₅, f₄, f₃, f₂, Frame.set, hb₁, hf]
      have hfe₅ := hfe₁.keep (Runs.seq hr₂ (Runs.seq hr₃ (Runs.seq hr₄ hr₅))).keep
      have hr₆ := atomWord_u64 (κ := κ) (ω := ω) len RT hb₅ henv hfe₅ hl hnh.2.2 hnL hnU
      let f₆ := f₅.set RT (len.denote env)
      have hr₇ := Runs.bin (κ := κ) (ω := ω) (L := L) .ule RX (.slot RT) (.slot RX) f₆ h
      let f₇ := f₆.set RX (BinOp.ule.eval ((Operand.slot RT).eval f₆) ((Operand.slot RX).eval f₆))
      have hr₈ := Runs.bin (κ := κ) (ω := ω) (L := L) .band RY (.slot RY) (.slot RX) f₇ h
      let f₈ := f₇.set RY (BinOp.band.eval ((Operand.slot RY).eval f₇) ((Operand.slot RX).eval f₇))
      refine ⟨f₈, Runs.seq hr₁ (Runs.seq hr₂ (Runs.seq hr₃ (Runs.seq hr₄ (Runs.seq hr₅
        (Runs.seq hr₆ (Runs.seq hr₇ hr₈)))))), by simp [f₈, f₇, f₆, Frame.set, hb₅, hf], ?_⟩
      simp only [f₈, f₇, f₆, f₅, f₄, f₃, f₂, Frame.set_same, eval_slot, eval_imm, BinOp.eval]
      simp only [Frame.set, show (RY = RX) = False by decide, show (RY = RT) = False by decide,
        show (RX = RT) = False by decide,
        show (RX = RY) = False by decide, ↓reduceIte, hy₁]
      rw [range_bword _ _ _ hn]; rfl
    · cases hc
  | rangeS => intro c f _ _ hc; simp [placeCheck] at hc
  | pair2S => intro c f _ _ hc; simp [placeCheck] at hc
  | @pair2 t n _ p i j ih =>
    intro c f hf hfe hc hnh
    simp only [placeCheck] at hc
    split at hc
    · rename_i hn
      obtain ⟨c₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hc
      obtain ⟨f₁, hr₁, hb₁, hy₁⟩ := ih c₀ f hf hfe h₀ hnh.1
      have hfe₁ := hfe.keep hr₁.keep
      have hr₂ := atomWord_u64 (κ := κ) (ω := ω) i RX (hb₁.trans hf) henv hfe₁ hl hnh.2.1 hnL hnU
      let f₂ := f₁.set RX (i.denote env)
      have hr₃ := Runs.bin (κ := κ) (ω := ω) (L := L) .ult RX (.slot RX) (.imm (UInt64.ofNat n)) f₂ h
      let f₃ := f₂.set RX (BinOp.ult.eval ((Operand.slot RX).eval f₂)
        ((Operand.imm (UInt64.ofNat n)).eval f₂))
      have hr₄ := Runs.bin (κ := κ) (ω := ω) (L := L) .band RY (.slot RY) (.slot RX) f₃ h
      let f₄ := f₃.set RY (BinOp.band.eval ((Operand.slot RY).eval f₃) ((Operand.slot RX).eval f₃))
      have hb₄ : f₄ BP = UInt64.ofNat bp := by simp [f₄, f₃, f₂, Frame.set, hb₁, hf]
      have hy₄ : f₄ RY = bword (p.check env && decide ((i.denote env).toNat < n)) := by
        simp only [f₄, f₃, f₂, Frame.set_same, eval_slot, eval_imm, BinOp.eval]
        rw [Frame.set_ne _ _ (by decide), Frame.set_ne _ _ (by decide), hy₁, ult_bword _ hn, bword_and]
      have hfe₄ := hfe₁.keep (Runs.seq hr₂ (Runs.seq hr₃ hr₄)).keep
      have hr₅ := atomWord_u64 (κ := κ) (ω := ω) j RX hb₄ henv hfe₄ hl hnh.2.2 hnL hnU
      let f₅ := f₄.set RX (j.denote env)
      have hr₆ := Runs.bin (κ := κ) (ω := ω) (L := L) .ult RX (.slot RX) (.imm (UInt64.ofNat n)) f₅ h
      let f₆ := f₅.set RX (BinOp.ult.eval ((Operand.slot RX).eval f₅)
        ((Operand.imm (UInt64.ofNat n)).eval f₅))
      have hr₇ := Runs.bin (κ := κ) (ω := ω) (L := L) .band RY (.slot RY) (.slot RX) f₆ h
      let f₇ := f₆.set RY (BinOp.band.eval ((Operand.slot RY).eval f₆) ((Operand.slot RX).eval f₆))
      have hb₇ : f₇ BP = UInt64.ofNat bp := by simp [f₇, f₆, f₅, Frame.set, hb₄]
      have hy₇ : f₇ RY = bword (p.check env && decide ((i.denote env).toNat < n) &&
          decide ((j.denote env).toNat < n)) := by
        simp only [f₇, f₆, f₅, Frame.set_same, eval_slot, eval_imm, BinOp.eval]
        rw [Frame.set_ne _ _ (by decide), Frame.set_ne _ _ (by decide), hy₄, ult_bword _ hn, bword_and]
      have hfe₇ := hfe₄.keep (Runs.seq hr₅ (Runs.seq hr₆ hr₇)).keep
      have hr₈ := atomWord_u64 (κ := κ) (ω := ω) i RX hb₇ henv hfe₇ hl hnh.2.1 hnL hnU
      let f₈ := f₇.set RX (i.denote env)
      have hb₈ : f₈ BP = UInt64.ofNat bp := by simp [f₈, Frame.set, hb₇]
      have hr₉ := atomWord_u64 (κ := κ) (ω := ω) j RT hb₈ henv (hfe₇.keep hr₈.keep) hl hnh.2.2 hnL
        hnU
      let f₉ := f₈.set RT (j.denote env)
      have hr₁₀ := Runs.bin (κ := κ) (ω := ω) (L := L) .ne RX (.slot RX) (.slot RT) f₉ h
      let f₁₀ := f₉.set RX (BinOp.ne.eval ((Operand.slot RX).eval f₉) ((Operand.slot RT).eval f₉))
      have hr₁₁ := Runs.bin (κ := κ) (ω := ω) (L := L) .band RY (.slot RY) (.slot RX) f₁₀ h
      let f₁₁ := f₁₀.set RY (BinOp.band.eval ((Operand.slot RY).eval f₁₀)
        ((Operand.slot RX).eval f₁₀))
      refine ⟨f₁₁, Runs.seq hr₁ (Runs.seq hr₂ (Runs.seq hr₃ (Runs.seq hr₄ (Runs.seq hr₅
        (Runs.seq hr₆ (Runs.seq hr₇ (Runs.seq hr₈ (Runs.seq hr₉ (Runs.seq hr₁₀ hr₁₁))))))))),
        by simp [f₁₁, f₁₀, f₉, f₈, Frame.set, hb₇, hf], ?_⟩
      simp only [f₁₁, f₁₀, f₉, f₈, Frame.set_same, eval_slot, BinOp.eval]
      rw [Frame.set_ne _ _ (by decide), Frame.set_ne _ _ (by decide), Frame.set_ne _ _ (by decide),
        hy₇, Frame.set_ne _ _ (by decide), Frame.set_same, ne_bword, bword_and]
      simp only [Place.check, Bool.and_assoc]
    · cases hc

/-- Whether a place has a run-time check does not depend on the layout. -/
theorem placeCheck_isSome {Γ : List Ty} (ρ ρ' : List Loc) :
    ∀ {t : Ty} (p : Place Γ t), (placeCheck p ρ).isSome = (placeCheck p ρ').isSome := by
  intro t p
  induction p with
  | var => rfl
  | field p l ih => exact ih
  | index p i ih =>
    simp only [placeCheck]; split <;> simp [Option.isSome_map, ih]
  | pair2 p i j ih =>
    simp only [placeCheck]; split <;> simp [Option.isSome_map, ih]
  | range p lo len ih =>
    simp only [placeCheck]; split <;> simp [Option.isSome_map, ih]
  | slot => rfl
  | rangeS => rfl
  | pair2S => rfl

theorem result_unit_size : (Ty.result .unit .unit).size = 1 := by decide

/-- The case of `guard (valid p)`, in which the check's bit is the tag byte of the
`Result Unit Unit`. -/
theorem msound_guard {Γ : List Ty} {t : Ty} (p : Place Γ t) (hck : p.checkable = true)
    (hp : (placeCheck p []).isSome = true) : MSoundAt κ ω (.guard (.valid p hck)) := by
  refine .leaf fun L W ρ S n d bp env k f h w c H => ?_
  have hdn := H.dn0; have hd := H.away0; have hb := H.nU; have hbL := H.nL
  have hS := result_unit_size
  rw [placeCheck_isSome [] ρ, Option.isSome_iff_exists] at hp
  obtain ⟨c₀, h₀⟩ := hp
  obtain ⟨f₁, hr₁, hb₁, hy₁⟩ := placeCheck_runs (κ := κ) (ω := ω) (L := L) H.envRel H.lay (by omega)
    (by omega) p c₀ f H.bpOk H.sl.rel h₀ (p.nh_of .read fun i H' h' => H.hole i H' h').1
  have hst : Runs κ ω L (.store .w8 (.slot BP) (UInt64.ofNat d) (.slot RY)) f₁ h f₁
      (h.store8 (UInt64.ofNat (bp + d)) (bword (p.check env)).toUInt8) :=
    Runs.congr (Runs.store _ _ _ _ _ _ (acc_off (b := 1) (by omega) (by omega) (hb₁.trans H.bpOk))) rfl
      (by simp only [eval_slot, hb₁, H.bpOk, hy₁, ofNat_add_ofNat]; rfl)
  have hrun : Runs κ ω L (guardCode (.valid p hck) ρ d) f h f₁
      (h.store8 (UInt64.ofNat (bp + d)) (bword (p.check env)).toUInt8) := by
    simp only [guardCode, h₀, Option.getD_some]
    exact Runs.seq hr₁ hst
  refine MSim.tick_done H.run hrun rfl (by simp [Exp.exec, Tick.cost, Guard.depth]) hb₁ ?_ ?_
  · show Data.reprBytes _ (rd _ _ (Data.shape (Ty.unit.result Ty.unit).carrier).size)
    rw [show (Data.shape (Ty.unit.result Ty.unit).carrier).size = 1 by decide]
    simp only [Exp.exec, Guard.denote]
    have hrd : rd (h.store8 (UInt64.ofNat (bp + d)) (bword (p.check env)).toUInt8) (bp + d) 1 =
        [(bword (p.check env)).toUInt8] := by simp [rd, Heap.store8]
    rw [hrd]
    by_cases hc : p.check env = true
    · simp only [hc, ↓reduceIte]
      exact result_repr_ok (ε := .unit) (α := .unit) () _ (by rw [hS]; rfl) rfl
        ⟨rfl, Data.encode_repr ()⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact result_repr_err (ε := .unit) (α := .unit) () _ (by rw [hS]; rfl) rfl
        ⟨rfl, Data.encode_repr ()⟩
  · intro x hx; unfold Prot InR at hx
    simp only [Heap.store8]
    rw [ite_eq_right (ofNat_ne (by omega) (by omega) (by omega))]

end

end Millipede.Flat
