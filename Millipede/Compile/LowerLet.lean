import Millipede.Compile.LowerCalls

/-!
# The memory refinement of `let`

`let x := e₁; e₂` lowers `e₁` to the binder's storage and `e₂` under the binder. A slot-resident
binder receives its value in its frame slots. When every tail of `e₁` can compute into the slots,
`e₁` is lowered in tail mode `Tl.word`; otherwise it is lowered to the binder's memory and the value
is loaded into the slots. The tails that compute into slots include atoms, primitives, contiguous
place reads, whole-word fields, extern and call results, and `ok` and `err`, so this module comes
after the proofs for calls and externs.
-/

namespace Millipede.Flat

section
variable {κ : CostModel} {ω : Oracle} {L : Nat}

/-! ## `let` -/

/-- A term uses its view variables in tail mode `word k` as in mode `none`, since only the
in-place components of a `split` mode differ. -/
theorem _root_.Millipede.Exp.VSafe_word {Γ : List Ty} {t : Ty} (e : Exp Γ t) (k : Nat) :
    ∀ i, e.VSafe i (.word k) = e.VSafe i .none := by
  induction e <;> intro i <;> simp_all [Exp.VSafe, Tl.up]

/-- A slot-resident binder receives its value in the slots from `K = FR + slotsIn ρ`. The bound
term `e₁` computes it straight into them when its tails allow, and otherwise it is lowered to its
memory destination `n` and loaded. Then `rest` runs in a frame whose slots from `K` hold `e₁`'s
value and whose slots of `ρ`'s variables are unchanged. -/
theorem msim_slotInit {Γ : List Ty} {s β : Ty} (e₁ : Exp Γ s) (ih₁ : MSoundAt κ ω e₁)
    {ρ : List Loc} {S : List SI} {W : List Bool} {n bp : Nat} {env : Env Γ} {f : Frame}
    {h : Heap} {w : World} {c : Nat} {rest : Stmt} {k : List Kont} {Q : β.carrier → Frame → Heap → Prop}
    {prot pf : Nat → Prop} {r₂ : Out β.carrier}
    (H₁ : MHyp ω e₁ .none L (noW W) ρ S (n + s.size) n bp env f h w) (hts : s.slotTy = true)
    (hp : ∀ a, prot a → Prot bp (n + s.size) n s.size Γ S (noW W) a)
    (hpf : ∀ x, pf x → SProt ρ (noW W) x)
    (hhalt : (e₁.exec ω κ .copy env w).world.halted = true → r₂.world = (e₁.exec ω κ .copy env w).world)
    (h₂ : ∀ f₁ m₁, f₁ BP = f BP → (∀ x, FR ≤ x → x < FR + slotsIn ρ → f₁ x = f x) →
      WordsRel s (e₁.exec ω κ .copy env w).val f₁ (FR + slotsIn ρ) →
      (∀ a, Prot bp (n + s.size) n s.size Γ S (noW W) a →
        m₁ (UInt64.ofNat a) = h (UInt64.ofNat a)) →
      (e₁.exec ω κ .copy env w).world.halted = false →
      MSim κ ω L ⟨rest, k, f₁, m₁, (e₁.exec ω κ .copy env w).world, c + (e₁.exec ω κ .copy env w).steps⟩ k
        Q prot r₂ pf) :
    MSim κ ω L ⟨.seq (if e₁.Conf (.word (FR + slotsIn ρ)) then
          lowerM e₁ (.word (FR + slotsIn ρ)) ρ (n + s.size) n
        else .seq (lowerM e₁ .none ρ (n + s.size) n)
          (ldSlots (scalarWidth s.size) (FR + slotsIn ρ) (.slot BP) n s.slotN)) rest,
      k, f, h, w, c⟩ k Q prot ⟨r₂.val, r₂.world, (e₁.exec ω κ .copy env w).steps + r₂.steps⟩ pf := by
  have hok := H₁.sl.ok
  have hroom := H₁.room
  have hsz := H₁.size
  -- the bound term's code leaves its value in the slots from `K`
  have hX : MSim κ ω L ⟨if e₁.Conf (.word (FR + slotsIn ρ)) then
          lowerM e₁ (.word (FR + slotsIn ρ)) ρ (n + s.size) n
        else .seq (lowerM e₁ .none ρ (n + s.size) n)
          (ldSlots (scalarWidth s.size) (FR + slotsIn ρ) (.slot BP) n s.slotN),
        .seq rest :: k, f, h, w, c⟩ (.seq rest :: k)
      (fun v f' _ => WordsRel s v f' (FR + slotsIn ρ)) (Prot bp (n + s.size) n s.size Γ S (noW W))
      (e₁.exec ω κ .copy env w) (SProt ρ (noW W)) := by
    split
    · rename_i hw
      exact (ih₁.app (tm := .word (FR + slotsIn ρ)) ⟨hw, Tl.Ok.word_top _ hok, H₁.restr, H₁.lawful,
        H₁.frozen, H₁.hole, H₁.lay,
        by simp [Tl.dsz], H₁.away.sub (Nat.le_refl _) (by simp [Tl.dsz]), H₁.size, H₁.bpOk, H₁.envRel,
        H₁.safe, H₁.run, H₁.room, H₁.vs.mono fun i h => by rw [Exp.VSafe_word]; exact h,
        H₁.sl.sub H₁.sl.rel fun i h _ => ⟨h, by simp [Tl.vars]⟩⟩ _ c).weaken
        (fun a (ha : Prot bp (n + s.size) n s.size Γ S (noW W) a) =>
          ⟨ha.1, by simp [Tl.dsz, InR], ha.2.2⟩)
    · exact (MSim.seq_intro H₁.run (MSim.bindKF (r₂ := ⟨(e₁.exec ω κ .copy env w).val,
          (e₁.exec ω κ .copy env w).world, 0⟩) (ih₁.app H₁ _ c) (fun _ => rfl)
        (fun a ha => ⟨ha, ha⟩) (fun x hx => ⟨hx, hx⟩)
        (fun f₁ m₁ hf₁ hfk hv hm hh => by
          obtain ⟨f', hld, hfb, hlo, hword⟩ := load_words (κ := κ) (ω := ω) (L := L)
            (K := FR + slotsIn ρ) hts (hf₁.trans H₁.bpOk) (by decide) (Nat.le_add_right _ _) hv
            (by omega) (by omega)
          exact MSim.reaches_done hh hld rfl rfl hfb hword (fun _ _ => rfl)
            fun x _ hp => hlo x (SProt.lt hok hp)))).of_eq rfl rfl (by simp)
  exact MSim.seq_intro H₁.run (MSim.bindKF hX hhalt (fun a ha => ⟨hp a ha, ha⟩)
    (fun x hx => ⟨hpf x hx, hx⟩)
    fun f₁ m₁ hf₁ hfk hv hm hh => h₂ f₁ m₁ hf₁
      (fun x hx hlt => hfk x hx (let ⟨i, hi⟩ := hok.cover x hx hlt; ⟨i, hi, noW_getD W i⟩))
      hv hm hh)

/-- `let` lowers the bound term to the binder's storage, which is its memory at the watermark or,
for a slot-resident binder, its frame slots, and then the body under the binder. -/
theorem msound_let {Γ : List Ty} {s t : Ty} (e₁ : Exp Γ s) (e₂ : Exp (s :: Γ) t)
    (ih₁ : MSoundAt κ ω e₁) (ih₂ : MSoundAt κ ω e₂) : MSoundAt κ ω (.let_ e₁ e₂) := by
  refine .intro fun tm L W ρ S n d bp env k f h w c H => ?_
  have hb := H.size; have hbL := H.room; have hdn := H.dn; have hs := H.safe
  simp only [Exp.memNeed] at hb hbL
  simp only [Exp.safe] at hs
  have hm₁ := Nat.le_max_left e₁.memNeed e₂.memNeed
  have hm₂ := Nat.le_max_right e₁.memNeed e₂.memNeed
  have hna₁ : ∀ i, (Exp.let_ e₁ e₂).noAddr i = true → e₁.noAddr i = true := fun i h => by
    simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.1
  have hna₂ : ∀ i, (Exp.let_ e₁ e₂).noAddr i = true → e₂.noAddr (i + 1) = true := fun i h => by
    simp only [Exp.noAddr, Bool.and_eq_true] at h; exact h.2
  have H₁ : MHyp ω e₁ .none L (noW W) ρ S (n + s.size) n bp env f h w :=
    ⟨by simp, trivial, H.restr.1, H.lawful.1, H.frozen.1, H.hole.sub fun _ _ h => h.1,
      H.lay.noW.mono (by omega), by simp [Tl.dsz], H.lay.away (Nat.le_refl _), by omega, H.bpOk,
      H.envRel, hs.1, H.run, by omega,
      H.vs.mono (fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.1),
      H.sl.sub H.sl.rel fun i h _ => ⟨hna₁ i h, by simp [Tl.vars]⟩⟩
  have hp : ∀ a, Prot bp n d (tm.dsz t) Γ S W a → Prot bp (n + s.size) n s.size Γ S (noW W) a :=
    fun a ha => ⟨by unfold Prot at ha; omega,
      fun e => by unfold InR at e; unfold Prot at ha; omega, InW.noW⟩
  have henv₂ : ∀ m₁ : Heap, (∀ a, Prot bp (n + s.size) n s.size Γ S (noW W) a →
      m₁ (UInt64.ofNat a) = h (UInt64.ofNat a)) → MEnvRel m₁ bp env ρ S := fun m₁ hm =>
    H.envRel.of_prot (sz := s.size) (H.lay.mono (Nat.le_add_right n s.size))
      (H.lay.away (Nat.le_refl _)) hm
  have hsafe₂ : e₂.safe ω (.cons (e₁.exec ω κ .copy env w).val env) (e₁.exec ω κ .copy env w).world := by
    rw [Exp.exec_val, Exp.exec_world]; exact hs.2
  have hV₂ : VS S fun i => e₂.VSafe (i + 1) tm.up :=
    H.vs.mono fun i h => by simp only [Exp.VSafe, Bool.and_eq_true] at h; exact h.2
  by_cases hsb : e₂.slotBind = true
  · have hts : s.slotTy = true := by
      simp only [Exp.slotBind, Bool.and_eq_true] at hsb; exact hsb.1.1
    have hna0 : e₂.noAddr 0 = true := by
      simp only [Exp.slotBind, Bool.and_eq_true] at hsb; exact hsb.1.2
    simp only [lowerM, hsb, ↓reduceIte]
    have hbind := msim_slotInit (pf := SProt ρ W) (prot := Prot bp n d (tm.dsz t) Γ S W)
      (Q := TQ tm bp d ρ S t) (k := k) (c := c + κ.let_)
      (rest := lowerM e₂ tm.up (.slot n (FR + slotsIn ρ) s.slotN :: ρ) (n + s.size) d)
      (r₂ := e₂.exec ω κ tm.up.hb (.cons (e₁.exec ω κ .copy env w).val env) (e₁.exec ω κ .copy env w).world)
      e₁ ih₁ H₁ hts hp (fun x hx => hx.noW)
      (fun hh => exec_halted ω κ e₂ _ _ hh)
      (fun f₁ m₁ hf₁ hfρ hw hm hh => .unpush (Nat.le_refl _) (ih₂.app (H.pushSlot _ (Nat.le_refl _)
        (conf_let H.conf) H.restr.2 H.lawful.2 H.frozen.2 (H.hole.push _ rfl fun _ _ h => h.2)
        (by omega) (by omega) (hf₁.trans H.bpOk) (henv₂ m₁ hm)
        (H.sl.rel.below H.sl.ok hfρ) hts hw hsafe₂ hV₂ hh hna0 hna₂) k _))
    have := MSim.tick (t := .let_) H.run hbind
    exact this.of_eq (by simp [Exp.exec, Tl.hb_up]) (by simp [Exp.exec, Tl.hb_up]) (by simp [Exp.exec, Tick.cost, Tl.hb_up]; omega)
  · simp only [lowerM, hsb, Bool.false_eq_true, ↓reduceIte]
    have h₁ := ih₁.app H₁ (.seq (lowerM e₂ tm.up (.own n :: ρ) (n + s.size) d) :: k) (c + κ.let_)
    have hbind := MSim.bindF (pf := SProt ρ W) (prot₂ := Prot bp n d (tm.dsz t) Γ S W)
      (r₂ := e₂.exec ω κ tm.up.hb (.cons (e₁.exec ω κ .copy env w).val env) (e₁.exec ω κ .copy env w).world) h₁
      (fun hh => exec_halted ω κ e₂ _ _ hh) (fun a ha => ⟨hp a ha, ha⟩)
      (fun x hx => ⟨by obtain ⟨i, hi, _⟩ := hx; exact ⟨i, hi, noW_getD W i⟩, hx⟩)
      (fun f₁ m₁ hf₁ hfk hv hm hh => .unpush (Nat.le_refl _) (ih₂.app (H.push _ (Nat.le_refl _)
        (conf_let H.conf) H.restr.2 H.lawful.2 H.frozen.2 (H.hole.push _ rfl fun _ _ h => h.2)
        (by omega) (by omega) (hf₁.trans H.bpOk) (henv₂ m₁ hm) (H.sl.rel.prot hfk) hv
        hsafe₂ hV₂ hh hna₂) k _))
    have := MSim.tick (t := .let_) H.run (MSim.seq_intro H.run hbind)
    exact this.of_eq (by simp [Exp.exec, Tl.hb_up]) (by simp [Exp.exec, Tl.hb_up]) (by simp [Exp.exec, Tick.cost, Tl.hb_up]; omega)

end

end Millipede.Flat
