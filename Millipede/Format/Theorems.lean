import Millipede.Format.Model

/-!
# Format descriptions: the theorems

Proved once, for every description `f` (`Millipede/Format/Model.lean`):

- `Fmt.parse_write`: parsing the bytes of a value of `f`, followed by any bytes, gives the value
  back and the bytes that follow;
- `Fmt.write_length_le`: the bytes of a value are at most `f.maxSize`;
- `Fmt.parse_sound`: a parsed value is a value of `f`, and the bytes consumed are a prefix of the
  input as long as the value's bytes, so at most `f.maxSize` (`Fmt.parse_consumed_le`);
- `Fmt.parse_canonical`: when `f` is canonical, the bytes consumed are the bytes of the parsed
  value, so no two byte strings parse to the same value (`Fmt.parse_injective`);
- `Fmt.check_eq`, `Fmt.valid_iff`: the validator accepts exactly what the parser accepts, and
  leaves the same bytes.

Each is the instance at tag 0 of a statement over every selected tag (`…T`), proved by one
induction over the description.
-/

namespace Millipede.Format

/-! ## Integers -/

@[simp] theorem leBytes_length (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n <;> simp [leBytes, *]

theorem leVal_leBytes (k n : Nat) : leVal (leBytes k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [leBytes, leVal, Nat.mod_one]
  | succ k ih =>
    simp only [leBytes, leVal, ih]
    rw [Nat.pow_succ', Nat.mod_mul]
    simp

theorem leVal_lt (l : List UInt8) : leVal l < 256 ^ l.length := by
  induction l with
  | nil => simp [leVal]
  | cons b l ih =>
    simp only [leVal, List.length_cons, Nat.pow_succ']
    have := b.toNat_lt
    omega

theorem leBytes_leVal (l : List UInt8) : leBytes l.length (leVal l) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.length_cons, leBytes, leVal]
    have := b.toNat_lt
    rw [show (b.toNat + 256 * leVal l) / 256 = leVal l by omega,
      show (b.toNat + 256 * leVal l) % 256 = b.toNat by omega, ih]
    simp

@[simp] theorem encUint_length (k : Nat) (e : Endian) (n : Nat) : (encUint k e n).length = k := by
  cases e <;> simp [encUint]

theorem decUint_encUint (k : Nat) (e : Endian) (n : Nat) (h : n < 256 ^ k) :
    decUint e (encUint k e n) = n := by
  cases e <;> simp [decUint, encUint, leVal_leBytes, Nat.mod_eq_of_lt h]

theorem decUint_lt (e : Endian) (l : List UInt8) : decUint e l < 256 ^ l.length := by
  cases e <;> simp only [decUint]
  · simpa using leVal_lt l.reverse
  · exact leVal_lt l

theorem encUint_decUint (e : Endian) (l : List UInt8) : encUint l.length e (decUint e l) = l := by
  cases e <;> simp only [decUint, encUint]
  · rw [← List.length_reverse, leBytes_leVal, List.reverse_reverse]
  · exact leBytes_leVal l

theorem readUint_encUint (k : Nat) (e : Endian) (n : Nat) (rest : List UInt8) (h : n < 256 ^ k) :
    readUint k e (encUint k e n ++ rest) = some (n, rest) := by
  simp [readUint, List.take_left', List.drop_left', decUint_encUint k e n h]

theorem readUint_some {k : Nat} {e : Endian} {bs r : List UInt8} {n : Nat}
    (h : readUint k e bs = some (n, r)) : n < 256 ^ k ∧ bs = encUint k e n ++ r := by
  simp only [readUint] at h
  split at h
  · cases h
    have hl : (bs.take k).length = k := by simp; omega
    have hlt := decUint_lt e (bs.take k)
    rw [hl] at hlt
    refine ⟨hlt, ?_⟩
    have he := encUint_decUint e (bs.take k)
    rw [hl] at he
    rw [he, List.take_append_drop]
  · cases h

/-! ## Repetitions -/

section Items
variable {p : List UInt8 → Option (Val × List UInt8)} {w : Val → List UInt8} {okf : Val → Bool}

theorem parseItems_write (h : ∀ v rest, okf v = true → p (w v ++ rest) = some (v, rest))
    (v : Val) (rest : List UInt8) (hv : v.allItems okf = true) :
    parseItems p v.count (v.writeItems w ++ rest) = some (v, rest) := by
  induction v <;> grind [Val.allItems, Val.count, Val.writeItems, parseItems]

theorem writeItems_length_le {M : Nat} (h : ∀ v, okf v = true → (w v).length ≤ M) (v : Val)
    (hv : v.allItems okf = true) : (v.writeItems w).length ≤ v.count * M := by
  induction v with
  | pair a b _ ihb =>
    simp only [Val.allItems, Bool.and_eq_true] at hv
    simp only [Val.writeItems, Val.count, List.length_append, Nat.succ_mul]
    have := h a hv.1; have := ihb hv.2; omega
  | _ => simp [Val.writeItems]

theorem parseItems_sound
    (h : ∀ bs v r, p bs = some (v, r) → okf v = true ∧
      ∃ pre, bs = pre ++ r ∧ pre.length = (w v).length ∧ (c → pre = w v))
    (n : Nat) (bs : List UInt8) (v : Val) (r : List UInt8) (hp : parseItems p n bs = some (v, r)) :
    v.allItems okf = true ∧ v.count = n ∧
      ∃ pre, bs = pre ++ r ∧ pre.length = (v.writeItems w).length ∧ (c → pre = v.writeItems w) := by
  induction n generalizing bs v r with
  | zero =>
    simp only [parseItems, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨rfl, rfl, [], by simp, by simp [Val.writeItems], by simp [Val.writeItems]⟩
  | succ n ih =>
    simp only [parseItems] at hp
    split at hp; · cases hp
    rename_i a r₁ ha
    split at hp; · cases hp
    rename_i vs r₂ hvs
    cases hp
    obtain ⟨hoa, pa, rfl, hla, hca⟩ := h _ _ _ ha
    obtain ⟨hos, hcs, ps, rfl, hls, hcs'⟩ := ih _ _ _ hvs
    refine ⟨by simp [Val.allItems, hoa, hos], by simp [Val.count, hcs], pa ++ ps, by simp,
      by simp [Val.writeItems, hla, hls], fun hc => by simp [Val.writeItems, hca hc, hcs' hc]⟩

theorem checkItems_eq {q : List UInt8 → Option (List UInt8)}
    (h : ∀ bs, q bs = (p bs).map Prod.snd) (n : Nat) (bs : List UInt8) :
    checkItems q n bs = (parseItems p n bs).map Prod.snd := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    simp only [checkItems, parseItems, h]
    cases p bs with
    | none => rfl
    | some x => simp only [Option.map_some, ih]; cases parseItems p n x.2 <;> rfl

end Items

/-! ## The theorems, for every selected tag -/

namespace Fmt

theorem parseT_writeT (f : Fmt) (t : Nat) (v : Val) (rest : List UInt8) (h : f.okT t v = true) :
    f.parseT t (f.writeT t v ++ rest) = some (v, rest) := by
  induction f generalizing t v rest with
  | uint k e =>
    cases v <;> simp_all [okT, writeT, parseT, readUint_encUint]
  | bytes n => cases v <;> simp_all [okT, writeT, parseT]
  | const l => cases v <;> simp_all [okT, writeT, parseT]
  | skip n => cases v <;> simp_all [okT, writeT, parseT]
  | unit => cases v <;> simp_all [okT, writeT, parseT]
  | pair a b iha ihb =>
    cases v <;> simp_all [okT, writeT, parseT]
  | lbytes k e m =>
    cases v <;> simp_all [okT, writeT, parseT, readUint_encUint]
  | array k e m f ih =>
    simp only [okT, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [writeT, parseT, List.append_assoc, readUint_encUint _ _ _ _ h.1.2, h.1.1, ite_true]
    exact parseItems_write (fun v r hv => ih 0 v r hv) v rest h.2
  | union k e arms ih =>
    cases v <;> simp_all [okT, writeT, parseT, readUint_encUint]
  | arm tag f rest' ihf ihr =>
    simp only [okT, writeT, parseT] at h ⊢
    split <;> simp_all
  | noArm => simp [okT] at h

theorem writeT_length_le (f : Fmt) (t : Nat) (v : Val) (h : f.okT t v = true) :
    (f.writeT t v).length ≤ f.maxSize := by
  induction f generalizing t v with
  | array k e m f ih =>
    simp only [okT, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [writeT, maxSize, List.length_append, encUint_length]
    have := writeItems_length_le (fun v hv => ih 0 v hv) v h.2
    have := Nat.mul_le_mul_right f.maxSize h.1.1
    omega
  | arm tag f rest ihf ihr =>
    simp only [okT, writeT, maxSize] at h ⊢
    split at h
    · simp only [*, ite_true]; have := ihf _ _ h; omega
    · simp only [*, ite_false]; have := ihr _ _ h; omega
  | pair a b iha ihb =>
    cases v <;> simp_all [okT, writeT, maxSize]
    have := iha _ _ h.1; have := ihb _ _ h.2; omega
  | union k e arms ih =>
    cases v <;> simp_all [okT, writeT, maxSize]
  | noArm => simp [okT] at h
  | _ => cases v <;> simp_all [okT, writeT, maxSize]

/-- What a parse returns: a value of the description, after a prefix of the input as long as the
value's bytes, which is those bytes when the description is canonical. -/
def Sound (f : Fmt) (t : Nat) (bs : List UInt8) (v : Val) (r : List UInt8) : Prop :=
  f.okT t v = true ∧ ∃ pre, bs = pre ++ r ∧ pre.length = (f.writeT t v).length ∧
    (f.canonical = true → pre = f.writeT t v)

theorem parseT_sound (f : Fmt) (t : Nat) (bs : List UInt8) (v : Val) (r : List UInt8)
    (h : f.parseT t bs = some (v, r)) : f.Sound t bs v r := by
  induction f generalizing t bs v r with
  | uint k e =>
    simp only [parseT, Option.map_eq_some_iff] at h
    obtain ⟨⟨n, r'⟩, hr, he⟩ := h
    cases he
    obtain ⟨hn, rfl⟩ := readUint_some hr
    exact ⟨by simp [okT, hn], _, rfl, by simp [writeT], by simp [writeT]⟩
  | bytes n =>
    simp only [parseT] at h
    split at h <;> cases h
    exact ⟨by simp [okT]; omega, _, (List.take_append_drop n bs).symm, by simp [writeT], by simp [writeT]⟩
  | const l =>
    simp only [parseT] at h
    split at h <;> cases h
    rename_i he
    exact ⟨by simp [okT], _, (List.take_append_drop _ bs).symm, by simp [writeT, he],
      by simp [writeT, he]⟩
  | skip n =>
    simp only [parseT] at h
    split at h <;> cases h
    exact ⟨by simp [okT], _, (List.take_append_drop n bs).symm, by simp [writeT]; omega,
      by simp [canonical]⟩
  | unit =>
    simp only [parseT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [okT], [], by simp, by simp [writeT], by simp [writeT]⟩
  | pair a b iha ihb =>
    simp only [parseT] at h
    split at h; · cases h
    rename_i va r₁ ha
    split at h; · cases h
    rename_i vb r₂ hb
    cases h
    obtain ⟨hoa, pa, rfl, hla, hca⟩ := iha _ _ _ _ ha
    obtain ⟨hob, pb, rfl, hlb, hcb⟩ := ihb _ _ _ _ hb
    refine ⟨by simp [okT, hoa, hob], pa ++ pb, by simp, by simp [writeT, hla, hlb], fun hc => ?_⟩
    simp only [canonical, Bool.and_eq_true] at hc
    simp [writeT, hca hc.1, hcb hc.2]
  | lbytes k e m =>
    simp only [parseT] at h
    split at h; · cases h
    rename_i n r₁ hr
    split at h <;> cases h
    rename_i hn
    obtain ⟨hk, rfl⟩ := readUint_some hr
    have hl : (r₁.take n).length = n := by simp; omega
    refine ⟨by simp [okT, hl]; omega, encUint k e n ++ r₁.take n, by simp, ?_, ?_⟩ <;>
      simp [writeT, hl]
  | array k e m f ih =>
    simp only [parseT] at h
    split at h; · cases h
    rename_i c r₁ hr
    by_cases hcm : c ≤ m
    case neg => simp [hcm] at h
    simp only [hcm, ite_true] at h
    obtain ⟨hk, rfl⟩ := readUint_some hr
    obtain ⟨hall, hcnt, pre, rfl, hl, hcan⟩ :=
      parseItems_sound (w := writeT f 0) (c := f.canonical = true) (fun bs v r hp => ih _ _ _ _ hp)
        _ _ _ _ h
    subst hcnt
    refine ⟨by simp [okT, hall, hk, hcm], encUint k e v.count ++ pre, by simp,
      by simp [writeT, hl], fun hc => by simp [writeT, hcan (by simpa [canonical] using hc)]⟩
  | union k e arms ih =>
    simp only [parseT] at h
    split at h; · cases h
    rename_i tg r₁ hr
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨va, r₂⟩, ha, he⟩ := h
    cases he
    obtain ⟨hk, rfl⟩ := readUint_some hr
    obtain ⟨hoa, pa, rfl, hla, hca⟩ := ih _ _ _ _ ha
    exact ⟨by simp [okT, hk, hoa], encUint k e tg ++ pa, by simp, by simp [writeT, hla],
      fun hc => by simp [writeT, hca (by simpa [canonical] using hc)]⟩
  | arm tag f rest ihf ihr =>
    simp only [parseT] at h
    unfold Sound
    simp only [okT, writeT, canonical, Bool.and_eq_true]
    split at h <;> rename_i ht
    · obtain ⟨ho, pre, he, hl, hc⟩ := ihf _ _ _ _ h
      simp only [ite_eq_left ht]
      exact ⟨ho, pre, he, hl, fun hc' => hc hc'.1⟩
    · obtain ⟨ho, pre, he, hl, hc⟩ := ihr _ _ _ _ h
      simp only [ite_eq_right ht]
      exact ⟨ho, pre, he, hl, fun hc' => hc hc'.2⟩
  | noArm => simp [parseT] at h

theorem checkT_eq (f : Fmt) (t : Nat) (bs : List UInt8) :
    f.checkT t bs = (f.parseT t bs).map Prod.snd := by
  induction f generalizing t bs with
  | uint k e =>
    simp only [checkT, parseT, readUint]
    split <;> simp
  | pair a b iha ihb =>
    simp only [checkT, parseT, iha]
    cases parseT a 0 bs with
    | none => rfl
    | some x => simp only [Option.map_some, ihb]; cases parseT b 0 x.2 <;> rfl
  | lbytes k e m =>
    simp only [checkT, parseT]
    cases readUint k e bs with
    | none => rfl
    | some x => simp only; split <;> simp
  | array k e m f ih =>
    simp only [checkT, parseT]
    cases readUint k e bs with
    | none => rfl
    | some x => simp only; split <;> simp [checkItems_eq (fun bs => ih 0 bs)]
  | union k e arms ih =>
    simp only [checkT, parseT]
    cases readUint k e bs with
    | none => rfl
    | some x => simp [ih, Option.map_map, Function.comp_def]
  | arm tag f rest ihf ihr =>
    simp only [checkT, parseT]
    split <;> simp [ihf, ihr]
  | _ => simp only [checkT, parseT] <;> (try split) <;> simp

end Fmt

/-! ## The theorems -/

namespace Fmt

/-- Parsing the bytes of a value, followed by any bytes, gives the value and those bytes. -/
theorem parse_write (f : Fmt) (v : Val) (rest : List UInt8) (h : f.ok v = true) :
    f.parse (f.write v ++ rest) = some (v, rest) :=
  parseT_writeT f 0 v rest h

/-- Parsing the bytes of a value gives the value and nothing left. -/
theorem parse_write_nil (f : Fmt) (v : Val) (h : f.ok v = true) :
    f.parse (f.write v) = some (v, []) := by
  simpa using parse_write f v [] h

/-- The bytes of a value are at most the static bound. -/
theorem write_length_le (f : Fmt) (v : Val) (h : f.ok v = true) : (f.write v).length ≤ f.maxSize :=
  writeT_length_le f 0 v h

/-- A parsed value is a value of the description, and the bytes consumed are a prefix of the input
as long as the value's bytes. -/
theorem parse_sound {f : Fmt} {bs : List UInt8} {v : Val} {r : List UInt8}
    (h : f.parse bs = some (v, r)) :
    f.ok v = true ∧ ∃ pre, bs = pre ++ r ∧ pre.length = (f.write v).length := by
  obtain ⟨ho, pre, he, hl, _⟩ := parseT_sound f 0 bs v r h
  exact ⟨ho, pre, he, hl⟩

/-- A parse consumes exactly the length of the value's bytes, at most the static bound. -/
theorem parse_consumed {f : Fmt} {bs : List UInt8} {v : Val} {r : List UInt8}
    (h : f.parse bs = some (v, r)) : bs.length = (f.write v).length + r.length ∧
      (f.write v).length ≤ f.maxSize := by
  obtain ⟨ho, pre, rfl, hl⟩ := parse_sound h
  exact ⟨by simp [hl], write_length_le f v ho⟩

/-- When the description is canonical, the bytes consumed are the bytes of the parsed value. -/
theorem parse_canonical {f : Fmt} (hc : f.canonical = true) {bs : List UInt8} {v : Val}
    {r : List UInt8} (h : f.parse bs = some (v, r)) : bs = f.write v ++ r := by
  obtain ⟨_, pre, he, _, hcan⟩ := parseT_sound f 0 bs v r h
  rw [he, hcan hc]; rfl

/-- When the description is canonical, two inputs that parse to the same value with the same
bytes left over are equal: no two byte strings mean the same value. -/
theorem parse_injective {f : Fmt} (hc : f.canonical = true) {bs bs' : List UInt8} {v : Val}
    {r : List UInt8} (h : f.parse bs = some (v, r)) (h' : f.parse bs' = some (v, r)) : bs = bs' := by
  rw [parse_canonical hc h, parse_canonical hc h']

/-- The validator leaves the bytes the parser leaves. -/
theorem check_eq (f : Fmt) (bs : List UInt8) : f.check bs = (f.parse bs).map Prod.snd :=
  checkT_eq f 0 bs

/-- The validator accepts exactly the inputs the parser accepts. -/
theorem valid_iff (f : Fmt) (bs : List UInt8) : f.valid bs = true ↔ (f.parse bs).isSome = true := by
  simp [valid, check_eq]

end Fmt

end Millipede.Format
