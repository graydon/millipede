import Tests.KVSpec
import Tests.FormatKVSrv

/-!
# The key-value server refines the abstract store

Tests/KVSpec.lean specifies the server `kvsrv` of Tests/FormatKVSrv.lean: `kvTrace ω` is its
whole trace under the oracle `ω`, built from the abstract store `Store` and the formats' model.
This file proves it.

* The store's four slots refine the abstract map (`Refines`, `kvServe_refines`): when the used
  slots hold the abstract map's entries, in some order, the server's answer `kvServe` to a request
  is the abstract machine's `Store.apply`, and the slots after it hold the entries of the map after
  it. The order of the slots is not visible: two maps that hold the same entries give the same
  responses (`Store.apply_resp_of_refines`).
* For every oracle and every `n`, the trace of `kvsrv` after `n` steps is the first `n` events of
  `kvTrace ω` (`kvsrv_events`). Each step makes exactly one call: a read, a write of one
  response, or the exit. The proof uses only the contracts of `srvInit` and `srvStep`, through
  `kvsrv.events_reach`, which `mp program` derives from them, and an induction over
  `Program.Reach` (`kvsrv_reach`). It does not unfold `srvStep`, `handle` or `fill`.
* For every `b` that a sound compiler produced from `kvsrv`, on either target, the bytes load and
  for every oracle the machine never gets stuck, every trace it shows is a prefix of `kvTrace ω`,
  and it shows the whole of it (`kvsrv_behaviour`). When the input the server reads is the bytes
  of a sequence of requests, followed by nothing or by bytes that do not begin with a request,
  the writes are the abstract store's responses to that sequence and the exit status is 0 or 1
  (`kvsrv_answers`).

The guarantee is one-sided: it says what the server does for every behaviour of the peer (the
oracle), and nothing about the peer.
-/

namespace Millipede.Tests.KV

open Millipede Millipede.Format Millipede.Tests.FormatKV

/-! ## The slots refine the abstract map -/

/-- The entries of the used slots, in slot order. -/
def toStore (st : List Slot) : Store := st.filterMap id

/-- The slots `st` hold the entries of the abstract map `m`: there are `capacity` slots, the keys
of `m` are distinct, and the used slots hold exactly `m`'s entries, in some order. -/
def Refines (st : List Slot) (m : Store) : Prop :=
  st.length = capacity ∧ (m.map Prod.fst).Nodup ∧ (toStore st).Perm m

theorem Store.get_of_mem {m : Store} {k : Key} {v : Value} (hnd : (m.map Prod.fst).Nodup)
    (h : (k, v) ∈ m) : m.get k = some v := by
  induction m with
  | nil => simp at h
  | cons e m ih =>
    obtain ⟨k₀, v₀⟩ := e
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp [Store.get]
    · have : k₀ ≠ k := fun e => hnd.1 ⟨(k, v), h, e.symm⟩
      simp [Store.get, this, ih hnd.2 h]

theorem Store.mem_of_get {m : Store} {k : Key} {v : Value} (h : m.get k = some v) : (k, v) ∈ m := by
  induction m with
  | nil => simp [Store.get] at h
  | cons e m ih =>
    obtain ⟨k₀, v₀⟩ := e
    simp only [Store.get] at h
    split at h
    · cases h; subst_vars; simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- Where a present key sits in the map, and what `set` and `erase` do there. -/
theorem Store.split {m : Store} {k : Key} {v₀ : Value} (h : m.get k = some v₀) :
    ∃ ma mb, m = ma ++ (k, v₀) :: mb ∧ ma.get k = none ∧ (∀ v, m.set k v = ma ++ (k, v) :: mb) ∧
      m.erase k = ma ++ mb := by
  induction m with
  | nil => simp [Store.get] at h
  | cons e m ih =>
    obtain ⟨k₀, v₁⟩ := e
    by_cases hk : k₀ = k
    · subst hk
      simp only [Store.get, ite_true, Option.some.injEq] at h
      subst h
      exact ⟨[], m, rfl, rfl, fun v => by simp [Store.set], by simp [Store.erase]⟩
    · simp only [Store.get, hk, ite_false] at h
      obtain ⟨ma, mb, rfl, hma, hset, her⟩ := ih h
      exact ⟨(k₀, v₁) :: ma, mb, rfl, by simp [Store.get, hk, hma],
        fun v => by simp [Store.set, hk, hset], by simp [Store.erase, hk, her]⟩

theorem Store.set_of_get_none {m : Store} {k : Key} (v : Value) (h : m.get k = none) :
    m.set k v = m ++ [(k, v)] := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    obtain ⟨k₀, v₀⟩ := e
    by_cases hk : k₀ = k
    · simp [Store.get, hk] at h
    · simp only [Store.get, hk, ite_false] at h
      simp [Store.set, hk, ih h]

theorem Store.get_isSome_of_mem {m : Store} {k : Key} {v : Value} (h : (k, v) ∈ m) :
    (m.get k).isSome := by
  induction m with
  | nil => simp at h
  | cons e m ih =>
    obtain ⟨k₀, v₀⟩ := e
    simp only [Store.get]
    split
    · rfl
    · simp only [List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, -⟩ | h
      · contradiction
      · exact ih h

theorem Store.not_mem_keys {m : Store} {k : Key} (h : m.get k = none) : k ∉ m.map Prod.fst := by
  intro hk
  obtain ⟨⟨k', v⟩, hm, rfl⟩ := List.mem_map.mp hk
  simpa [h] using Store.get_isSome_of_mem hm

/-- `Store.apply` keeps the keys distinct. -/
theorem Store.apply_nodup (m : Store) (q : Req) (hnd : (m.map Prod.fst).Nodup) :
    ((m.apply q).1.map Prod.fst).Nodup := by
  have hset : ∀ k v, ((m.set k v).map Prod.fst).Nodup := fun k v => by
    cases h : m.get k with
    | none =>
      rw [Store.set_of_get_none v h]
      have := Store.not_mem_keys h
      simp only [List.map_append, List.map_cons, List.map_nil]
      exact List.nodup_append.mpr ⟨hnd, by simp,
        fun a ha b hb => by simp at hb; subst hb; exact fun e => this (e ▸ ha)⟩
    | some v₀ =>
      obtain ⟨ma, mb, rfl, -, hs, -⟩ := Store.split h
      rw [hs]; simpa using hnd
  cases q with
  | get k => exact hnd
  | put k v =>
    simp only [Store.apply]; split
    · exact hset k v
    · exact hnd
  | del k =>
    simp only [Store.apply]; split
    · rename_i h
      obtain ⟨v₀, hv⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨ma, mb, rfl, -, -, he⟩ := Store.split hv
      rw [he]
      simp only [List.map_append, List.map_cons] at hnd ⊢
      exact ((List.perm_middle.nodup_iff).mp hnd).of_cons
    · exact hnd

/-! ### The slots -/

theorem lookup_found {st : List Slot} {k : Key} (h : lookup st k < st.length) :
    ∃ v, st[lookup st k]? = some (some (k, v)) := by
  obtain ⟨x, hx⟩ : ∃ x, st[lookup st k]? = some x := ⟨_, List.getElem?_eq_getElem h⟩
  have hp := List.findIdx_of_getElem?_eq_some hx
  rcases x with _ | ⟨k', v⟩
  · simp at hp
  · simp only [Option.any_some, beq_iff_eq] at hp
    subst hp; exact ⟨v, hx⟩

theorem lookup_missing {st : List Slot} {k : Key} (h : ¬ lookup st k < st.length) (v : Value) :
    some (k, v) ∉ st := by
  intro hm
  exact h (List.findIdx_lt_length.mpr ⟨_, hm, by simp⟩)

theorem lookup_eq_length {st : List Slot} {k : Key} (h : ¬ lookup st k < st.length) :
    lookup st k = st.length :=
  Nat.le_antisymm List.findIdx_le_length (Nat.le_of_not_lt h)

theorem freeAt_found {st : List Slot} (h : freeAt st < st.length) :
    st[freeAt st]? = some none := by
  obtain ⟨x, hx⟩ : ∃ x, st[freeAt st]? = some x := ⟨_, List.getElem?_eq_getElem h⟩
  have hp := List.findIdx_of_getElem?_eq_some hx
  cases x
  · exact hx
  · simp at hp

theorem freeAt_lt_iff (st : List Slot) : freeAt st < st.length ↔ none ∈ st := by
  simp [freeAt]

theorem toStore_length_lt (st : List Slot) : (toStore st).length < st.length ↔ none ∈ st := by
  induction st with
  | nil => simp [toStore]
  | cons x st ih =>
    have := List.length_filterMap_le id st
    cases x
    · rw [show toStore (none :: st) = toStore st from rfl]
      simp only [toStore, List.length_cons, List.mem_cons, true_or, iff_true]
      omega
    · simp_all [toStore]

theorem mem_toStore {st : List Slot} {e : Key × Value} : e ∈ toStore st ↔ some e ∈ st := by
  simp [toStore]

/-- The entries of the slots around slot `j`, before and after it is set to `y`. -/
theorem toStore_set {st : List Slot} {j : Nat} {x : Slot} (hx : st[j]? = some x) (y : Slot) :
    ∃ a b, toStore st = a ++ x.toList ++ b ∧ toStore (st.set j y) = a ++ y.toList ++ b := by
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hx
  refine ⟨toStore (st.take j), toStore (st.drop (j + 1)), ?_, ?_⟩
  · have hst : st = st.take j ++ x :: st.drop (j + 1) := by
      rw [← he, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
    conv => lhs; rw [hst]
    cases x <;> simp [toStore, List.filterMap_append]
  · rw [List.set_eq_take_append_cons_drop, ite_eq_left_iff.mpr (fun h => absurd hj h)]
    cases y <;> simp [toStore, List.filterMap_append]

/-- Replacing one entry on both sides of a permutation. -/
theorem perm_replace {α : Type} {a b c d : List α} {e e' : α} (h : (a ++ e :: b).Perm (c ++ e :: d)) :
    (a ++ e' :: b).Perm (c ++ e' :: d) :=
  List.perm_middle.trans ((List.perm_middle.symm.trans (h.trans List.perm_middle)).cons_inv.cons e'
    |>.trans List.perm_middle.symm)

/-- Removing one entry on both sides of a permutation. -/
theorem perm_remove {α : Type} {a b c d : List α} {e : α} (h : (a ++ e :: b).Perm (c ++ e :: d)) :
    (a ++ b).Perm (c ++ d) :=
  (List.perm_middle.symm.trans (h.trans List.perm_middle)).cons_inv

theorem Refines.found {st : List Slot} {m : Store} {k : Key} (h : Refines st m)
    (hl : lookup st k < st.length) :
    ∃ v, st[lookup st k]? = some (some (k, v)) ∧ m.get k = some v := by
  obtain ⟨v, hv⟩ := lookup_found hl
  refine ⟨v, hv, Store.get_of_mem h.2.1 (h.2.2.subset (mem_toStore.mpr ?_))⟩
  exact List.mem_of_getElem? hv

theorem Refines.missing {st : List Slot} {m : Store} {k : Key} (h : Refines st m)
    (hl : ¬ lookup st k < st.length) : m.get k = none := by
  cases hg : m.get k with
  | none => rfl
  | some v =>
    exact absurd (mem_toStore.mp (h.2.2.symm.subset (Store.mem_of_get hg))) (lookup_missing hl v)

/-- The server's answer to a request from slots that hold the abstract map `m` is the abstract
store's answer, and the slots after it hold the abstract map after it. -/
theorem kvServe_refines {st : List Slot} {m : Store} (h : Refines st m) (id : Nat) (q : Req) :
    Refines (kvServe st (q.toVal id)).1 (m.apply q).1 ∧
      (kvServe st (q.toVal id)).2 = (m.apply q).2.toVal id := by
  have hlen : st.length = 4 := h.1
  have hnd' := Store.apply_nodup m q h.2.1
  cases q with
  | get k =>
    simp only [Req.toVal, kvServe, Store.apply]
    refine ⟨?_, ?_⟩
    · split <;> exact h
    by_cases hl : lookup st k < st.length
    · obtain ⟨v, hv, hg⟩ := h.found hl
      simp [hv, hg, respVal, Resp.toVal]
    · rw [h.missing hl, lookup_eq_length hl, List.getElem?_eq_none (Nat.le_refl _)]
      simp [respVal, Resp.toVal]
  | put k v =>
    simp only [Req.toVal, kvServe, Store.apply] at hnd' ⊢
    by_cases hl : lookup st k < st.length
    · obtain ⟨v₀, hv, hg⟩ := h.found hl
      have hs : (m.get k).isSome ∨ m.length < capacity := Or.inl (by simp [hg])
      simp only [hl, ite_true, hs, ite_true] at hnd' ⊢
      refine ⟨⟨by simp [hlen, capacity], hnd', ?_⟩, rfl⟩
      obtain ⟨a, b, hst, hst'⟩ := toStore_set hv (some (k, v))
      obtain ⟨ma, mb, hm, -, hset, -⟩ := Store.split hg
      rw [hst', hset]
      have hp := h.2.2
      rw [hst, hm] at hp
      simpa using perm_replace (e' := (k, v)) (by simpa using hp)
    · have hg := h.missing hl
      simp only [hl, ite_false, hg, Option.isSome_none, Bool.false_eq_true, false_or] at hnd' ⊢
      by_cases hf : freeAt st < st.length
      · have hroom : m.length < capacity := by
          rw [← h.2.2.length_eq]
          exact Nat.lt_of_lt_of_eq ((toStore_length_lt st).mpr ((freeAt_lt_iff st).mp hf)) hlen
        simp only [hf, ite_true, hroom, ite_true] at hnd' ⊢
        refine ⟨⟨by simp [hlen, capacity], hnd', ?_⟩, rfl⟩
        obtain ⟨a, b, hst, hst'⟩ := toStore_set (freeAt_found hf) (some (k, v))
        rw [hst', Store.set_of_get_none v hg]
        have hp := h.2.2
        rw [hst] at hp
        simp only [Option.toList_some, Option.toList_none, List.append_nil] at hp ⊢
        simp only [List.append_assoc, List.singleton_append]
        exact List.perm_middle.trans ((hp.cons _).trans (List.perm_append_singleton _ _).symm)
      · have hfull : ¬ m.length < capacity := by
          rw [← h.2.2.length_eq]
          have : ¬ (toStore st).length < st.length :=
            fun hc => hf ((freeAt_lt_iff st).mpr ((toStore_length_lt st).mp hc))
          simp [capacity]; omega
        simp only [hf, ite_false, hfull] at hnd' ⊢
        exact ⟨h, rfl⟩
  | del k =>
    simp only [Req.toVal, kvServe, Store.apply] at hnd' ⊢
    by_cases hl : lookup st k < st.length
    · obtain ⟨v₀, hv, hg⟩ := h.found hl
      simp only [hl, ite_true, hg, Option.isSome_some] at hnd' ⊢
      refine ⟨⟨by simp [hlen, capacity], hnd', ?_⟩, rfl⟩
      obtain ⟨a, b, hst, hst'⟩ := toStore_set hv none
      obtain ⟨ma, mb, hm, -, -, her⟩ := Store.split hg
      rw [hst', her]
      have hp := h.2.2
      rw [hst, hm] at hp
      simpa using perm_remove (by simpa using hp)
    · simp only [hl, ite_false, h.missing hl, Option.isSome_none] at hnd' ⊢
      exact ⟨h, rfl⟩

/-- The order of the slots is not visible: two abstract maps that the same slots hold answer
every request alike. -/
theorem Store.apply_resp_of_refines {st : List Slot} {m m' : Store} (h : Refines st m)
    (h' : Refines st m') (q : Req) : (m.apply q).2 = (m'.apply q).2 := by
  have e := (kvServe_refines h 0 q).2.symm.trans (kvServe_refines h' 0 q).2
  cases hq : (m.apply q).2 <;> cases hq' : (m'.apply q).2 <;> simp_all [Resp.toVal]

/-- The empty slots hold the empty map. -/
theorem Refines.empty : Refines [none, none, none, none] [] := ⟨rfl, by simp, by simp [toStore]⟩

/-! ## The trace -/

/-- The rest of the trace while the server serves the bytes `bs` from the map `m`, after the
history `h`. -/
def fullS (ω : Oracle) (h : List Event) (f : Nat) (m : Store) (bs : List UInt8) : List Event :=
  h ++ writes ω h (answersN f m bs).1 ++ [Examples.exitEvent (answersN f m bs).2]

/-- The rest of the trace while the server reads, after the history `h`. -/
def fullR (ω : Oracle) (f : Nat) (h : List Event) (buf : List UInt8) (len : Nat) : List Event :=
  fullS ω (readsN ω f h buf len).1 (readsN ω f h buf len).2.length [] (readsN ω f h buf len).2

theorem kvTrace_eq (ω : Oracle) : kvTrace ω = fullR ω 257 [] (List.replicate 256 0) 0 := rfl

/-- One read of `fullR`. -/
theorem fullR_succ (ω : Oracle) (f : Nat) (h : List Event) (buf : List UInt8) (len : Nat) :
    let a := ω.answer h (readCall len)
    let h' := h ++ [(readCall len).event a]
    let buf' := Flat.splice buf len ((fitOut [256 - len] a.bytesOut).headD [])
    fullR ω (f + 1) h buf len =
      if a.result.toNat = 0 ∨ 256 - len < a.result.toNat then
        fullS ω h' (buf.take len).length [] (buf.take len)
      else if len + a.result.toNat = 256 then fullS ω h' (buf'.take 256).length [] (buf'.take 256)
      else fullR ω f h' buf' (len + a.result.toNat) := by
  simp only [fullR, readsN]; split <;> (try split) <;> rfl

/-- The root `s` after the history `h`: reading, with the rest of the trace `fullR`, or serving,
with the rest of the trace `fullS`; in both the slots hold the abstract map. -/
def Cfg (ω : Oracle) (h : List Event) (s : Srv) : Prop :=
  SrvInv s ∧
  ((∃ f, s.eof = 0 ∧ s.pos = 0 ∧ Refines (absTab s.tab) [] ∧ s.inLen.toNat < 256 ∧
      256 - s.inLen.toNat < f ∧ fullR ω f h s.inb.toList s.inLen.toNat = kvTrace ω) ∨
    (∃ f m, s.eof ≠ 0 ∧ Refines (absTab s.tab) m ∧ (inp s).length ≤ f ∧
      fullS ω h f m (inp s) = kvTrace ω))

theorem readsN_prefix (ω : Oracle) (f : Nat) (h : List Event) (buf : List UInt8) (len : Nat) :
    ∃ t, (readsN ω f h buf len).1 = h ++ t := by
  induction f generalizing h buf len with
  | zero => exact ⟨[], by simp [readsN]⟩
  | succ f ih =>
    simp only [readsN]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · obtain ⟨t, ht⟩ := ih (h ++ _) _ _
        exact ⟨_, by rw [ht, List.append_assoc]⟩

/-- The history of a configuration is a prefix of the trace. -/
theorem Cfg.prefix {ω : Oracle} {h : List Event} {s : Srv} (hc : Cfg ω h s) :
    ∃ t, h ++ t = kvTrace ω := by
  rcases hc.2 with ⟨f, -, -, -, -, -, hL⟩ | ⟨f, m, -, -, -, hL⟩
  · obtain ⟨t, ht⟩ := readsN_prefix ω f h s.inb.toList s.inLen.toNat
    exact ⟨_, by rw [← hL, fullR, fullS, ht, List.append_assoc, List.append_assoc]⟩
  · exact ⟨_, by rw [← hL, fullS, List.append_assoc]⟩

/-- A step from a reading root, by the contract of `srvStep`: one read, and the root after it
reads on or serves the input. -/
theorem cfg_read {ω : Oracle} {h evs : List Event} {e : Bool} {s s' : Srv} (hinv' : SrvInv s')
    (f : Nat) (heof : s.eof = 0) (hpos : s.pos = 0) (htab : Refines (absTab s.tab) [])
    (hlen : s.inLen.toNat < 256) (hf : 256 - s.inLen.toNat < f)
    (hL : fullR ω f h s.inb.toList s.inLen.toNat = kvTrace ω) (hS : StepSpec ω h s evs e s') :
    evs.length = 1 ∧ e = false ∧ Cfg ω (h ++ evs) s' := by
  simp only [StepSpec, heof, ite_true] at hS
  obtain ⟨rfl, rfl, hpos', htab', hbuf, hstop, hgo⟩ := hS
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  rw [fullR_succ, List.headD_eq_head?_getD] at hL
  generalize ω.answer h (KV.readCall s.inLen.toNat) = a at hbuf hstop hgo hL
  refine ⟨rfl, rfl, hinv', ?_⟩
  have hpre : ∀ k, k ≤ s.inLen.toNat → s'.inb.toList.take k = s.inb.toList.take k := by
    intro k hk
    simp [hbuf, Flat.splice, List.take_append, List.take_take, Nat.min_eq_left hk,
      show k - min s.inLen.toNat 256 = 0 by omega]
  by_cases hs : a.result.toNat = 0 ∨ 256 - s.inLen.toNat < a.result.toNat
  · obtain ⟨hl', he'⟩ := hstop hs
    simp only [hs, ↓reduceIte] at hL
    have hi : inp s' = s.inb.toList.take s.inLen.toNat := by
      simp [inp, hpos', hpos, hl', hpre _ (Nat.le_refl _)]
    refine Or.inr ⟨_, [], by simp [he'], htab' ▸ htab, Nat.le_refl _, ?_⟩
    rw [hi]; exact hL
  · obtain ⟨hl', he'⟩ := hgo hs
    simp only [hs, ↓reduceIte] at hL
    by_cases hfull : s.inLen.toNat + a.result.toNat = 256
    · simp only [hfull, ↓reduceIte] at hL
      have hi : inp s' = (Flat.splice s.inb.toList s.inLen.toNat
          ((fitOut [256 - s.inLen.toNat] a.bytesOut).head?.getD [])).take 256 := by
        simp [inp, hpos', hpos, hl', hfull, hbuf]
      refine Or.inr ⟨_, [], by simp [he', hfull], htab' ▸ htab, Nat.le_refl _, ?_⟩
      rw [hi]; exact hL
    · simp only [hfull, ↓reduceIte] at hL
      refine Or.inl ⟨f, by simp [he', hfull], hpos' ▸ hpos, htab' ▸ htab, by omega,
        by omega, ?_⟩
      rw [hbuf, hl']; exact hL

/-- A step from a serving root, by the contract of `srvStep`: the exit at the end of the input or
at a malformed request, or the write of the response, after which the root serves the rest. -/
theorem cfg_serve {ω : Oracle} {h evs : List Event} {e : Bool} {s s' : Srv} (hinv : SrvInv s)
    (hinv' : SrvInv s') (f : Nat) (m : Store) (heof : s.eof ≠ 0) (htab : Refines (absTab s.tab) m)
    (hf : (inp s).length ≤ f) (hL : fullS ω h f m (inp s) = kvTrace ω)
    (hS : StepSpec ω h s evs e s') :
    evs.length = 1 ∧ (e = false → Cfg ω (h ++ evs) s') ∧ (e = true → h ++ evs = kvTrace ω) := by
  simp only [StepSpec, heof, ite_false] at hS
  by_cases hpos : s.pos = s.inLen
  · -- the end of the input
    simp only [hpos, ↓reduceIte] at hS
    obtain ⟨rfl, rfl⟩ := hS
    have hi : inp s = [] := List.drop_eq_nil_of_le (by simp [hpos]; have := hinv.1; omega)
    rw [hi] at hL
    refine ⟨rfl, (fun h => nomatch h), fun _ => ?_⟩
    rw [← hL]; cases f <;> simp [fullS, answersN, writes]
  simp only [hpos, ↓reduceIte] at hS
  obtain ⟨b, bs, hbs⟩ : ∃ b bs, inp s = b :: bs := by
    cases e : inp s with
    | nil =>
      have := congrArg List.length e
      have : s.pos.toNat ≠ s.inLen.toNat := fun e => hpos (UInt64.toNat_inj.mp e)
      simp [inp] at *; have := hinv.2.1; have := hinv.1; omega
    | cons b bs => exact ⟨b, bs, rfl⟩
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by rw [hbs] at hf; simp at hf; omega⟩
  simp only [kvStep] at hS
  cases hparse : reqFmt.parse (inp s) with
  | none =>
    rw [hparse] at hS
    obtain ⟨rfl, rfl⟩ := hS
    rw [hbs] at hL hparse
    refine ⟨rfl, (fun h => nomatch h), fun _ => ?_⟩
    rw [← hL]; simp [fullS, answersN, hparse, writes]
  | some vr =>
    obtain ⟨v, rest⟩ := vr
    rw [hparse] at hS
    obtain ⟨rfl, rfl, heof', hst, hrest⟩ := hS
    obtain ⟨id, q, hq, rfl⟩ := Req.ofVal_of_ok (Fmt.parse_sound hparse).1
    obtain ⟨hst', hresp⟩ := kvServe_refines htab id q
    refine ⟨rfl, fun _ => ⟨hinv', Or.inr ⟨f, (m.apply q).1, heof' ▸ heof, hst ▸ hst', ?_, ?_⟩⟩,
      fun h => nomatch h⟩
    · rw [hrest]
      have := Fmt.parse_consumed hparse
      have := List.length_pos_iff.mpr (Req.bytes_ne_nil id q)
      simp only [Req.bytes] at this
      omega
    · have hparse' := hparse
      rw [hbs] at hL hparse'
      rw [hrest, ← hL, hresp]
      simp [fullS, answersN, hparse', Req.ofVal_toVal, writes, writeCall, Resp.bytes]

/-- What the contracts of `srvInit` and `srvStep` say of a state after `n` steps: before `exit`
its history has `n` events and is a configuration of `Cfg`; after `exit` it is the whole trace. -/
theorem kvsrv_reach (ω : Oracle) (n : Nat) (s : kvsrv.State.carrier × World)
    (h : kvsrv.Reach (kvsrv.initRel ω) (kvsrv.stepRel ω) n s) :
    (s.2.halted = false → s.2.events.length = n ∧ Cfg ω s.2.events s.1) ∧
      (s.2.halted = true → s.2.events = kvTrace ω ∧ (kvTrace ω).length ≤ n) := by
  induction h with
  | init r evs e hi =>
    obtain ⟨rfl, rfl, rfl⟩ := hi
    refine ⟨fun _ => ⟨rfl, srvInit.post, Or.inl ⟨257, rfl, rfl, ?_, by decide, by decide, ?_⟩⟩,
      fun h => nomatch h⟩
    · simpa [srvInit, absTab, Entry.slot] using Refines.empty
    · rw [kvTrace_eq]; congr 2 <;> simp [srvInit]
  | step n r r' h evs e _ hE ih =>
    change Srv at r r'
    obtain ⟨hl, hc⟩ := ih.1 rfl
    obtain ⟨hinv', hS⟩ := hE hc.1
    have hnext : evs.length = 1 ∧ (e = false → Cfg ω (h ++ evs) r') ∧
        (e = true → h ++ evs = kvTrace ω) := by
      rcases hc.2 with ⟨f, heof, hpos, htab, hlen, hf, hL⟩ | ⟨f, m, heof, htab, hf, hL⟩
      · obtain ⟨h1, rfl, h3⟩ := cfg_read hinv' f heof hpos htab hlen hf hL hS
        exact ⟨h1, fun _ => h3, fun h => nomatch h⟩
      · exact cfg_serve hc.1 hinv' f m heof htab hf hL hS
    obtain ⟨h1, h2, h3⟩ := hnext
    refine ⟨fun he => ⟨by simp [hl, h1], h2 he⟩, fun he => ⟨h3 he, ?_⟩⟩
    rw [← h3 he]; simp [hl, h1]
  | halted n r r' w _ hw ih =>
    obtain ⟨h1, h2⟩ := ih.2 hw
    exact ⟨fun h => by simp_all, fun _ => ⟨h1, by omega⟩⟩

/-- For every oracle and every number of steps `n`, the trace of `kvsrv` is the first `n` events
of `kvTrace ω`: each step makes one call, a read, a write of one response or the exit, and the
server exits at the end of `kvTrace ω`. The proof cites `kvsrv.events_reach`, which `mp program`
derived from the contracts of `srvInit` and `srvStep`, and does not unfold `srvStep`. -/
theorem kvsrv_events (ω : Oracle) (n : Nat) : kvsrv.events ω n = (kvTrace ω).take n := by
  obtain ⟨r, hr⟩ := kvsrv.events_reach ω n
  have h := kvsrv_reach ω n _ hr
  simp only at h
  cases hx : kvsrv.halted ω n
  · obtain ⟨hl, hc⟩ := h.1 hx
    obtain ⟨t, ht⟩ := hc.prefix
    rw [← ht, List.take_left' hl]
  · obtain ⟨he, hl⟩ := h.2 hx
    rw [he, List.take_of_length_le hl]

/-! ## The bytes -/

/-- Whatever bytes a sound compiler produced for `kvsrv`, they load, and for every oracle the
machine never gets stuck, every trace it shows is a prefix of `kvTrace ω`, and it shows the whole
of it: the reads, a write of each response of the abstract store, and the exit. -/
theorem kvsrv_behaviour {cc : Program → Target → Except String ByteArray} {t : Target}
    (hcc : Examples.Sound cc t) (b : ByteArray) (hc : cc kvsrv t = .ok b) :
    ∃ s₀, t.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle, let m := Machine.run t s₀ ω
        m.NeverStuck ∧ (∀ n, m.trace n <+: kvTrace ω) ∧ ∃ n, m.trace n = kvTrace ω := by
  obtain ⟨s₀, hl, h⟩ := kvsrv.behaviour_of_events hcc kvsrv.safe (fun ω n => (kvTrace ω).take n)
    kvsrv_events hc
  exact ⟨s₀, hl, fun ω => ⟨(h ω).1, TraceEq.const (TraceEq.take (h ω).2)⟩⟩

/-- The trace when the input is the bytes of the well-formed requests `qs`, followed by nothing or
by bytes that do not begin with a request. -/
theorem kvTrace_of_input (ω : Oracle) (qs : List (Nat × Req)) (hok : ∀ x ∈ qs, x.2.Ok x.1)
    (tail : List UInt8) (hin : (reads ω).2 = encode qs ++ tail)
    (htail : tail = [] ∨ (tail ≠ [] ∧ reqFmt.parse tail = none)) :
    kvTrace ω = (reads ω).1 ++ writes ω (reads ω).1 (Store.run [] qs) ++
      [Examples.exitEvent (if tail = [] then 0 else 1)] := by
  rcases htail with rfl | ⟨hne, hp⟩
  · simp only [List.append_nil] at hin
    simp [kvTrace, hin, answers_encode qs hok]
  · simp [kvTrace, hin, answers_encode_bad qs hok tail hne hp, hne]

/-- The compiled server answers every request sequence as the abstract key-value store does, and
exits 1 at the first malformed request. Whatever bytes a sound compiler produced for `kvsrv`, they
load, and for every oracle whose reads deliver the bytes of well-formed requests `qs` followed by
nothing or by bytes that do not begin with a request, the machine never gets stuck, every trace it
shows is a prefix of the reads, then a `write(1, …)` of each of the abstract store's responses to
`qs` from the empty store, then `exit` with 0 or 1, and it shows the whole of it. -/
theorem kvsrv_answers {cc : Program → Target → Except String ByteArray} {t : Target}
    (hcc : Examples.Sound cc t) (b : ByteArray) (hc : cc kvsrv t = .ok b) :
    ∃ s₀, t.fmt.load b.data.toList = some s₀ ∧
      ∀ (ω : Oracle) (qs : List (Nat × Req)) (tail : List UInt8), (∀ x ∈ qs, x.2.Ok x.1) →
        (reads ω).2 = encode qs ++ tail → (tail = [] ∨ (tail ≠ [] ∧ reqFmt.parse tail = none)) →
        let tr := (reads ω).1 ++ writes ω (reads ω).1 (Store.run [] qs) ++
          [Examples.exitEvent (if tail = [] then 0 else 1)]
        let m := Machine.run t s₀ ω
        m.NeverStuck ∧ (∀ n, m.trace n <+: tr) ∧ ∃ n, m.trace n = tr := by
  obtain ⟨s₀, hl, h⟩ := kvsrv_behaviour hcc b hc
  refine ⟨s₀, hl, fun ω qs tail hok hin htail => ?_⟩
  rw [← kvTrace_of_input ω qs hok tail hin htail]
  exact h ω

theorem mem_writes (ω : Oracle) (h : List Event) {rs : List (List UInt8)} {r : List UInt8}
    (hr : r ∈ rs) : ∃ e ∈ writes ω h rs, e.sym = "write" ∧ e.args = [1] ∧ e.bytesIn = [r] := by
  induction rs generalizing h with
  | nil => simp at hr
  | cons r' rs ih =>
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨_, List.mem_cons_self .., rfl, rfl, rfl⟩
    · obtain ⟨e, he, hs⟩ := ih _ hr
      exact ⟨e, List.mem_cons_of_mem _ he, hs⟩

/-- A get of `k` after a put of `k` that the store had room for, with no put or delete of `k`
between them, is answered with the value put, by the compiled server: for every oracle whose reads
deliver those requests, the machine writes the response `value v` to the get. -/
theorem kvsrv_put_get {cc : Program → Target → Except String ByteArray} {t : Target}
    (hcc : Examples.Sound cc t) (b : ByteArray) (hc : cc kvsrv t = .ok b) :
    ∃ s₀, t.fmt.load b.data.toList = some s₀ ∧
      ∀ (ω : Oracle) (pre mid post : List (Nat × Req)) (id id' : Nat) (k : Key) (v : Value)
        (tail : List UInt8),
        let qs := pre ++ (id, .put k v) :: mid ++ (id', .get k) :: post
        (∀ x ∈ qs, x.2.Ok x.1) → (reads ω).2 = encode qs ++ tail →
        (tail = [] ∨ (tail ≠ [] ∧ reqFmt.parse tail = none)) →
        ((Store.after [] pre).get k).isSome ∨ (Store.after [] pre).length < capacity →
        (∀ x ∈ mid, ¬ x.2.Touches k) →
        ∃ n, ∃ e ∈ (Machine.run t s₀ ω).trace n,
          e.sym = "write" ∧ e.args = [1] ∧ e.bytesIn = [(Resp.value v).bytes id'] := by
  obtain ⟨s₀, hl, h⟩ := kvsrv_answers hcc b hc
  refine ⟨s₀, hl, fun ω pre mid post id id' k v tail hok hin htail hroom hmid => ?_⟩
  obtain ⟨-, -, n, hn⟩ := h ω _ tail hok hin htail
  refine ⟨n, ?_⟩
  rw [hn]
  have hr : (Resp.value v).bytes id' ∈ Store.run [] (pre ++ (id, .put k v) :: mid ++ (id', .get k) :: post) := by
    rw [List.append_assoc, Store.run_append, Store.run_put_get _ _ _ _ _ _ _ hroom hmid]
    simp
  obtain ⟨e, he, hs⟩ := mem_writes ω (reads ω).1 hr
  exact ⟨e, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr he))), hs⟩

/-- `kvsrv_answers` for the bytes of `compile` on x64 Linux. -/
example (b : ByteArray) (hc : compile kvsrv x64Linux = .ok b) :=
  kvsrv_answers Examples.sound_compile.1 b hc

/-- `kvsrv_answers` for the bytes of `compile` on arm64 Linux. -/
example (b : ByteArray) (hc : compile kvsrv arm64Linux = .ok b) :=
  kvsrv_answers Examples.sound_compile.2 b hc

/-! ## Tests

The oracle `feed data k` delivers the bytes `data` in reads of at most `k` bytes and accepts every
write whole. The checks compare the source trace `kvsrv.events`, computed by running the
program's denotation, with `kvTrace`, and pin the response bytes. Wrong specifications, a delete
that leaves the key and responses with the id in little-endian order, are refuted by the source
trace. -/

/-- The bytes already delivered: the sum of the counts of the reads in `h`. -/
def delivered' (h : List Event) : Nat :=
  (h.filter (·.sym == "read")).foldl (fun a e => a + e.result.toNat) 0

/-- An oracle that delivers `data` in reads of at most `k` bytes, and writes everything. -/
def feed (data : List UInt8) (k : Nat) : Oracle := ⟨fun h c =>
  if c.sym == "read" then
    let d := ((data.drop (delivered' h)).take k).take (c.outCaps.headD 0)
    ⟨UInt64.ofNat d.length, [d]⟩
  else ⟨UInt64.ofNat (c.bytesIn.headD []).length, []⟩⟩

/-- An oracle whose first read claims `claim` bytes and delivers `d`, and whose later reads
deliver nothing. -/
def liar (claim : UInt64) (d : List UInt8) : Oracle := ⟨fun h c =>
  if c.sym == "read" then (if delivered' h = 0 && h.isEmpty then ⟨claim, [d]⟩ else ⟨0, []⟩)
  else ⟨UInt64.ofNat (c.bytesIn.headD []).length, []⟩⟩

/-- The requests: put `ab` → `xy`, get it, delete it, get it, put four more keys of which the
last does not fit. -/
def sample : List (Nat × Req) :=
  [(1, .put [97, 98] [120, 121]), (2, .get [97, 98]), (3, .del [97, 98]), (4, .get [97, 98]),
   (5, .put [1] [1]), (6, .put [2] [2]), (7, .put [3] [3]), (8, .put [4] [4]), (9, .put [5] [5]),
   (10, .get [3])]

/-- The responses of the abstract store to `sample`. -/
def sampleResps : List Resp :=
  [.done, .value [120, 121], .done, .notFound, .done, .done, .done, .done, .full, .value [3]]

#guard Store.run [] sample == (sample.zip sampleResps).map fun (x, r) => r.bytes x.1
-- the response to the get: id 2 big-endian, status 0, length 2 big-endian, the value
#guard (Resp.value [120, 121]).bytes 2 == [0, 2, 0, 0, 2, 120, 121]
#guard (Resp.full).bytes 9 == [0, 9, 2, 1]

/-- The source trace after `n` steps is the specification's first `n` events. -/
def agrees (ω : Oracle) (n : Nat) : Bool := kvsrv.events ω n == (kvTrace ω).take n

-- well-formed requests delivered 7 bytes at a time: reads, ten writes, exit 0
#guard (kvTrace (feed (encode sample) 7)).length == (encode sample).length / 7 + 2 + 10 + 1
#guard agrees (feed (encode sample) 7) 100
#guard (kvTrace (feed (encode sample) 7)).getLast? == some (Examples.exitEvent 0)
-- one request then bytes that do not begin with a request: one write, exit 1
#guard agrees (feed (encode (sample.take 1) ++ [0, 1, 9]) 256) 10
#guard kvTrace (feed (encode (sample.take 1) ++ [0, 1, 9]) 256) ==
  [(readCall 0).event ⟨13, [encode (sample.take 1) ++ [0, 1, 9]]⟩,
   (readCall 13).event ⟨0, [[]]⟩,
   (writeCall [0, 1, 1]).event ⟨3, []⟩, Examples.exitEvent 1]
-- a read that claims 9 bytes and delivers 4: the input's last 5 bytes are the buffer's zeros, so
-- the input is a get of the empty key, answered "not found", then operation 0, malformed
#guard agrees (liar 9 [0, 1, 1, 0]) 10
#guard (reads (liar 9 [0, 1, 1, 0])).2 == [0, 1, 1, 0, 0, 0, 0, 0, 0]
#guard (answers (reads (liar 9 [0, 1, 1, 0])).2) == ([Resp.notFound.bytes 1], 1)
-- a read whose count is above the buffer ends the input with nothing read
#guard agrees (liar (UInt64.ofNat (2 ^ 64 - 1)) [1, 2, 3]) 10
#guard (reads (liar (UInt64.ofNat (2 ^ 64 - 1)) [1, 2, 3])).2 == []
-- more than 256 bytes: the server reads 256 and answers the requests in them
#guard agrees (feed (encode (sample ++ sample ++ sample ++ sample)) 64) 200

/-- A wrong store whose delete leaves the key in place. -/
def badRun : Store → List (Nat × Req) → List (List UInt8)
  | _, [] => []
  | m, (id, .del k) :: qs => (if (m.get k).isSome then Resp.done else Resp.notFound).bytes id :: badRun m qs
  | m, (id, q) :: qs => (m.apply q).2.bytes id :: badRun (m.apply q).1 qs

/-- Responses with the id in little-endian order. -/
def leId : List UInt8 → List UInt8
  | a :: b :: r => b :: a :: r
  | r => r

/-- The trace that a specification built from responses `rs` would give. -/
def traceWith (ω : Oracle) (rs : List (List UInt8)) (code : UInt64) : List Event :=
  (reads ω).1 ++ writes ω (reads ω).1 rs ++ [Examples.exitEvent code]

#guard kvsrv.events (feed (encode sample) 7) 100 ==
  traceWith (feed (encode sample) 7) (Store.run [] sample) 0
#guard kvsrv.events (feed (encode sample) 7) 100 !=
  traceWith (feed (encode sample) 7) (badRun [] sample) 0
#guard kvsrv.events (feed (encode sample) 7) 100 !=
  traceWith (feed (encode sample) 7) ((Store.run [] sample).map leId) 0

end Millipede.Tests.KV
