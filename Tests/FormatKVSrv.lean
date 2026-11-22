import Tests.FormatKV
import Tests.KVSpec
import Millipede.Meta.Emit
import Millipede.Meta.Report

/-!
# A key-value server over the formats of Tests/FormatKV.lean

The program `kvsrv` reads its whole input (at most 256 bytes) into a buffer, then answers one
request per step and writes the response, and it exits with 0 at the end of the input and with 1
at the first malformed request. Building this file writes the images `.lake/kvsrv-x64` and
`.lake/kvsrv-a64`, which `scripts/format-check.sh` runs on sample and generated inputs.

The answer to one request is `kvStep`, a function of the store's slots and the input bytes
defined with the model: the request is `Fmt.parse reqFmt` of the bytes, `kvServe` answers it, and
the response is `Fmt.write respFmt` of the answer. The contract of `handle` says that it answers
the request at the position as `kvStep` does. The contract of `fill` is about events: one read
`KV.readCall` of the specification (Tests/KVSpec.lean) and what its reply does to the buffer
(`ReadStep`). The contract of `srvStep` is about events too: it keeps the bounds `SrvInv`, which
are also the program's root invariant, and makes one step of the protocol (`StepSpec`), a read,
the write of the response `kvStep` gives, or an exit. It is proved from the contracts of `fill`
and `handle`. From it `mp program` derives `kvsrv.reach`, and Tests/KVRefine.lean proves from that
alone that the server's trace is the one of an abstract key-value store, for every oracle.
-/

namespace Millipede.Tests.FormatKV

open Millipede Millipede.Format Std.WP

set_option experimental.vcgen true

mp extern "read" kvRead (fd : UInt64) (buf : &mut [U8]) : UInt64
mp extern "write" kvWrite (fd : UInt64) (buf : &[U8]) : UInt64
mp extern noreturn "exit" kvExit (code : UInt64) : UInt64

/-- An entry of the store. -/
structure Entry where
  used : UInt64
  key : LBytes 16
  val : LBytes 32
deriving Data

instance : Inhabited Entry := ⟨⟨0, ⟨0, Vector.replicate 16 0⟩, ⟨0, Vector.replicate 32 0⟩⟩⟩

set_option mp.autoSpec false in
/-- Whether two keys are equal. -/
mp def keyEq (a : &LBytes 16) (b : &LBytes 16)
    requires a.len.toNat ≤ 16 ∧ b.len.toNat ≤ 16
    ensures result = decide (a.bytes = b.bytes) : Bool := do
  if a.len != b.len then return false
  let mut eq := true
  for i in 0...16 do
    if i < a.len && a.data[i] != b.data[i] then eq := false
  eq

mp prove keyEq.spec := by
  intro a b
  vcgen [keyEq] invariants
  · fun done _ eq => eq = decide (∀ j < done.length, j < a.len.toNat → vget a.data j 0 = vget b.data j 0)
  case vc1 => simp
  case vc2 hpre heq ih =>
    subst ih
    simp only [decide_eq_decide, LBytes.bytes_eq_iff hpre.1 hpre.2, List.length_range, heq, true_and]
    exact ⟨fun h j hj => h j (by omega) hj, fun h j _ hj => h j hj⟩
  case vc7 hpre hne => simp [LBytes.bytes_eq_iff hpre.1 hpre.2, hne]
  all_goals
    rename_i hpre heq pref cur suff hr e ih hc hne
    obtain ⟨rfl, _⟩ := range_split hr
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc
    subst ih
    simp only [List.length_append, List.length_singleton, decide_eq_decide,
      UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega)] at hne ⊢
  case vc3 =>
    have : vget a.data pref.length default ≠ vget b.data pref.length default := by simpa using hne
    simp only [Bool.false_eq, decide_eq_false_iff_not]
    exact fun h => this (h _ (by omega) hc)
  case vc4 =>
    have : vget a.data pref.length default = vget b.data pref.length default := by simpa using hne
    exact ⟨fun h j hj hja => if e : j = pref.length then e ▸ this else h j (by omega) hja,
      fun h j hj hja => h j (by omega) hja⟩
  case vc5 => simp at hne
  case vc6 => exact ⟨fun h j hj hja => h j (by omega) hja, fun h j hj hja => h j (by omega) hja⟩

/-! ## The store as the specification sees it -/

/-- A slot of the store: the key and the value of a used entry, or nothing. -/
abbrev Slot := Option (List UInt8 × List UInt8)

/-- The slot an entry stands for. -/
def Entry.slot (e : Entry) : Slot := if e.used = 1 then some (e.key.bytes, e.val.bytes) else none

/-- The slots of the store. -/
def absTab (t : Arr Entry 4) : List Slot := t.toList.map Entry.slot

/-- Every entry's key and value are within their bounds. -/
def TabOk (t : Arr Entry 4) : Prop :=
  ∀ j < 4, (vget t j default).key.len.toNat ≤ 16 ∧ (vget t j default).val.len.toNat ≤ 32

/-- The index of the first slot that holds the key `k`, or the number of slots. -/
def lookup (st : List Slot) (k : List UInt8) : Nat := st.findIdx fun s => s.any (·.1 == k)

/-- The index of the first free slot, or the number of slots. -/
def freeAt (st : List Slot) : Nat := st.findIdx Option.isNone

/-- The first index of a vector's elements that satisfies `p`, from where the search stopped. -/
theorem findIdx_toList {α β : Type} [Inhabited α] {n : Nat} (t : Vector α n) (f : α → β) (p : β → Bool)
    {i : Nat} (hi : i ≤ n) (hfound : i < n → p (f (vget t i default)) = true)
    (hbefore : ∀ j < i, p (f (vget t j default)) = false) : (t.toList.map f).findIdx p = i := by
  by_cases h : i < n
  · rw [List.findIdx_eq (by simpa using h)]
    refine ⟨by simpa [vget, h] using hfound h, fun j hj => ?_⟩
    simpa [vget, show j < n by omega] using hbefore j hj
  · refine (List.findIdx_eq_length.mpr fun x hx => ?_).trans (by simp; omega)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_map, Vector.length_toList] at hj
    simpa [vget, hj] using hbefore j (by omega)

/-- Entry `j` is used and holds the key `k`. -/
def Hit (t : Arr Entry 4) (k : List UInt8) (j : Nat) : Prop :=
  (vget t j default).used = 1 ∧ (vget t j default).key.bytes = k

theorem Entry.slot_any (e : Entry) (k : List UInt8) :
    (e.slot.any fun s => s.1 == k) = decide (e.used = 1 ∧ e.key.bytes = k) := by
  unfold Entry.slot; split <;> simp_all [Bool.beq_eq_decide_eq]

theorem lookup_eq {t : Arr Entry 4} {k : List UInt8} {i : Nat} (hi : i ≤ 4)
    (hf : i < 4 → Hit t k i) (hb : ∀ j < i, ¬ Hit t k j) : lookup (absTab t) k = i :=
  findIdx_toList t Entry.slot _ hi (fun h => by simpa [Entry.slot_any, Hit] using hf h)
    (fun j hj => by simpa [Entry.slot_any, Hit] using hb j hj)

set_option mp.autoSpec false in
/-- The index of the used entry with key `k`, or 4. -/
mp def find (t : &Arr Entry 4) (k : &LBytes 16) requires TabOk t ∧ k.len.toNat ≤ 16
    ensures result.toNat = lookup (absTab t) k.bytes : UInt64 := do
  for i in 0...4 do
    if t[i].used == 1 && keyEq (&t[i].key) (&k) then return i
  return 4

mp prove find.spec := by
  intro t k
  vcgen [find] invariants
  · fun done _ st => (st.2.1 = false → ∀ j < done.length, ¬ Hit t k.bytes j) ∧
      (st.2.1 = true → st.2.2.1.toNat < 4 ∧ Hit t k.bytes st.2.2.1.toNat ∧
        ∀ j < st.2.2.1.toNat, ¬ Hit t k.bytes j)
  all_goals dsimp only at *
  case vc1 => simp
  case vc2 hpre fl v ih hfl =>
    obtain ⟨hlt, hhit, hb⟩ := ih.2 hfl
    exact (lookup_eq (by omega) (fun _ => hhit) hb).symm
  case vc3 hpre fl v ih hfl =>
    have := ih.1 (by simpa using hfl)
    exact (lookup_eq (i := 4) (by omega) (by omega) (by simpa using this)).symm
  case vc9 hpre pref cur suff hr fl v ih hfl =>
    exact ⟨fun h => absurd h hfl, ih.2⟩
  case vc4 hpre pref cur suff hr _ fl v _ ih hfl hu =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    simp only [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega)] at *
    exact ⟨(hpre.1 _ hlt).1, hpre.2⟩
  case vc5 hpre pref cur suff hr _ fl v _ ih hfl hu e _ he hit =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    simp only [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega), List.length_append,
      List.length_singleton] at *
    subst he
    exact ⟨by simp, fun _ => ⟨hlt, ⟨hu, by simpa using hit⟩, ih.1 hfl⟩⟩
  case vc6 hpre pref cur suff hr _ fl v _ ih hfl hu e _ he hit =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    simp only [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega), List.length_append,
      List.length_singleton] at *
    subst he
    refine ⟨fun _ j hj => ?_, fun h => absurd h (by simp [hfl])⟩
    by_cases e : j = pref.length
    · subst e; exact fun h => hit (by simpa using h.2)
    · exact ih.1 hfl j (by omega)
  case vc7 hpre pref cur suff hr _ fl v _ ih hfl hu h => simp at h
  case vc8 hpre pref cur suff hr _ fl v _ ih hfl hu _ =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    simp only [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega), List.length_append,
      List.length_singleton] at *
    refine ⟨fun _ j hj => ?_, fun h => absurd h (by simp [hfl])⟩
    by_cases e : j = pref.length
    · subst e; exact fun h => hu h.1
    · exact ih.1 hfl j (by omega)

/-- Entry `j` is free. -/
def Free (t : Arr Entry 4) (j : Nat) : Prop := (vget t j default).used ≠ 1

theorem freeAt_eq {t : Arr Entry 4} {i : Nat} (hi : i ≤ 4) (hf : i < 4 → Free t i)
    (hb : ∀ j < i, ¬ Free t j) : freeAt (absTab t) = i :=
  findIdx_toList t Entry.slot _ hi (fun h => by simpa [Entry.slot, Free] using hf h)
    (fun j hj => by simpa [Entry.slot, Free] using hb j hj)

set_option mp.autoSpec false in
/-- The index of an unused entry, or 4. -/
mp def freeSlot (t : &Arr Entry 4) ensures result.toNat = freeAt (absTab t) : UInt64 := do
  for i in 0...4 do
    if t[i].used != 1 then return i
  return 4

mp prove freeSlot.spec := by
  intro t
  vcgen [freeSlot] invariants
  · fun done _ st => (st.2.1 = false → ∀ j < done.length, ¬ Free t j) ∧
      (st.2.1 = true → st.2.2.1.toNat < 4 ∧ Free t st.2.2.1.toNat ∧ ∀ j < st.2.2.1.toNat, ¬ Free t j)
  all_goals dsimp only at *
  case vc1 => simp
  case vc2 _ fl v _ ih hfl =>
    obtain ⟨hlt, hfree, hb⟩ := ih.2 hfl
    exact (freeAt_eq (by omega) (fun _ => hfree) hb).symm
  case vc3 _ fl v _ ih hfl =>
    exact (freeAt_eq (i := 4) (by omega) (by omega) (by simpa using ih.1 (by simpa using hfl))).symm
  case vc6 _ fl v _ ih hfl => exact ⟨fun h => absurd h hfl, ih.2⟩
  case vc4 pref cur suff hr _ fl v _ ih hfl hu =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    simp only [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega), List.length_append,
      List.length_singleton] at *
    refine ⟨fun _ j hj => ?_, fun h => absurd h (by simp [hfl])⟩
    by_cases e : j = pref.length
    · subst e; exact fun h => h hu
    · exact ih.1 hfl j (by omega)
  case vc5 pref cur suff hr _ fl v _ ih hfl hu =>
    obtain ⟨rfl, hlt⟩ := range_split hr
    simp only [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega), List.length_append,
      List.length_singleton] at *
    exact ⟨by simp, fun _ => ⟨hlt, hu, ih.1 hfl⟩⟩

/-! ## One request -/

/-- A response value: the request's id, then the status and its arm. -/
def respVal (id status : Nat) (v : Val) : Val := .pair (.num id) (.tag status v)

/-- The answer to a request value from the slots `st`, with the slots after it. A get (1) answers
the value of the key or the error code 2, a put (2) stores the value in the key's slot or else in
the first free slot and answers nothing, or the error code 1 when the store is full, and a delete
(3) frees the key's slot and answers nothing, or the error code 2. -/
def kvServe (st : List Slot) : Val → List Slot × Val
  | .pair (.num id) (.tag 1 (.bytes k)) =>
    match st[lookup st k]? with
    | some (some (_, v)) => (st, respVal id 0 (.bytes v))
    | _ => (st, respVal id 2 (.num 2))
  | .pair (.num id) (.tag 2 (.pair (.bytes k) (.bytes v))) =>
    let i := lookup st k
    let j := if i < st.length then i else freeAt st
    if j < st.length then (st.set j (some (k, v)), respVal id 1 .unit)
    else (st, respVal id 2 (.num 1))
  | .pair (.num id) (.tag 3 (.bytes k)) =>
    let i := lookup st k
    if i < st.length then (st.set i none, respVal id 1 .unit) else (st, respVal id 2 (.num 2))
  | _ => (st, .unit)

/-- One step of the protocol: the request at the front of `bs` is parsed by `reqFmt` and answered
from the slots `st`; the result is the slots after it, the bytes of the response by `respFmt` and
the bytes after the request, or `none` when no request parses. -/
def kvStep (st : List Slot) (bs : List UInt8) : Option (List Slot × List UInt8 × List UInt8) :=
  match reqFmt.parse bs with
  | none => none
  | some (q, rest) => some ((kvServe st q).1, respFmt.write (kvServe st q).2, rest)

/-- A request the server answers: a value of `reqFmt` whose byte strings are within their
bounds. -/
def ReqOk (q : KReq) : Prop :=
  reqFmt.ok q.toVal = true ∧ q.key.len.toNat ≤ 16 ∧ (q.op.toNat = 2 → q.val.len.toNat ≤ 32)

/-- A request of `reqFmt` has an id of two bytes and the operation 1, 2 or 3. -/
theorem ReqOk.cases {q : KReq} (h : reqFmt.ok q.toVal = true) :
    q.id.toNat < 65536 ∧ (q.op.toNat = 1 ∨ q.op.toNat = 2 ∨ q.op.toNat = 3) := by
  simp only [reqFmt, Fmt.ok, Fmt.okT, KReq.toVal, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨by simpa using h.1, ?_⟩
  by_cases h1 : q.op.toNat = 1; · exact Or.inl h1
  by_cases h2 : q.op.toNat = 2; · exact Or.inr (Or.inl h2)
  by_cases h3 : q.op.toNat = 3; · exact Or.inr (Or.inr h3)
  simp [h1, h2, h3] at h

/-- A response whose fields are in range is a value of `respFmt`. -/
theorem KResp.ok_of {r : KResp} (hi : r.id.toNat < 65536) (hs : r.status.toNat ≤ 2)
    (hc : r.code.toNat < 256) (hv : r.val.len.toNat ≤ 32) : respFmt.ok r.toVal = true := by
  have : r.status.toNat = 0 ∨ r.status.toNat = 1 ∨ r.status.toNat = 2 := by omega
  rcases this with h | h | h <;>
    simp [respFmt, valFmt, Fmt.ok, Fmt.okT, KResp.toVal, LBytes.toVal, h, hi, hc] <;> omega

@[simp] theorem absTab_length (t : Arr Entry 4) : (absTab t).length = 4 := by simp [absTab]

theorem absTab_getElem? {t : Arr Entry 4} {j : Nat} (h : j < 4) :
    (absTab t)[j]? = some (vget t j default).slot := by
  simp [absTab, vget, h]

theorem absTab_vset {t : Arr Entry 4} {j : Nat} {e : Entry} (h : j < 4) :
    absTab (vset t j e) = (absTab t).set j e.slot := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [absTab_length] at h1
  simp only [absTab, vset, h, ↓reduceDIte, List.getElem_map, Vector.getElem_toList, List.getElem_set,
    Vector.getElem_set]
  split <;> rfl

theorem TabOk.vset {t : Arr Entry 4} {j : Nat} {e : Entry} (ht : TabOk t) (hk : e.key.len.toNat ≤ 16)
    (hv : e.val.len.toNat ≤ 32) : TabOk (vset t j e) := by
  intro i hi
  by_cases e' : j = i
  · subst e'; simp [vget_vset_same _ _ _ _ hi, hk, hv]
  · rw [vget_vset_ne _ _ _ _ _ e']; exact ht i hi

/-- The slot `lookup` finds holds the key. -/
theorem lookup_hit {t : Arr Entry 4} {k : List UInt8} (h : lookup (absTab t) k < 4) :
    Hit t k (lookup (absTab t) k) := by
  have hw : (absTab t).findIdx (fun s => s.any (·.1 == k)) < (absTab t).length := by
    simpa [lookup] using h
  have := List.findIdx_getElem (w := hw)
  simp only [absTab, List.getElem_map, Vector.getElem_toList, Entry.slot_any, decide_eq_true_eq] at this
  simp only [Hit, vget, dite_eq_left h]
  simpa [lookup, absTab] using this

theorem KReq.toVal_eq (q : KReq) : q.toVal = .pair (.num q.id.toNat) (.tag q.op.toNat
    (if q.op.toNat = 1 then .bytes q.key.bytes
      else if q.op.toNat = 2 then .pair (.bytes q.key.bytes) (.bytes q.val.bytes)
      else if q.op.toNat = 3 then .bytes q.key.bytes else .unit)) :=
  rfl

theorem KResp.toVal_eq (r : KResp) : r.toVal = respVal r.id.toNat r.status.toNat
    (if r.status.toNat = 0 then .bytes r.val.bytes else if r.status.toNat = 1 then .unit
      else if r.status.toNat = 2 then .num r.code.toNat else .unit) := rfl

set_option mp.autoSpec false in
/-- Answer the request `q` from the store `tab` into `resp`. -/
mp def serve (tab : &mut Arr Entry 4) (q : &KReq) (resp : &mut KResp)
    requires TabOk tab ∧ ReqOk q ∧ resp.val.len.toNat ≤ 32
    ensures TabOk tab' ∧ resp'.val.len.toNat ≤ 32 ∧ respFmt.ok resp'.toVal ∧
      (absTab tab', resp'.toVal) = kvServe (absTab tab) q.toVal : Unit := do
  let op := q.op
  let i := find (&tab) (&q.key)
  resp.id := q.id
  resp.code := 0
  if op == 1 then
    if i < 4 then
      resp.status := 0
      resp.val := tab[i]!.val
    else
      resp.status := 2
      resp.code := 2
  else if op == 2 then
    let j := if i < 4 then i else freeSlot (&tab)
    if j < 4 then
      tab[j]! := { used := 1, key := q.key, val := q.val }
      resp.status := 1
    else
      resp.status := 2
      resp.code := 1
  else if i < 4 then
    let mut e := tab[i]!
    e.used := 0
    tab[i]! := e
    resp.status := 1
  else
    resp.status := 2
    resp.code := 2

mp prove serve.spec := by
  intro tab q resp
  vcgen [serve]
  case vc1 hpre => exact ⟨hpre.1, hpre.2.1.2.1⟩
  all_goals dsimp only at *
  all_goals simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at *
  case vc2 hpre i _ hi hop hlt =>
    obtain ⟨htab, hq, hrv⟩ := hpre
    obtain ⟨hid, -⟩ := ReqOk.cases hq.1
    have hq1 : q.op.toNat = 1 := by simp [hop]
    rw [hi] at hlt
    obtain ⟨hu, hk⟩ := lookup_hit hlt
    rw [← hi] at hu hk hlt
    refine ⟨htab, (htab _ hlt).2, KResp.ok_of hid (by simp) (by simp) (htab _ hlt).2, ?_⟩
    simp only [KReq.toVal_eq, hq1, ↓reduceIte, kvServe]
    rw [← hi, absTab_getElem? hlt]
    simp [Entry.slot, hu, KResp.toVal_eq, LBytes.bytes]
  case vc3 hpre i _ hi hop hlt =>
    obtain ⟨htab, hq, hrv⟩ := hpre
    obtain ⟨hid, -⟩ := ReqOk.cases hq.1
    have hq1 : q.op.toNat = 1 := by simp [hop]
    refine ⟨htab, hrv, KResp.ok_of hid (by simp) (by simp) hrv, ?_⟩
    simp only [KReq.toVal_eq, hq1, ↓reduceIte, kvServe]
    rw [← hi, List.getElem?_eq_none (by simp; omega)]
    simp [KResp.toVal_eq]
  case vc4 hpre i _ hi hop1 hop2 hlt _ =>
    obtain ⟨htab, hq, hrv⟩ := hpre
    obtain ⟨hid, -⟩ := ReqOk.cases hq.1
    have hq2 : q.op.toNat = 2 := by simp [hop2]
    refine ⟨htab.vset hq.2.1 (hq.2.2 hq2), hrv, KResp.ok_of hid (by simp) (by simp) hrv, ?_⟩
    simp only [KReq.toVal_eq, hq2, Nat.reduceEqDiff, ↓reduceIte, kvServe, absTab_length]
    rw [← hi, ite_eq_left hlt, ite_eq_left hlt, absTab_vset hlt]
    simp [Entry.slot, KResp.toVal_eq, LBytes.bytes]
  case vc5 hlt hlt' => exact absurd hlt hlt'
  case vc6 hpre i _ hi hop1 hop2 j _ hj hlt hlt' =>
    obtain ⟨htab, hq, hrv⟩ := hpre
    obtain ⟨hid, -⟩ := ReqOk.cases hq.1
    have hq2 : q.op.toNat = 2 := by simp [hop2]
    refine ⟨htab.vset hq.2.1 (hq.2.2 hq2), hrv, KResp.ok_of hid (by simp) (by simp) hrv, ?_⟩
    simp only [KReq.toVal_eq, hq2, Nat.reduceEqDiff, ↓reduceIte, kvServe, absTab_length]
    rw [← hi, ite_eq_right hlt, ← hj, ite_eq_left hlt', absTab_vset hlt']
    simp [Entry.slot, KResp.toVal_eq, LBytes.bytes]
  case vc7 hpre i _ hi hop1 hop2 j _ hj hlt hlt' =>
    obtain ⟨htab, hq, hrv⟩ := hpre
    obtain ⟨hid, -⟩ := ReqOk.cases hq.1
    have hq2 : q.op.toNat = 2 := by simp [hop2]
    refine ⟨htab, hrv, KResp.ok_of hid (by simp) (by simp) hrv, ?_⟩
    simp only [KReq.toVal_eq, hq2, Nat.reduceEqDiff, ↓reduceIte, kvServe, absTab_length]
    rw [← hi, ite_eq_right hlt, ← hj, ite_eq_right hlt']
    simp [KResp.toVal_eq]
  case vc8 hpre i _ hi hop1 hop2 hlt =>
    obtain ⟨htab, hq, hrv⟩ := hpre
    obtain ⟨hid, hops⟩ := ReqOk.cases hq.1
    have hq3 : q.op.toNat = 3 := by
      have : q.op.toNat ≠ 1 := fun h => hop1 (UInt64.toNat_inj.mp h)
      have : q.op.toNat ≠ 2 := fun h => hop2 (UInt64.toNat_inj.mp h)
      omega
    refine ⟨htab.vset (htab _ hlt).1 (htab _ hlt).2, hrv, KResp.ok_of hid (by simp) (by simp) hrv, ?_⟩
    simp only [KReq.toVal_eq, hq3, Nat.reduceEqDiff, ↓reduceIte, kvServe, absTab_length]
    rw [← hi, ite_eq_left hlt, absTab_vset hlt]
    simp [Entry.slot, KResp.toVal_eq]
  case vc9 hpre i _ hi hop1 hop2 hlt =>
    obtain ⟨htab, hq, hrv⟩ := hpre
    obtain ⟨hid, hops⟩ := ReqOk.cases hq.1
    have hq3 : q.op.toNat = 3 := by
      have : q.op.toNat ≠ 1 := fun h => hop1 (UInt64.toNat_inj.mp h)
      have : q.op.toNat ≠ 2 := fun h => hop2 (UInt64.toNat_inj.mp h)
      omega
    refine ⟨htab, hrv, KResp.ok_of hid (by simp) (by simp) hrv, ?_⟩
    simp only [KReq.toVal_eq, hq3, Nat.reduceEqDiff, ↓reduceIte, kvServe, absTab_length]
    rw [← hi, ite_eq_right hlt]
    simp [KResp.toVal_eq]

/-- What answering the request at `pos` in the bytes `B` did, against `kvStep` from the slots
`st`: when no request parses, `n` is 0; otherwise `n` is the length of the response, `st'` the
slots after it, `out'` is `out` with the response written at its start, and `pos'` is the position
after the request. -/
def Handled (B : List UInt8) (pos : UInt64) (st : List Slot) (n pos' : UInt64) (st' : List Slot)
    (out out' : Slots UInt8 64) : Prop :=
  match kvStep st (B.drop pos.toNat) with
  | none => n = 0
  | some (st'', w, rest) => n.toNat = w.length ∧ w ≠ [] ∧ st' = st'' ∧ Writes out out' 0 w ∧
      pos'.toNat + rest.length = B.length

/-- A response whose value is within its bound is within `KResp.Bound`. -/
theorem KResp.bound_of_len {r : KResp} (h : r.val.len.toNat ≤ 32) : r.Bound := fun _ => h

/-- A value of `reqFmt` within the bounds `KReq.Bound` is a request the server answers. -/
theorem KReq.reqOk {q : KReq} (hok : reqFmt.ok q.toVal = true) (hb : q.Bound) : ReqOk q := by
  obtain ⟨-, hop⟩ := ReqOk.cases hok
  simp only [KReq.Bound, ← UInt64.toNat_inj, UInt64.reduceToNat] at hb
  exact ⟨hok, by omega, by omega⟩

/-- A request that `KReq.parseAt` accepted is one the server answers. -/
theorem KReq.parseAt_ok {N : Nat} {hN : N < 2 ^ 64} {s : Slots UInt8 N} {sl pos : UInt64} {q : KReq}
    (hpre : pos.toNat ≤ sl.toNat ∧ sl.toNat ≤ N ∧ ∀ k < sl.toNat, s.isFull k = true)
    (h : (KReq.parseAt N hN s sl pos q).run.fst = true) :
    ReqOk (KReq.parseAt N hN s sl pos q).run.snd.fst := by
  have hp := KReq.parseAt.post N hN s sl pos q hpre
  rw [h] at hp
  exact KReq.reqOk (hp.1.okT (by simpa using hpre.1)) (hp.2 rfl).2

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- Answer the request at `pos` in `s` from the store `tab`, and write the response at the start of
`out`; the result is the response's length, or 0 when no request parses. -/
mp def handle (s : &[UInt8; 256]) (pos : &mut UInt64) (q : &mut KReq) (tab : &mut Arr Entry 4)
    (resp : &mut KResp) (out : &mut [UInt8; 64])
    requires pos.toNat ≤ s.len.toNat ∧ TabOk tab ∧ resp.val.len.toNat ≤ 32 ∧ 37 ≤ out.len.toNat
    ensures TabOk tab' ∧ resp'.val.len.toNat ≤ 32 ∧ result.toNat ≤ 37 ∧
      (result ≠ 0 → pos'.toNat ≤ s.len.toNat) ∧
      Handled (Slots.bytes s s.len.toNat) pos (absTab tab) result pos' (absTab tab') out out' :
      UInt64 := do
  let ok := KReq.parseAt (&s) (&mut pos) (&mut q)
  if !ok then return 0
  serve (&mut tab) (&q) (&mut resp)
  let mut p : UInt64 := 0
  KResp.writeAt (&mut out) (&mut p) (&resp)
  p

mp prove handle.safe := by
  mp_auto [KReq.parseAt_ok, respFmt_maxSize, ReqOk, KResp.bound_of_len]

mp prove handle.spec := by
  intro s sl pos q tab resp out ol
  vcgen [handle]
  all_goals try dsimp only at *
  case vc1 hpre => exact ⟨hpre.1.1, hpre.2.1.1, hpre.2.1.2⟩
  case vc2 hpre ok q' p' _ hpost hfl =>
    subst hfl
    refine ⟨hpre.1.2.1, hpre.1.2.2.1, by simp, by simp, ?_⟩
    simp [Handled, kvStep, Fmt.parse, ParsedT.none_of_false hpost.1]
  case vc3 hpre ok q' p' _ hpost hfl =>
    have hok : ok = true := by simpa using hfl
    subst hok
    exact ⟨hpre.1.2.1, KReq.reqOk (hpost.1.okT (by simpa using hpre.1.1)) (hpost.2 rfl).2,
      hpre.1.2.2.1⟩
  case vc4 hpre ok q' p' _ hpost hfl _ resp' tab' _ hserve =>
    have := hpre.1.2.2.2
    exact ⟨⟨by simp [respFmt_maxSize]; omega, fun _ => hserve.2.1⟩, hpre.2.2⟩
  case vc5 hpre ok q' p' _ hpost hfl _ resp' tab' _ hserve _ p'' out' _ hw =>
    have hok : ok = true := by simpa using hfl
    subst hok
    have hB : pos.toNat ≤ (Slots.bytes s sl.toNat).length := by simpa using hpre.1.1
    obtain ⟨hP, -, hp'⟩ := hpost.1.ok_eq hB
    obtain ⟨htab', hrv', hrok, heq⟩ := hserve
    obtain ⟨⟨hn, hwr⟩, -⟩ := hw
    have hlen := Fmt.write_length_le respFmt _ hrok
    rw [respFmt_maxSize] at hlen
    simp only [UInt64.toNat_zero, Nat.zero_add] at hn
    refine ⟨htab', hrv', by simp only [Fmt.write] at hlen; omega, fun _ => (hpost.2 rfl).1, ?_⟩
    simp only [Handled, kvStep, Fmt.parse, hP, ← heq]
    refine ⟨hn, ?_, ?_, hwr, ?_⟩
    · apply List.ne_nil_of_length_pos
      simp only [KResp.toVal_eq, respVal, respFmt, Fmt.write, Fmt.writeT, List.length_append,
        encUint_length]
      omega
    · simp
    · simp at hp' ⊢; omega

/-! ## The server -/

/-- The server's root: the input read so far, the position of the next request, whether the
input has ended, the store, the current request and response, and the output buffer. -/
structure Srv where
  inb : Arr UInt8 256
  inLen : UInt64
  pos : UInt64
  eof : UInt64
  tab : Arr Entry 4
  req : KReq
  resp : KResp
  out : Arr UInt8 64
deriving Data

/-- The bounds the server keeps. -/
def SrvInv (r : Srv) : Prop :=
  r.inLen.toNat ≤ 256 ∧ r.pos.toNat ≤ r.inLen.toNat ∧ TabOk r.tab ∧ r.resp.val.len.toNat ≤ 32

/-- What a read whose reply is `a` does to the input buffer `inb` holding `len` bytes and the
end-of-input flag `eof`, as one read of `KV.readsN`: the bytes delivered land at `len`; a count of
0, or one above the room left, ends the input with the length unchanged; otherwise the length grows
by the count, and the input ends when the buffer is full. -/
def ReadStep (a : Reply) (inb : Arr UInt8 256) (len eof : UInt64) (inb' : Arr UInt8 256)
    (len' eof' : UInt64) : Prop :=
  inb'.toList = Flat.splice inb.toList len.toNat ((fitOut [256 - len.toNat] a.bytesOut).head?.getD []) ∧
  ((a.result.toNat = 0 ∨ 256 - len.toNat < a.result.toNat) → len' = len ∧ eof' = 1) ∧
  (¬ (a.result.toNat = 0 ∨ 256 - len.toNat < a.result.toNat) →
    len'.toNat = len.toNat + a.result.toNat ∧
      eof' = if len.toNat + a.result.toNat = 256 then 1 else eof)

/-- The buffer after a read at `len`: the bytes delivered land at `len`. -/
theorem ReadStep.of_vwrite {a : Reply} {inb : Arr UInt8 256} {len eof len' eof' : UInt64}
    (hl : len.toNat ≤ 256)
    (h1 : (a.result.toNat = 0 ∨ 256 - len.toNat < a.result.toNat) → len' = len ∧ eof' = 1)
    (h2 : ¬ (a.result.toNat = 0 ∨ 256 - len.toNat < a.result.toNat) →
      len'.toNat = len.toNat + a.result.toNat ∧
        eof' = if len.toNat + a.result.toNat = 256 then 1 else eof) :
    ReadStep a inb len eof
      (vwrite inb len.toNat ((fitOut [256 - len.toNat] a.bytesOut).head?.getD [])) len' eof' := by
  have := fitOut_one_le (256 - len.toNat) a.bytesOut
  rw [List.headD_eq_head?_getD] at this
  exact ⟨Flat.vwrite_toList inb len.toNat ((fitOut [256 - len.toNat] a.bytesOut).head?.getD []) (by omega), h1, h2⟩

/-- The call the code makes is `KV.readCall`. -/
theorem readCall_eq {len : UInt64} (h : len.toNat ≤ 256) :
    (⟨"read", [0], [], [(256 - len).toNat]⟩ : Call) = KV.readCall len.toNat := by
  have hle : len ≤ 256 := UInt64.le_iff_toNat_le.mpr (by simpa using h)
  simp [KV.readCall, UInt64.toNat_sub_of_le _ _ hle]

set_option mp.autoSpec false in
/-- Read more input, until the end of the input or a full buffer. The contract is one read of
`KV.readsN`: the call `KV.readCall` and what its reply does (`ReadStep`). -/
mp def fill (inb : &mut Arr UInt8 256) (inLen : &mut UInt64) (eof : &mut UInt64)
    requires inLen.toNat ≤ 256
    ensures events = [(KV.readCall inLen.toNat).event (ω.answer history (KV.readCall inLen.toNat))] ∧
      exited = false ∧ inLen.toNat ≤ inLen'.toNat ∧ inLen'.toNat ≤ 256 ∧
      ReadStep (ω.answer history (KV.readCall inLen.toNat)) inb inLen eof inb' inLen' eof' :
      Unit := do
  let n := inLen
  let k := kvRead 0 (&mut inb[n..256])
  let stop := k == 0 || k > 256 -! n
  let m := if stop then n else n +! k
  inLen := m
  eof := if stop || m == 256 then 1 else eof

mp prove fill.spec := by
  intro ω inb inLen eof; mp_history; rename_i hl
  have hle : inLen ≤ 256 := UInt64.le_iff_toNat_le.mpr (by simpa using hl)
  vcgen [fill]
  all_goals subst_vars
  all_goals simp only [World.ask_mk_live, readCall_eq hl] at *
  all_goals simp only [headD_match, UInt64.toNat_sub_of_le _ _ hle, UInt64.reduceToNat] at *
  all_goals generalize ω.answer history (KV.readCall inLen.toNat) = a at *
  all_goals exact ⟨_, rfl, rfl, trivial, by grind, by grind, ReadStep.of_vwrite hl (by grind) (by grind)⟩

theorem drop_eq_of_length {B pre rest : List UInt8} {p p' : Nat} (hB : B.drop p = pre ++ rest)
    (hp : p' + rest.length = B.length) : B.drop p' = rest := by
  have hr : B.drop (p + pre.length) = rest := by
    rw [← List.drop_drop, hB, List.drop_left]
  have hl := congrArg List.length hB
  simp only [List.length_drop, List.length_append] at hl
  by_cases h : p ≤ B.length
  · rw [show p' = p + pre.length by omega, hr]
  · have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp at hp; simp [List.drop_eq_nil_of_le, hp]

/-- The input left: the bytes read so far after the position of the next request. -/
def inp (s : Srv) : List UInt8 := (s.inb.toList.take s.inLen.toNat).drop s.pos.toNat

/-- What one step of the server does from the root `r` and the history `h`: the events `evs` it
appends, whether it exits (`e`), and the root `r'` after it. Before the end of the input it makes
one read of `KV.readsN` (`ReadStep`). At the end of the input with no request left it exits with
0. Otherwise it answers the request at the front of the input left as `kvStep` does, with
`Fmt.parse reqFmt` and `Fmt.write respFmt`: when no request parses it exits with 1, else it writes
the response, the slots become those `kvServe` gives, and the input left is the bytes after the
request. -/
def StepSpec (ω : Oracle) (h : List Event) (r : Srv) (evs : List Event) (e : Bool) (r' : Srv) :
    Prop :=
  if r.eof = 0 then
    evs = [(KV.readCall r.inLen.toNat).event (ω.answer h (KV.readCall r.inLen.toNat))] ∧
      e = false ∧ r'.pos = r.pos ∧ r'.tab = r.tab ∧
      ReadStep (ω.answer h (KV.readCall r.inLen.toNat)) r.inb r.inLen r.eof r'.inb r'.inLen r'.eof
  else if r.pos = r.inLen then evs = [Examples.exitEvent 0] ∧ e = true
  else match kvStep (absTab r.tab) (inp r) with
    | none => evs = [Examples.exitEvent 1] ∧ e = true
    | some (st, w, rest) =>
      evs = [(KV.writeCall w).event (ω.answer h (KV.writeCall w))] ∧ e = false ∧
        r'.eof = r.eof ∧ absTab r'.tab = st ∧ inp r' = rest

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- One step: read until the input ends, then answer one request; exit with 0 at the end of the
input and with 1 at a malformed request. Its contract keeps the bounds `SrvInv` and is one step of
the protocol, `StepSpec`. -/
mp def srvStep (r : &mut Srv) requires SrvInv r
    ensures SrvInv r' ∧ StepSpec ω history r events exited r' : Unit := do
  if r.eof == 0 then fill (&mut r.inb) (&mut r.inLen) (&mut r.eof)
  else if r.pos == r.inLen then
    let _ := kvExit 0
  else
    let n := r.inLen
    let m := handle (&r.inb[0..n]) (&mut r.pos) (&mut r.req) (&mut r.tab) (&mut r.resp)
      (&mut r.out[0..64])
    if m == 0 then
      r.pos := n
      let _ := kvExit 1
    else
      let _ := kvWrite 1 (&r.out[0..m])

/-- The precondition of `handle` in a step of the server. -/
theorem handle_pre {r : Srv} (h : SrvInv r) :
    (r.pos.toNat ≤ r.inLen.toNat ∧ TabOk r.tab ∧ r.resp.val.len.toNat ≤ 32 ∧ 37 ≤ (64 : UInt64).toNat) ∧
      (r.inLen.toNat ≤ 256 ∧ ∀ k < r.inLen.toNat, (vview r.inb 0 r.inLen.toNat).isFull k = true) ∧
      (64 : UInt64).toNat ≤ 64 ∧ ∀ k < (64 : UInt64).toNat, (vview r.out 0 64).isFull k = true := by
  obtain ⟨hl, hp, htab, hrv⟩ := h
  simp only [vview_isFull, UInt64.reduceToNat]
  exact ⟨⟨hp, htab, hrv, by decide⟩, ⟨hl, fun k hk => by simp; omega⟩, by decide, fun k hk => by simp; omega⟩

/-- A response fits the output buffer. -/
theorem handle_le {r : Srv} (h : SrvInv r) :
    (handle (vview r.inb 0 r.inLen.toNat) r.inLen r.pos r.req r.tab r.resp (vview r.out 0 64) 64).run.fst.toNat ≤ 64 := by
  have := (handle.post (vview r.inb 0 r.inLen.toNat) r.inLen r.pos r.req r.tab r.resp
    (vview r.out 0 64) 64 (handle_pre h)).2.2.1
  omega

-- `mp_auto` would pass `fill.post`, a contract about events, to `grind`, which rejects it, so
-- the obligations are discharged by `mp_safe` with the other callees' contracts.
mp prove srvStep.safe := by
  mp_safe [srvStep, fill.Safe', fill.req, handle.Safe', handle.req, handle.exp_denote, Lens.fst,
    Lens.snd] using fill.Safe', handle.Safe' grind [SrvInv, TabOk, handle_le, handle.post]

mp prove srvStep.spec := by
  intro ω r; mp_history; rename_i hinv
  vcgen [srvStep]
  all_goals subst_vars
  case vc1 heof =>
    refine ⟨fun _ => ⟨hinv.1, fun x evs e hE => ?_⟩, fun h => absurd h (by simp)⟩
    obtain ⟨rfl, rfl, h1, h2, hR⟩ := hE
    simp only [binderNameHint]; vcgen
    have := hinv.2.1
    exact ⟨_, rfl, ⟨h2, by dsimp only; omega, hinv.2.2⟩, by simpa [StepSpec, heof] using hR⟩
  case vc2 heof hpos => exact ⟨_, rfl, hinv, by simp [StepSpec, heof, hpos]; rfl⟩
  all_goals
    rename_i heof hpos hm
    have hh := handle.post _ r.inLen r.pos r.req r.tab r.resp _ 64 (handle_pre hinv)
    simp only [UInt64.sub_zero] at hm ⊢
    generalize (handle (vview r.inb 0 r.inLen.toNat) r.inLen r.pos r.req r.tab r.resp
      (vview r.out 0 64) 64).run = R at hh hm ⊢
    obtain ⟨n, out', resp', tab', q', pos', u⟩ := R
    obtain ⟨htab', hrv', hle, hpos', hH⟩ := hh
    simp only [Slots.bytes_vview r.inb hinv.1, Handled] at hH
    change match kvStep (absTab r.tab) (inp r) with
      | none => _
      | some (st'', w, rest) => _ at hH
    dsimp only at hm hpos' hle ⊢
    simp only [StepSpec, heof, hpos, ite_false, World.call_mk_exit, World.call_mk_live]
  case vc3 =>
    refine ⟨_, rfl, ⟨hinv.1, by simp, htab', hrv'⟩, ?_⟩
    split
    · exact ⟨rfl, trivial⟩
    · rename_i hk; rw [hk] at hH
      exact absurd (List.eq_nil_of_length_eq_zero (by simp [← hH.1, hm])) hH.2.1
  case vc4 =>
    refine ⟨_, rfl, ⟨hinv.1, hpos' hm, htab', hrv'⟩, ?_⟩
    split
    · rename_i hk; rw [hk] at hH; exact absurd hH hm
    · rename_i st w rest hk
      rw [hk] at hH
      obtain ⟨hn, hne, rfl, hw, hrest⟩ := hH
      simp only [kvStep] at hk
      split at hk
      · cases hk
      · rename_i q rest' hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨-, rfl, rfl⟩ := hk
        refine ⟨?_, by trivial, by trivial, by trivial, ?_⟩
        · rw [vrange, List.drop_zero, hn, vunview_take hw (by omega) (by decide)]; rfl
        · exact drop_eq_of_length (Fmt.parse_canonical reqFmt_canonical hp) (by simpa using hrest)

/-- An empty byte string. -/
mp def LBytes.empty16 : LBytes 16 := { len := 0, data := Vector.replicate 16 0 }
/-- An empty byte string. -/
mp def LBytes.empty32 : LBytes 32 := { len := 0, data := Vector.replicate 32 0 }

set_option mp.autoSpec false in
/-- The initial root. -/
mp def srvInit ensures SrvInv result : Srv :=
  { inb := Vector.replicate 256 0, inLen := 0, pos := 0, eof := 0,
    tab := Vector.replicate 4 { used := 0, key := LBytes.empty16, val := LBytes.empty32 },
    req := { id := 0, op := 0, key := LBytes.empty16, val := LBytes.empty32 },
    resp := { id := 0, status := 0, val := LBytes.empty32, code := 0 },
    out := Vector.replicate 64 0 }

mp prove srvInit.spec := by
  vcgen [srvInit, LBytes.empty16, LBytes.empty32]
  simp only [SrvInv, TabOk, vget]
  exact ⟨by decide, by decide, fun j hj => by simp [hj], by decide⟩

mp program kvsrv (root : Srv) init srvInit step srvStep invariant SrvInv

example := @kvsrv.events_reach

-- The step keeps the bounds from every world, also after `exit`, where the contract of `srvStep`,
-- which is about a run from a live world, says nothing of the root. So this goal is proved from
-- the body, with `fill` unfolded and the contract of `handle`.
mp prove kvsrv.inv_step := by
  intro ω r
  refine ⟨id, ?_⟩
  have hpre := handle_pre (r := r)
  vcgen [srvStep, fill]
  all_goals
    have hh := handle.post _ r.inLen r.pos r.req r.tab r.resp _ 64 (hpre ‹_›)
    simp only [UInt64.sub_zero] at *
    grind [SrvInv]

example : kvsrv.Safe := kvsrv.safe

#mp_compile kvsrv ".lake/kvsrv-x64"
#mp_compile kvsrv ".lake/kvsrv-a64" "arm64-linux"

end Millipede.Tests.FormatKV
