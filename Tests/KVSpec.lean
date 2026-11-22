import Tests.FormatKV
import Millipede.Top.Behaviour

/-!
# The key-value server's specification

This file says what the server `kvsrv` of Tests/FormatKVSrv.lean does, in plain Lean that does not
mention the compiler or the server's code. Tests/KVRefine.lean proves that the server's event trace
is the one given here, for every oracle, and carries that to the compiled bytes.

* The store is a finite map from keys to values with room for `capacity` = 4 keys (`Store`). A
  request gets, puts or deletes one key (`Req`), and `Store.apply` answers it: a get answers the
  key's value or "not found", a put stores the value and answers "done", or answers "full" and
  changes nothing when the key is absent and 4 keys are present, and a delete removes the key and
  answers "done", or answers "not found".
* On the wire a request is a value of the format `reqFmt` and a response one of `respFmt`
  (Tests/FormatKV.lean). A request is decoded from its value by `Req.ofVal`, and the response
  carries the request's id. `answers bs` answers the requests at the front of the bytes `bs`
  from the empty store, each decoded by `Fmt.parse reqFmt`, and gives the bytes of each response,
  `Fmt.write respFmt`, and the exit status: 0 when the bytes end after a request, 1 at the first
  request that does not parse.
* The server first reads its input. It keeps a buffer of 256 bytes, of which the first `len`
  are input, and asks `read(0, buf + len, 256 - len)`. The oracle answers with a count `k` and
  the bytes it delivers, at most `256 - len`, which land at `buf + len`. A count of 0 or one
  above `256 - len` (an error, or a reply that claims more than the buffer holds) ends the input,
  with `len` unchanged; otherwise `len` grows by `k`, and the input ends when the buffer is
  full (`reads`). When a reply delivers fewer bytes than its count, the input's remaining bytes
  are what the buffer held before: zeros, or bytes an earlier reply delivered beyond its count.
* `kvTrace ω` is the whole trace: the reads, then one `write(1, …)` of each response, then
  `exit` with the status.

A `write` event records the bytes the server asked to write and the count the oracle returned.
The server does not look at that count, so after a short write the bytes not written are lost,
and the trace shows that only through the count.
-/

namespace Millipede.Tests.KV

open Millipede Millipede.Format Millipede.Tests.FormatKV

/-! ## The store -/

/-- A key. The format allows at most 16 bytes. -/
abbrev Key := List UInt8
/-- A value. The format allows at most 32 bytes. -/
abbrev Value := List UInt8

/-- The store: the keys that have a value, with their values, in the order in which they were
first put. `Store.apply` keeps each key at most once (`Store.apply_nodup`, Tests/KVRefine.lean). -/
abbrev Store := List (Key × Value)

/-- The number of keys the store has room for. -/
def capacity : Nat := 4

/-- The value of the key `k`. -/
def Store.get : Store → Key → Option Value
  | [], _ => none
  | (k', v) :: m, k => if k' = k then some v else Store.get m k

/-- The store with the value `v` for `k`: in place when `k` is present, else at the end. -/
def Store.set : Store → Key → Value → Store
  | [], k, v => [(k, v)]
  | (k', v') :: m, k, v => if k' = k then (k, v) :: m else (k', v') :: Store.set m k v

/-- The store without the key `k`. -/
def Store.erase : Store → Key → Store
  | [], _ => []
  | (k', v') :: m, k => if k' = k then m else (k', v') :: Store.erase m k

/-- A request. -/
inductive Req where
  | get (k : Key)
  | put (k : Key) (v : Value)
  | del (k : Key)
deriving DecidableEq, Repr

/-- A response. -/
inductive Resp where
  | value (v : Value)
  | done
  | notFound
  | full
deriving DecidableEq, Repr

/-- The answer to a request, and the store after it. A put of a key that is absent when the store
holds `capacity` keys answers `full` and changes nothing. -/
def Store.apply (m : Store) : Req → Store × Resp
  | .get k => (m, match m.get k with
    | some v => .value v
    | none => .notFound)
  | .put k v =>
    if (m.get k).isSome ∨ m.length < capacity then (m.set k v, .done) else (m, .full)
  | .del k => if (m.get k).isSome then (m.erase k, .done) else (m, .notFound)

/-! ## The wire -/

/-- The request a value of `reqFmt` stands for, with its id: operation 1 is a get, 2 a put and 3 a
delete. Every value that `Fmt.parse reqFmt` returns has one of these forms
(`Req.ofVal_of_ok`). -/
def Req.ofVal : Val → Option (Nat × Req)
  | .pair (.num id) (.tag 1 (.bytes k)) => some (id, .get k)
  | .pair (.num id) (.tag 2 (.pair (.bytes k) (.bytes v))) => some (id, .put k v)
  | .pair (.num id) (.tag 3 (.bytes k)) => some (id, .del k)
  | _ => none

/-- The value of `respFmt` of a response to the request with id `id`: status 0 with the value,
status 1, or status 2 with the error code 2 (not found) or 1 (full). -/
def Resp.toVal (id : Nat) : Resp → Val
  | .value v => .pair (.num id) (.tag 0 (.bytes v))
  | .done => .pair (.num id) (.tag 1 .unit)
  | .notFound => .pair (.num id) (.tag 2 (.num 2))
  | .full => .pair (.num id) (.tag 2 (.num 1))

/-- The value of `reqFmt` of the request `q` with id `id`. -/
def Req.toVal (id : Nat) : Req → Val
  | .get k => .pair (.num id) (.tag 1 (.bytes k))
  | .put k v => .pair (.num id) (.tag 2 (.pair (.bytes k) (.bytes v)))
  | .del k => .pair (.num id) (.tag 3 (.bytes k))

/-- The bytes of a request. -/
def Req.bytes (id : Nat) (q : Req) : List UInt8 := reqFmt.write (q.toVal id)

/-- A request the format can carry: an id of two bytes, a key of at most 16 bytes and a value of
at most 32. -/
def Req.Ok (id : Nat) : Req → Prop
  | .get k | .del k => id < 65536 ∧ k.length ≤ 16
  | .put k v => id < 65536 ∧ k.length ≤ 16 ∧ v.length ≤ 32

/-- The bytes of a response. -/
def Resp.bytes (id : Nat) (r : Resp) : List UInt8 := respFmt.write (r.toVal id)

/-- The bytes of the responses to the requests at the front of `bs` from the store `m`, and the
exit status: 0 when `bs` ends after a request, 1 at the first request that does not parse. The
first argument bounds the number of requests; each request takes at least one byte, so
`bs.length` is enough (`answers`). -/
def answersN : Nat → Store → List UInt8 → List (List UInt8) × UInt64
  | _, _, [] => ([], 0)
  | 0, _, _ :: _ => ([], 1)
  | n + 1, m, b :: bs => match reqFmt.parse (b :: bs) with
    | none => ([], 1)
    | some (v, rest) => match Req.ofVal v with
      | none => ([], 1)
      | some (id, q) =>
        ((m.apply q).2.bytes id :: (answersN n (m.apply q).1 rest).1,
          (answersN n (m.apply q).1 rest).2)

/-- The bytes of the responses to the requests in `bs`, from the empty store, and the exit
status. -/
def answers (bs : List UInt8) : List (List UInt8) × UInt64 := answersN bs.length [] bs

/-! ## The trace -/

/-- The call `read(0, buf + len, 256 - len)`. -/
def readCall (len : Nat) : Call := ⟨"read", [0], [], [256 - len]⟩

/-- The call `write(1, bs)`. -/
def writeCall (bs : List UInt8) : Call := ⟨"write", [1], [bs], []⟩

/-- The read phase from the history `h` and the buffer `buf` holding `len` bytes of input: the
history after the reads and the input. Each read asks for the rest of the buffer, and the
oracle's reply `r` gives the count and the bytes `d` that land at `len` (`Flat.splice` replaces
the bytes of a list at an offset). A count of 0, or one above
`256 - len`, ends the input with `len` unchanged. Otherwise the input grows by the count, and it
ends when the buffer is full. The first argument bounds the number of reads; 257 is enough
(`reads`), since each read but the last adds at least one byte. -/
def readsN (ω : Oracle) : Nat → List Event → List UInt8 → Nat → List Event × List UInt8
  | 0, h, buf, len => (h, buf.take len)
  | n + 1, h, buf, len =>
    let r := ω.answer h (readCall len)
    let h' := h ++ [(readCall len).event r]
    let buf' := Flat.splice buf len ((fitOut [256 - len] r.bytesOut).headD [])
    if r.result.toNat = 0 ∨ 256 - len < r.result.toNat then (h', buf.take len)
    else if len + r.result.toNat = 256 then (h', buf'.take 256)
    else readsN ω n h' buf' (len + r.result.toNat)

/-- The read phase of the server: the history after the reads, and the input. The buffer starts
as 256 zero bytes. -/
def reads (ω : Oracle) : List Event × List UInt8 := readsN ω 257 [] (List.replicate 256 0) 0

/-- The events of writing each of the byte strings `rs` to file descriptor 1, after the history
`h`. The count of each write is the oracle's answer. -/
def writes (ω : Oracle) : List Event → List (List UInt8) → List Event
  | _, [] => []
  | h, r :: rs =>
    (writeCall r).event (ω.answer h (writeCall r)) ::
      writes ω (h ++ [(writeCall r).event (ω.answer h (writeCall r))]) rs

/-- The trace of the server under the oracle `ω`: the reads, then a `write` of each response to
the requests in the input, then `exit` with 0 at the end of the input or 1 at the first request
that does not parse. -/
def kvTrace (ω : Oracle) : List Event :=
  (reads ω).1 ++ writes ω (reads ω).1 (answers (reads ω).2).1 ++
    [Examples.exitEvent (answers (reads ω).2).2]

/-! ## Request sequences

`Store.run m qs` is what the abstract machine answers to the requests `qs`, each with its id, in
order, and `encode qs` their bytes. `answers_encode` says that `answers` of those bytes is
`Store.run` from the empty store: the server's input is decoded exactly into the requests. -/

/-- The bytes of the responses to the requests `qs` from the store `m`, in order. -/
def Store.run : Store → List (Nat × Req) → List (List UInt8)
  | _, [] => []
  | m, (id, q) :: qs => (m.apply q).2.bytes id :: Store.run (m.apply q).1 qs

/-- The bytes of the requests `qs`, one after the other. -/
def encode : List (Nat × Req) → List UInt8
  | [] => []
  | (id, q) :: qs => q.bytes id ++ encode qs

/-- The store after the requests `qs`. -/
def Store.after : Store → List (Nat × Req) → Store
  | m, [] => m
  | m, (_, q) :: qs => Store.after (m.apply q).1 qs

/-- `q` puts or deletes the key `k`. -/
def Req.Touches (k : Key) : Req → Prop
  | .get _ => False
  | .put k' _ | .del k' => k' = k

/-! ## Properties of the store -/

theorem Store.get_set (m : Store) (k k' : Key) (v : Value) :
    (m.set k v).get k' = if k = k' then some v else m.get k' := by
  induction m with
  | nil => simp [Store.set, Store.get]
  | cons e m ih =>
    obtain ⟨k₀, v₀⟩ := e
    by_cases h : k₀ = k
    · subst h; by_cases h' : k₀ = k' <;> simp [Store.set, Store.get, h']
    · simp only [Store.set, h, ite_false, Store.get, ih]
      by_cases h' : k₀ = k' <;> by_cases h'' : k = k' <;> simp_all

theorem Store.get_erase_ne (m : Store) {k k' : Key} (hk : k ≠ k') :
    (m.erase k).get k' = m.get k' := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    obtain ⟨k₀, v₀⟩ := e
    by_cases h : k₀ = k
    · subst h; simp [Store.erase, Store.get, hk]
    · simp only [Store.erase, h, ite_false, Store.get, ih]

/-- A request that neither puts nor deletes `k` leaves the value of `k` as it was. -/
theorem Store.get_apply_of_not_touches (m : Store) {k : Key} {q : Req} (hq : ¬ q.Touches k) :
    (m.apply q).1.get k = m.get k := by
  cases q with
  | get k' => rfl
  | put k' v =>
    simp only [Req.Touches] at hq
    simp only [Store.apply]; split
    · simp [Store.get_set, hq]
    · rfl
  | del k' =>
    simp only [Req.Touches] at hq
    simp only [Store.apply]; split
    · exact Store.get_erase_ne m hq
    · rfl

/-- After a put that the store has room for, the key has the value put. -/
theorem Store.get_put (m : Store) (k : Key) (v : Value)
    (h : (m.get k).isSome ∨ m.length < capacity) : (m.apply (.put k v)).1.get k = some v := by
  simp [Store.apply, h, Store.get_set]

/-- A get answers the key's value. -/
theorem Store.apply_get (m : Store) (k : Key) (v : Value) (h : m.get k = some v) :
    (m.apply (.get k)).2 = .value v := by
  simp [Store.apply, h]

/-- A request answers a get of another key as before it: no request changes the answer for a key
it does not put or delete. -/
theorem Store.apply_get_other (m : Store) (k : Key) {q : Req} (hq : ¬ q.Touches k) :
    ((m.apply q).1.apply (.get k)).2 = (m.apply (.get k)).2 := by
  simp only [Store.apply.eq_1 (m.apply q).1, Store.apply.eq_1 m, Store.get_apply_of_not_touches m hq]

theorem Store.after_get (m : Store) (k : Key) (qs : List (Nat × Req))
    (h : ∀ x ∈ qs, ¬ x.2.Touches k) : (m.after qs).get k = m.get k := by
  induction qs generalizing m with
  | nil => rfl
  | cons x qs ih =>
    obtain ⟨id, q⟩ := x
    simp only [Store.after]
    rw [ih _ (fun y hy => h y (by simp [hy])), Store.get_apply_of_not_touches m (h (id, q) (by simp))]

theorem Store.run_append (m : Store) (qs qs' : List (Nat × Req)) :
    m.run (qs ++ qs') = m.run qs ++ (m.after qs).run qs' := by
  induction qs generalizing m with
  | nil => rfl
  | cons x qs ih => obtain ⟨id, q⟩ := x; simp [Store.run, Store.after, ih]

/-- A get of `k` after a put of `k` that the store had room for, with no put or delete of `k`
between them, answers the value put. -/
theorem Store.run_put_get (m : Store) (k : Key) (v : Value) (id id' : Nat)
    (mid rest : List (Nat × Req)) (hroom : (m.get k).isSome ∨ m.length < capacity)
    (hmid : ∀ x ∈ mid, ¬ x.2.Touches k) :
    m.run ((id, .put k v) :: mid ++ (id', .get k) :: rest) =
      m.run ((id, .put k v) :: mid) ++
        (Resp.value v).bytes id' :: ((m.after ((id, .put k v) :: mid)).apply (.get k)).1.run rest := by
  rw [Store.run_append]
  congr 1
  simp only [Store.run, Store.after]
  rw [Store.apply_get _ _ _ (by rw [Store.after_get _ _ _ hmid, Store.get_put _ _ _ hroom])]

/-! ## Decoding -/

theorem Req.toVal_ok {id : Nat} {q : Req} (h : q.Ok id) : reqFmt.ok (q.toVal id) = true := by
  cases q <;>
    simp_all [Req.Ok, Req.toVal, reqFmt, keyFmt, valFmt, Fmt.ok, Fmt.okT] <;> omega

theorem Req.ofVal_toVal (id : Nat) (q : Req) : Req.ofVal (q.toVal id) = some (id, q) := by
  cases q <;> rfl

/-- Every value that `reqFmt` parses is a request. -/
theorem Req.ofVal_of_ok {v : Val} (h : reqFmt.ok v = true) : ∃ id q, Req.ofVal v = some (id, q) ∧
    v = q.toVal id := by
  rcases v with _ | _ | _ | ⟨_ | _ | _ | _ | _, _ | _ | _ | _ | ⟨t, a⟩⟩ | _ <;>
    simp only [reqFmt, keyFmt, valFmt, Fmt.ok, Fmt.okT, Bool.false_eq_true, Bool.and_false,
      Bool.false_and] at h
  case pair.num.tag id =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨-, -, h⟩ := h
    by_cases h1 : t = 1
    · subst h1
      rcases a with _ | k | _ | _ | _ <;> simp [Fmt.okT] at h
      exact ⟨id, .get k, rfl, rfl⟩
    by_cases h2 : t = 2
    · subst h2
      rcases a with _ | _ | _ | ⟨_ | k | _ | _ | _, _ | v | _ | _ | _⟩ | _ <;> simp [Fmt.okT] at h
      exact ⟨id, .put k v, rfl, rfl⟩
    by_cases h3 : t = 3
    · subst h3
      rcases a with _ | k | _ | _ | _ <;> simp [Fmt.okT] at h
      exact ⟨id, .del k, rfl, rfl⟩
    simp [h1, h2, h3] at h

/-- The bytes of a request are at least one byte. -/
theorem Req.bytes_ne_nil (id : Nat) (q : Req) : q.bytes id ≠ [] := by
  cases q <;> simp [Req.bytes, Req.toVal, reqFmt, Fmt.write, Fmt.writeT, encUint, leBytes]

theorem Req.parse_bytes {id : Nat} {q : Req} (h : q.Ok id) (rest : List UInt8) :
    reqFmt.parse (q.bytes id ++ rest) = some (q.toVal id, rest) :=
  Fmt.parse_write reqFmt _ rest (Req.toVal_ok h)

theorem encode_length (qs : List (Nat × Req)) : qs.length ≤ (encode qs).length := by
  induction qs with
  | nil => simp [encode]
  | cons x qs ih =>
    obtain ⟨id, q⟩ := x
    have := List.length_pos_iff.mpr (Req.bytes_ne_nil id q)
    simp [encode]; omega

/-- With enough requests allowed, the answers to the bytes of the requests `qs` followed by `tail`
are the abstract machine's responses to `qs`, followed by the answers to `tail`. -/
theorem answersN_encode (qs : List (Nat × Req)) (hok : ∀ x ∈ qs, x.2.Ok x.1) (m : Store)
    (tail : List UInt8) (n : Nat) (hn : qs.length ≤ n) :
    answersN n m (encode qs ++ tail) =
      (m.run qs ++ (answersN (n - qs.length) (m.after qs) tail).1,
        (answersN (n - qs.length) (m.after qs) tail).2) := by
  induction qs generalizing m n with
  | nil => simp [encode, Store.run, Store.after]
  | cons x qs ih =>
    obtain ⟨id, q⟩ := x
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    have hq : q.Ok id := hok (id, q) (by simp)
    obtain ⟨b, bs, hb⟩ : ∃ b bs, q.bytes id ++ (encode qs ++ tail) = b :: bs := by
      cases h : q.bytes id with
      | nil => exact absurd h (Req.bytes_ne_nil id q)
      | cons b bs => exact ⟨b, bs ++ (encode qs ++ tail), rfl⟩
    have hp := Req.parse_bytes hq (encode qs ++ tail)
    simp only [encode, List.append_assoc, hb] at hp ⊢
    simp only [answersN, hp, Req.ofVal_toVal]
    rw [ih (fun y hy => hok y (by simp [hy])) _ n (by simp at hn; omega)]
    simp [Store.run, Store.after]

/-- The answers to the bytes of well-formed requests are the abstract machine's responses from
the empty store, with status 0. -/
theorem answers_encode (qs : List (Nat × Req)) (hok : ∀ x ∈ qs, x.2.Ok x.1) :
    answers (encode qs) = (Store.run [] qs, 0) := by
  have := answersN_encode qs hok [] [] (encode qs).length (encode_length qs)
  simp only [List.append_nil] at this
  rw [answers, this]
  cases (encode qs).length - qs.length <;> simp [answersN]

/-- The answers to the bytes of well-formed requests followed by bytes that do not begin with a
request are the abstract machine's responses, with status 1: the server answers every request
before the first malformed one and stops there. -/
theorem answers_encode_bad (qs : List (Nat × Req)) (hok : ∀ x ∈ qs, x.2.Ok x.1)
    (bad : List UInt8) (hbad : bad ≠ []) (hp : reqFmt.parse bad = none) :
    answers (encode qs ++ bad) = (Store.run [] qs, 1) := by
  have h := answersN_encode qs hok [] bad (encode qs ++ bad).length
    (by have := encode_length qs; simp; omega)
  rw [answers, h]
  obtain ⟨b, bs, rfl⟩ : ∃ b bs, bad = b :: bs := by
    cases bad with
    | nil => exact absurd rfl hbad
    | cons b bs => exact ⟨b, bs, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, (encode qs ++ b :: bs).length - qs.length = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by have := encode_length qs; simp; omega)).symm⟩
  rw [hn]
  simp [answersN, hp]

end Millipede.Tests.KV
