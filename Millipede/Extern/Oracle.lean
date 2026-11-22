/-!
# Extern events, oracles and the world

An extern call is observed as an `Event`, which records the symbol, the integer arguments, the
contents of the buffers the callee reads, the result word, and the contents of the buffers it
writes. Buffer addresses never appear, because an extern's answer depends only on contents.

An `Oracle` answers every call, given the history of events so far. Both the source semantics and
the machine semantics are functions of the oracle, and the observable behaviour of a program is
its event trace. A theorem that holds for every oracle treats the oracle as an adversary.

`World` is the state that the semantics threads, which is the events so far and whether the
program has exited. After `exit` the trace is frozen, so later calls record nothing and return
`0`. This module is independent of the object language, so the machine side can import it alone.
The world is described in doc/design/world.md.
-/

namespace Millipede

/-- A call as the caller presents it. It holds the symbol, the word arguments in parameter order
without the buffers, the bytes of each input buffer in parameter order, and the capacity of each
output buffer. -/
structure Call where
  sym : String
  args : List UInt64
  bytesIn : List (List UInt8)
  outCaps : List Nat := []
deriving DecidableEq, Repr

/-- The oracle's answer to a call, which is the result word and the bytes it writes into each
output buffer, truncated to the buffer's capacity when recorded. -/
structure Reply where
  result : UInt64
  bytesOut : List (List UInt8) := []
deriving DecidableEq, Repr

/-- One observed extern call. -/
structure Event where
  sym : String
  args : List UInt64
  bytesIn : List (List UInt8)
  result : UInt64
  bytesOut : List (List UInt8)
deriving DecidableEq, Repr

/-- An oracle answers each call given the history, which is all earlier events, oldest first. The
position of a call in the trace is `history.length`. -/
structure Oracle where
  answer : List Event → Call → Reply

/-- The bytes actually written, which for each output buffer of capacity `cap` are the first `cap`
bytes the oracle offered, or none if it offered none. It is structural on the capacity list. -/
def fitOut : List Nat → List (List UInt8) → List (List UInt8)
  | [], _ => []
  | _ :: caps, [] => [] :: fitOut caps []
  | cap :: caps, bs :: bss => bs.take cap :: fitOut caps bss

/-- One output buffer of capacity `c` receives at most `c` bytes. -/
theorem fitOut_one_le (c : Nat) (bss : List (List UInt8)) : ((fitOut [c] bss).headD []).length ≤ c := by
  cases bss <;> simp [fitOut] <;> omega

/-- The event recorded for call `c` answered by `r`. -/
def Call.event (c : Call) (r : Reply) : Event :=
  { sym := c.sym, args := c.args, bytesIn := c.bytesIn, result := r.result,
    bytesOut := fitOut c.outCaps r.bytesOut }

/-- The state that the semantics threads, which is the events so far, oldest first, and whether
`exit` has been called. -/
structure World where
  events : List Event
  halted : Bool
deriving DecidableEq, Repr

/-- The world before the program starts. -/
def World.init : World := ⟨[], false⟩

/-- The word a call delivers to the program. A call with exactly one output buffer, of capacity
`1` as in `read(fd, buf, 1)`, delivers the byte read when the result is `1`, and `2^64 - 1`
otherwise, for end of input or an error, which is the convention of `getc`. The byte is the one
the oracle offered, or `0` if it offered none, since the compiled code clears the buffer first.
Every other call delivers the result word. -/
def Call.value (c : Call) (r : Reply) : UInt64 :=
  if c.outCaps = [1] then
    if r.result = 1 then (((fitOut [1] r.bytesOut).headD []).headD 0).toUInt64
    else UInt64.ofNat (2 ^ 64 - 1)
  else r.result

/-- Perform an extern call under the oracle `ω`. If the program has already exited, nothing is
recorded and the result is `0`. A `noreturn` extern such as `exit` records its event with result
`0` without consulting the oracle, and halts the world. Otherwise the oracle answers given the
history, the event is appended, and the program gets the call's value `Call.value`. -/
def World.call (ω : Oracle) (c : Call) (noreturn : Bool) (w : World) : UInt64 × World :=
  if w.halted then (0, w)
  else if noreturn then (0, ⟨w.events ++ [c.event ⟨0, []⟩], true⟩)
  else
    let r := ω.answer w.events c
    (c.value r, ⟨w.events ++ [c.event r], false⟩)

/-- The raw answer to a call as the machine sees it, with the result word in a register and the
bytes written into the output buffers. It is the oracle's reply, or `⟨0, []⟩` once halted or for
a `noreturn` call, together with the world that `World.call` produces. -/
def World.ask (ω : Oracle) (c : Call) (noreturn : Bool) (w : World) : Reply × World :=
  if w.halted then (⟨0, []⟩, w)
  else if noreturn then (⟨0, []⟩, ⟨w.events ++ [c.event ⟨0, []⟩], true⟩)
  else
    let r := ω.answer w.events c
    (r, ⟨w.events ++ [c.event r], false⟩)

/-- `World.ask` and `World.call` produce the same world. -/
@[simp] theorem World.ask_snd (ω : Oracle) (c : Call) (nr : Bool) (w : World) :
    (w.ask ω c nr).2 = (w.call ω c nr).2 := by
  unfold World.ask World.call; split <;> (try split) <;> rfl

/-- For a call without output buffers, `World.call` delivers the raw result word. -/
theorem World.ask_fst_nil (ω : Oracle) (sym : String) (args : List UInt64)
    (bs : List (List UInt8)) (nr : Bool) (w : World) :
    (w.ask ω ⟨sym, args, bs, []⟩ nr).1.result = (w.call ω ⟨sym, args, bs, []⟩ nr).1 := by
  unfold World.ask World.call; split <;> (try split) <;> rfl

/-- A call that is answered delivers the value of the raw answer. -/
theorem World.call_fst (ω : Oracle) (c : Call) (w : World) (hh : w.halted = false) :
    (w.call ω c false).1 = c.value (w.ask ω c false).1 := by
  simp [World.call, World.ask, hh]

/-- Calls only ever append to the trace. -/
theorem World.call_prefix (ω : Oracle) (c : Call) (nr : Bool) (w : World) :
    w.events <+: (w.call ω c nr).2.events := by
  unfold World.call
  split
  · exact List.prefix_refl _
  · split <;> exact List.prefix_append _ _

/-- Once halted, a call changes nothing and returns `0`. -/
@[simp] theorem World.call_halted (ω : Oracle) (c : Call) (nr : Bool) (w : World)
    (h : w.halted = true) : w.call ω c nr = (0, w) := by
  simp [World.call, h]

end Millipede
