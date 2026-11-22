import Millipede.Top.Accept

/-!
# Tests of the behaviour theorems of `hello` and `revchunks`

The specifications are instantiated at a concrete oracle and checked by the kernel, the
theorems are instantiated on both targets, a wrong specification is refuted, and the default
compiler's acceptance, which the kernel does not evaluate, is checked by compiled evaluation.
-/

namespace Millipede.Examples.WitnessTest

open RevChunks

/-- Input `abc` and then end of input; every write reports all its bytes written. -/
def ωabc : Oracle :=
  ⟨fun h c => if c.sym = "read" then
      (if h.length = 0 then ⟨3, [[97, 98, 99]]⟩ else ⟨0, []⟩)
    else ⟨(c.bytesIn.headD []).length.toUInt64, []⟩⟩

/-- The specification at `ωabc`: read `abc`, write `cba`, read nothing, exit 0. -/
example : (RevChunks.spec ωabc 2).1 =
    [readEvent 3 [97, 98, 99], ⟨"write", [1], [[99, 98, 97]], 3, []⟩,
     readEvent 0 [], exitEvent 0] := by decide

/-- The specification is the source trace, so the source semantics agrees at `ωabc`. -/
example : revProg.events ωabc 2 = (RevChunks.spec ωabc 2).1 := revProg_events ωabc 2

/-- An oracle whose read reports 2 bytes but delivers 1: the buffer's older byte (a zero, at the
start) is written with it. -/
def ωshort : Oracle :=
  ⟨fun h c => if c.sym = "read" then
      (if h.length = 0 then ⟨2, [[120]]⟩ else ⟨0, []⟩)
    else ⟨0, []⟩⟩

example : (RevChunks.spec ωshort 1).1 =
    [readEvent 2 [120], ⟨"write", [1], [[0, 120]], 0, []⟩] := by decide

/-! ## A wrong specification is refuted -/

/-- A round that writes the bytes read without reversing them. -/
def badRound (ω : Oracle) (h : List Event) (buf : List UInt8) : List Event × Bool × List UInt8 :=
  let r := ω.answer h readCall
  let d := (fitOut [16] r.bytesOut).headD []
  let h' := h ++ [readCall.event r]
  let b := fill buf d
  if r.result = 0 then (h' ++ [exitEvent 0], true, b)
  else if r.result ≤ 16 then
    let out := b.take r.result.toNat
    (h' ++ [(writeCall out).event (ω.answer h' (writeCall out))], false, b)
  else (h' ++ [exitEvent 1], true, b)

def badSpec (ω : Oracle) : Nat → List Event × Bool × List UInt8
  | 0 => ([], false, List.replicate 16 0)
  | n + 1 => match badSpec ω n with
    | (h, false, buf) => badRound ω h buf
    | s => s

/-- The unreversed specification is false: at `ωabc` the program writes `cba`, not `abc`. -/
theorem badSpec_false : ¬ ∀ ω n, revProg.events ω n = (badSpec ω n).1 := by
  intro h
  have := h ωabc 1
  rw [revProg_events] at this
  exact absurd this (by decide)

/-- `hello world\n`, without the comma. -/
def noComma : List UInt8 := [104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 10]

/-- A `hello` that writes without the comma is refuted at every oracle. -/
theorem badHello_false (ω : Oracle) :
    hello.events ω 0 ≠ [(⟨"write", [1], [noComma], []⟩ : Call).event
      (ω.answer [] ⟨"write", [1], [noComma], []⟩), exitEvent 0] := by
  rw [hello_events]
  simp [Hello.spec, Hello.writeCall, Hello.msg, Call.event, noComma]

/-! ## The theorems on both targets -/

example (b : ByteArray) (hc : compile revProg x64Linux = .ok b) :=
  revProg_behaviour sound_compile.1 b hc
example (b : ByteArray) (hc : compile revProg arm64Linux = .ok b) :=
  revProg_rounds sound_compile.2 b hc
example (b : ByteArray) (hc : compile hello arm64Linux = .ok b) :=
  hello_behaviour sound_compile.2 b hc
example := hello_runs x64Linux (.inl rfl)
example := exit42_runs arm64Linux (.inr rfl)

/-! ## The default compiler's acceptance, by compiled evaluation (`CompileAccepts.Statement`) -/

#guard [exit42, hello, revProg].all fun p =>
  [x64Linux, arm64Linux].all fun t => (compile p t).toBool

end Millipede.Examples.WitnessTest
