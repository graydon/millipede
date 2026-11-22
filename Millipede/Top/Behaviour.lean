import Millipede.Top.Examples
import Millipede.Top.Trace
import Millipede.Top.SoundA64
import Millipede.Compile.LowerExt

/-!
# What `hello` and `revchunks` do, for every oracle

`compile_sound` says that the machine's trace is the source trace `p.events ω`. This file says
what that trace is, for every oracle `ω`, for two programs of `Examples.registry`, and composes the
two statements.

* `hello` writes `hello, world\n` to file descriptor 1 and exits with status 0
  (`Hello.spec`, `hello_events`).
* `revchunks` runs in rounds (`RevChunks.spec`, `revProg_events`). A round asks to read up to 16
  bytes from file descriptor 0 into its buffer. The oracle chooses the count `n` and the bytes.
  At `n = 0` the program exits with status 0, and at `n > 16`, an error, with status 1. Otherwise
  it writes the first `n` bytes of its buffer, reversed, to file descriptor 1, and the next round
  follows. When the read delivered `n` bytes, which is what a kernel does, the write is exactly
  those bytes reversed (`RevChunks.Rounds`, `revProg_rounds`). The contract of `revStep` is one
  round (`RevChunks.round`, in Millipede/Top/Examples.lean), proved there by the automatic
  attempt, and `revProg_events` follows from it without unfolding `revStep`.

The trace records what the program asked for. A `write` event holds the bytes the program passed,
and its result is the count the kernel reports. Neither program looks at that count, so after a
short write the bytes not written are lost and the trace says so only through the result. A read
whose reply offers fewer bytes than its count leaves the buffer's older bytes in place, and
`RevChunks.spec` states what is then written.

`hello_behaviour` and `revProg_behaviour` carry these statements to the machine through
`compile_sound` and `compile_sound_arm64`: for every `b` with `compile p t = .ok b`, the bytes load
and, for every oracle, the machine never gets stuck and its trace is the specified one.
-/

namespace Millipede.Examples

/-! ## `hello` -/

namespace Hello

/-- The trace of `hello` under `ω`: one `write` of `hello, world\n` to file descriptor 1, whose
result is the oracle's answer, then `exit(0)`. -/
def spec (ω : Oracle) : List Event := [writeCall.event (ω.answer [] writeCall), exitEvent 0]

end Hello

/-- For every oracle and every number of steps, the trace of `hello` is `Hello.spec ω`. The proof
cites the contract of `helloInit` and does not unfold it. -/
theorem hello_events (ω : Oracle) (n : Nat) : hello.events ω n = Hello.spec ω := by
  obtain ⟨evs, he, hevs, hx⟩ := helloInit.post ω []
  have h0 : (hello.run ω 0).2 = ((helloInit ω).run World.init).2 := by
    rw [Program.run, hello, helloInit.exp_denote]
  rw [Program.events_of_init_halts _ _ (by rw [h0]; exact hx) n, h0]
  exact he.trans hevs

/-! ## `revchunks` -/

namespace RevChunks

/-- The history of `revchunks` after `n` reactor steps, whether it has exited, and its buffer.
The buffer starts as 16 zero bytes, and after `exit` nothing changes. -/
def spec (ω : Oracle) : Nat → List Event × Bool × List UInt8
  | 0 => ([], false, List.replicate 16 0)
  | n + 1 => match spec ω n with
    | (h, false, buf) => round ω h buf
    | s => s

/-- A read that delivers as many bytes as its count says, up to 16, as a kernel's `read`
does. -/
def Honest (ω : Oracle) : Prop :=
  ∀ h, (ω.answer h readCall).result.toNat ≤ 16 →
    ((fitOut [16] (ω.answer h readCall).bytesOut).headD []).length =
      (ω.answer h readCall).result.toNat

/-- The event of a read of `n` that delivered the bytes `d`. -/
def readEvent (n : UInt64) (d : List UInt8) : Event := ⟨"read", [0], [], n, [d]⟩

/-- The rounds of `revchunks` as a property of a trace, for reads that deliver as many bytes as
their count says. `Rounds e t` says that `t` is a sequence of rounds, and `e` whether the last
one exited. A round is a read of `n` bytes `d`, `1 ≤ n ≤ 16`, followed by a write of `d` reversed
to file descriptor 1, whatever the write's result `res`. The last round may instead be a read of
0 bytes followed by `exit(0)`, or a read whose count is above 16 followed by `exit(1)`. -/
inductive Rounds : Bool → List Event → Prop
  | nil : Rounds false []
  | round (t : List Event) (d : List UInt8) (res : UInt64) (h0 : d ≠ []) (h : d.length ≤ 16) :
      Rounds false t →
      Rounds false (t ++ [readEvent (UInt64.ofNat d.length) d, ⟨"write", [1], [d.reverse], res, []⟩])
  | eof (t : List Event) : Rounds false t → Rounds true (t ++ [readEvent 0 [], exitEvent 0])
  | error (t : List Event) (n : UInt64) (d : List UInt8) (h : 16 < n.toNat) :
      Rounds false t → Rounds true (t ++ [readEvent n d, exitEvent 1])

end RevChunks

/-! ### The trace of `revchunks` -/

open RevChunks

/-- What the contracts of `chunkInit` and `revStep` say of a state after `n` steps: its world is
the history of `RevChunks.spec` and whether it exited, and before `exit` its buffer is the
buffer of `RevChunks.spec`. -/
theorem revProg_reach (ω : Oracle) (n : Nat) (s : revProg.State.carrier × World)
    (h : revProg.Reach (revProg.initRel ω) (revProg.stepRel ω) n s) :
    s.2 = ⟨(spec ω n).1, (spec ω n).2.1⟩ ∧
      ((spec ω n).2.1 = false → (s.1 : Chunk).bytes.toList = (spec ω n).2.2) := by
  induction h with
  | init r evs e hi => obtain ⟨rfl, rfl, rfl⟩ := hi; exact ⟨rfl, fun _ => rfl⟩
  | step n r r' h evs e _ hE ih =>
    change Chunk at r r'
    obtain ⟨hw, hb⟩ := ih
    simp only [World.mk.injEq] at hw hb
    obtain ⟨he, hx, hb'⟩ := hE
    have hs : spec ω n = (h, false, r.bytes.toList) := by
      rw [hw.1, hw.2, hb hw.2.symm]
    simp only [spec, hs]
    exact ⟨by rw [he, hx], fun hf => hb' (hx ▸ hf)⟩
  | halted n r r' w _ hw ih =>
    obtain ⟨rfl, -⟩ := ih
    simp only at hw
    simp only [spec]; split <;> simp_all

/-- For every oracle and every number of steps, the trace of `revchunks` is the history of
`RevChunks.spec`. The proof cites `revProg.events_reach`, which `mp program` derived
from the contracts of `chunkInit` and `revStep`, and does not unfold `revStep`. -/
theorem revProg_events (ω : Oracle) (n : Nat) : revProg.events ω n = (RevChunks.spec ω n).1 := by
  obtain ⟨r, hr⟩ := revProg.events_reach ω n
  exact congrArg World.events (revProg_reach ω n _ hr).1

/-- The read event of a round is `readEvent` of the count and the delivered bytes. -/
theorem readCall_event (r : Reply) :
    readCall.event r = readEvent r.result ((fitOut [16] r.bytesOut).headD []) := by
  rcases r with ⟨res, _ | ⟨b, bs⟩⟩ <;> rfl

/-- When every read delivers as many bytes as its count says, the history of `RevChunks.spec`
is a sequence of `Rounds`. -/
theorem spec_rounds (ω : Oracle) (hω : Honest ω) (n : Nat) :
    Rounds (spec ω n).2.1 (spec ω n).1 := by
  induction n with
  | zero => exact Rounds.nil
  | succ n ih =>
    simp only [spec]
    split
    · rename_i h buf hs
      rw [hs] at ih
      have hh := hω h
      simp only [round, readCall_event]
      generalize ω.answer h readCall = r at hh ⊢
      generalize (fitOut [16] r.bytesOut).headD [] = d at hh ⊢
      by_cases h0 : r.result = 0
      · have hd : d = [] := List.eq_nil_of_length_eq_zero (by simp_all)
        simp only [h0, ite_true, hd, List.append_assoc, List.cons_append, List.nil_append]
        exact Rounds.eof _ ih
      by_cases h16 : r.result ≤ 16
      · have hn : r.result.toNat ≤ 16 := by simpa using UInt64.le_iff_toNat_le.mp h16
        have hd := hh hn
        have hr : r.result = UInt64.ofNat d.length := by rw [hd]; simp
        have ht : (fill buf d).take r.result.toNat = d := by simp [fill, ← hd]
        simp only [h0, h16, ite_false, ite_true]
        simp only [ht, List.append_assoc, List.cons_append, List.nil_append, Call.event, writeCall,
          fitOut]
        rw [hr]
        refine Rounds.round _ d _ ?_ (by omega) ih
        intro hd0; apply h0; rw [hr, hd0]; rfl
      · have hn : 16 < r.result.toNat := by
          have := mt UInt64.le_iff_toNat_le.mpr h16; simp at this; omega
        simp only [h0, h16, ite_false, List.append_assoc, List.cons_append, List.nil_append]
        exact Rounds.error _ _ _ hn ih
    · exact ih

/-! ## The bytes -/

/-- The compilers that the soundness theorems cover: `compile` and `compileWith o` for every `o`,
on both targets. -/
def Sound (cc : Program → Target → Except String ByteArray) (t : Target) : Prop :=
  CompileSound.Statement cc t

theorem sound_compile : Sound compile x64Linux ∧ Sound compile arm64Linux :=
  ⟨compile_sound, compile_sound_arm64⟩

theorem sound_compileWith (o : Compile.Options) :
    Sound (compileWith o) x64Linux ∧ Sound (compileWith o) arm64Linux :=
  compileWith_sound o

/-- Whatever bytes a sound compiler produced for `hello`, they load, and for every oracle the
machine never gets stuck, every trace it shows is a prefix of `Hello.spec ω`, and it shows the
whole of it: `write(1, "hello, world\n")` and then `exit(0)`. -/
theorem hello_behaviour {cc : Program → Target → Except String ByteArray} {t : Target}
    (hcc : Sound cc t) (b : ByteArray) (hc : cc hello t = .ok b) :
    ∃ s₀, t.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle, let m := Machine.run t s₀ ω
        m.NeverStuck ∧ (∀ n, m.trace n <+: Hello.spec ω) ∧ ∃ n, m.trace n = Hello.spec ω := by
  obtain ⟨s₀, hl, h⟩ := hello.behaviour_of_events hcc hello.safe (fun ω _ => Hello.spec ω)
    hello_events hc
  exact ⟨s₀, hl, fun ω => ⟨(h ω).1, TraceEq.const (h ω).2⟩⟩

/-- Whatever bytes a sound compiler produced for `revchunks`, they load, and for every oracle the
machine never gets stuck and its trace is the limit of the histories of `RevChunks.spec ω`:
every trace it shows is a prefix of the history after some number of rounds, and the history
after every number of rounds is a prefix of a trace it shows. -/
theorem revProg_behaviour {cc : Program → Target → Except String ByteArray} {t : Target}
    (hcc : Sound cc t) (b : ByteArray) (hc : cc revProg t = .ok b) :
    ∃ s₀, t.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle, let m := Machine.run t s₀ ω
        m.NeverStuck ∧ TraceEq m.trace (fun n => (RevChunks.spec ω n).1) :=
  revProg.behaviour_of_events hcc revProg.safe _ revProg_events hc

/-- `revProg_behaviour` read through `Rounds`: when every read delivers as many bytes as its count
says, every trace the machine shows is a prefix of a sequence of rounds, each a read of `n`
bytes followed by a write of those bytes reversed, ending, if it ends, with `exit(0)` after a
read of 0 bytes or `exit(1)` after an error. -/
theorem revProg_rounds {cc : Program → Target → Except String ByteArray} {t : Target}
    (hcc : Sound cc t) (b : ByteArray) (hc : cc revProg t = .ok b) :
    ∃ s₀, t.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle, Honest ω → let m := Machine.run t s₀ ω
        m.NeverStuck ∧ ∀ n, ∃ e tr, Rounds e tr ∧ m.trace n <+: tr := by
  obtain ⟨s₀, hl, h⟩ := revProg_behaviour hcc b hc
  refine ⟨s₀, hl, fun ω hω => ⟨(h ω).1, fun n => ?_⟩⟩
  obtain ⟨k, hk⟩ := (h ω).2.1 n
  exact ⟨_, _, spec_rounds ω hω k, hk⟩

end Millipede.Examples
