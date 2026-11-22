import Millipede.Core.Effects
import Millipede.Top.SoundA64

/-!
# Capabilities on the machine

`p.NoCalls S` says that no source trace of `p` has an event whose symbol is in `S`. The machine
trace of a compiled program is the source trace, by `compile_sound`, so the machine never makes
such a call either. `Program.NoCalls.machine` states this for any compiler with the statement of
`compile_sound`, and `Program.NoCalls.x64` and `Program.NoCalls.arm64` for `compile` on both
targets.
-/

namespace Millipede

/-- A program that calls no symbol of `S` compiles, under a sound compiler, to a binary whose
machine run calls no symbol of `S`, at every time and under every oracle. -/
theorem Program.NoCalls.machine {compile : Program → Target → Except String ByteArray}
    {t : Target} (hc : CompileSound.Statement compile t) {p : Program} {S : List String}
    {b : ByteArray} (hb : compile p t = .ok b) (hs : p.Safe) (hn : p.NoCalls S) :
    ∃ s₀, t.fmt.load b.data.toList = some s₀ ∧
      ∀ (ω : Oracle) (n : Nat), ∀ ev ∈ (Machine.run t s₀ ω).trace n, ev.sym ∉ S := by
  obtain ⟨s₀, hl, h⟩ := hc p b hb hs
  refine ⟨s₀, hl, fun ω n ev hm => ?_⟩
  obtain ⟨m, hp⟩ := (h ω).2.1.1 n
  exact hn ω m ev (hp.subset hm)

/-- `Program.NoCalls.machine` for `compile` on x64 Linux. -/
theorem Program.NoCalls.x64 {p : Program} {S : List String} {b : ByteArray}
    (hb : compile p x64Linux = .ok b) (hs : p.Safe) (hn : p.NoCalls S) :
    ∃ s₀, x64Linux.fmt.load b.data.toList = some s₀ ∧
      ∀ (ω : Oracle) (n : Nat), ∀ ev ∈ (Machine.run x64Linux s₀ ω).trace n, ev.sym ∉ S :=
  Program.NoCalls.machine compile_sound hb hs hn

/-- `Program.NoCalls.machine` for `compile` on arm64 Linux. -/
theorem Program.NoCalls.arm64 {p : Program} {S : List String} {b : ByteArray}
    (hb : compile p arm64Linux = .ok b) (hs : p.Safe) (hn : p.NoCalls S) :
    ∃ s₀, arm64Linux.fmt.load b.data.toList = some s₀ ∧
      ∀ (ω : Oracle) (n : Nat), ∀ ev ∈ (Machine.run arm64Linux s₀ ω).trace n, ev.sym ∉ S :=
  Program.NoCalls.machine compile_sound_arm64 hb hs hn

end Millipede
