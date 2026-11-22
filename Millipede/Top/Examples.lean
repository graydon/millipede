import Millipede.Meta.MpDef
import Millipede.Top.Sound
import Millipede.Lib.Pool
import Millipede.Lib.Bump
import Millipede.Lib.Slice
import Millipede.Top.Requests
import Millipede.Top.Tally
import Millipede.Meta.Emit

/-!
# Example programs

This file defines the small reactors that the `mpc` driver compiles with
`lake exe mpc <instance> -o <file>`. They are the following:

* `exit42` calls `exit(42)`.
* `hello` writes `hello, world` and exits with status 0.
* `sum` sums `0 + 1 + … + 9` in a loop and exits with the sum, 45, as its status.
* `ticks` counts its steps and writes `tick` at each one, and its fourth step exits with status 3.
* `readcount` reads its input byte by byte and exits with the count as its status.
* `revchunks` keeps a byte buffer as its root. Each step reads up to 16 bytes into the buffer,
  reverses them in place through a slice passed to the library loop `Slice.reverse`, and writes
  them out, and the program exits with status 0 at the end of its input.
* `pooltally`, defined in `Millipede/Top/Tally.lean`, keeps a pool, a stack of up to 8 linear keys
  and a total in its root. For each input byte it allocates a node with the unchecked `alloc!`,
  first freeing the newest key when 8 are held. At the end of its input it frees one key per step,
  adding the freed node's value to the total, and then exits with the sum of its input bytes
  modulo 256 as its status.
* `reqspool` and `reqsbump`, defined in `Millipede/Top/Requests.lean`, are one client of the
  allocator interface, proved once and instantiated with the bitmap pool and the bump arena.

`Examples.registry` lists the driver's entries, each with a name, a description, the program and
the proof of its safety, so a program without a proof of safety cannot be registered.
-/

namespace Millipede.Examples

mp extern "write" sysWrite (fd : UInt64) (buf : Bytes) : UInt64
mp extern noreturn "exit" sysExit (code : UInt64) : UInt64

/-- The unit state is kept as it is. -/
mp def keepUnit (s : Unit) : Unit := s

mp def exit42Init : Unit :=
  let _x := sysExit 42
  ()

/-- `exit(42)`. -/
def exit42 : Program := ⟨Ty.unit, exit42Init.exp, keepUnit.exp⟩

namespace Hello

/-- The bytes of `hello, world\n`. -/
def msg : List UInt8 := [104, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 10]

/-- The call `write(1, "hello, world\n")`. -/
def writeCall : Call := ⟨"write", [1], [msg], []⟩

end Hello

/-- The event of `exit(code)`. -/
def exitEvent (code : UInt64) : Event := ⟨"exit", [code], [], 0, []⟩

/-- Writes the greeting and exits. Its contract is the two events, the write's result being the
oracle's answer; the automatic attempt proves it. -/
mp def helloInit
    ensures events = [Hello.writeCall.event (ω.answer history Hello.writeCall), exitEvent 0] ∧
      exited : Unit :=
  let _w := sysWrite 1 "hello, world\n"
  let _x := sysExit 0
  ()

/-- `write(1, "hello, world\n"); exit(0)`. -/
def hello : Program := ⟨Ty.unit, helloInit.exp, keepUnit.exp⟩

mp def sumInit : Unit := do
  let mut s : UInt64 := 0
  for i in 0...10 do
    s := s +! i
  let _x := sysExit s
  ()

/-- A loop computes `0 + 1 + … + 9 = 45`, which becomes the exit status. -/
def sum : Program := ⟨Ty.unit, sumInit.exp, keepUnit.exp⟩

mp def ticksInit : UInt64 := 0

mp def ticksStep (s : UInt64) : UInt64 :=
  let _w := sysWrite 1 "tick\n"
  if s == 3 then
    let _x := sysExit 3
    s
  -- `+` wraps, which is harmless because the step after state 3 exits, so `s` stays below 4
  -- in every run, although the reactor states no invariant
  else s + 1

/-- A reactor in which each step writes `tick\n` and the fourth step, in state 3, exits with
status 3. -/
def ticks : Program := ⟨Ty.u64, ticksInit.exp, ticksStep.exp⟩

/-! ## `readcount`: input through `read` -/

/-- `read(fd, buf, 1)`, which returns the byte read, or `2^64 - 1` at the end of input or on an
error. -/
mp extern "read" sysRead (fd : UInt64) (buf : OutByte) : UInt64

mp def countStep (n : UInt64) : UInt64 :=
  let c := sysRead 0
  -- a count of input bytes, which wraps only after 2^64 bytes, a length no run reaches; `+` is
  -- used because the reactor states no bound on its input
  if c < 256 then n + 1
  else
    let _x := sysExit n
    n

/-- A reactor that counts its input bytes and exits with the count at the end of its input. -/
def readcount : Program := ⟨Ty.u64, ticksInit.exp, countStep.exp⟩

/-! ## `revchunks`: input into a byte buffer, transformed through a slice, written out

The root `Chunk` is a 16-byte buffer and the number of bytes it holds. Each step reads up to 16
bytes of input straight into the buffer, where the extern writes the bytes that the oracle
chooses and the step receives the count. The step then passes the bytes read as a mutable slice to
the library loop `Slice.reverse`, which swaps the cells in place, and writes them out. At the end of
input, when `read` returns 0, the program exits with status 0, and on an error, a count above 16,
with status 1. No byte is copied between the buffer, the helper and the externs, since every
slice is passed as a pointer and a length. `mp def` discharges its obligations. What its trace
is, for every oracle, is `revProg_events` in `Millipede/Top/Behaviour.lean`, and `revProg_behaviour`
there carries it to any bytes that `compile` produces. -/

/-- `read(fd, buf, cap)` into a mutable byte slice, which returns the count read or `-errno`. -/
mp extern "read" sysReadInto (fd : UInt64) (buf : &mut [U8]) : UInt64

/-- `write(fd, buf, len)` from a byte slice or a string literal. -/
mp extern "write" sysWriteS (fd : UInt64) (buf : &[U8]) : UInt64

/-- The root of `revchunks`, a byte buffer and the number of bytes it holds. -/
structure Chunk where
  bytes : Arr UInt8 16
  len : UInt64
deriving Data

mp def chunkInit : Chunk := { bytes := Vector.replicate 16 0, len := 0 }

namespace RevChunks

/-- The call `read(0, buf, 16)`. -/
def readCall : Call := ⟨"read", [0], [], [16]⟩

/-- The call `write(1, bs)`. -/
def writeCall (bs : List UInt8) : Call := ⟨"write", [1], [bs], []⟩

/-- The buffer after a read that delivered the bytes `d`, which overwrite its first cells. -/
def fill (buf d : List UInt8) : List UInt8 := d ++ buf.drop d.length

/-- One round from the history `h` and the buffer `buf`. It returns the history after the round,
whether the program has exited, and the buffer. The reply `r` to the read is the oracle's, and
`d` is the bytes it delivered, at most 16. -/
def round (ω : Oracle) (h : List Event) (buf : List UInt8) : List Event × Bool × List UInt8 :=
  let r := ω.answer h readCall
  let d := (fitOut [16] r.bytesOut).headD []
  let h' := h ++ [readCall.event r]
  let b := fill buf d
  if r.result = 0 then (h' ++ [exitEvent 0], true, b)
  else if r.result ≤ 16 then
    let out := (b.take r.result.toNat).reverse
    (h' ++ [(writeCall out).event (ω.answer h' (writeCall out))], false,
      out ++ b.drop r.result.toNat)
  else (h' ++ [exitEvent 1], true, b)

/-! The three lemmas below are what the automatic proof of `revStep`'s contract needs about the
buffer, stated in the form that `simp` sees after `vcgen`. -/

/-- A read into the whole buffer: the bytes delivered overwrite its first cells. -/
@[simp] theorem vwrite_fill (v : Vector UInt8 16) (bs : List (List UInt8)) :
    (vwrite v 0 ((fitOut [16] bs).head?.getD [])).toList =
      fill v.toList ((fitOut [16] bs).head?.getD []) := by
  have := fitOut_one_le 16 bs
  rw [List.headD_eq_head?_getD] at this
  rw [Flat.vwrite_toList _ _ _ (by omega)]; simp [Flat.splice, fill]

/-- A view reversed in its first `n` cells, written back, reverses the first `n` elements. -/
theorem vunview_reverse {N : Nat} (v : Vector UInt8 N) (n : Nat) (hn : n ≤ N) (s : Slots UInt8 N)
    (hs : ∀ k, k < N → s.cell k =
      if k < n then (vview v 0 n).cell (n - 1 - k) else (vview v 0 n).cell k) :
    (vunview v 0 n s).toList = (v.toList.take n).reverse ++ v.toList.drop n := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [Vector.length_toList] at h1
    have hk := hs j h1
    simp only [vview_cell] at hk
    simp only [vunview, Vector.toList_ofFn, List.getElem_ofFn, Nat.zero_le, true_and,
      Nat.sub_zero, List.getElem_append, List.length_reverse, List.length_take,
      Vector.length_toList, List.getElem_reverse, List.getElem_take, List.getElem_drop]
    by_cases hj : j < n
    · simp only [hj, ite_true, show n - 1 - j < n ∧ n - 1 - j < N by omega, and_self,
        Nat.zero_add] at hk
      simp only [hj, ite_true, show j < min n N by omega, dite_true, hk,
        List.getElem?_eq_getElem (show n - 1 - j < v.toList.length by simp; omega),
        Option.getD_some, Vector.getElem_toList]
      congr 1; omega
    · simp [hj, show ¬ j < min n N by omega]
      congr 1; omega

/-- `Slice.reverse` on the view of the first `n` bytes reverses them in place. -/
@[simp] theorem reverse_view (B : Vector UInt8 16) (n : UInt64) (hn : n ≤ 16) (hp : 16 < 2 ^ 64) :
    (vunview B 0 n.toNat (Lib.Slice.reverse UInt8 16 hp (vview B 0 n.toNat) n).run.2.1).toList =
      (B.toList.take n.toNat).reverse ++ B.toList.drop n.toNat := by
  have hn' : n.toNat ≤ 16 := by simpa using UInt64.le_iff_toNat_le.mp hn
  have := Spec.run_of_triple (Lib.Slice.reverse.spec UInt8 16 hp (vview B 0 n.toNat) n)
    ⟨hn', fun k hk => by simp; omega⟩
  exact vunview_reverse B n.toNat hn' _ this

/-- The first `n` bytes after the reversal are the first `n` before it, reversed. -/
@[simp] theorem vrange_reverse_view (B : Vector UInt8 16) (n : UInt64) (hn : n ≤ 16)
    (hp : 16 < 2 ^ 64) :
    vrange (vunview B 0 n.toNat (Lib.Slice.reverse UInt8 16 hp (vview B 0 n.toNat) n).run.2.1) 0
      n.toNat = (B.toList.take n.toNat).reverse := by
  have h : n.toNat ≤ 16 := by simpa using UInt64.le_iff_toNat_le.mp hn
  rw [vrange, List.drop_zero, reverse_view B n hn hp, List.take_left']
  simp; omega

end RevChunks

set_option maxRecDepth 8192 in
open Millipede.Lib in
/-- One step, which reads up to 16 bytes into the buffer, reverses them in place through a slice
passed to `Slice.reverse`, and writes them. Its contract is one round of `RevChunks.round` from
the history before the step: the events it appends, whether it exits, and the buffer after. The
automatic attempt proves it, with the lemmas above. -/
mp def revStep (r : &mut Chunk)
    ensures history ++ events = (RevChunks.round ω history r.bytes.toList).1 ∧
      exited = (RevChunks.round ω history r.bytes.toList).2.1 ∧
      (exited = false → r'.bytes.toList = (RevChunks.round ω history r.bytes.toList).2.2)
    : Unit := do
  let n := sysReadInto 0 (&mut r.bytes[0:16])
  if n == 0 then
    let _x := sysExit 0
    ()
  else if n <= 16 then
    r.len := n
    let _ := Slice.reverse (&mut r.bytes[0..n])
    let _w := sysWriteS 1 (&r.bytes[0..n])
    ()
  else
    let _x := sysExit 1
    ()

set_option maxRecDepth 8192 in
mp program revProg (root : Chunk) init chunkInit step revStep

/-- `compile_sound` for `revchunks`: for any bytes `b` that `compile` produces, the bytes load and
the machine matches the source. Its obligations hold for every oracle and were discharged when
`mp def` elaborated `Slice.reverse` and `revStep`. That `compile` accepts `revchunks` is checked by
compiled evaluation (`CompileAccepts.Statement`), not by the kernel. -/
theorem revProg_sound (b : ByteArray) (hc : compile revProg x64Linux = .ok b) :
    ∃ s₀, x64Linux.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle,
        let m := Machine.run x64Linux s₀ ω
        m.NeverStuck ∧ TraceEq m.trace (revProg.events ω) ∧
        m.StackWithin (revProg.stackBytes x64Linux.φ) ∧
        m.StepsWithin (revProg.events ω) (fun k => revProg.stepCost k ω x64Linux.κ) :=
  compile_sound revProg b hc revProg.safe

/-! ## Safety of the programs built without `mp program` -/

theorem exit42.safe : exit42.Safe := Program.safe_of_total _ (by decide) (by decide)
theorem hello.safe : hello.Safe := Program.safe_of_total _ (by decide) (by decide)
theorem sum.safe : sum.Safe :=
  Program.safe_of_parts _ (fun ω => sumInit.safe ω _) (fun ω _ _ => Exp.safe_of_total ω _ (by decide) _ _)
theorem ticks.safe : ticks.Safe := Program.safe_of_total _ (by decide) (by decide)
theorem readcount.safe : readcount.Safe := Program.safe_of_total _ (by decide) (by decide)

/-- The instances that `mpc` knows, each with a name, a description, the program and its safety
proof. -/
def registry : List Entry :=
  [mp_entry% "exit42" "exit(42)" exit42,
   mp_entry% "hello" "write(1, \"hello, world\\n\"); exit(0)" hello,
   mp_entry% "sum" "exit status = 0 + 1 + ... + 9 = 45, computed by a loop" sum,
   mp_entry% "ticks" "reactor: writes tick\\n four times, then exit(3)" ticks,
   mp_entry% "readcount" "reactor: counts the bytes of its input (read), exit status = the count" readcount,
   mp_entry% "pooltally" "reactor with a pool: reads bytes, allocs a node per byte (unchecked alloc!) holding up to 8 keys live, frees them; exit status = sum of the bytes mod 256" PoolTally.prog,
   mp_entry% "revchunks" "reactor with a byte buffer: reads up to 16 bytes into it (read into a slice), reverses them in place through a slice passed to a helper loop, writes them (write of a slice); exit 0 at end of input" revProg,
   mp_entry% "reqspool" "reactor, a client of the allocator interface over the bitmap pool (Reqs Pool8.impl): per input byte c serves (c, c+1, c+2) in a fresh arena; exit status = sum of (3c + 3) mod 256" ReqsPool.prog,
   mp_entry% "reqsbump" "the same client over the bump arena (Reqs Bump8.impl): same behaviour" ReqsBump.prog]

end Millipede.Examples
