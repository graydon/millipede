import Millipede.Lib.ByteBuf
import Millipede.Lib.Cap
import Millipede.Top.Sound
import Millipede.Top.NoCalls
import Tests.RevChunks

/-!
# A log with capability tokens and typestate

This file is the worked example of capability tokens and of typestate on a handle. The class
`Fs` governs the extern symbol `write`, so only a function that holds an `Fs` token may write,
and the program receives its one `Fs` token at `init` and keeps it in its root. The class
`Clock` governs `clock_gettime`, which the program is never granted, so `logProg.noCalls` says
that no trace of the program calls it.

A log handle `Log s` holds a file descriptor and a buffer of 16 bytes, and its state `s` says
whether the buffer holds bytes not yet written. `Log.open` needs an `Fs` token and returns a
clean log. `Log.write` turns a clean log dirty by appending bytes to its buffer, `Log.more`
appends to a dirty log in place, `Log.sync` writes the buffer and returns the log clean, and
`Log.close` takes only a clean log. The handle is sealed and linear, so outside this file it can
be made only by `Log.open` and ended only by `Log.close`. Tests/Tokens.lean checks that the
checker rejects the misuses.

Each step of `logProg` reads up to 16 bytes from standard input and passes them through a log
on standard output, which it opens, writes, syncs and closes within the step. It exits with 0 at
the end of input and with 1 on an error. The program is compiled for both targets.
-/

namespace Millipede.Tests.Log

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true

/-- The authority to write to files. -/
mp capability Fs for "write"

/-- The authority to read the clock, which `logProg` is not granted. -/
mp capability Clock for "clock_gettime"

/-- `write(fd, buf, len)`, which needs an `Fs` token. -/
mp extern "write" fsWrite (fs : &Fs) (fd : UInt64) (buf : &[U8]) : UInt64

mp extern noreturn "exit" logExit (code : UInt64) : UInt64

/-- The state of a log: every byte written to its buffer has been written out, or not. -/
inductive LogSt where
  | clean
  | dirty

/-- The state of a log as a zero-size linear value, sealed in this file. -/
structure LogTok (s : LogSt) where
  private mk ::
  tok : LinTok
deriving Data

/-- Mint a state. The layout does not depend on the state, so the law is the one for `clean`. -/
private def LogTok.mint (s : LogSt) : Ctor [] ⟨LogTok s⟩ :=
  ⟨"LogTok.mint", .struct, fun _ => ⟨⟨⟩⟩, some ⟨Flat.CtorLaw.struct _ rfl _ (by
      have h1 : Data.shape (LogTok s) = Data.shape (LogTok .clean) := rfl
      have h2 : Flat.planOf [] ⟨LogTok s⟩ .struct = Flat.planOf [] ⟨LogTok .clean⟩ .struct := rfl
      rw [h1, h2]; decide) (by
    intro _ _ _; exact ⟨⟨by show (slice _ _ 0).length = 0; simp [slice], trivial⟩, trivial⟩)⟩,
    none⟩

/-- A log on the file descriptor `fd` in state `s`, with the bytes not yet written in `buf`. -/
structure Log (s : LogSt) where
  private mk ::
  fd : UInt64
  buf : ByteBuf 16
  st : LogTok s
deriving Data

instance {s : LogSt} : Inhabited (Log s) := ⟨⟨0, ⟨Vector.replicate 16 0, 0⟩, ⟨⟨⟩⟩⟩⟩

/-- End a log. -/
private def Log.burn (s : LogSt) : Ctor [⟨Log s⟩] Ty.unit :=
  ⟨"Log.burn", .struct, fun _ => (), some ⟨Flat.CtorLaw.unit _ _ _⟩, none⟩

/-- Open a log on `fd`, which needs the authority to write files. -/
mp def Log.open (fs : &Fs) (fd : UInt64) ensures ByteBuf.Inv 16 result.buf : Log .clean :=
  { fd := fd, buf := ByteBuf.new, st := LogTok.mint .clean }

/-- Append the bytes that `src` holds to a clean log's buffer, which makes it dirty. -/
mp def Log.write (h : Log .clean) (src : &ByteBuf 16)
    requires ByteBuf.Inv 16 h.buf ∧ ByteBuf.Inv 16 src
    ensures ByteBuf.Inv 16 result.buf : Log .dirty := do
  let fd := h.fd
  let mut b := h.buf
  let _ := Log.burn .clean h
  let n := src.len
  let _ := ByteBuf.append (&mut b) (&src.bytes[0..n])
  { fd := fd, buf := b, st := LogTok.mint .dirty }

mp prove Log.write.safe := by mp_auto [ByteBuf.Inv]

mp prove Log.write.spec := by mp_auto [ByteBuf.Inv, vview_isFull]

/-- Write the buffer of a dirty log and empty it, which makes it clean. -/
mp def Log.sync (fs : &Fs) (h : Log .dirty) requires ByteBuf.Inv 16 h.buf
    ensures result.buf.len = 0 : Log .clean := do
  let fd := h.fd
  let mut b := h.buf
  let _ := Log.burn .dirty h
  let n := b.len
  let _ := fsWrite (&fs) fd (&b.bytes[0..n])
  b.len := 0
  { fd := fd, buf := b, st := LogTok.mint .clean }

/-- The slice of the bytes held fits the buffer, by its invariant. -/
mp prove Log.sync.safe := by mp_auto [ByteBuf.Inv]

/-- Close a clean log. -/
mp def Log.close (h : Log .clean) : Unit := do
  let _ := Log.burn .clean h
  ()

/-- The root: the program's `Fs` token and the input buffer. -/
structure LogRoot where
  fs : Fs
  inb : ByteBuf 16
deriving Data

/-- `init` receives the program's `Fs` token and keeps it in the root. -/
mp def logInit (fs : Fs) : LogRoot := { fs := fs, inb := ByteBuf.new }

/-- One step: read up to 16 bytes and pass them through a log on standard output. -/
mp def logStep (r : &mut LogRoot) : Unit := do
  r.inb.len := 0
  let n := ByteBuf.readFrom (&mut r.inb) 0
  if n == 0 then
    let _x := logExit 0
    ()
  else if n <= 16 then
    let h0 := Log.open (&r.fs) 1
    let h1 := Log.write h0 (&r.inb)
    let h2 := Log.sync (&r.fs) h1
    Log.close h2
  else
    let _x := logExit 1
    ()

/-- The step's obligations are those of `readFrom`, which hold after the reset, and those of
`Log.write`, which hold since `Log.open` returns a buffer with its invariant. -/
mp prove logStep.safe := by mp_auto [ByteBuf.Inv]

mp program logProg (root : LogRoot) init logInit step logStep

example : logProg.Safe := logProg.safe

/-- No trace of the program calls the clock, whose token it is not granted. -/
example : logProg.NoCalls Clock.syms := logProg.noCalls

/-- The executable that `compile` makes of the program never calls the clock either. -/
example (b : ByteArray) (h : compile logProg x64Linux = .ok b) :
    ∃ s₀, x64Linux.fmt.load b.data.toList = some s₀ ∧
      ∀ (ω : Oracle) (n : Nat), ∀ ev ∈ (Machine.run x64Linux s₀ ω).trace n,
        ev.sym ∉ Clock.syms :=
  Program.NoCalls.x64 h logProg.safe logProg.noCalls

/-- `Log.close` holds no token, so no run of it calls `write` or the clock. -/
example : Log.close.exp.NoCalls (Fs.syms ++ Clock.syms) := Log.close.noCalls

/-- `Log.sync` holds an `Fs` token, so only the clock is excluded. -/
example : Log.sync.exp.NoCalls Clock.syms := Log.sync.noCalls

/-! ## Runs and compilation -/

open Millipede.Tests.RevChunks (chunks written exited)

-- each chunk read is written through the log, and the end of input exits with 0
#guard written (logProg.events (chunks [[1, 2, 3], [4], (List.range 16).map (·.toUInt8)]) 5) =
  [[1, 2, 3], [4], (List.range 16).map (·.toUInt8)]
#guard exited 0 (logProg.events (chunks [[1, 2, 3], [4]]) 5)
-- a count above the free space is an error: nothing is written and the program exits with 1
#guard exited 1 (logProg.events (chunks [(List.range 17).map (·.toUInt8)]) 3)
#guard written (logProg.events (chunks [(List.range 17).map (·.toUInt8)]) 3) = []

#guard (compile logProg x64Linux).toBool
#guard (compile logProg arm64Linux).toBool

#guard_msgs (drop info) in
#mp_compile logProg ".lake/test-log"

#guard_msgs (drop info) in
#mp_compile logProg ".lake/test-log-a64" "arm64-linux"

end Millipede.Tests.Log
