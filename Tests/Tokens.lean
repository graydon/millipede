import Tests.Log

/-!
# Tests of capability tokens and typestate

The tests use the classes `Fs` and `Clock` and the log handle of Tests/Log.lean, which is another
module, so the token type and the handle are sealed here.

A token cannot be forged, by `Cap.mint`, a struct literal, an anonymous constructor, a `match`
that rebuilds it or `default`, and a log cannot be forged or have its fields written either. A
token is linear, so using it twice or not at all, copying it out of a place or a shared
reference, dropping it on one arm only and using it in a loop are rejected, while `Cap.drop`
gives it up and a `Slots` cell may hold it. An extern that requires a token rejects a call
without one, a call with a token of another class and a call with a token already moved, and a
function that reaches a governed symbol through a tokenless extern, a generic callee or a
function written for an interface is rejected unless it holds a token of the class, directly or
inside its root. Use after close, double close, a leaked log and a transition from the wrong
state are rejected, including from a function generic over the state. The declarations of
classes and externs refuse a symbol claimed twice and a token of a class that does not govern
the extern's symbol. A program whose `init` takes no token gets `p.noCalls` for every class, and
`mp program` refuses an `init` with other parameters.
-/

namespace Millipede.Tests.Tokens

open Millipede Millipede.Lib Millipede.Tests.Log Std.WP

/-! ## Forging -/

/-- error: `Millipede.Lib.Cap` is sealed (its constructor is private to its module): it cannot be built here -/
#guard_msgs in
mp def forge1 : Fs := Cap.mint "Millipede.Tests.Log.Fs"

/-- error: `Millipede.Lib.Cap` is sealed (its constructor is private to its module): it cannot be built here -/
#guard_msgs in
mp def forge2 : Fs := { tok := ⟨⟩ }

/-- error: `Millipede.Lib.Cap` is sealed (its constructor is private to its module): it cannot be built here -/
#guard_msgs in
mp def forge3 : Fs := ⟨⟨⟩⟩

/-- error: `Millipede.Tests.Log.Log` is sealed (its constructor is private to its module): it cannot be built here -/
#guard_msgs in
mp def forgeLog (fd : UInt64) : Log .clean := { fd := fd, buf := ByteBuf.new, st := ⟨⟨⟩⟩ }

/-- error: unknown function `LogTok.mint` (not an earlier `mp def` or `mp extern`) -/
#guard_msgs in
mp def forgeState : LogTok .clean := LogTok.mint .clean

/-- error: unknown variable `default` -/
#guard_msgs in
mp def forgeDefault : Fs := default

/-- error: `Millipede.Lib.Cap` is not an enum -/
#guard_msgs in
mp def rebuild (t : Fs) : Fs := match t with
  | ⟨k⟩ => ⟨k⟩

/-- error: `Millipede.Lib.Cap` is sealed (its constructor is private to its module): it cannot be built here -/
#guard_msgs in
mp def forgeByType : Cap "Millipede.Tests.Log.Fs" := Cap.mint "Millipede.Tests.Log.Fs"

/-- error: unknown variable `default` -/
#guard_msgs in
mp def forgeLogDefault : Log .clean := default

/-- error: `Millipede.Tests.Log.Log` is not an enum -/
#guard_msgs in
mp def openLog (h : Log .dirty) : Unit := match h with
  | ⟨_, _, _⟩ => ()

/-- error: `Millipede.Tests.Log.Log` is sealed (its constructor is private to its module): it cannot have its fields written here -/
#guard_msgs in
mp def retarget (fs : &Fs) : Unit := do
  let mut h := Log.open (&fs) 1
  h.fd := 7
  Log.close h

/-! ## Linearity of tokens -/

/-- error: linear parameter `fs` of type Millipede.Lib.Cap _ is used 2 times; it must be used exactly once -/
#guard_msgs in
mp def dup (fs : Fs) : Unit := do
  let _ := Cap.drop "Millipede.Tests.Log.Fs" fs
  let _ := Cap.drop "Millipede.Tests.Log.Fs" fs
  ()

/-- error: unused linear parameter `fs` of type Millipede.Lib.Cap _: a linear value must be used exactly once (consume it with `match`) -/
#guard_msgs in
mp def lose (fs : Fs) : Unit := ()

/-- error: cannot copy the linear value of type Millipede.Lib.Cap _ out of a place (it would be used twice); move a whole variable, or `take!` it out of a `Slots` -/
#guard_msgs in
mp def copyOut (r : &LogRoot) : Fs := r.fs

/-- error: cannot move the linear value out of the shared reference `t` -/
#guard_msgs in
mp def outOfBorrow (t : &Fs) : Fs := t

/-- error: cannot copy the linear value of type Millipede.Lib.Cap _ out of a place (it would be used twice); move a whole variable, or `take!` it out of a `Slots` -/
#guard_msgs in
mp def fromArr (a : &Arr Fs 2) : Fs := a[0]!

/-- error: linear variable `t` is used 1 time(s) in the then-branch but 0 time(s) in the else-branch; a linear value must be used the same number of times on every path -/
#guard_msgs in
mp def dropOneArm (t : Fs) (b : Bool) : Unit :=
  if b then
    let _ := Cap.drop "Millipede.Tests.Log.Fs" t
    ()
  else ()

/-- error: linear variable `t` is bound outside this loop and used inside it; a loop may run any number of times -/
#guard_msgs in
mp def inLoop (t : Fs) : Unit := do
  for i in 0...2 do
    let _ := Cap.drop "Millipede.Tests.Log.Fs" t
  ()

/-- error: type mismatch: expected Millipede.Lib.Cap _, but this has type Millipede.Lib.Cap _ -/
#guard_msgs in
mp def dropOther (t : Clock) : Unit := do
  let _ := Cap.drop "Millipede.Tests.Log.Fs" t
  ()

/-- error: use of `t` after it was moved (a linear value is used once) -/
#guard_msgs in
mp def writeAfterDrop (t : Fs) : UInt64 := do
  let _ := Cap.drop "Millipede.Tests.Log.Fs" t
  fsWrite (&t) 1 "x"

/-- A token may be stored in a `Slots` cell, under the obligation that the cell is empty. -/
mp def intoSlots (s : &mut Slots Fs 2) (t : Fs) requires s.isVacant 0 : Unit := do
  let _ := s.put! 0 t
  ()

/-- A token may be given up. -/
mp def giveUp (fs : Fs) : Unit := do
  let _ := Cap.drop "Millipede.Tests.Log.Fs" fs
  ()

/-! ## Calls that need a token -/

/-- error: extern `fsWrite` expects 3 argument(s), got 2 -/
#guard_msgs in
mp def noTok (fd : UInt64) : UInt64 := fsWrite fd "x"

/-- error: the parameter `fs` of `fsWrite` is a token: pass `&t` for a token `t` of the capability `Millipede.Tests.Log.Fs` -/
#guard_msgs in
mp def wrongTok (c : &Clock) (fd : UInt64) : UInt64 := fsWrite (&c) fd "x"

/-- error: `Log.sync` expects 2 argument(s), got 1 -/
#guard_msgs in
mp def syncNoTok (h : Log .dirty) requires ByteBuf.Inv 16 h.buf : Log .clean := Log.sync h

/-- error: `ambient` calls the extern symbol "write", which needs the capability `Millipede.Tests.Log.Fs`, but holds no `Millipede.Tests.Log.Fs` token: take one as a parameter, such as `(c : &Millipede.Tests.Log.Fs)` -/
#guard_msgs in
mp def ambient (b : &ByteBuf 16) requires ByteBuf.Inv 16 b : UInt64 := ByteBuf.writeTo (&b) 1

/-- The same call, holding the token. -/
mp def ambientOk (fs : &Fs) (b : &ByteBuf 16) requires ByteBuf.Inv 16 b : UInt64 :=
  ByteBuf.writeTo (&b) 1

/-- The token held in the root. -/
mp def viaRoot (r : &LogRoot) requires ByteBuf.Inv 16 r.inb : UInt64 :=
  ByteBuf.writeTo (&r.inb) 1

/-- `viaRoot` holds an `Fs` token, so only the clock is excluded. -/
example : viaRoot.exp.NoCalls Clock.syms := viaRoot.noCalls

/-- A function without tokens calls neither class. -/
mp def pure1 (x : UInt64) : UInt64 := x + 1

example : pure1.exp.NoCalls (Fs.syms ++ Clock.syms) := pure1.noCalls

/-! ## The clock, which needs its own token -/

/-- `clock_gettime(id, …)`, which needs a `Clock` token. -/
mp extern "clock_gettime" clockGet (c : &Clock) (id : UInt64) : UInt64

/-- error: the parameter `c` of `clockGet` is a token: pass `&t` for a token `t` of the capability `Millipede.Tests.Log.Clock` -/
#guard_msgs in
mp def peek (r : &LogRoot) : UInt64 := clockGet (&r.fs) 0

/-- A tokenless declaration of the same symbol. -/
mp extern "clock_gettime" clockAmbient (id : UInt64) : UInt64

/-- error: `peekViaTokenless` calls the extern symbol "clock_gettime", which needs the capability `Millipede.Tests.Log.Clock`, but holds no `Millipede.Tests.Log.Clock` token: take one as a parameter, such as `(c : &Millipede.Tests.Log.Clock)` -/
#guard_msgs in
mp def peekViaTokenless (r : &LogRoot) : UInt64 := clockAmbient 0

/-! ## Generic functions, interfaces and states -/

section
variable (T : Type) [Data T]
/-- A generic function is not checked, so it may call the clock for any `T`. -/
mp def genClock (x : &T) : UInt64 := clockAmbient 0
end

/-- error: `useGen` calls the extern symbol "clock_gettime", which needs the capability `Millipede.Tests.Log.Clock`, but holds no `Millipede.Tests.Log.Clock` token: take one as a parameter, such as `(c : &Millipede.Tests.Log.Clock)` -/
#guard_msgs in
mp def useGen (x : UInt64) : UInt64 := genClock (&x)

mp interface Tick where
  S : Type
  op tick (r : &S) : UInt64

/-- error: `clkTick` calls the extern symbol "clock_gettime", which needs the capability `Millipede.Tests.Log.Clock`, but holds no `Millipede.Tests.Log.Clock` token: take one as a parameter, such as `(c : &Millipede.Tests.Log.Clock)` -/
#guard_msgs in
mp def clkTick (r : &UInt64) : UInt64 := clockAmbient 0

section
variable (s : LogSt)
/-- error: type mismatch: expected Millipede.Tests.Log.Log clean, but this has type Millipede.Tests.Log.Log _ -/
#guard_msgs in
mp def anyToClean (h : Log s) : Log .clean := h
end

/-! ## Declarations -/

/-- error: the extern symbol "clock_gettime" does not belong to the capability `Millipede.Tests.Log.Fs`, whose symbols are [write] -/
#guard_msgs in
mp extern "clock_gettime" clockBad (c : &Fs) (id : UInt64) : UInt64

/-- error: the symbol "clock_gettime" already belongs to the capability `Millipede.Tests.Log.Clock` -/
#guard_msgs in
mp capability Clock2 for "clock_gettime"

/-! ## Typestate of the log -/

/-- error: linear let `h` of type Millipede.Tests.Log.Log clean is used 2 times; it must be used exactly once -/
#guard_msgs in
mp def doubleClose (fs : &Fs) : Unit := do
  let h := Log.open (&fs) 1
  let _ := Log.close h
  let _ := Log.close h
  ()

/-- error: linear let `h` of type Millipede.Tests.Log.Log clean is used 2 times; it must be used exactly once -/
#guard_msgs in
mp def useAfterClose (fs : &Fs) (src : &ByteBuf 16) requires ByteBuf.Inv 16 src : Unit := do
  let h := Log.open (&fs) 1
  let _ := Log.close h
  let h1 := Log.write h (&src)
  let h2 := Log.sync (&fs) h1
  Log.close h2

/-- error: unused linear let `h` of type Millipede.Tests.Log.Log clean: a linear value must be used exactly once (consume it with `match`) -/
#guard_msgs in
mp def leak (fs : &Fs) : Unit := do
  let h := Log.open (&fs) 1
  ()

/-- error: type mismatch: expected Millipede.Tests.Log.Log clean, but this has type Millipede.Tests.Log.Log dirty -/
#guard_msgs in
mp def closeDirty (fs : &Fs) (src : &ByteBuf 16) requires ByteBuf.Inv 16 src : Unit := do
  let h0 := Log.open (&fs) 1
  let h1 := Log.write h0 (&src)
  Log.close h1

/-- error: type mismatch: expected Millipede.Tests.Log.Log clean, but this has type Millipede.Tests.Log.Log dirty -/
#guard_msgs in
mp def writeDirty (fs : &Fs) (src : &ByteBuf 16) requires ByteBuf.Inv 16 src : Unit := do
  let h0 := Log.open (&fs) 1
  let h1 := Log.write h0 (&src)
  let h2 := Log.write h1 (&src)
  let h3 := Log.sync (&fs) h2
  Log.close h3

/-! ## Programs -/

mp extern "read" roRead (fd : UInt64) (buf : OutByte) : UInt64

mp def roInit : UInt64 := 0

mp def roStep (r : &mut UInt64) : Unit := do
  let c := roRead 0
  r := c
  ()

/-- A program that is granted no token. -/
mp program readOnly (root : UInt64) init roInit step roStep

/-- No trace of `readOnly` writes or reads the clock. -/
example : readOnly.NoCalls (Fs.syms ++ Clock.syms) := readOnly.noCalls

mp def badInit (x : UInt64) : UInt64 := x

/-- error: `init` must take no parameter, or only tokens of capability classes, and return the root type UInt64: its parameter `x` is not a token -/
#guard_msgs in
mp program bad1 (root : UInt64) init badInit step roStep

mp def refInit (fs : &Fs) : UInt64 := 0

/-- error: `init` takes its tokens by value: `fs` is a reference -/
#guard_msgs in
mp program bad2 (root : UInt64) init refInit step roStep

/-- An `init` granted both classes, which gives up the clock. -/
mp def twoInit (fs : Fs) (c : Clock) : LogRoot := do
  let _ := Cap.drop "Millipede.Tests.Log.Clock" c
  { fs := fs, inb := ByteBuf.new }

mp program both (root : LogRoot) init twoInit step logStep

example : both.Safe := both.safe

-- Both classes are granted, so there is no class to exclude and no `both.noCalls`.
run_cmd do
  if (← Lean.getEnv).contains `Millipede.Tests.Tokens.both.noCalls then
    Lean.logError "both.noCalls should not exist"

end Millipede.Tests.Tokens
