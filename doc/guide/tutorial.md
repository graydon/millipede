# Tutorial: a bracket checker

This tutorial builds one program, `brackets`, from a first function to a running binary. The
program reads text on standard input and checks that the brackets `()`, `[]` and `{}` in it nest
correctly. You write it in Millipede, state what it must do, have Lean prove most of that
automatically, and compile it to an x64 Linux executable. You need to know a systems language
such as C, but not Lean, and each Lean idea is explained where it first appears.

Every code block is cut from [Tests/Tutorial.lean](../../Tests/Tutorial.lean), which the test suite
builds, and a message in the comment above `#guard_msgs` is the one Lean really prints. The finished
program keeps one entry for each open bracket, at most 8 deep. At the end of the input it prints
`balanced, max depth N` and exits with 0, or prints what went wrong and exits with 10 for a
mismatch, 11 for nesting deeper than 8, 12 for an unclosed bracket, or 13 for input over 1 KiB.

## 1. A first function

Build the library once with `lake build Millipede`. A program file imports the library modules it
uses and sets `set_option experimental.vcgen true`, which turns on the tactic that proves contracts.

The first two functions test a byte, passed as a `UInt64` word because that is how `read`
returns it:

```lean
-- [tutorial:isOpen]
mp def isOpen (c : UInt64) : Bool := c == 40 || c == 91 || c == 123   -- ( [ {
mp def isClose (c : UInt64) : Bool := c == 41 || c == 93 || c == 125  -- ) ] }
/-- info: true -/
#guard_msgs in
#eval isOpen 91
example : isClose 40 = pure false := rfl
/-- info: Millipede.Tests.Tutorial.isOpen.exp : Exp [Ty.u64] Ty.bool -/
#guard_msgs in
#check isOpen.exp
/-- info: Millipede.Tests.Tutorial.isOpen.wf : isOpen.fn.wf = true -/
#guard_msgs in
#check isOpen.wf
```

When Lean accepts the file, `mp def` has done three things. It has turned the body into a Core
term, `isOpen.exp`, which is the program as data and is what the compiler reads. It has checked
the term's types, its use of linear values and its borrows, and kept the proof of that check as
`isOpen.wf`. And it has defined an ordinary Lean function `isOpen`, the normal form, which `#eval`
runs and proofs reason about. A pure function's result is written `pure true`, and `rfl` is a
proof by computation.

## 2. Arrays and obligations

Each opening bracket has a kind, 0, 1 or 2, and kind 3 means "not a bracket". A table maps each
kind to its closing bracket. A first attempt indexes the table directly, and a second one adds
`!` to the index:

```lean
-- [tutorial:closer-tries]
/-- error: cannot show that this index is below 4: use a literal below 4 or the counter of a loop `for i in 0...N` with N ≤ 4; otherwise write `a[i]!` (an obligation of `f.safe`) or `a[i]?` (checked, a Result) -/
#guard_msgs in
mp def closerOf0 (k : UInt64) : UInt64 :=
  let closers : Arr UInt64 4 := #v[41, 93, 125, 0]
  closers[k]
/-- info: the obligations of `closerOf1` were not discharged automatically; prove them with `mp prove closerOf1.safe := …` (the goal is `closerOf1.SafeGoal`); left:
k : UInt64
⊢ k.toNat < 4 -/
#guard_msgs in
mp def closerOf1 (k : UInt64) : UInt64 :=
  let closers : Arr UInt64 4 := #v[41, 93, 125, 0]
  closers[k]!
```

Lean rejects `closers[k]` because it cannot see that `k < 4`. `closers[k]!` is accepted with an
obligation, a fact that must be proved before the program can be compiled. Here the fact is false
for large `k`, so `mp def` says with an information message that it is not proved. `closerOf1`
exists and runs, but its proof of safety, `closerOf1.safe`, does not. After `left:` the message
shows the hypotheses and, after `⊢`, the goal that could not be proved. `toNat` reads a word as a
natural number.

When an obligation is not proved, the usual fix is to state what the caller promises. That is a
precondition, written with `requires`:

```lean
-- [tutorial:closerOf]
/-- The closing bracket of kind `k` (0, 1, 2), or 0 for kind 3 ("not a bracket"). -/
mp def closerOf (k : UInt64) requires k ≤ 3 : UInt64 :=
  let closers : Arr UInt64 4 := #v[41, 93, 125, 0]
  closers[k]!
/-- info: `Millipede.Tests.Tutorial.closerOf`: the analyser certified all (0 overflow, 1 other partial operations); `safe` proved -/
#guard_msgs in
#mp_analyse closerOf
```

Every caller of `closerOf` must now establish `k ≤ 3`. `#mp_analyse` reports that the analyser,
a verified range analysis that reads bounds from the precondition, proved the obligation. When
the analyser cannot prove an obligation, `mp def` tries the tactics `mp_safe` and `mp_auto`, and
when they fail too, you prove it yourself with `mp prove f.safe := proof`.

## 3. Arithmetic

Each of `+`, `-` and `*` comes in three forms, which differ in what happens when the result does
not fit in a word:

```lean
-- [tutorial:arith]
mp def nextW (n : UInt64) : UInt64 := n + 1
mp def nextC (n : UInt64) : Result Unit UInt64 := n +? 1
example : nextW 0xFFFFFFFFFFFFFFFF = pure 0 := rfl
example : (nextC 0xFFFFFFFFFFFFFFFF).run = .error () := rfl
example : (nextC 41).run = .ok 42 := rfl
/-- info: the obligations of `nextO` were not discharged automatically; prove them with `mp prove nextO.safe := …` (the goal is `nextO.SafeGoal`); left:
n : UInt64
⊢ n.toNat + 1 < 18446744073709551616 -/
#guard_msgs in
mp def nextO (n : UInt64) : UInt64 := n +! 1
/-- The ASCII digit of `m`. -/
mp def digit (m : UInt64) requires m ≤ 8 : UInt8 := (m +! 48).toUInt8
/-- info: `Millipede.Tests.Tutorial.digit`: the analyser certified all (1 overflow, 0 other partial operations); `safe` proved -/
#guard_msgs in
#mp_analyse digit
```

`+` wraps around modulo 2^64, as in C, and carries no obligation, so it suits checksums and counters
that may wrap. `+?` tests the result when the program runs and gives `ok` with the sum, or an error
when it does not fit, so it suits a value that comes from the input. `+!` compiles to the same
instruction as `+` and carries the obligation that the true sum fits, so it suits sizes, indices and
budgets, where a result that wrapped would be a bug. `nextO`'s obligation is false for the largest
word, and Lean says so in the same way as in step 2. `digit`'s obligation holds under `requires m ≤
8`, and the analyser proves it. `.toUInt8` narrows a word to a byte.

## 4. A loop, a structure and a reference

A body with statements is written after `do`, in the notation of Lean's `do` blocks. `for i in
0...3 do body` runs the body for `i` equal to 0, 1 and 2, and `return i` leaves the function with
the value `i`. Every loop has a bound, and no function calls itself.

```lean
-- [tutorial:kindOf]
#guard_msgs in
mp def kindOf (c : UInt64) ensures result ≤ 3 : UInt64 := do
  let openers : Arr UInt64 3 := #v[40, 91, 123]
  for i in 0...3 do
    if openers[i] == c then return i
  return 3
```

`openers[i]` needs no `!`, because `i` is the counter of a loop over the array. The clause `ensures
result ≤ 3` is a postcondition, which is proved here with no help. A structure declared with
`deriving Data` gets a memory layout, the one a C compiler would give it. A parameter `(d : &mut
Depth)` is an exclusive reference, through which the function may change the caller's value, and
`d.cur := v` assigns one of its fields:

```lean
-- [tutorial:depth]
structure Depth where
  cur : UInt64
  max : UInt64
deriving Data
/-- One level deeper; `max` follows. -/
mp def enter (d : &mut Depth) requires d.cur < 8 ∧ d.max ≤ 8
    ensures d'.cur = d.cur + 1 ∧ d'.max ≤ 8 : Unit := do
  d.cur := d.cur +! 1
  if d.max < d.cur then d.max := d.cur
```

The obligation of `d.cur +! 1` and the contract are both proved from `requires`. In the
postcondition, `d'` is the value of `d` at the end of the function.

While an exclusive borrow is live, the place it borrows may be used only through it. The borrow
checker rejects code that breaks this rule, and the fix is to use the place through the reference:

```lean
-- [tutorial:borrow-bad]
/-- error: `d` is used here while an overlapping place is borrowed with `&mut` by `r`; while `r` is live, no overlapping place may be used except through `r` -/
#guard_msgs in
mp def peek (d : &mut Depth) : UInt64 :=
  let r := &mut d.cur
  d.cur
```

## 5. Contracts

A function's precondition and postcondition together are its contract. `mp def` tries to prove
the contract as `f.spec`, and callers use the contract instead of looking inside the function.
The contract of `kindOf` was proved with no help. A loop needs an invariant, a fact that is true
before and after every iteration, and `mp def` tries the postcondition at the loop's state as
the invariant. When the postcondition is not an invariant, the message prints the shape of the
proof. In `opensIn` below, `n ≤ 4` is not kept by an iteration, since from `n = 4` an iteration
could give 5. The invariant "`n` is at most the number of iterations done" is kept:

```lean
-- [tutorial:kindOf-spec]
/-- info: the contract of `opensIn` was not proved automatically: a loop needs an invariant (a fact about the counters done, the counters left and the carried value, true before and after every iteration; the postcondition at the carried value was tried and is not one). Prove it with
  mp prove opensIn.spec := by
    intro w; vcgen [opensIn, isOpen] invariants
    · fun done left acc => …
    all_goals (try have := range_split ‹List.range _ = _ ++ _ :: _›); grind
(`range_split`: the counter is below the bound; the goal is `opensIn.SpecGoal`); left:
⊢ ?inv1 [] (List.range 4) 0 -/
#guard_msgs in
/-- How many of four bytes open a bracket. -/
mp def opensIn (w : Arr UInt64 4) ensures result ≤ 4 : UInt64 := do
  let mut n := 0
  for i in 0...4 do
    if isOpen w[i] then n := n + 1
  n
mp prove opensIn.spec := by
  intro w; vcgen [opensIn, isOpen] invariants
  · fun done _ n => n.toNat ≤ done.length
  all_goals (try have := range_split ‹List.range _ = _ ++ _ :: _›); grind
```

The invariant's arguments are the counter values done, the values left and the loop's state. `vcgen`
turns the contract into goals and `grind` closes them, and `range_split` tells `grind` that the
counter is below the bound. A caller needs nothing more. Below, `closerOf`'s precondition `k ≤ 3`
follows from `kindOf`'s postcondition, and `kindOf.post` is that contract as a plain fact about
`(kindOf c).run`.

```lean
-- [tutorial:expected]
/-- The closing bracket `c` asks for, or 0 when `c` is not an opening bracket. -/
mp def expected (c : UInt64) : UInt64 := closerOf (kindOf c)
/-- info: Millipede.Tests.Tutorial.kindOf.post (c : UInt64) : (kindOf c).run ≤ 3 -/
#guard_msgs in
#check kindOf.post
```

## 6. Units

The program reads at most 1 KiB of input, counted in bytes. A quantity `Q u` is a word tagged
with a unit `u`, and the tags are checked by Lean and cost nothing at run time.

```lean
-- [tutorial:budget]
/-- More input may be read: fewer than `cap` seen (a budget of at most 64 KiB). -/
mp def underBudget (seen : Q byte) (cap : Q KiB) requires cap ≤ 64
    ensures result = true → seen.toNat < cap.toNat * 1024 : Bool :=
  seen < cap.to! byte
```

`cap.to! byte` converts kibibytes to bytes with the obligation that the product fits, which
follows from `requires cap ≤ 64`. Comparing a `Q byte` with a `Q KiB` directly is rejected, and
the message says which conversion to write. A structure cannot have a quantity field, so the root
keeps `seen` as a word and the caller writes `byte r.seen`.

## 7. The root, a pool and keys

A program keeps its state in one value, the root, in static memory, and there is no heap. Storage
whose use varies is held in the library's arenas. `Pool8` is a pool of 8 cells of words.
`Pool8.alloc!` stores a value in a free cell and returns a key, and `Pool8.free` consumes the key
and returns the value. Keys are linear, which means each must be used exactly once. Ours go on a
stack, `Slots Pool8.Key 8`, whose 8 cells are each empty or full. `mp extern` declares the system
calls the program uses.

```lean
-- [tutorial:root]
mp extern "read" bRead (fd : UInt64) (buf : OutByte) : UInt64
mp extern "write" bWrite (fd : UInt64) (buf : Bytes) : UInt64
mp extern "write" bWriteS (fd : UInt64) (buf : &[U8]) : UInt64
mp extern noreturn "exit" bExit (code : UInt64) : UInt64

structure Br where
  pool : Pool8              -- 8 cells, each holds the closer one open bracket expects
  keys : Slots Pool8.Key 8  -- the keys of the open brackets, innermost last
  d : Depth                 -- d.cur keys are held
  seen : UInt64             -- bytes read
  out : Arr UInt8 2         -- the digit printed at the end, and a newline
deriving Data

def BrInv (r : Br) : Prop :=
  r.pool.Inv ∧ Pool8.impl.KeyStack r.pool r.keys r.d.cur ∧ r.d.max ≤ 8
```

`BrInv` is the root's invariant, which every step may assume and must keep. It says that the pool
is consistent, that `d.cur` keys are on the stack and each owns a distinct cell, and that the
maximum depth is at most 8. `KeyStack` is the library's invariant for keys kept in `Slots`, and
without it nothing would record that the pool's cells in use are those of the keys on the stack.

`brInit` builds the root, and its contract is proved with no help because `mp def` unfolds
`BrInv`, which is defined in the same file:

```lean
-- [tutorial:init]
#guard_msgs in
mp def brInit ensures BrInv result : Br :=
  { pool := Pool8.new, keys := Slots.empty 8, d := { cur := 0, max := 0 }, seen := 0,
    out := #v[0, 10] }
```

`push` stores the expected closing bracket in a fresh cell and pushes the key, and `pop` undoes
it. Their obligations and contracts are proved automatically:

```lean
-- [tutorial:push-pop]
/-- Open a bracket: keep the closer `e` in a fresh cell and push its key. -/
mp def push (r : &mut Br) (e : UInt64) requires BrInv r ∧ r.d.cur < 8 ensures BrInv r' : Unit :=
  let k := Pool8.alloc! (&mut r.pool) e
  let i := r.d.cur
  let _ := r.keys.put! i k
  enter (&mut r.d)
/-- Close a bracket: pop the innermost key, free its cell, return the closer it held. -/
mp def pop (r : &mut Br) requires BrInv r ∧ 0 < r.d.cur ensures BrInv r' : UInt64 := do
  let i := r.d.cur -! 1
  let k := r.keys.take! i
  let v := Pool8.free (&mut r.pool) k
  r.d.cur := i
  v
```

`alloc!` needs a free cell, `put!` an empty cell of the stack, and `take!` and `free` full ones.
All of these follow from `BrInv`, and none is checked at run time. When such an obligation is not
proved, the message often ends with a hint that the invariant needs `KeyStack`. Using a key after
it was freed, or forgetting it, is rejected:

```lean
-- [tutorial:linear]
/-- error: use of `k` after it was moved (a linear value is used once) -/
#guard_msgs in
mp def popTwice (r : &mut Br) requires BrInv r ∧ 0 < r.d.cur : UInt64 :=
  let k := r.keys.take! (r.d.cur -! 1)
  let v := Pool8.free (&mut r.pool) k
  v + Pool8.get (&r.pool) (&k)
```

## 8. Generic code

A definition can be written once for every element type and size. In the `variable` line below,
`T` is a type with a memory layout whose values may be copied and have a default, and `n` is a
size. A structure with such parameters derives its layout for every `T` and `n`. `Log.add` is
checked and its contract proved once, and `logBoth` uses it at two instances. Each call infers
`T` and `n` from the type of its argument.

```lean
-- [tutorial:generic]
structure Log (T : Type) (n : Nat) where
  items : Arr T n
  len : UInt64
deriving Data
section
variable (T : Type) [Data T] [Data.Copy T] [Inhabited T] (n : Nat)
mp def Log.add (l : &mut Log T n) (v : T) requires l.len.toNat < n
    ensures l'.len = l.len + 1 : Unit := do
  l.items[l.len]! := v
  l.len := l.len + 1
end
mp def logBoth (a : &mut Log UInt64 4) (b : &mut Log UInt8 16) (c : UInt64)
    requires a.len.toNat < 4 ∧ b.len.toNat < 16 : Unit := do
  let _ := Log.add (&mut a) c
  Log.add (&mut b) c.toUInt8
```

An interface states what an implementation provides. `mp interface` declares abstract types, a model
such as `val`, and the operations with their contracts. `mp implementation` gives each operation as
an `mp def`, whose contract becomes the operation's. A client under `variable (A : Counter)` is
proved once, from the interface's contracts, for every implementation. It takes the state by `&mut`,
because it must treat a value of an abstract type as linear.

```lean
-- [tutorial:interface]
mp interface Counter where
  S : Type
  val : S → UInt64
  op zero ensures val result = 0 : S
  op bump (s : &mut S) requires val s < 1000 ensures val s' = val s + 1 : Unit
  op read (s : &S) ensures result = val s : UInt64
mp def Ctr.zero ensures result = 0 : UInt64 := 0
mp def Ctr.bump (c : &mut UInt64) requires c < 1000 ensures c' = c + 1 : Unit := do
  c := c + 1
mp def Ctr.read (c : &UInt64) ensures result = c : UInt64 := c
mp implementation Ctr.impl : Counter where
  S := UInt64
  val c := c
  op zero := Ctr.zero
  op bump := Ctr.bump
  op read := Ctr.read
section
variable (A : Counter)
mp def bumpTwice (s : &mut A.S) requires A.val s < 100 ensures result = A.val s + 2 :
    UInt64 := do
  let _ := A.bump (&mut s)
  let _ := A.bump (&mut s)
  A.read (&s)
end
```

## 9. The reactor

A program has the shape of a reactor, in which `init` builds the root once and then `step` runs
with `&mut root`, again and again, until it calls `exit`. Ours reads one byte per step, and
`read` returns 2^64 − 1 at the end of the input.

```lean
-- [tutorial:step]
/-- Report an error and exit with `code`. -/
mp def fail (code : UInt64) : Unit :=
  let _w := if code == 10 then bWrite 1 "mismatch\n"
    else if code == 11 then bWrite 1 "too deep\n"
    else if code == 12 then bWrite 1 "unclosed\n"
    else bWrite 1 "too long\n"
  let _x := bExit code
  ()
/-- End of input: print the verdict and exit. -/
mp def finish (r : &mut Br) requires BrInv r ensures BrInv r' : Unit := do
  if r.d.cur == 0 then
    r.out[0] := digit r.d.max
    let _w := bWrite 1 "balanced, max depth "
    let _v := bWriteS 1 (&r.out[0..2])
    let _x := bExit 0
  else fail 12
/-- One input byte. -/
mp def brStep (r : &mut Br) requires BrInv r ensures BrInv r' : Unit := do
  let c := bRead 0
  if c >= 256 then finish (&mut r)
  else if underBudget (byte r.seen) (KiB 1) then
    r.seen := r.seen +! 1
    let e := expected c
    if e != 0 then
      if r.d.cur < 8 then push (&mut r) e
      else fail 11
    else if isClose c then
      if r.d.cur == 0 then fail 10
      else
        let want := pop (&mut r)
        if want != c then fail 10
  else fail 13
```

A string can be passed only to an extern, which is why `fail` chooses among four calls to
`bWrite`. `bWriteS` writes a slice of a byte array, `&r.out[0..2]`. `brStep` is proved from its
callees' contracts. When `underBudget` returns `true`, fewer than 1024 bytes have been seen, so
`r.seen +! 1` cannot overflow. The program itself is declared with `mp program`:

```lean
-- [tutorial:program]
mp program brackets (root : Br) init brInit step brStep invariant BrInv
example : brackets.Safe := brackets.safe
```

From the contracts of `brInit` and `brStep`, `mp program` proves that the invariant holds after
any number of steps, `brackets.inv`, and that every obligation of every step holds,
`brackets.safe`, for any input. When a function of the program still has an open obligation,
`mp program` says that `brackets.safe` was not generated and names the function.

## 10. Compiling and running

`#mp_compile` writes the x64 Linux ELF file and its assumption ledger, the list of what the
binary relies on. It refuses a program whose `safe` is not proved, and names the missing proof.

```lean
-- [tutorial:compile]
#mp_compile brackets ".lake/brackets"
```

Checking the file writes `.lake/brackets` and its ledger. Run the program under qemu:

```sh
printf 'f(a[b]{c})' | ~/tools/bin/qemu-x86_64 .lake/brackets; echo "exit $?"
# balanced, max depth 2
# exit 0
```

On an x64 Linux machine, run `.lake/brackets` directly. What the proofs say about this binary is
`compile_sound` applied to it:

```lean
-- [tutorial:sound]
theorem brackets_sound (b : ByteArray) (hc : compile brackets x64Linux = .ok b) :
    ∃ s₀, x64Linux.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle,
        let m := Machine.run x64Linux s₀ ω
        m.NeverStuck ∧ TraceEq m.trace (brackets.events ω) ∧
        m.StackWithin (brackets.stackBytes x64Linux.φ) ∧
        m.StepsWithin (brackets.events ω) (fun k => brackets.stepCost k ω x64Linux.κ) :=
  compile_sound brackets b hc brackets.safe
```

If `compile` produced the bytes `b`, then the model of the ELF loader loads them. For every input
`ω`, the machine never gets stuck, makes exactly the system calls that the source program makes,
stays within the program's stack bound, and runs at most a computed number of instructions per
step. The theorem holds of models of the x64 instructions, of Linux's `read`, `write` and `exit`,
and of the ELF loader, which are trusted and are tested against qemu and the GNU tools. It says
nothing about what you meant, so no theorem says that `brackets` checks brackets.

## 11. Measuring

`#mp_report` prints a program's figures and how each proof was made:

```lean
-- [tutorial:report]
#mp_report brackets
```

For `brackets` on x64 the root takes 176 bytes, the stack bound is 15,416 bytes, `init` runs at most
2,185 instructions and each step at most 7,678, and the code takes 24,576 bytes. The counts are
bounds, not measurements. Each function follows with its stack bound and the status of its proofs,
where "automatic" means that no line of proof was written, "mp_auto" a one-line
`mp prove … := by mp_auto`, and "by hand" any other `mp prove`. No function of `brackets` needed a
written proof, and `scripts/proof-burden.sh` counts 129 lines of program, 33 of contracts and 25 of
proofs in the whole file.

## 12. When something goes wrong

The [messages](../reference/messages.md) part of the reference lists the messages beyond those
shown here, the [surface reference](../reference/surface.md) describes every command, and the
[glossary](../reference/glossary.md) defines the terms.
