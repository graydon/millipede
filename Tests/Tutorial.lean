import Millipede.Lib.Pool
import Millipede.Lib.Units
import Millipede.Meta.Report
import Millipede.Meta.Emit

/-!
# The tutorial's program, a bracket checker

Every code block of doc/guide/tutorial.md is the text of this file between the markers
`-- [tutorial:NAME]` and `-- [/tutorial:NAME]`, which `scripts/doc-check.sh` compares. So the
build checks the tutorial's code, and `#guard_msgs` checks the messages it quotes.

The program `brackets` reads its input byte by byte. It keeps the closing bracket that each
opening bracket expects in a cell of a pool arena, and the cells' keys on a stack of at most 8.
At the end of the input it prints `balanced, max depth N` and exits with 0, or prints what went
wrong and exits with 10 for a mismatch, 11 when nesting is deeper than 8, 12 when a bracket is
left unclosed and 13 when the input exceeds 1 KiB.

The negative examples under `#guard_msgs` are the rejections the tutorial shows. A seeded bug,
checked by hand, is a `pop` that forgets `r.d.cur := i`, which leaves `pop.spec` unproved, so
`brackets.safe` is not generated.

Building this file writes the ELF file `.lake/brackets` and its ledger, in step 10.
-/

namespace Millipede.Tests.Tutorial

open Millipede Millipede.Lib Std.WP

set_option experimental.vcgen true

/-! ## Step 1: a pure function -/

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
-- [/tutorial:isOpen]

/-! ## Step 2: indexing an array; obligations -/

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
-- [/tutorial:closer-tries]

-- [tutorial:closerOf]
/-- The closing bracket of kind `k` (0, 1, 2), or 0 for kind 3 ("not a bracket"). -/
mp def closerOf (k : UInt64) requires k ≤ 3 : UInt64 :=
  let closers : Arr UInt64 4 := #v[41, 93, 125, 0]
  closers[k]!
/-- info: `Millipede.Tests.Tutorial.closerOf`: the analyser certified all (0 overflow, 1 other partial operations); `safe` proved -/
#guard_msgs in
#mp_analyse closerOf
-- [/tutorial:closerOf]

-- [tutorial:closer-named]
def IsKind (k : UInt64) : Prop := k ≤ 3
#guard_msgs in
mp def closerOf2 (k : UInt64) requires IsKind k : UInt64 :=
  let closers : Arr UInt64 4 := #v[41, 93, 125, 0]
  closers[k]!
example : closerOf2.SafeGoal := closerOf2.safe
-- [/tutorial:closer-named]

/-! ## Step 3: arithmetic -/

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
-- [/tutorial:arith]

/-! ## Step 4: a loop, a struct, `&mut` -/

-- [tutorial:kindOf]
#guard_msgs in
mp def kindOf (c : UInt64) ensures result ≤ 3 : UInt64 := do
  let openers : Arr UInt64 3 := #v[40, 91, 123]
  for i in 0...3 do
    if openers[i] == c then return i
  return 3
-- [/tutorial:kindOf]

example : kindOf 91 = pure 1 := rfl
example : kindOf 7 = pure 3 := rfl

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
-- [/tutorial:depth]

-- [tutorial:borrow-bad]
/-- error: `d` is used here while an overlapping place is borrowed with `&mut` by `r`; while `r` is live, no overlapping place may be used except through `r` -/
#guard_msgs in
mp def peek (d : &mut Depth) : UInt64 :=
  let r := &mut d.cur
  d.cur
-- [/tutorial:borrow-bad]

/-! ## Step 5: contracts -/

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
-- [/tutorial:kindOf-spec]

-- [tutorial:expected]
/-- The closing bracket `c` asks for, or 0 when `c` is not an opening bracket. -/
mp def expected (c : UInt64) : UInt64 := closerOf (kindOf c)
/-- info: Millipede.Tests.Tutorial.kindOf.post (c : UInt64) : (kindOf c).run ≤ 3 -/
#guard_msgs in
#check kindOf.post
-- [/tutorial:expected]

/-! ## Step 6: units -/

-- [tutorial:budget]
/-- More input may be read: fewer than `cap` seen (a budget of at most 64 KiB). -/
mp def underBudget (seen : Q byte) (cap : Q KiB) requires cap ≤ 64
    ensures result = true → seen.toNat < cap.toNat * 1024 : Bool :=
  seen < cap.to! byte
-- [/tutorial:budget]
/-- error: `<` needs quantities of the same unit, but the operands are Q byte (dimension Size) and Q KiB (dimension Size): units of one dimension do not mix; convert with `.to byte` -/
#guard_msgs in
mp def underBudgetBad (seen : Q byte) : Bool := seen < KiB 1

/-! ## Step 7: the pool, the root, keys -/

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
-- [/tutorial:root]

-- [tutorial:init]
#guard_msgs in
mp def brInit ensures BrInv result : Br :=
  { pool := Pool8.new, keys := Slots.empty 8, d := { cur := 0, max := 0 }, seen := 0,
    out := #v[0, 10] }
-- [/tutorial:init]

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
-- [/tutorial:push-pop]

-- [tutorial:linear]
/-- error: use of `k` after it was moved (a linear value is used once) -/
#guard_msgs in
mp def popTwice (r : &mut Br) requires BrInv r ∧ 0 < r.d.cur : UInt64 :=
  let k := r.keys.take! (r.d.cur -! 1)
  let v := Pool8.free (&mut r.pool) k
  v + Pool8.get (&r.pool) (&k)
-- [/tutorial:linear]
/-- error: unused linear let `k` of type Millipede.Lib.Pool.Key UInt64 8 1: a linear value must be used exactly once (an arena key: free it with the arena's `free`, or store it, e.g. in `Slots` with `put!`) -/
#guard_msgs in
mp def popLeak (r : &mut Br) requires BrInv r ∧ 0 < r.d.cur : Unit :=
  let k := r.keys.take! (r.d.cur -! 1)
  ()

/-! ## Step 8: generic code -/

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
-- [/tutorial:generic]
example := @Log.add.spec
example := @logBoth.safe

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
-- [/tutorial:interface]
example := @bumpTwice.spec
example : (bumpTwice Ctr.impl 5).run.1 = 7 := by decide

/-! ## Step 9: the reactor -/

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
-- [/tutorial:step]

-- [tutorial:program]
mp program brackets (root : Br) init brInit step brStep invariant BrInv
example : brackets.Safe := brackets.safe
-- [/tutorial:program]
example : ∀ ω n, BrInv (brackets.run ω n).1 := brackets.inv

/-! ## Step 10: compile; what the theorem says about this binary -/

-- [tutorial:compile]
#mp_compile brackets ".lake/brackets"
-- [/tutorial:compile]

-- [tutorial:sound]
theorem brackets_sound (b : ByteArray) (hc : compile brackets x64Linux = .ok b) :
    ∃ s₀, x64Linux.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle,
        let m := Machine.run x64Linux s₀ ω
        m.NeverStuck ∧ TraceEq m.trace (brackets.events ω) ∧
        m.StackWithin (brackets.stackBytes x64Linux.φ) ∧
        m.StepsWithin (brackets.events ω) (fun k => brackets.stepCost k ω x64Linux.κ) :=
  compile_sound brackets b hc brackets.safe
-- [/tutorial:sound]

/-! ## Step 11: measuring

The report is not under `#guard_msgs`, because its figures change with the compiler. -/

-- [tutorial:report]
#mp_report brackets
-- [/tutorial:report]

end Millipede.Tests.Tutorial

