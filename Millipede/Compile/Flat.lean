import Millipede.Core.Cost
import Millipede.Compile.Sem

/-!
# The Flat language

Flat is the compiler's first untyped representation, in which every value is a 64-bit word.
Variables are numbered word slots of the current activation's frame, and an operand is a slot or
an immediate word. Statements are structured, with `seq`, `ite` and `while`, and they include
moves, binary operations, byte-addressed loads and stores, calls, extern calls and cost ticks. The
lowering keeps every Core value in memory, which is why loads and stores are byte-addressed. A call
carries the callee's code at the call site, as in Core, so there is no recursion.

The clock of a Flat run is the sum of the `κ`-weights of the ticks executed. A statement `tick t`
costs `t.cost κ` and every other statement costs nothing. The lowering places one tick per Core
construct, except that a large constructor written by a loop splits its tick between the
constructor and the loop's iterations, so the Flat clock is exactly the step count of Core's
instrumented semantics `Exp.exec`, and later passes must bound their work by the ticks they
inherit.

The semantics is a small-step machine with an explicit continuation stack, in which a call pushes
a `ret` continuation holding the caller's frame. `next κ ω s` is the transition, which is total. A
state whose world has halted steps to itself, and so does a finished program, which is `skip` with
an empty continuation. `Flat.sem κ` is never stuck, because memory is total here and only Lin bounds
it to a data region.

See doc/design/compiler.md.
-/

namespace Millipede.Flat

/-- The number of words occupied by a value of type `t`, which is the width argument of the
width-aware ticks. -/
abbrev width (t : Ty) : Nat := t.data.shape.words

/-- An operand: a frame slot or an immediate word. -/
inductive Operand where
  | slot (x : Nat)
  | imm (w : UInt64)
deriving DecidableEq, Repr, Inhabited

/-- Binary word operations. Comparisons yield `1` for true and `0` for false, `udiv` and `umod` are
total with `x / 0 = 0` and `x % 0 = x`, and shift amounts are taken mod 64. -/
inductive BinOp where
  | add | sub | mul | udiv | umod | band | bor | bxor | shl | shr
  | eq | ne | ult | ule
deriving DecidableEq, Repr

/-- The meaning of a binary operation, exact to the machine as `Prim.denote` is. -/
def BinOp.eval : BinOp → UInt64 → UInt64 → UInt64
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .udiv, x, y => x / y
  | .umod, x, y => x % y
  | .band, x, y => x &&& y
  | .bor, x, y => x ||| y
  | .bxor, x, y => x ^^^ y
  | .shl, x, y => x <<< y
  | .shr, x, y => x >>> y
  | .eq, x, y => if x = y then 1 else 0
  | .ne, x, y => if x = y then 0 else 1
  | .ult, x, y => if x < y then 1 else 0
  | .ule, x, y => if x ≤ y then 1 else 0

/-- The Core construct that a tick pays for. Its weight is the matching `CostModel` field, plus
`κ.word` per word copied for the constructs whose Core cost depends on width, where the argument is
that width as `Exp.cost` charges it. -/
inductive Tick where
  | atom (w : Nat) | let_ | ite | prim | div | loop (w : Nat) | iter (w : Nat)
  | call (w : Nat) | ctor (w : Nat) | match_ (w : Nat)
  /-- An extern call passing `r` slices, each as an address and a length, with `d` place
  selectors. -/
  | ext (d r : Nat)
  /-- A memory operation, which is a read, assign, put, take or guard, with `d` place selectors,
  copying `w` words. -/
  | mem (d w : Nat)
  /-- A borrow, which makes a reference with `d` place selectors. -/
  | ref (d : Nat)
  /-- A call with reference arguments, with `d` place selectors, `r` references and `w` words of
  owned arguments copied. -/
  | callR (d r w : Nat)
  /-- One iteration of a store loop that fills `w` words' worth of a constructed value. The
  construct's own tick pays its constant and the words that the loop does not fill. -/
  | words (w : Nat)
deriving DecidableEq, Repr

/-- The weight of a tick under `κ`. -/
def Tick.cost (κ : CostModel) : Tick → Nat
  | .atom w => κ.atom + w * κ.word
  | .let_ => κ.let_
  | .ite => κ.ite
  | .prim => κ.prim
  | .div => κ.div
  | .loop w => κ.loop + w * κ.word
  | .iter w => κ.iter + w * κ.word
  | .call w => κ.call + w * κ.word
  | .ctor w => κ.ctor + w * κ.word
  | .match_ w => κ.match_ + w * κ.word
  | .ext d r => κ.ext + κ.place * d + κ.ref * r
  | .mem d w => κ.mem + d * κ.place + w * κ.word
  | .ref d => κ.ref + d * κ.place
  | .callR d r w => κ.call + d * κ.place + r * κ.ref + w * κ.word
  | .words w => w * κ.word

/-- An extern argument. It is a word, an input buffer, an output buffer of `cap` bytes, or an
output buffer in memory. An input buffer holds constant bytes or the `len` bytes of memory from
address `a`, which is how a slice is passed as a pointer and a length. The contents of an output
buffer reach the program through the call's value, and the backend provides the buffer. An output
buffer in memory, `outMem a cap`, is a mutable slice passed as a pointer and a capacity, and the
extern writes at most `cap` bytes from address `a` while the call delivers the raw result word. -/
inductive ExtArg where
  | word (a : Operand)
  | bytes (bs : List UInt8)
  | mem (a len : Operand)
  | out (cap : Nat)
  | outMem (a cap : Operand)
deriving DecidableEq, Repr

/-- The width of a memory access. -/
inductive Width where
  | w8 | w64
deriving DecidableEq, Repr

/-- The bytes of a memory access of width `w`. -/
def Width.bytes : Width → Nat
  | .w8 => 1
  | .w64 => 8

/-- Flat statements. -/
inductive Stmt where
  | skip
  | seq (a b : Stmt)
  /-- `x := a`. -/
  | mov (x : Nat) (a : Operand)
  /-- `x := op a b`. -/
  | bin (op : BinOp) (x : Nat) (a b : Operand)
  /-- `x := mem[a + off]`, zero-extended for `w8` and little-endian for `w64`. -/
  | load (w : Width) (x : Nat) (a : Operand) (off : UInt64)
  /-- `mem[a + off] := b`, the low byte for `w8` and little-endian for `w64`. -/
  | store (w : Width) (a : Operand) (off : UInt64) (b : Operand)
  /-- `if c ≠ 0 then t else e`. -/
  | ite (c : Operand) (t e : Stmt)
  /-- `loop { pre; if c = 0 then break; body }`. -/
  | while (pre : Stmt) (c : Operand) (body : Stmt)
  /-- A call runs `body` in a fresh frame that holds the argument words in slots `0, 1, …`, then
  writes the words of `ret`, evaluated in the callee's frame, to the caller's slots
  `dst, dst+1, …`. `name` is used only for symbols. `frame` is the callee's declared frame size in
  words, which the semantics does not consult; the lowering guarantees that `body` and `ret` use
  only slots below it. -/
  | call (name : String) (frame : Nat) (body : Stmt) (ret : List Operand) (args : List Operand)
      (dst : Nat)
  /-- An extern call, whose result word goes to slot `x`. -/
  | ext (sym : String) (noreturn : Bool) (x : Nat) (args : List ExtArg)
  /-- Pays for one Core construct. -/
  | tick (t : Tick)
deriving Repr, Inhabited

/-- A frame has one word per slot. It is unbounded, and the lowering bounds the slots it uses. -/
abbrev Frame := Nat → UInt64

/-- Writes one slot. -/
def Frame.set (f : Frame) (x : Nat) (v : UInt64) : Frame := fun y => if y = x then v else f y

@[simp] theorem Frame.set_same (f : Frame) (x : Nat) (v : UInt64) : f.set x v x = v := by
  simp [Frame.set]

theorem Frame.set_ne (f : Frame) {x y : Nat} (v : UInt64) (h : y ≠ x) : f.set x v y = f y := by
  simp [Frame.set, h]

/-- Writes consecutive slots `d, d+1, …`. -/
def Frame.writes : Frame → Nat → List UInt64 → Frame
  | f, _, [] => f
  | f, d, v :: vs => Frame.writes (f.set d v) (d + 1) vs

/-- A frame holding `vs` in slots `0, 1, …` and zeros elsewhere. -/
def Frame.ofList (vs : List UInt64) : Frame := fun i => vs.getD i 0

/-- The all-zero frame. -/
def Frame.zero : Frame := fun _ => 0

/-- The value of an operand in a frame. -/
def Operand.eval (f : Frame) : Operand → UInt64
  | .slot x => f x
  | .imm w => w

@[simp] theorem eval_slot (f : Frame) (x : Nat) : Operand.eval f (.slot x) = f x := rfl
@[simp] theorem eval_imm (f : Frame) (w : UInt64) : Operand.eval f (.imm w) = w := rfl

/-- Byte-addressed memory. It is total, and Lin bounds it by its data region. -/
abbrev Heap := UInt64 → UInt8

/-- A little-endian load. -/
def Heap.load (h : Heap) : Width → UInt64 → UInt64
  | .w8, a => (h a).toUInt64
  | .w64, a =>
    (List.range 8).foldr (fun i acc => (acc <<< 8) ||| (h (a + UInt64.ofNat i)).toUInt64) 0

/-- Stores one byte. -/
def Heap.store8 (h : Heap) (a : UInt64) (b : UInt8) : Heap := fun y => if y = a then b else h y

/-- A little-endian store. -/
def Heap.store (h : Heap) : Width → UInt64 → UInt64 → Heap
  | .w8, a, v => h.store8 a v.toUInt8
  | .w64, a, v =>
    (List.range 8).foldl (fun h i => h.store8 (a + UInt64.ofNat i) (v >>> (8 * UInt64.ofNat i)).toUInt8) h

/-- Continuations. -/
inductive Kont where
  /-- Then run `s`. -/
  | seq (s : Stmt)
  /-- The `pre` part of `while pre c body` has run, and `c` is tested next. -/
  | loop (pre : Stmt) (c : Operand) (body : Stmt)
  /-- Return from a call, writing `ret`, evaluated in the callee's frame, to `dst…` of the saved
  frame. -/
  | ret (ret : List Operand) (dst : Nat) (saved : Frame)

/-- A Flat machine state. -/
structure State where
  cur : Stmt
  kont : List Kont
  frame : Frame
  mem : Heap
  world : World
  clock : Nat

/-- The word arguments of an extern call, in order. -/
def extWords (f : Frame) : List ExtArg → List UInt64
  | [] => []
  | .word a :: as => a.eval f :: extWords f as
  | .bytes _ :: as => extWords f as
  | .mem _ _ :: as => extWords f as
  | .out _ :: as => extWords f as
  | .outMem _ _ :: as => extWords f as

/-- The `n` bytes of memory from address `a`, where addresses wrap. -/
def Heap.read (h : Heap) (a : UInt64) (n : Nat) : List UInt8 :=
  (List.range n).map fun i => h (a + UInt64.ofNat i)

/-- The input-buffer contents of an extern call, in order, with a memory buffer read from `h`. -/
def extBytes (h : Heap) (f : Frame) : List ExtArg → List (List UInt8)
  | [] => []
  | .word _ :: as => extBytes h f as
  | .bytes bs :: as => bs :: extBytes h f as
  | .mem a n :: as => h.read (a.eval f) (n.eval f).toNat :: extBytes h f as
  | .out _ :: as => extBytes h f as
  | .outMem _ _ :: as => extBytes h f as

/-- The output-buffer capacities of an extern call, in order. An output buffer in memory has a
capacity known only at run time. -/
def extCaps (f : Frame) : List ExtArg → List Nat
  | [] => []
  | .word _ :: as => extCaps f as
  | .bytes _ :: as => extCaps f as
  | .mem _ _ :: as => extCaps f as
  | .out c :: as => c :: extCaps f as
  | .outMem _ c :: as => (c.eval f).toNat :: extCaps f as

/-- The address and capacity operands of the first output buffer in memory, if any. -/
def extOutArg : List ExtArg → Option (Operand × Operand)
  | [] => none
  | .outMem a c :: _ => some (a, c)
  | _ :: as => extOutArg as

/-- Writes bytes sequentially from address `a`, where addresses wrap. -/
def Heap.writeBytes : Heap → UInt64 → List UInt8 → Heap
  | h, _, [] => h
  | h, a, b :: bs => Heap.writeBytes (h.store8 a b) (a + 1) bs

/-- An extern call in frame `f`, memory `h` and world `w`, giving the word delivered to the program
and the memory and world after the call. The call record has the word arguments, the input-buffer
contents and the output capacities. Without an output buffer in memory the call delivers its value
through `World.call`. With one, `outMem a cap` for a mutable slice, the oracle's raw reply from
`World.ask` is used, so the bytes it supplies for that buffer, at most its capacity, are written
from `a` and the result word is delivered. -/
def extRun (ω : Oracle) (sym : String) (nr : Bool) (args : List ExtArg) (f : Frame) (h : Heap)
    (w : World) : UInt64 × Heap × World :=
  let c : Call := ⟨sym, extWords f args, extBytes h f args, extCaps f args⟩
  match extOutArg args with
  | none => let r := w.call ω c nr; (r.1, h, r.2)
  | some (a, _) =>
    let r := w.ask ω c nr
    (r.1.result, h.writeBytes (a.eval f) ((fitOut c.outCaps r.1.bytesOut).headD []), r.2)

/-- An extern call without an output buffer in memory is `World.call`. -/
theorem extRun_none {ω : Oracle} {sym : String} {nr : Bool} {args : List ExtArg} {f : Frame}
    {h : Heap} {w : World} (hn : extOutArg args = none) :
    extRun ω sym nr args f h w =
      ((w.call ω ⟨sym, extWords f args, extBytes h f args, extCaps f args⟩ nr).1, h,
        (w.call ω ⟨sym, extWords f args, extBytes h f args, extCaps f args⟩ nr).2) := by
  simp [extRun, hn]

/-- A running world is halted after an extern call exactly when the call is `noreturn`. -/
theorem extRun_halted (ω : Oracle) (sym : String) (nr : Bool) (args : List ExtArg) (f : Frame)
    (h : Heap) {w : World} (hw : w.halted = false) :
    (extRun ω sym nr args f h w).2.2.halted = nr := by
  unfold extRun
  split <;> cases nr <;> simp [World.call, World.ask, hw]

theorem extRun_prefix (ω : Oracle) (sym : String) (nr : Bool) (args : List ExtArg) (f : Frame)
    (h : Heap) (w : World) : w.events <+: (extRun ω sym nr args f h w).2.2.events := by
  unfold extRun
  split
  · exact World.call_prefix _ _ _ _
  · show w.events <+: (w.ask ω _ nr).2.events
    rw [World.ask_snd]; exact World.call_prefix _ _ _ _

/-- One transition of a running state, one that has not halted. -/
def exec1 (κ : CostModel) (ω : Oracle) (s : State) : State :=
  match s.cur, s.kont with
  | .skip, [] => s
  | .skip, .seq b :: k => { s with cur := b, kont := k }
  | .skip, .loop pre c body :: k =>
    if c.eval s.frame = 0 then { s with kont := k }
    else { s with cur := body, kont := .seq (.while pre c body) :: k }
  | .skip, .ret ops d saved :: k =>
    { s with kont := k, frame := saved.writes d (ops.map (Operand.eval s.frame)) }
  | .seq a b, k => { s with cur := a, kont := .seq b :: k }
  | .mov x a, _ => { s with cur := .skip, frame := s.frame.set x (a.eval s.frame) }
  | .bin op x a b, _ =>
    { s with cur := .skip, frame := s.frame.set x (op.eval (a.eval s.frame) (b.eval s.frame)) }
  | .load w x a off, _ =>
    { s with cur := .skip, frame := s.frame.set x (s.mem.load w (a.eval s.frame + off)) }
  | .store w a off b, _ =>
    { s with cur := .skip, mem := s.mem.store w (a.eval s.frame + off) (b.eval s.frame) }
  | .ite c t e, _ => { s with cur := if c.eval s.frame = 0 then e else t }
  | .while pre c body, k => { s with cur := pre, kont := .loop pre c body :: k }
  | .call _ _ body ret args d, k =>
    { s with cur := body, kont := .ret ret d s.frame :: k,
             frame := Frame.ofList (args.map (Operand.eval s.frame)) }
  | .ext sym nr x args, _ =>
    let r := extRun ω sym nr args s.frame s.mem s.world
    { s with cur := .skip, frame := s.frame.set x r.1, mem := r.2.1, world := r.2.2 }
  | .tick t, _ => { s with cur := .skip, clock := s.clock + t.cost κ }

/-- The transition function, in which a halted state stutters. -/
def next (κ : CostModel) (ω : Oracle) (s : State) : State :=
  if s.world.halted then s else exec1 κ ω s

/-- `n` transitions. -/
def nextN (κ : CostModel) (ω : Oracle) : Nat → State → State
  | 0, s => s
  | n + 1, s => nextN κ ω n (next κ ω s)

/-- Flat as a `Sem` for cost model `κ`. Its events are the world's, its clock is the sum of the
ticks executed, and it has no stuck states. -/
abbrev sem (κ : CostModel) : Sem where
  State := State
  step ω s := some (next κ ω s)
  events s := s.world.events
  clock s := s.clock

/-- A Flat program is a single statement run in a zero frame from the initial world. `frame` is the
main frame's declared size in words, and the lowering guarantees that `main` stays below it. -/
structure Prog where
  main : Stmt
  frame : Nat
deriving Repr

/-- The initial state of a program. -/
def Prog.init (p : Prog) : State :=
  ⟨p.main, [], Frame.zero, fun _ => 0, World.init, 0⟩

/-! ## Basic laws -/

theorem run_eq (κ : CostModel) (ω : Oracle) :
    ∀ (n : Nat) (s : State), (sem κ).run ω s n = some (nextN κ ω n s)
  | 0, _ => rfl
  | n + 1, s => by
    rw [Sem.run_succ]; exact run_eq κ ω n (next κ ω s)

theorem nextN_add (κ : CostModel) (ω : Oracle) :
    ∀ (m n : Nat) (s : State), nextN κ ω (m + n) s = nextN κ ω n (nextN κ ω m s)
  | 0, n, s => by simp [nextN]
  | m + 1, n, s => by
    rw [Nat.add_right_comm]; exact nextN_add κ ω m n (next κ ω s)

theorem exec1_mono (κ : CostModel) (ω : Oracle) (s : State) :
    s.world.events <+: (exec1 κ ω s).world.events ∧ s.clock ≤ (exec1 κ ω s).clock := by
  unfold exec1
  split <;> (try split) <;> simp [extRun_prefix]

theorem next_mono (κ : CostModel) (ω : Oracle) (s : State) :
    s.world.events <+: (next κ ω s).world.events ∧ s.clock ≤ (next κ ω s).clock := by
  unfold next; split
  · exact ⟨List.prefix_refl _, Nat.le_refl _⟩
  · exact exec1_mono κ ω s

/-- Flat only extends the trace and never decreases the clock. -/
theorem sem_mono (κ : CostModel) : (sem κ).Mono where
  events ω s s' h := by cases h; exact (next_mono κ ω s).1
  clock ω s s' h := by cases h; exact (next_mono κ ω s).2

/-! ## Reachability -/

/-- `s'` is reachable from `s` in some number of transitions. -/
def Reach (κ : CostModel) (ω : Oracle) (s s' : State) : Prop := ∃ n, nextN κ ω n s = s'

theorem Reach.refl {κ : CostModel} {ω : Oracle} (s : State) : Reach κ ω s s := ⟨0, rfl⟩

/-- One transition of a running state is `exec1`. -/
theorem next_run {κ : CostModel} {ω : Oracle} {s : State} (h : s.world.halted = false) :
    next κ ω s = exec1 κ ω s := by simp [next, h]

/-! ## Frame discipline

`Stmt.Within s b` states that every slot `s` mentions in the current frame is below `b`. Every
call inside `s`, at any depth, has a body and return operands within its declared frame size, at
most that many argument words, and a result range within the caller's bound. `linearize` and the
stack bound rely on it. -/

/-- `ops` mention only slots below `n`. -/
def OpsBelow (ops : List Operand) (n : Nat) : Prop := ∀ x, Operand.slot x ∈ ops → x < n

/-- Every slot mentioned in the current frame is below `b`, and calls stay within their declared
frames. -/
def Stmt.Within : Stmt → Nat → Prop
  | .skip, _ => True
  | .seq a b, n => a.Within n ∧ b.Within n
  | .mov x a, n => x < n ∧ OpsBelow [a] n
  | .bin _ x a b, n => x < n ∧ OpsBelow [a, b] n
  | .load _ x a _, n => x < n ∧ OpsBelow [a] n
  | .store _ a _ b, n => OpsBelow [a, b] n
  | .ite c a b, n => OpsBelow [c] n ∧ a.Within n ∧ b.Within n
  | .while p c b, n => p.Within n ∧ OpsBelow [c] n ∧ b.Within n
  | .call _ fr body ret args d, n =>
    body.Within fr ∧ OpsBelow ret fr ∧ args.length ≤ fr ∧ OpsBelow args n ∧ d + ret.length ≤ n
  | .ext _ _ x args, n => x < n ∧ (∀ o, ExtArg.word o ∈ args → OpsBelow [o] n) ∧
    (∀ a l, ExtArg.mem a l ∈ args → OpsBelow [a, l] n) ∧
    ∀ a l, ExtArg.outMem a l ∈ args → OpsBelow [a, l] n
  | .tick _, _ => True

end Millipede.Flat
