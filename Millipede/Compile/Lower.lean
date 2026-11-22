import Millipede.Core.Program
import Millipede.Top.Statement
import Millipede.Compile.Flat

/-!
# Lowering Core to Flat

`lower` translates a Core program to Flat. Each Core value lives in byte-addressed memory, laid
out by its `Shape` and related to the Core value by `Data.repr`, except a small value that is
never addressed, which lives in frame slots instead.


Each activation, which is the program's main code or one call, owns a region of memory that starts
at its base pointer, held in frame slot `BP`. Every variable of the activation has a static
location `Loc`: its value at an offset from the base pointer, or the 8-byte address of its value
stored at such an offset when the variable is a reference. Memory is allocated statically by a
watermark, and because there is no recursion, a callee's region starts at its caller's watermark
and the whole program needs a fixed number of bytes.

The root of a program is the main activation's offset `0`, in static storage. `init` builds it in
place. A step that hands back its parameter runs on the root in place, and any other step writes
its result to a temporary above the root, which is then copied over it.

The first `FR` frame slots of an activation are the base pointer and scratch slots for addresses,
operands and extern arguments. The slots of the slot-resident variables follow them.


A variable whose value is never addressed, and whose type is a flat shape of one byte or of one to
`SLOT_CAP` whole words, is kept in consecutive frame slots as its bytes chunked into 64-bit
words. Its uses become slot reads and writes, so no address is formed. This applies to the binders
of `let`, of `match` and `case` arms, of `take` and of an extern's result word, to loop counters,
accumulators and loop-carried variables, and to a callee's one-word parameters. Anything else
stays in memory, which is always correct.

Values of slot-resident type are computed straight into their slots when every tail of the term
allows it, and through memory and loads otherwise. A `match` or `case` on a slot-resident value
tests the low byte of its first word and takes the payload from the words after it. A whole-word
field of a slot-resident structure is read and written as its slots. A call returns a result of
slot-resident type as words and passes one-word parameters in its argument list.


`lowerM e tm ρ n d` writes the value of `e` at offset `d`, which its caller allocated below the
watermark `n`. Both branches of a conditional write the same destination, so a join needs no copy.
A move is a copy, a word at a time and then the remaining bytes, and a literal is written as its
encoded bytes.

A place computes its address into `RA`: a variable's offset or the pointer it holds, plus field
offsets and `i * size` for an element. A reference is a pointer. A borrow stores the address of
its place in an 8-byte slot, reads and writes through the reference go to the place itself, and
nothing is copied when the borrow begins or ends. A slice is passed as the address of its first
element and its length, and a reference to the pair `p[i], p[j]` as the addresses of its two
elements.

In the value semantics, a borrow body or a callee hands back the final value of each `&mut`
reference, which is written back into the lender. The lowered code needs no write-back, because
the handed-back components must be the references themselves, so their bytes are already in
place. Only the result is written, which is what the tail mode `Tl` describes.

An extern call loads its word arguments into the slots from `REXT` and passes a slice of a byte
array as two words, its address and its length, so that the machine reads or writes the bytes in
place. A constructor copies each argument to its offset and writes the tag byte of a variant, and
`match` and `case` load the tag byte and compare it. `Result` is laid out as a sum with tag `0` for
an error and `1` for ok. A `Slots` cell has no tag, so `put` writes the cell and `take` copies it
out. A ghost has size `0`, so copying it emits no code. A constructor of at least `fillMin` bytes
that fills an array with a literal, or whose first argument is a variable in memory, writes those
bytes with a loop of 8-byte stores or copies instead of one store per word (`mkCode?`).

Each Core construct costs one tick, charged where `Exp.exec` charges it, so the Flat clock ends at
`exec`'s step count. The exceptions are the tick of a loop iteration, which is charged at the
start of the body when the condition holds and after the condition when it fails, and the loop of
a large constructor, whose iterations each charge the tick `words w` for the words they write while
the constructor's own tick charges the rest. Every path of
the linearized code that re-enters the body then passes a tick, which the instruction budget of
`select` relies on.


`Exp.memOk` decides the fragment that `lower` handles. It refuses the following constructs:

* a slice view used other than through its elements, except that it may be passed on whole by
  reference to a callee that uses it through its elements and, for `&mut`, hands it back with its
  occupancy unchanged;
* a slice of a non-contiguous place;
* `guard` on a place that cannot be checked at run time;
* `case` on a sum of more than 256 variants, since the tag is one byte;
* the pair `p[i], p[j]` under further selectors, and a reference to the pair used other than
  through its fields;
* a borrow body or callee whose handed-back values are not its references;
* a `&mut` slice borrow or callee whose body does not meet the hand-back condition `Exp.HB`;
* a reference call whose `&mut` argument goes through a `Slots` cell that an earlier argument on
  the same root may empty;
* a loop bound of `2^64` or more, an extern call with more than `FR - REXT` argument words, a slice
  of a non-contiguous array passed to an extern, and an extern call that writes a mutable slice
  together with another output buffer.
-/

namespace Millipede.Flat

/-- The Flat operation for a primitive, given one operand per argument: the tick, the operation
and its two operands. Booleans are the words `0` and `1`. -/
def primCode {ps : List Ty} {r : Ty} (p : Prim ps r) (as : List Operand) :
    Tick × BinOp × Operand × Operand :=
  let a := as.getD 0 (.imm 0)
  let b := as.getD 1 (.imm 0)
  match p with
  | .add => (.prim, .add, a, b)
  | .sub => (.prim, .sub, a, b)
  | .mul => (.prim, .mul, a, b)
  | .udiv => (.div, .udiv, a, b)
  | .umod => (.div, .umod, a, b)
  | .band => (.prim, .band, a, b)
  | .bor => (.prim, .bor, a, b)
  | .bxor => (.prim, .bxor, a, b)
  | .shl => (.prim, .shl, a, b)
  | .shr => (.prim, .shr, a, b)
  | .bnot => (.prim, .bxor, a, .imm 0xFFFFFFFFFFFFFFFF)
  | .eq => (.prim, .eq, a, b)
  | .ne => (.prim, .ne, a, b)
  | .ult => (.prim, .ult, a, b)
  | .ule => (.prim, .ule, a, b)
  | .ugt => (.prim, .ult, b, a)
  | .uge => (.prim, .ule, b, a)
  | .not => (.prim, .bxor, a, .imm 1)
  | .and => (.prim, .band, a, b)
  | .or => (.prim, .bor, a, b)
  | .beq => (.prim, .eq, a, b)
  | .zext8 => (.prim, .bor, a, .imm 0)
  | .trunc8 => (.prim, .band, a, .imm 0xFF)
  | .addNuw => (.prim, .add, a, b)
  | .subNuw => (.prim, .sub, a, b)
  | .mulNuw => (.prim, .mul, a, b)
  | .trunc8Nuw => (.prim, .band, a, .imm 0xFF)

/-! ## Registers and constants -/

/-- The frame slot that holds the activation's base pointer. -/
abbrev BP : Nat := 0
/-- The scratch slot that holds a place's address. -/
abbrev RA : Nat := 1
/-- The scratch slot that holds the second element's address of a two-element place. -/
abbrev RB : Nat := 2
/-- The scratch slot that holds a byte or word being copied. -/
abbrev RT : Nat := 3
/-- The scratch slots that hold the operands of an operation. -/
abbrev RX : Nat := 4
abbrev RY : Nat := 5
/-- The scratch slot that holds a variable's address while a referenced value is copied. -/
abbrev RP : Nat := 6
/-- The first of the scratch slots that hold an extern's word arguments. -/
abbrev REXT : Nat := 7
/-- The number of fixed slots at the start of every activation's frame. -/
abbrev FR : Nat := 16

/-- The memory width of a scalar of `size` bytes, `w8` for one byte and `w64` otherwise. -/
def scalarWidth (size : Nat) : Width := if size = 1 then .w8 else .w64

/-- The word a scalar literal stands for, which is its encoded bytes decoded as a word. -/
def litWord {t : Ty} (v : t.carrier) : UInt64 := decodeLE (Data.encodeBytes v)

/-! ## Slot-resident types -/

/-- The most frame slots that one slot-resident value takes. -/
abbrev SLOT_CAP : Nat := 4

/-- The type is a one-word scalar, a 64-bit word or a byte. Primitives take and return values of
these types. -/
def _root_.Millipede.Ty.wordTy (t : Ty) : Bool :=
  match t.data.shape with
  | .word .w64 => true
  | .word .w8 => true
  | _ => false

mutual
/-- The shape contains no array and no `Slots`. -/
def _root_.Millipede.Shape.flat : Shape → Bool
  | .word _ => true
  | .prod fs => Shape.flatL fs
  | .sum vs => Shape.flatL vs
  | .array _ _ => false
  | .slots _ _ => false
  | .ghost => true
/-- Every shape of the list is flat. -/
def _root_.Millipede.Shape.flatL : List Shape → Bool
  | [] => true
  | s :: ss => s.flat && Shape.flatL ss
end

/-- The number of 64-bit words that hold a value's bytes, which is `⌈size / 8⌉`. A slot-resident
value takes this many frame slots. -/
def _root_.Millipede.Ty.slotN (t : Ty) : Nat := (t.size + 7) / 8

/-- The type can be slot-resident: its shape is flat, its size is one byte or one to `SLOT_CAP`
whole words, and its word count is at most `Shape.words` of its shape. Chunk `j` of its bytes is bytes `8j` to
`8j + 7`, moved by a `w64` access, or the single byte of a one-byte type, moved by a `w8` access. -/
def _root_.Millipede.Ty.slotTy (t : Ty) : Bool :=
  t.data.shape.flat &&
    (t.size == 1 || (t.size % 8 == 0 && decide (0 < t.size) && decide (t.size ≤ 8 * SLOT_CAP))) &&
    decide (t.slotN ≤ t.data.shape.words)

/-- The payload is empty, or slot-resident and a whole number of words. -/
def _root_.Millipede.Ty.wordPay (p : Ty) : Bool := p.size == 0 || (p.slotTy && p.size % 8 == 0)

/-- A `Result ε α` that can be matched in frame slots. It is slot-resident, and its payloads are
whole words starting at the word after the tag, or both are empty. The tag is the low byte of the
first word. -/
def _root_.Millipede.Ty.slotSum (ε α : Ty) : Bool :=
  (Ty.result ε α).slotTy &&
    (payloadOff (Data.shape (Except ε.carrier α.carrier)) == 8 || (ε.size == 0 && α.size == 0)) &&
    ε.wordPay && α.wordPay

/-- The little-endian words of the first `n` 8-byte chunks of `B`. -/
def chunks (B : List UInt8) : Nat → List UInt64
  | 0 => []
  | n + 1 => decodeLE (B.take 8) :: chunks (B.drop 8) n

/-! ## Locations of variables -/

/-- Where a variable lives. `own o` holds its value at offset `o` from the base pointer, and
`ref o` holds the 8-byte address of its value at offset `o`, for a reference binder or parameter.
`ref2 o` holds two addresses at `o` and `o + 8`, those of the two elements of a borrowed pair
`p[i], p[j]`. `slot o k n` keeps the value in the `n` frame slots from `k`, as its bytes chunked
into little-endian words; the bytes from `o` that it would have had in memory are reserved but never
read or written. -/
inductive Loc where
  | own (o : Nat)
  | ref (o : Nat)
  | ref2 (o : Nat)
  | slot (o k n : Nat)
deriving DecidableEq, Repr

instance : Inhabited Loc := ⟨.own 0⟩

/-- The offset of a location's bytes in the activation's region. -/
def Loc.off : Loc → Nat
  | .own o => o
  | .ref o => o
  | .ref2 o => o
  | .slot o _ _ => o

/-- The size of a location's bytes: the value's size, or 8 or 16 bytes for one or two addresses. -/
def Loc.size (t : Ty) : Loc → Nat
  | .own _ => t.size
  | .ref _ => 8
  | .ref2 _ => 16
  | .slot _ _ _ => t.size

/-- The first frame slot of a slot-resident variable. -/
def Loc.slot? : Loc → Option Nat
  | .slot _ k _ => some k
  | _ => none

/-- The number of frame slots of a location, which is `0` unless it is slot-resident. -/
def Loc.nw : Loc → Nat
  | .slot _ _ n => n
  | _ => 0

/-- Frame slot `x` is one of the location's slots. -/
def Loc.holds (l : Loc) (x : Nat) : Bool :=
  match l with
  | .slot _ k n => decide (k ≤ x) && decide (x < k + n)
  | _ => false

/-- The variable is slot-resident. -/
def Loc.isSlot (l : Loc) : Bool := l.slot?.isSome

/-- The number of frame slots that the slot-resident variables of a context take, so the next one
starts at slot `FR + slotsIn ρ`. -/
def slotsIn : List Loc → Nat
  | [] => 0
  | l :: ρ => l.nw + slotsIn ρ

/-! ## Byte copies -/

/-- Copy `len` bytes from `sb + so` to `db + d` through `RT`, eight bytes at a time and then the
remaining bytes one at a time. The two ranges never overlap. -/
def copyB (sb : Operand) (so : Nat) (db : Operand) (d : Nat) : Nat → Stmt
  | 0 => .skip
  | len + 8 =>
    .seq (.load .w64 RT sb (UInt64.ofNat so))
      (.seq (.store .w64 db (UInt64.ofNat d) (.slot RT)) (copyB sb (so + 8) db (d + 8) len))
  | len + 1 =>
    .seq (.load .w8 RT sb (UInt64.ofNat so))
      (.seq (.store .w8 db (UInt64.ofNat d) (.slot RT)) (copyB sb (so + 1) db (d + 1) len))

/-- Write constant bytes at `db + d`, one at a time. -/
def writeB1 (db : Operand) (d : Nat) : List UInt8 → Stmt
  | [] => .skip
  | b :: bs => .seq (.store .w8 db (UInt64.ofNat d) (.imm b.toUInt64)) (writeB1 db (d + 1) bs)

/-- Write constant bytes at `db + d`, eight bytes at a time as one little-endian word and the
remaining bytes one at a time. -/
def writeB (db : Operand) (d : Nat) : List UInt8 → Stmt
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs =>
    .seq (.store .w64 db (UInt64.ofNat d) (.imm (decodeLE [b0, b1, b2, b3, b4, b5, b6, b7])))
      (writeB db (d + 8) bs)
  | [] => .skip
  | [b0] => writeB1 db d [b0]
  | [b0, b1] => writeB1 db d [b0, b1]
  | [b0, b1, b2] => writeB1 db d [b0, b1, b2]
  | [b0, b1, b2, b3] => writeB1 db d [b0, b1, b2, b3]
  | [b0, b1, b2, b3, b4] => writeB1 db d [b0, b1, b2, b3, b4]
  | [b0, b1, b2, b3, b4, b5] => writeB1 db d [b0, b1, b2, b3, b4, b5]
  | [b0, b1, b2, b3, b4, b5, b6] => writeB1 db d [b0, b1, b2, b3, b4, b5, b6]

/-- `n` copies of the bytes `B`, one after another. -/
abbrev reps (n : Nat) (B : List UInt8) : List UInt8 := (List.replicate n B).flatten

/-- The `while` part of `wordLoop`. -/
abbrev wordWhile (k w : Nat) (B : Stmt) : Stmt :=
  .while (.bin .ult RX (.slot RA) (.imm (UInt64.ofNat (8 * k)))) (.slot RX)
    (.seq (.tick (.words w))
      (.seq (.bin .add RB (.slot BP) (.slot RA)) (.seq B (.bin .add RA (.slot RA) (.imm 8)))))

/-- A loop over `k` words of the activation: the byte offset `8 j` counts up in `RA`, `RB` holds
the base pointer plus `8 j`, and each iteration charges the tick `words w` and runs `B`. -/
abbrev wordLoop (k w : Nat) (B : Stmt) : Stmt := .seq (.mov RA (.imm 0)) (wordWhile k w B)

/-- Store the word `P` at offsets `d, d + 8, …, d + 8 (k - 1)` from the base pointer, each
iteration charging `words w`. -/
abbrev fillLoop (d k : Nat) (P : UInt64) (w : Nat) : Stmt :=
  wordLoop k w (.store .w64 (.slot RB) (UInt64.ofNat d) (.imm P))

/-- Copy `k` words from offset `so` to offset `dd`, both from the base pointer, each iteration
charging `words w`. The two ranges do not overlap. -/
abbrev copyLoop (so dd k w : Nat) : Stmt :=
  wordLoop k w (.seq (.load .w64 RT (.slot RB) (UInt64.ofNat so))
    (.store .w64 (.slot RB) (UInt64.ofNat dd) (.slot RT)))

/-- Copy bytes within the activation, both offsets counted from the base pointer. -/
abbrev copyM (so d len : Nat) : Stmt := copyB (.slot BP) so (.slot BP) d len

/-- Load the address of a variable at location `l` into slot `x`. -/
def varAddr (l : Loc) (x : Nat) : Stmt :=
  match l with
  | .own o | .slot o _ _ => .bin .add x (.slot BP) (.imm (UInt64.ofNat o))
  | .ref o => .load .w64 x (.slot BP) (UInt64.ofNat o)
  | .ref2 o => .load .w64 x (.slot BP) (UInt64.ofNat o)

/-! ## Frame slots of slot-resident values -/

/-- Load `n` chunks of width `w` from `b + o, b + o + 8, …` into slots `k, k + 1, …`. -/
def ldSlots (w : Width) (k : Nat) (b : Operand) (o : Nat) : Nat → Stmt
  | 0 => .skip
  | n + 1 => .seq (.load w k b (UInt64.ofNat o)) (ldSlots w (k + 1) b (o + 8) n)

/-- Store `n` chunks of width `w` from slots `k, k + 1, …` at `b + o, b + o + 8, …`. -/
def stSlots (w : Width) (b : Operand) (o k : Nat) : Nat → Stmt
  | 0 => .skip
  | n + 1 => .seq (.store w b (UInt64.ofNat o) (.slot k)) (stSlots w b (o + 8) (k + 1) n)

/-- Copy the `n` slots from `k'` to the slots from `k`, in increasing order. -/
def movSlots (k k' : Nat) : Nat → Stmt
  | 0 => .skip
  | n + 1 => .seq (.mov k (.slot k')) (movSlots (k + 1) (k' + 1) n)

/-- Write the words `vs` to slots `k, k + 1, …`. -/
def immSlots (k : Nat) : List UInt64 → Stmt
  | [] => .skip
  | v :: vs => .seq (.mov k (.imm v)) (immSlots (k + 1) vs)

/-- Write the value of an atom at offset `d`. -/
def atomTo {Γ : List Ty} {t : Ty} : Atom Γ t → List Loc → Nat → Stmt
  | .var m, ρ, d =>
    match ρ.getD m.idx default with
    | .own o => copyM o d t.size
    | .ref o => .seq (.load .w64 RP (.slot BP) (UInt64.ofNat o)) (copyB (.slot RP) 0 (.slot BP) d t.size)
    | .ref2 o => .seq (.load .w64 RP (.slot BP) (UInt64.ofNat o)) (copyB (.slot RP) 0 (.slot BP) d t.size)
    | .slot _ k n => stSlots (scalarWidth t.size) (.slot BP) d k n
  | .lit v, _, d => writeB (.slot BP) d (Data.encodeBytes v)

/-- Load a one-word scalar atom, of type `U64`, `U8` or `Bool`, into slot `x` as a word. -/
def atomWord {Γ : List Ty} {t : Ty} : Atom Γ t → List Loc → Nat → Stmt
  | .var m, ρ, x =>
    match ρ.getD m.idx default with
    | .own o => .load (scalarWidth t.size) x (.slot BP) (UInt64.ofNat o)
    | .ref o => .seq (.load .w64 x (.slot BP) (UInt64.ofNat o)) (.load (scalarWidth t.size) x (.slot x) 0)
    | .ref2 o => .seq (.load .w64 x (.slot BP) (UInt64.ofNat o)) (.load (scalarWidth t.size) x (.slot x) 0)
    | .slot _ k _ => .mov x (.slot k)
  | .lit v, _, x => .mov x (.imm (litWord v))

/-- Load the words of an atom of slot-resident type into the `cnt` slots from `x`, from memory,
from its variable's slots, or from a literal. The caller passes `t.slotN` as `cnt`, which keeps
the frame bound of the code syntactic. -/
def atomSlots {Γ : List Ty} {t : Ty} : Atom Γ t → List Loc → Nat → Nat → Stmt
  | .var m, ρ, x, cnt =>
    match ρ.getD m.idx default with
    | .own o => ldSlots (scalarWidth t.size) x (.slot BP) o cnt
    | .ref o => .seq (.load .w64 RP (.slot BP) (UInt64.ofNat o))
        (ldSlots (scalarWidth t.size) x (.slot RP) 0 cnt)
    | .ref2 o => .seq (.load .w64 RP (.slot BP) (UInt64.ofNat o))
        (ldSlots (scalarWidth t.size) x (.slot RP) 0 cnt)
    | .slot _ k n => movSlots x k (min n cnt)
  | .lit v, _, x, cnt => immSlots x (chunks (Data.encodeBytes v) cnt)

/-- The first frame slot of an atom that is a slot-resident variable. -/
def _root_.Millipede.Atom.slotOf {Γ : List Ty} {t : Ty} (a : Atom Γ t) (ρ : List Loc) : Option Nat :=
  match a with
  | .var m => (ρ.getD m.idx default).slot?
  | .lit _ => none

/-- The number of frame slots of an atom's variable, which is `0` for a literal or a variable in
memory. -/
def _root_.Millipede.Atom.slotNw {Γ : List Ty} {t : Ty} (a : Atom Γ t) (ρ : List Loc) : Nat :=
  match a with
  | .var m => (ρ.getD m.idx default).nw
  | .lit _ => 0

/-- Copy an atom's words to the slots from `x`. When its variable's slots straddle `x` from below,
the copy goes through the scratch slots from `REXT`, because a forward copy would overwrite its
later words before reading them. -/
def atomSlotsS {Γ : List Ty} {t : Ty} (a : Atom Γ t) (ρ : List Loc) (x cnt : Nat) : Stmt :=
  match a.slotOf ρ with
  | some k => if x ≤ k ∨ k + cnt ≤ x then atomSlots a ρ x cnt
      else .seq (atomSlots a ρ REXT cnt) (movSlots x REXT cnt)
  | none => atomSlots a ρ x cnt

/-! ## Layout helpers -/

/-- The offset of the field that a lens selects in its structure's shape. -/
def lensOff {s t : Ty} (l : Lens s t) : Nat :=
  match s.data.shape with
  | .prod fs => Shape.fieldOffset fs l.index
  | _ => 0

/-- The offsets of values of the types `ps` laid out one after another from `o`. -/
def paramOffs : List Ty → Nat → List Nat
  | [], _ => []
  | t :: ts, o => o :: paramOffs ts (o + t.size)

/-- The size of values of the types `ps` laid out one after another. -/
def ctxSize : List Ty → Nat
  | [] => 0
  | t :: ts => t.size + ctxSize ts

/-- The plan of a constructor: one list of offsets per argument, and the tag it writes when it
builds a variant. The offsets come from the target type's shape, and an argument of a `fill` is
copied to every element. -/
def _root_.Millipede.Ctor.plan {ps : List Ty} {t : Ty} (c : Ctor ps t) : List (List Nat) × Option Nat :=
  planOf ps t c.kind

/-- The rest mode of a split, from the shapes. -/
def _root_.Millipede.Split.mode {t p q : Ty} (_sp : Split t p q) : RestMode :=
  match t.data.shape, q.data.shape with
  | .sum vs, .sum vs' => if vs.length ≤ 2 then .payload
      else if vs'.length = vs.length then .whole
      else .retag (Shape.payloadOffset vs') (Shape.sizeMax vs')
  | _, _ => .payload

/-- A `case` that can be taken apart in frame slots. The scrutinee is slot-resident, and the
tested variant's payload and the rest are each empty or whole words starting at the word after the
tag. The rest is either the other payload or the whole value; a renumbered rest is built in
memory instead. The tag is the low byte of the first word. -/
def _root_.Millipede.Split.slotOk {t p q : Ty} (sp : Split t p q) : Bool :=
  t.slotTy && p.wordPay && (p.size == 0 || payloadOff t.data.shape == 8) &&
    match sp.mode with
    | .payload => q.wordPay && (q.size == 0 || payloadOff t.data.shape == 8)
    | .whole => q.slotTy
    | .retag _ _ => false

/-- The slot of a slot-resident scrutinee at which a `case`'s rest starts: the first slot when
the rest is the whole value, the slot after the tag when it is the other payload. -/
def _root_.Millipede.Split.restOff {t p q : Ty} (sp : Split t p q) : Nat :=
  if sp.mode = .whole then 0 else 1

/-! ## Places -/

/-- `RA := RA + i * size`, the address of element `i` of the array or `Slots` at `RA`. -/
def elemAddr {Γ : List Ty} (i : Atom Γ .u64) (ρ : List Loc) (size : Nat) : Stmt :=
  .seq (atomWord i ρ RX)
    (.seq (.bin .mul RX (.slot RX) (.imm (UInt64.ofNat size))) (.bin .add RA (.slot RA) (.slot RX)))

/-- After code `b` that puts a base address in `RA`, put the address of element `i` in `RA` and
that of element `j` in `RB`, for the pair `p[i], p[j]`. -/
def pairAddrCode {Γ : List Ty} (b : Stmt) (i j : Atom Γ .u64) (ρ : List Loc) (size : Nat) : Stmt :=
  .seq b (.seq (.mov RB (.slot RA)) (.seq (elemAddr i ρ size)
    (.seq (atomWord j ρ RX) (.seq (.bin .mul RX (.slot RX) (.imm (UInt64.ofNat size)))
      (.bin .add RB (.slot RB) (.slot RX))))))

/-- Store the two addresses in `RA`, `RB` at offsets `n`, `n + 8`. -/
def pairStore (n : Nat) : Stmt :=
  .seq (.store .w64 (.slot BP) (UInt64.ofNat n) (.slot RA))
    (.store .w64 (.slot BP) (UInt64.ofNat (n + 8)) (.slot RB))

/-- Store the address in `RA` and the length `len` at offsets `n` and `n + 8`, as a slice. -/
def sliceStore {Γ : List Ty} (len : Atom Γ .u64) (ρ : List Loc) (n : Nat) : Stmt :=
  .seq (.store .w64 (.slot BP) (UInt64.ofNat n) (.slot RA))
    (.seq (atomWord len ρ RX) (.store .w64 (.slot BP) (UInt64.ofNat (n + 8)) (.slot RX)))

/-- The slot of a place that is a variable at a two-address location `Loc.ref2`. -/
def _root_.Millipede.Place.loc2 {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc) : Option Nat :=
  match p with
  | .var m =>
    match ρ.getD m.idx default with
    | .ref2 o => some o
    | _ => none
  | _ => none

/-- Compute the address of a place into `RA`. For a slice this is the address of its first
element, and for the pair `p[i], p[j]` the address of element `i` goes into `RA` and that of
element `j` into `RB`. A field of a variable at a `Loc.ref2` location is the address its slot holds
for that field. -/
def placeAddr {Γ : List Ty} : {t : Ty} → Place Γ t → List Loc → Stmt
  | _, .var m, ρ => varAddr (ρ.getD m.idx default) RA
  | _, .field p l, ρ =>
    match p.loc2 ρ with
    | some o => .load .w64 RA (.slot BP) (UInt64.ofNat (if l.index = 0 then o else o + 8))
    | none => .seq (placeAddr p ρ) (.bin .add RA (.slot RA) (.imm (UInt64.ofNat (lensOff l))))
  | _, .index (t := t) (dflt := _) p i, ρ => .seq (placeAddr p ρ) (elemAddr i ρ t.size)
  | _, .slot (t := t) (dflt := _) p i, ρ => .seq (placeAddr p ρ) (elemAddr i ρ t.size)
  | _, .range (t := t) p lo _, ρ => .seq (placeAddr p ρ) (elemAddr lo ρ t.size)
  | _, .pair2 (t := t) (dflt := _) p i j, ρ => pairAddrCode (placeAddr p ρ) i j ρ t.size
  | _, .rangeS (t := t) m lo _, ρ => .seq (varAddr (ρ.getD m.idx default) RA) (elemAddr lo ρ t.size)
  | _, .pair2S (t := t) (dflt := _) m i j, ρ =>
    pairAddrCode (varAddr (ρ.getD m.idx default) RA) i j ρ t.size

/-- The size of the slot that a borrow of a place, or a reference argument for it, takes: one
address, or two words for a slice, which is an address and a length, and for the pair
`p[i], p[j]`, which is two addresses. -/
def _root_.Millipede.Place.slotW {Γ : List Ty} : {t : Ty} → Place Γ t → Nat
  | _, .range _ _ _ => 16
  | _, .pair2 (dflt := _) _ _ _ => 16
  | _, .rangeS _ _ _ => 16
  | _, .pair2S (dflt := _) _ _ _ => 16
  | _, _ => 8

/-- Store the reference to a place, whose address is in `RA`, at offset `n`. A slice also stores its
length at `n + 8`, and the pair `p[i], p[j]` the address of element `j` from `RB`. -/
def refStore {Γ : List Ty} : {t : Ty} → Place Γ t → List Loc → Nat → Stmt
  | _, .range _ _ len, ρ, n => sliceStore len ρ n
  | _, .pair2 (dflt := _) _ _ _, _, n => pairStore n
  | _, .rangeS _ _ len, ρ, n => sliceStore len ρ n
  | _, .pair2S (dflt := _) _ _ _, _, n => pairStore n
  | _, _, _, n => .store .w64 (.slot BP) (UInt64.ofNat n) (.slot RA)

/-- The location of a reference binder or parameter for a place whose slot is at `o`: two
addresses for the pair `p[i], p[j]`, one otherwise. -/
def _root_.Millipede.Place.refLoc {Γ : List Ty} {t : Ty} (p : Place Γ t) (o : Nat) : Loc :=
  match p with
  | .pair2 (dflt := _) _ _ _ => .ref2 o
  | .pair2S (dflt := _) _ _ _ => .ref2 o
  | _ => .ref o

/-- The place is the pair of elements `p[i], p[j]`. -/
def _root_.Millipede.Place.isPair2 {Γ : List Ty} : {t : Ty} → Place Γ t → Bool
  | _, .pair2 (dflt := _) _ _ _ => true
  | _, .pair2S (dflt := _) _ _ _ => true
  | _, _ => false

/-- The place is a slice. -/
def _root_.Millipede.Place.isRange {Γ : List Ty} : {t : Ty} → Place Γ t → Bool
  | _, .range _ _ _ => true
  | _, .rangeS _ _ _ => true
  | _, _ => false


/-- The place is contiguous: it has no slice selector and is not a pair of two elements. -/
def _root_.Millipede.Place.contig {Γ : List Ty} : {t : Ty} → Place Γ t → Bool
  | _, .var _ => true
  | _, .field p _ => p.contig
  | _, .index (dflt := _) p _ => p.contig
  | _, .slot (dflt := _) p _ => p.contig
  | _, _ => false

/-- The place can be borrowed by one address: it is contiguous, or a slice of a contiguous place. -/
def _root_.Millipede.Place.borrowOk {Γ : List Ty} : {t : Ty} → Place Γ t → Bool
  | _, .range p _ _ => p.contig
  | _, .rangeS _ _ _ => true
  | _, p => p.contig

/-- The place can be borrowed by reference: it is contiguous, a slice of a contiguous place, or
the pair `p[i], p[j]` of a contiguous `p`. -/
def _root_.Millipede.Place.refOk {Γ : List Ty} {t : Ty} (p : Place Γ t) : Bool :=
  match p with
  | .pair2 (dflt := _) q _ _ => q.contig
  | .pair2S (dflt := _) _ _ _ => true
  | p => p.borrowOk

/-- The place can be lowered: it is contiguous, or the pair `p[i], p[j]` of a contiguous `p`. -/
def _root_.Millipede.Place.memOk {Γ : List Ty} : {t : Ty} → Place Γ t → Bool
  | _, .pair2 (dflt := _) p _ _ => p.contig
  | _, p => p.contig

/-- Copy the value of a place to offset `d`. -/
def placeRead {Γ : List Ty} : {t : Ty} → Place Γ t → List Loc → Nat → Stmt
  | _, .pair2 (t := t) (dflt := _) p i j, ρ, d =>
    .seq (placeAddr p ρ) (.seq (.mov RB (.slot RA))
      (.seq (atomWord i ρ RX) (.seq (.bin .mul RX (.slot RX) (.imm (UInt64.ofNat t.size)))
      (.seq (.bin .add RA (.slot RA) (.slot RX))
      (.seq (copyB (.slot RA) 0 (.slot BP) d t.size)
      (.seq (atomWord j ρ RX) (.seq (.bin .mul RX (.slot RX) (.imm (UInt64.ofNat t.size)))
      (.seq (.bin .add RB (.slot RB) (.slot RX))
        (copyB (.slot RB) 0 (.slot BP) (d + fieldOff (Data.shape (t.carrier × t.carrier)) 1) t.size)))))))))
  | t, p, ρ, d => .seq (placeAddr p ρ) (copyB (.slot RA) 0 (.slot BP) d t.size)

/-- Copy the value at offset `src` into a place. For `p[i], p[j]` both element addresses are
computed before either element is written, because an index variable may live inside the array's
root variable, and Core evaluates both indices before the update. -/
def placeWrite {Γ : List Ty} : {t : Ty} → Place Γ t → List Loc → Nat → Stmt
  | _, .pair2 (t := t) (dflt := _) p i j, ρ, src =>
    .seq (placeAddr p ρ) (.seq (.mov RB (.slot RA))
      (.seq (atomWord i ρ RX) (.seq (.bin .mul RX (.slot RX) (.imm (UInt64.ofNat t.size)))
      (.seq (.bin .add RA (.slot RA) (.slot RX))
      (.seq (atomWord j ρ RX) (.seq (.bin .mul RX (.slot RX) (.imm (UInt64.ofNat t.size)))
      (.seq (.bin .add RB (.slot RB) (.slot RX))
      (.seq (copyB (.slot BP) src (.slot RA) 0 t.size)
        (copyB (.slot BP) (src + fieldOff (Data.shape (t.carrier × t.carrier)) 1) (.slot RB) 0 t.size)))))))))
  | t, p, ρ, src => .seq (placeAddr p ρ) (copyB (.slot BP) src (.slot RA) 0 t.size)

/-- Compute `Place.check` into `RY` as `1` or `0`. The result is `none` when a selector cannot be
checked at run time, such as a `Slots` cell, which has no tag, or when an array's length does not
fit a word. -/
def placeCheck {Γ : List Ty} : {t : Ty} → Place Γ t → List Loc → Option Stmt
  | _, .var _, _ => some (.mov RY (.imm 1))
  | _, .field p _, ρ => placeCheck p ρ
  | _, .index (n := n) (dflt := _) p i, ρ =>
    if n < UInt64.size then (placeCheck p ρ).map fun c =>
    .seq c (.seq (atomWord i ρ RX) (.seq (.bin .ult RX (.slot RX) (.imm (UInt64.ofNat n)))
      (.bin .band RY (.slot RY) (.slot RX))))
    else none
  | _, .pair2 (n := n) (dflt := _) p i j, ρ =>
    if n < UInt64.size then (placeCheck p ρ).map fun c =>
    .seq c (.seq (atomWord i ρ RX) (.seq (.bin .ult RX (.slot RX) (.imm (UInt64.ofNat n)))
      (.seq (.bin .band RY (.slot RY) (.slot RX))
      (.seq (atomWord j ρ RX) (.seq (.bin .ult RX (.slot RX) (.imm (UInt64.ofNat n)))
      (.seq (.bin .band RY (.slot RY) (.slot RX))
      (.seq (atomWord i ρ RX) (.seq (atomWord j ρ RT) (.seq (.bin .ne RX (.slot RX) (.slot RT))
        (.bin .band RY (.slot RY) (.slot RX)))))))))))
    else none
  | _, .range (n := n) p lo len, ρ =>
    -- `lo + len ≤ n` without overflow: `lo ≤ n` and `len ≤ n - lo`
    if n < UInt64.size then (placeCheck p ρ).map fun c =>
    .seq c (.seq (atomWord lo ρ RX) (.seq (.bin .ule RT (.slot RX) (.imm (UInt64.ofNat n)))
      (.seq (.bin .band RY (.slot RY) (.slot RT))
      (.seq (.bin .sub RX (.imm (UInt64.ofNat n)) (.slot RX))
      (.seq (atomWord len ρ RT) (.seq (.bin .ule RX (.slot RT) (.slot RX))
        (.bin .band RY (.slot RY) (.slot RX))))))))
    else none
  | _, _, _ => none

/-! ## Extern arguments -/

/-- Load the arguments of an extern call into `REXT, REXT + 1, …` and build its argument list. A
word takes one slot, and a slice `a[lo..lo+len]` takes two, the address of element `lo` and the
length. -/
def extArgs {Γ : List Ty} : {ps : List ExtParam} → EArgs Γ ps → List Loc → Nat → Stmt × List ExtArg
  | _, .nil, _, _ => (.skip, [])
  | _, .word a as, ρ, x =>
    let r := extArgs as ρ (x + 1)
    (.seq (atomWord a ρ x) r.1, .word (.slot x) :: r.2)
  | _, .bufIn (.const bs) as, ρ, x =>
    let r := extArgs as ρ x
    (r.1, .bytes bs :: r.2)
  | _, .bufIn (.slice a lo len) as, ρ, x =>
    let r := extArgs as ρ (x + 2)
    (.seq (sliceArg a lo len ρ x) r.1, .mem (.slot x) (.slot (x + 1)) :: r.2)
  | _, .bufOut (cap := c) as, ρ, x =>
    let r := extArgs as ρ x
    (r.1, .out c :: r.2)
  | _, .sliceOut a lo cap as, ρ, x =>
    let r := extArgs as ρ (x + 2)
    (.seq (sliceArg a lo cap ρ x) r.1, .outMem (.slot x) (.slot (x + 1)) :: r.2)
where
  /-- The address of element `lo` of the byte array `a` into slot `x`, and the length into
  `x + 1`. -/
  sliceArg {n : Nat} (a : Place Γ (.arr .u8 n)) (lo len : Atom Γ .u64) (ρ : List Loc) (x : Nat) :
      Stmt :=
    .seq (placeAddr (.range a lo len) ρ) (.seq (.mov x (.slot RA)) (atomWord len ρ (x + 1)))

/-- The number of argument slots of an extern call, where a slice takes two. -/
def _root_.Millipede.EArgs.wordCount {Γ : List Ty} : {ps : List ExtParam} → EArgs Γ ps → Nat
  | _, .nil => 0
  | _, .word _ as => as.wordCount + 1
  | _, .bufIn (.const _) as => as.wordCount
  | _, .bufIn (.slice _ _ _) as => as.wordCount + 2
  | _, .bufOut as => as.wordCount
  | _, .sliceOut _ _ _ as => as.wordCount + 2

/-- The array places of the slices can be lowered, so each is contiguous. -/
def _root_.Millipede.EArgs.memOk {Γ : List Ty} : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => true
  | _, .word _ as => as.memOk
  | _, .bufIn (.const _) as => as.memOk
  | _, .bufIn (.slice a _ _) as => a.contig && as.memOk
  | _, .bufOut as => as.memOk
  | _, .sliceOut a _ _ as => a.contig && as.memOk

/-- The call has no `bufOut` output buffer. -/
def _root_.Millipede.EArgs.noBufOut {Γ : List Ty} : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => true
  | _, .word _ as => as.noBufOut
  | _, .bufIn _ as => as.noBufOut
  | _, .bufOut _ => false
  | _, .sliceOut _ _ _ as => as.noBufOut

/-- The only output buffer is one mutable slice, into which the machine writes the reply's bytes. -/
def _root_.Millipede.EArgs.oneOut {Γ : List Ty} : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => false
  | _, .word _ as => as.oneOut
  | _, .bufIn _ as => as.oneOut
  | _, .bufOut _ => false
  | _, .sliceOut _ _ _ as => as.noOut && as.noBufOut

/-! ## Constructors and calls -/

/-- Copy each argument atom to its offsets, counted from `d`. -/
def argsTo {Γ : List Ty} : {ps : List Ty} → Args Γ ps → List (List Nat) → List Loc → Nat → Stmt
  | _, .nil, _, _, _ => .skip
  | _, .cons _ as, [], ρ, d => argsTo as [] ρ d
  | _, .cons a as, os :: oss, ρ, d =>
    .seq (os.foldr (fun o c => .seq (atomTo a ρ (d + o)) c) .skip) (argsTo as oss ρ d)

/-- The smallest constructed value, in bytes, that a fill loop writes. -/
abbrev fillMin : Nat := 64

/-- The code of a constructor that fills an array of `n` elements of `s` bytes with a literal `B`,
written at `d` by a loop, or `none` when the constructor is not such a fill. The element size
divides 8, the elements are `s` bytes apart and fill the whole value, which is at least `fillMin`
bytes and below `2^64`. The loop stores the word of `8 / s` elements `k = n s / 8` times, each iteration paying
`w = 8 / s` elements' words, the bytes after the last full word are stored one word or byte at a
time, and the constructor's tick pays the rest of its charge `W`. -/
def fillCode? {Γ ps : List Ty} {t : Ty} (c : Ctor ps t) (args : Args Γ ps) (d W : Nat) :
    Option Stmt :=
  match args with
  | .nil => none
  | .cons (t := e) a _ =>
    match a with
    | .var _ => none
    | .lit v =>
      let B := Data.encodeBytes v
      let s := B.length
      match c.plan with
      | ([os], none) =>
        let n := os.length
        let k := n * s / 8
        let w := 8 / s * e.data.shape.words
        if 0 < s ∧ 8 % s = 0 ∧ os = (List.range n).map (· * s) ∧ t.size = n * s ∧
            fillMin ≤ n * s ∧ k * w ≤ W ∧ n * s < UInt64.size then
          some (.seq (.tick (.ctor (W - k * w))) (.seq (fillLoop d k (decodeLE (reps (8 / s) B)) w)
            (writeB (.slot BP) (d + 8 * k) (reps (n - k * (8 / s)) B))))
        else none
      | _ => none

/-- The first argument that is a variable in the activation's memory, placed once, of at least
`fillMin` bytes, a multiple of 8 and below `2^64`: its index, its variable's offset, its offset in
the constructed value and its size. -/
def bigVar? {Γ : List Ty} : {ps : List Ty} → Args Γ ps → List (List Nat) → List Loc →
    Option (Nat × Nat × Nat × Nat)
  | _, .nil, _, _ => none
  | _, .cons _ _, [], _ => none
  | _, .cons (t := e) a as, os :: oss, ρ =>
    let here : Option (Nat × Nat × Nat × Nat) :=
      match a, os with
      | .var m, [o1] =>
        match ρ.getD m.idx default with
        | .own o =>
          if e.size % 8 = 0 ∧ fillMin ≤ e.size ∧ e.size < UInt64.size then some (0, o, o1, e.size)
          else none
        | _ => none
      | _, _ => none
    match here with
    | some r => some r
    | none => (bigVar? as oss ρ).map fun (j, o, o1, sz) => (j + 1, o, o1, sz)

/-- The code of a constructor with a large argument found by `bigVar?`: a loop copies its `k`
words, each iteration paying one word, and `argsTo` copies the other arguments. The constructor's
tick pays the rest of its charge `W`. It is `none` for any other constructor. -/
def copyCode? {Γ ps : List Ty} {t : Ty} (c : Ctor ps t) (args : Args Γ ps) (ρ : List Loc)
    (d W : Nat) : Option Stmt :=
  match c.plan with
  | (oss, none) =>
    match bigVar? args oss ρ with
    | some (j, o, o1, sz) =>
      if sz / 8 * 1 ≤ W then
        some (.seq (.tick (.ctor (W - sz / 8 * 1)))
          (.seq (copyLoop o (d + o1) (sz / 8) 1) (argsTo args (oss.set j []) ρ d)))
      else none
    | none => none
  | _ => none

/-- The loop code of a large constructor, a fill or a copy, or `none`. -/
def mkCode? {Γ ps : List Ty} {t : Ty} (c : Ctor ps t) (args : Args Γ ps) (ρ : List Loc)
    (d W : Nat) : Option Stmt :=
  match fillCode? c args d W with
  | some s => some s
  | none => copyCode? c args ρ d W

/-- Pass the arguments of a call, parameter number `j` first. A word parameter's word goes into
the scratch slot `REXT + j`, and any other argument is copied to its offset from `d` in the
callee's region. -/
def argsPass {Γ : List Ty} (wp : Nat → Bool) : {ps : List Ty} → Args Γ ps → List Loc → Nat → Nat →
    Stmt
  | _, .nil, _, _, _ => .skip
  | _, .cons (t := t) a as, ρ, d, j =>
    .seq (if wp j then atomWord a ρ (REXT + j) else atomTo a ρ d) (argsPass wp as ρ (d + t.size) (j + 1))

/-- The locations of a callee's parameters, number `j` first, from offset `o`. A word parameter
lives in a slot of the callee's frame, numbered as `SlotsOk` requires so that the last one gets
`FR`, and any other at its offset. -/
def paramLocs (wp : Nat → Bool) : List Ty → Nat → Nat → List Loc
  | [], _, _ => []
  | t :: ts, o, j =>
    let rest := paramLocs wp ts (o + t.size) (j + 1)
    (if wp j then .slot o (FR + slotsIn rest) 1 else .own o) :: rest

/-- The words of a call's word parameters, last parameter first, with parameter `j`'s word in
scratch slot `REXT + j`. They become the callee's frame slots `FR, FR + 1, …`. -/
def paramWords (wp : Nat → Bool) : List Ty → Nat → List Operand
  | [], _ => []
  | _ :: ts, j => paramWords wp ts (j + 1) ++ (if wp j then [.slot (REXT + j)] else [])

/-- The argument words of a call: the callee's base pointer in `RX`, the scratch slots, and then
its word parameters' words. -/
def callOps (wp : Nat → Bool) (ps : List Ty) : List Operand :=
  .slot RX :: (List.replicate (FR - 1) (.imm 0) ++ paramWords wp ps 0)

/-- The callee's locations of a reference call's parameters, from offset `o`. An owned argument is
copied into the callee's region, and a reference argument is its place's address, or for a slice
its address and length. -/
def _root_.Millipede.RArgs.locs {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Nat → List Loc
  | _, _, .nil, _ => []
  | _, _, .own (t := t) _ as, o => .own o :: as.locs (o + t.size)
  | _, _, .shr p as, o => p.refLoc o :: as.locs (o + p.slotW)
  | _, _, .mut p as, o => p.refLoc o :: as.locs (o + p.slotW)

/-- The size of the parameters of a reference call. -/
def _root_.Millipede.RArgs.frame {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Nat
  | _, _, .nil => 0
  | _, _, .own (t := t) _ as => t.size + as.frame
  | _, _, .shr p as => p.slotW + as.frame
  | _, _, .mut p as => p.slotW + as.frame

/-- Pass a reference call's arguments at offsets from `d`. Owned atoms are copied, and for each
`&` or `&mut` argument the reference to its place is stored, so the referenced value is not
copied. -/
def rargsPass {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → List Loc → Nat → Stmt
  | _, _, .nil, _, _ => .skip
  | _, _, .own (t := t) a as, ρ, d => .seq (atomTo a ρ d) (rargsPass as ρ (d + t.size))
  | _, _, .shr p as, ρ, d =>
    .seq (.seq (placeAddr p ρ) (refStore p ρ d)) (rargsPass as ρ (d + p.slotW))
  | _, _, .mut p as, ρ, d =>
    .seq (.seq (placeAddr p ρ) (refStore p ρ d)) (rargsPass as ρ (d + p.slotW))

/-- The parameter numbers of the `&mut` arguments, counted from `i`. -/
def _root_.Millipede.RArgs.mutIdx {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Nat → List Nat
  | _, _, .nil, _ => []
  | _, _, .own _ as, i => as.mutIdx (i + 1)
  | _, _, .shr _ as, i => as.mutIdx (i + 1)
  | _, _, .mut _ as, i => i :: as.mutIdx (i + 1)

/-! ## Tail modes: handing back references in place -/

/-- How a term delivers its value, which is its tail mode:
* `none` writes it at the destination;
* `whole x` says the value is variable `x`'s, in place, so nothing is written;
* `split f0 cs` writes the value's first `f0` bytes, its first component, at the destination, and
  each `(x, off, sz)` in `cs` says that the `sz` bytes at offset `off` of the value are variable
  `x`'s, in place;
* `word k` says the value, of slot-resident type, is in the frame slots from `k`, and nothing is
  written to memory. -/
inductive Tl where
  | none
  | whole (x : Nat)
  | split (f0 : Nat) (cs : List (Nat × Nat × Nat))
  | word (k : Nat)
deriving DecidableEq, Repr

/-- The tail mode under one more binder. -/
def Tl.up : Tl → Tl
  | .none => .none
  | .whole x => .whole (x + 1)
  | .split f0 cs => .split f0 (cs.map fun c => (c.1 + 1, c.2))
  | .word k => .word k

/-- The bytes that a term in tail mode `tm` writes at its destination. -/
def Tl.dsz (t : Ty) : Tl → Nat
  | .none => t.size
  | .whole _ => 0
  | .split f0 _ => f0
  | .word _ => 0

/-- The cost mode of a tail mode: what its tails are charged for copying (`Hb`). A `split` mode
with no in-place component writes the whole value, as `none` does. -/
def Tl.hb : Tl → Hb
  | .whole x => .whole x
  | .split _ [] => .copy
  | .split _ (_ :: _) => .split
  | _ => .copy

@[simp] theorem Tl.hb_none : Tl.none.hb = .copy := rfl
@[simp] theorem Tl.hb_word (k : Nat) : (Tl.word k).hb = .copy := rfl
@[simp] theorem Tl.hb_whole (x : Nat) : (Tl.whole x).hb = .whole x := rfl

theorem Tl.hb_up (tm : Tl) : tm.up.hb = tm.hb.up := by
  cases tm with
  | split f0 cs => cases cs <;> rfl
  | _ => rfl

/-- The operands of the `n` frame slots from `k`, with which a callee returns its result as words. -/
def retSlots (k n : Nat) : List Operand := (List.range n).map fun j => .slot (k + j)

/-- The in-place components that a tail mode expects of a callee with reference parameters `args`
returning `r`: its `&mut` parameters, at their offsets in the handed-back tuple. -/
def _root_.Millipede.RArgs.comps {Γ : List Ty} {ps os : List Ty} (r : Ty) (as : RArgs Γ ps os) :
    List (Nat × Nat × Nat) :=
  (as.mutIdx 0).zip ((tupOffs os (fieldOff (Data.shape (r.carrier × (Ty.tup os).carrier)) 1)).zip
    (os.map Ty.size))

/-- The in-place components of a loop body's handed-back value: the carried variables, shifted by
two for the counter and the accumulator, at their offsets in `pair s (tup ts)`. -/
def _root_.Millipede.Carry.comps {Γ ts : List Ty} (s : Ty) (cs : Carry Γ ts) :
    List (Nat × Nat × Nat) :=
  (cs.idxs.map (· + 2)).zip ((tupOffs ts (fieldOff (Data.shape (s.carrier × (Ty.tup ts).carrier)) 1)).zip
    (ts.map Ty.size))

/-- The carried variables after the first occurrence of variable `i`, whose components are handed
back after `i`'s. -/
def _root_.Millipede.Carry.after {Γ : List Ty} (i : Nat) : {ts : List Ty} → Carry Γ ts → List Nat
  | _, .nil => []
  | _, .cons m cs => if m.idx = i then cs.idxs else cs.after i

/-- The atoms are the variables `xs`, in order. -/
def _root_.Millipede.Args.areVars {Γ : List Ty} : {ps : List Ty} → Args Γ ps → List Nat → Bool
  | _, .nil, [] => true
  | _, .cons (.var m) as, x :: xs => m.idx == x && as.areVars xs
  | _, _, _ => false

/-- The sizes of the types. -/
def tySizes (ps : List Ty) : List Nat := ps.map Ty.size

/-- The arguments' words fill the `n` words of the value in order. Each argument, of a type in
`ps` placed at its offset in `oss`, is empty, or slot-resident at a multiple of 8 bytes with its
words from word `lo` on, after the previous argument's or the tag's, and below `n`. -/
def wordsFit : List Ty → List (List Nat) → Nat → Nat → Bool
  | [], [], _, _ => true
  | p :: ps, [o] :: oss, lo, n =>
    if p.size = 0 then wordsFit ps oss lo n
    else p.slotTy && o % 8 == 0 && decide (lo ≤ o / 8) && decide (o / 8 + p.slotN ≤ n) &&
      wordsFit ps oss (o / 8 + p.slotN) n
  | _, _, _, _ => false

/-- A constructor that can be computed into frame slots. The value is slot-resident, the
arguments' words fit in order after the tag word, and a one-byte value is its tag or its one
argument, so that its word is the zero-extended byte. -/
def _root_.Millipede.Ctor.slotOk {ps : List Ty} {t : Ty} (c : Ctor ps t) : Bool :=
  t.slotTy && wordsFit ps c.plan.1 (if c.plan.2.isSome then 1 else 0) t.slotN &&
    (t.size % 8 == 0 || c.plan.2.isSome || tySizes ps == [t.size])

/-- The term can be delivered in tail mode `tm`. In a mode other than `none`, every tail of the
term is `atom (var x)` for `whole x`; a constructor whose first argument is the fresh component and
whose other arguments are the in-place variables at their offsets for `split`; and for `word k` a
slot-resident atom, primitive, contiguous place read, extern call, call, or constructor of
whole-word arguments. The tails are reached through `let`, `if`, `match`, `case`, assignments,
`put`, `take`, borrows and calls. -/
def _root_.Millipede.Exp.Conf : {Γ : List Ty} → {t : Ty} → Exp Γ t → Tl → Bool
  | _, _, _, .none => true
  | _, _, .atom (.var m), .whole x => m.idx == x
  | _, _, .atom (t := t) _, .word _ => t.slotTy
  | _, _, .prim _ _, .word _ => true
  | _, _, .read (t := t) p, .word _ => p.contig && t.slotTy
  | _, _, .ext _ _, .word _ => true
  | _, _, .call (r := r) _ _ _, .word _ => r.slotTy
  | _, _, .ok (ε := ε) (α := α) _, .word _ => Ty.slotSum ε α
  | _, _, .err (ε := ε) (α := α) _, .word _ => Ty.slotSum ε α
  | _, _, .mk (ps := ps) c args, .split f0 cs =>
    match ps, args with
    | p0 :: ps', .cons _ rest =>
      decide (c.plan.2 = none) && decide (p0.size = f0) &&
        decide (c.plan.1 = [0] :: cs.map fun c => [c.2.1]) &&
        rest.areVars (cs.map (·.1)) && decide (tySizes ps' = cs.map (·.2.2))
    | _, _ => false
  | _, _, .mk c _, .word _ => c.slotOk
  | _, _, .let_ _ e₂, tm => e₂.Conf tm.up
  | _, _, .ite _ e₁ e₂, tm => e₁.Conf tm && e₂.Conf tm
  | _, _, .match_ _ eE eO, tm => eE.Conf tm.up && eO.Conf tm.up
  | _, _, .assign _ _ k, tm => k.Conf tm
  | _, _, .case _ _ eP eQ, tm => eP.Conf tm.up && eQ.Conf tm.up
  | _, _, .put _ _ _ k, tm => k.Conf tm
  | _, _, .take (dflt := _) _ _ k, tm => k.Conf tm.up
  | _, _, .borrowShr _ _ k, tm => k.Conf tm.up
  | _, _, .borrowMut _ _ k, tm => k.Conf tm.up
  | _, _, .callRef _ _ _ _ k, tm => k.Conf tm.up
  | _, _, .extMut _ _ k, tm => k.Conf tm.up
  | _, _, .loop _ _ _ _ _ k, tm => k.Conf tm.up
  | _, _, _, _ => false

/-- A term conforms to handing back variable `x` in place exactly when every tail of it is `x`,
which is how the cost semantics decides the reactor step's mode. -/
theorem _root_.Millipede.Exp.conf_whole {Γ : List Ty} {t : Ty} (e : Exp Γ t) (x : Nat) :
    e.Conf (.whole x) = e.tailVar x := by
  induction e generalizing x with
  | atom a => cases a <;> rfl
  | _ => simp_all [Exp.Conf, Exp.tailVar, Tl.up]

/-! ## Slice views: used only through their elements -/

/-- The atom is variable number `i`. -/
def _root_.Millipede.Atom.isVar {Γ : List Ty} {t : Ty} (i : Nat) : Atom Γ t → Bool
  | .var m => m.idx == i
  | .lit _ => false

/-- Some argument atom is variable number `i`. -/
def _root_.Millipede.Args.mentions {Γ : List Ty} (i : Nat) : {ps : List Ty} → Args Γ ps → Bool
  | _, .nil => false
  | _, .cons a as => a.isVar i || as.mentions i

/-- Some word argument of an extern call is variable number `i`. -/
def _root_.Millipede.EArgs.mentions {Γ : List Ty} (i : Nat) : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => false
  | _, .word a as => a.isVar i || as.mentions i
  | _, .bufIn _ as => as.mentions i
  | _, .bufOut as => as.mentions i
  | _, .sliceOut _ _ _ as => as.mentions i

/-- Some index atom of the place is variable number `i`. -/
def _root_.Millipede.Place.idxMentions {Γ : List Ty} (i : Nat) : {t : Ty} → Place Γ t → Bool
  | _, .var _ => false
  | _, .field p _ => p.idxMentions i
  | _, .index (dflt := _) p j => p.idxMentions i || j.isVar i
  | _, .slot (dflt := _) p j => p.idxMentions i || j.isVar i
  | _, .range p lo len => p.idxMentions i || lo.isVar i || len.isVar i
  | _, .pair2 (dflt := _) p j k => p.idxMentions i || j.isVar i || k.isVar i
  | _, .rangeS _ lo len => lo.isVar i || len.isVar i
  | _, .pair2S (dflt := _) _ j k => j.isVar i || k.isVar i

/-- The place is variable number `i` itself. -/
def _root_.Millipede.Place.isVarAt {Γ : List Ty} (i : Nat) : {t : Ty} → Place Γ t → Bool
  | _, .var m => m.idx == i
  | _, _ => false

/-- At this place, view variable `i` is used through its elements only: the place is not the view
itself, and no index atom reads it. -/
def _root_.Millipede.Place.VSafe {Γ : List Ty} {t : Ty} (i : Nat) (p : Place Γ t) : Bool :=
  !p.idxMentions i && !p.isVarAt i

/-- The arguments of an extern call use view variable `i` through its elements only: no word
argument is the view, and the slices' places and atoms do not read it whole. -/
def _root_.Millipede.EArgs.VSafe {Γ : List Ty} (i : Nat) : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => true
  | _, .word a as => !a.isVar i && as.VSafe i
  | _, .bufIn (.const _) as => as.VSafe i
  | _, .bufIn (.slice a lo len) as => a.VSafe i && !lo.isVar i && !len.isVar i && as.VSafe i
  | _, .bufOut as => as.VSafe i
  | _, .sliceOut a lo cap as => a.VSafe i && !lo.isVar i && !cap.isVar i && as.VSafe i

/-- The type is a view's, a `Slots` shape. Only views are passed on whole. -/
def _root_.Millipede.Ty.isViewTy (t : Ty) : Bool :=
  match t.data.shape with
  | .slots _ _ => true
  | _ => false

/-- The arguments of a reference call use view variable `i` through its elements only, with two
exceptions. A `&` argument may be the view itself when the callee uses that parameter through its
elements only, which `vok j` says of parameter number `j`. A `&mut` argument may be the view
itself when moreover the callee hands it back with its occupancy unchanged, which `mok j` says. -/
def _root_.Millipede.RArgs.VSafe {Γ : List Ty} (i : Nat) (vok mok : Nat → Bool) :
    {ps os : List Ty} → RArgs Γ ps os → Nat → Bool
  | _, _, .nil, _ => true
  | _, _, .own a as, j => !a.isVar i && as.VSafe i vok mok (j + 1)
  | _, _, .shr (t := t) p as, j =>
    (p.VSafe i || p.isVarAt i && t.isViewTy && vok j) && as.VSafe i vok mok (j + 1)
  | _, _, .mut (t := t) p as, j =>
    (p.VSafe i || p.isVarAt i && t.isViewTy && mok j) && as.VSafe i vok mok (j + 1)

/-! ## The hand-back condition of a `&mut` slice borrow

When a `&mut` slice borrow ends, the value semantics writes the handed-back view back into the
array, and element `lo + k` becomes the view's cell `k` only if that cell is full. The machine has
already written the elements in place, so the handed-back view must still have its first `len`
cells full. `Exp.HB` is a syntactic condition under which it does: along every path to a tail, the
view variable is written only through its cells, and the tail constructor carries the hand-back
certificate `Ctor.occs`, with the view variable as its last argument. -/

/-- A write at the place keeps the full cells of view variable `i` full: the place is not rooted at
`i`, or it reaches into `i` through one of its cells first. -/
def _root_.Millipede.Place.keeps {Γ : List Ty} (i : Nat) : {t : Ty} → Place Γ t → Bool
  | _, .var m => m.idx != i
  | _, .field p _ => p.keeps i
  | _, .index (dflt := _) p _ => p.keeps i
  | _, .slot (dflt := _) p _ => p.isVarAt i || p.keeps i
  | _, .range p _ _ => p.keeps i
  | _, .pair2 (dflt := _) p _ _ => p.keeps i
  | _, .rangeS _ _ _ => true
  | _, .pair2S (dflt := _) _ _ _ => true

/-- The `&mut` argument places keep the full cells of view variable `i` full. -/
def _root_.Millipede.RArgs.keeps {Γ : List Ty} (i : Nat) (hb : Nat → Bool) :
    {ps os : List Ty} → RArgs Γ ps os → Nat → Bool
  | _, _, .nil, _ => true
  | _, _, .own _ as, j => as.keeps i hb (j + 1)
  | _, _, .shr _ as, j => as.keeps i hb (j + 1)
  | _, _, .mut p as, j => (p.keeps i || p.isVarAt i && hb j) && as.keeps i hb (j + 1)

/-- The `&mut` arguments of a reference call meet the exact hand-back condition for view variable
`i`. None is rooted at `i`, except `i` itself passed on whole to a parameter `j` with `hb j`, and
the first `&mut` argument when it keeps `i`'s cells, as the pair `(s[a], s[b])` or a sub-slice of
`i` does. The first argument is the one written back first, at the call's environment, where its
obligations hold. -/
def _root_.Millipede.RArgs.keepsX {Γ : List Ty} (i : Nat) (hb : Nat → Bool) :
    {ps os : List Ty} → RArgs Γ ps os → Nat → Bool → Bool
  | _, _, .nil, _, _ => true
  | _, _, .own _ as, j, s => as.keepsX i hb (j + 1) s
  | _, _, .shr _ as, j, s => as.keepsX i hb (j + 1) s
  | _, _, .mut p as, j, s =>
    (p.root != i || p.isVarAt i && hb j || !s && p.keeps i) && as.keepsX i hb (j + 1) true

/-- No mutable slice of an extern call is rooted at variable `i`. -/
def _root_.Millipede.EArgs.rootsNe {Γ : List Ty} (i : Nat) : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => true
  | _, .word _ as => as.rootsNe i
  | _, .bufIn _ as => as.rootsNe i
  | _, .bufOut as => as.rootsNe i
  | _, .sliceOut a _ _ as => a.root != i && as.rootsNe i

/-- The mutable slices of an extern call keep the full cells of view variable `i` full. -/
def _root_.Millipede.EArgs.keeps {Γ : List Ty} (i : Nat) : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => true
  | _, .word _ as => as.keeps i
  | _, .bufIn _ as => as.keeps i
  | _, .bufOut as => as.keeps i
  | _, .sliceOut a _ _ as => a.keeps i && as.keeps i

/-- The last arguments are the variables `ys`, in order. -/
def _root_.Millipede.Args.endVars {Γ : List Ty} : {ps : List Ty} → Args Γ ps → List Nat → Bool
  | _, .nil, ys => ys.isEmpty
  | _, .cons (ts := ts) a as, ys =>
    if ts.length + 1 = ys.length then
      match ys with
      | y :: ys' => a.isVar y && as.endVars ys'
      | [] => false
    else as.endVars ys

/-- The exact hand-back condition for view variable `i`, followed by the in-place components `xs`.
It strengthens `Exp.HBv` so that the view's occupancy is handed back unchanged, given the term's
obligations. The view is written only by assignments through its cells, whose obligation is that
the cell is full, or by passing it on whole to a callee that meets the exact condition for that
parameter, and no other `put`, `take`, borrow, reference argument or extern slice is rooted at it. -/
def _root_.Millipede.Exp.HBx : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat → List Nat → Bool
  | _, _, .let_ _ e₂, i, xs => e₂.HBx (i + 1) (xs.map (· + 1))
  | _, _, .ite _ e₁ e₂, i, xs => e₁.HBx i xs && e₂.HBx i xs
  | _, _, .match_ _ eE eO, i, xs => eE.HBx (i + 1) (xs.map (· + 1)) && eO.HBx (i + 1) (xs.map (· + 1))
  | _, _, .mk c args, i, xs => c.occs.isSome && args.endVars (i :: xs)
  | _, _, .assign p _ k, i, xs => p.keeps i && k.HBx i xs
  | _, _, .case _ _ eP eQ, i, xs => eP.HBx (i + 1) (xs.map (· + 1)) && eQ.HBx (i + 1) (xs.map (· + 1))
  | _, _, .put p _ _ k, i, xs => p.root != i && k.HBx i xs
  | _, _, .take (dflt := _) p _ k, i, xs => p.root != i && k.HBx (i + 1) (xs.map (· + 1))
  | _, _, .borrowShr _ _ k, i, xs => k.HBx (i + 1) (xs.map (· + 1))
  | _, _, .borrowMut p _ k, i, xs => p.keeps i && k.HBx (i + 1) (xs.map (· + 1))
  | _, _, .callRef _ _ body args k, i, xs =>
    args.keepsX i (fun j => body.HBx j ((args.mutIdx 0).filter (j < ·))) 0 false &&
      k.HBx (i + 1) (xs.map (· + 1))
  | _, _, .extMut _ args k, i, xs => args.rootsNe i && k.HBx (i + 1) (xs.map (· + 1))
  | _, _, .loop _ cs _ _ body k, i, xs =>
    cs.distinct && (!cs.idxs.contains i || body.HBx (i + 2) ((cs.after i).map (· + 2))) &&
      k.HBx (i + 1) (xs.map (· + 1))
  | _, _, _, _, _ => false

/-- The hand-back condition for view variable `i`, followed in the handed-back value by the
in-place components `xs`. Every tail is a certified hand-back constructor whose last arguments are
`i` and then `xs`, and every write on the way keeps `i`'s full cells full. -/
def _root_.Millipede.Exp.HBv : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat → List Nat → Bool
  | _, _, .let_ _ e₂, i, xs => e₂.HBv (i + 1) (xs.map (· + 1))
  | _, _, .ite _ e₁ e₂, i, xs => e₁.HBv i xs && e₂.HBv i xs
  | _, _, .match_ _ eE eO, i, xs => eE.HBv (i + 1) (xs.map (· + 1)) && eO.HBv (i + 1) (xs.map (· + 1))
  | _, _, .mk c args, i, xs => c.occs.isSome && args.endVars (i :: xs)
  | _, _, .assign p _ k, i, xs => p.keeps i && k.HBv i xs
  | _, _, .case _ _ eP eQ, i, xs => eP.HBv (i + 1) (xs.map (· + 1)) && eQ.HBv (i + 1) (xs.map (· + 1))
  | _, _, .put p _ _ k, i, xs => p.keeps i && k.HBv i xs
  | _, _, .take (dflt := _) p _ k, i, xs => p.keeps i && k.HBv (i + 1) (xs.map (· + 1))
  | _, _, .borrowShr _ _ k, i, xs => k.HBv (i + 1) (xs.map (· + 1))
  | _, _, .borrowMut p _ k, i, xs => p.keeps i && k.HBv (i + 1) (xs.map (· + 1))
  | _, _, .callRef _ _ body args k, i, xs =>
    args.keeps i (fun j => body.HBx j ((args.mutIdx 0).filter (j < ·))) 0 &&
      k.HBv (i + 1) (xs.map (· + 1))
  | _, _, .extMut _ args k, i, xs => args.keeps i && k.HBv (i + 1) (xs.map (· + 1))
  | _, _, .loop _ cs _ _ body k, i, xs =>
    cs.distinct && (!cs.idxs.contains i || body.HBv (i + 2) ((cs.after i).map (· + 2))) &&
      k.HBv (i + 1) (xs.map (· + 1))
  | _, _, _, _, _ => false

/-- The hand-back condition of a `&mut` slice borrow's body, where the view is variable `i` and is
the last handed-back component. -/
abbrev _root_.Millipede.Exp.HB {Γ : List Ty} {t : Ty} (e : Exp Γ t) (i : Nat) : Bool := e.HBv i []

/-- Slice view `i` is used only through its elements in a term delivered in tail mode `tm`. The
machine holds only a pointer and a length for the view, so the view is never copied whole, though a
tail constructor in a `split` mode may hand it back in place. It is never assigned whole, `put`
into, `take`n from or re-borrowed whole. It may be passed on whole by reference when the callee
uses that parameter through its elements only and, for `&mut`, hands it back with its occupancy
unchanged. -/
def _root_.Millipede.Exp.VSafe : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat → Tl → Bool
  | _, _, .atom a, i, _ => !a.isVar i
  | _, _, .let_ e₁ e₂, i, tm => e₁.VSafe i .none && e₂.VSafe (i + 1) tm.up
  | _, _, .ite c e₁ e₂, i, tm => !c.isVar i && e₁.VSafe i tm && e₂.VSafe i tm
  | _, _, .prim _ args, i, _ => !args.mentions i
  | _, _, .call _ _ args, i, _ => !args.mentions i
  | _, _, .ok a, i, _ => !a.isVar i
  | _, _, .err a, i, _ => !a.isVar i
  | _, _, .match_ s eE eO, i, tm => !s.isVar i && eE.VSafe (i + 1) tm.up && eO.VSafe (i + 1) tm.up
  | _, _, .ext _ args, i, _ => args.VSafe i
  | _, _, .extMut _ args k, i, tm => args.VSafe i && k.VSafe (i + 1) tm.up
  | _, _, .mk _ args, i, tm =>
    match tm, args with
    | .split _ _, .cons a _ => !a.isVar i
    | _, _ => !args.mentions i
  | _, _, .read p, i, _ => p.VSafe i
  | _, _, .assign p a k, i, tm => p.VSafe i && !a.isVar i && k.VSafe i tm
  | _, _, .case s _ eP eQ, i, tm => !s.isVar i && eP.VSafe (i + 1) tm.up && eQ.VSafe (i + 1) tm.up
  | _, _, .put p j a k, i, tm => p.VSafe i && !j.isVar i && !a.isVar i && k.VSafe i tm
  | _, _, .take (dflt := _) p j k, i, tm => p.VSafe i && !j.isVar i && k.VSafe (i + 1) tm.up
  | _, _, .borrowShr p body k, i, tm => p.VSafe i && body.VSafe (i + 1) .none && k.VSafe (i + 1) tm.up
  | _, _, .borrowMut (t := t) (u := u) p body k, i, tm =>
    p.VSafe i && body.VSafe (i + 1) (.split u.size [(0, fieldOff (Data.shape (u.carrier × t.carrier)) 1, t.size)]) &&
      k.VSafe (i + 1) tm.up
  | _, _, .callRef (r := r) _ _ body args k, i, tm =>
    args.VSafe i (fun j => body.VSafe j (.split r.size (args.comps r)))
      (fun j => body.VSafe j (.split r.size (args.comps r)) &&
        body.HBx j ((args.mutIdx 0).filter (j < ·))) 0 && k.VSafe (i + 1) tm.up
  | _, _, .guard (.valid p _), i, _ => p.VSafe i
  | _, _, .loop (s := s) _ cs init c body k, i, tm =>
    !init.isVar i && c.VSafe (i + 2) .none && body.VSafe (i + 2) (.split s.size (cs.comps s)) &&
      (!cs.idxs.contains i || body.HBx (i + 2) ((cs.after i).map (· + 2))) && k.VSafe (i + 1) tm.up

/-- The tail mode of a `&mut` borrow's body: the result `u` at the destination, and the reference,
variable `0`, handed back in place. -/
abbrev borrowTl (u t : Ty) : Tl := .split u.size [(0, fieldOff (Data.shape (u.carrier × t.carrier)) 1, t.size)]

/-- The tail mode of a loop body that writes carried variables: the new accumulator at the
destination, and the carried variables handed back in place. -/
abbrev loopTl {Γ ts : List Ty} (s : Ty) (cs : Carry Γ ts) : Tl := .split s.size (cs.comps s)

/-- The tail mode of a callee: the result at the destination, and the `&mut` parameters handed
back in place. -/
abbrev callTl {Γ ps os : List Ty} (r : Ty) (as : RArgs Γ ps os) : Tl := .split r.size (as.comps r)

theorem _root_.Millipede.RArgs.mutIdx_length {Γ : List Ty} :
    {ps os : List Ty} → (as : RArgs Γ ps os) → (i : Nat) → (as.mutIdx i).length = os.length
  | _, _, .nil, _ => rfl
  | _, _, .own _ as, i => as.mutIdx_length (i + 1)
  | _, _, .shr _ as, i => as.mutIdx_length (i + 1)
  | _, _, .mut _ as, i => by simp [RArgs.mutIdx, as.mutIdx_length (i + 1)]

theorem _root_.Millipede.Carry.idxs_length {Γ : List Ty} :
    {ts : List Ty} → (cs : Carry Γ ts) → cs.idxs.length = ts.length
  | _, .nil => rfl
  | _, .cons _ cs => by simp [Carry.idxs, cs.idxs_length]

/-- A callee hands back components in place, and is charged as `split`, exactly when it has
`&mut` parameters. -/
theorem callTl_hb {Γ ps os : List Ty} (r : Ty) (as : RArgs Γ ps os) :
    (callTl r as).hb = Hb.of !os.isEmpty := by
  have h : (as.comps r).length = os.length := by
    simp [RArgs.comps, as.mutIdx_length, tupOffs_length]
  unfold callTl; cases hc : as.comps r <;> cases os <;> simp_all [Tl.hb, Hb.of]

/-- A loop body in tail mode `split` hands back components in place exactly when the loop carries
variables. -/
theorem loopTl_hb {Γ ts : List Ty} (s : Ty) (cs : Carry Γ ts) :
    (loopTl s cs).hb = Hb.of !ts.isEmpty := by
  have h : (cs.comps s).length = ts.length := by
    simp [Carry.comps, cs.idxs_length, tupOffs_length]
  unfold loopTl; cases hc : cs.comps s <;> cases ts <;> simp_all [Tl.hb, Hb.of]

/-! ## Terms -/

/-- Load the one or two scalar arguments of a primitive into `RX` and `RY`. -/
def primLoad {Γ : List Ty} : {ps : List Ty} → Args Γ ps → List Loc → Stmt
  | _, .cons a (.cons b _), ρ => .seq (atomWord a ρ RX) (atomWord b ρ RY)
  | _, .cons a .nil, ρ => atomWord a ρ RX
  | _, .nil, _ => .skip

/-- The code that materialises a scrutinee: nothing for an owned variable, and a copy of its bytes
at `n` for a literal or a reference. -/
def scrutPre {Γ : List Ty} {t : Ty} : Atom Γ t → List Loc → Nat → Stmt
  | .var m, ρ, n =>
    match ρ.getD m.idx default with
    | .own _ | .slot _ _ _ => .skip
    | .ref _ => atomTo (.var m) ρ n
    | .ref2 _ => atomTo (.var m) ρ n
  | .lit v, _, n => writeB (.slot BP) n (Data.encodeBytes v)

/-- Where a scrutinee's bytes are: its variable's offset, or `n` for a literal or a reference. -/
def scrutLoc {Γ : List Ty} {t : Ty} : Atom Γ t → List Loc → Nat → Nat
  | .var m, ρ, n =>
    match ρ.getD m.idx default with
    | .own o | .slot o _ _ => o
    | .ref _ => n
    | .ref2 _ => n
  | .lit _, _, n => n

/-- The code that builds the rest of a `case`, the `q` value at `n'`, from the scrutinee at `ls`,
as `RestMode` says. -/
def restCode (mode : RestMode) (tag ls po n' qsize : Nat) : Stmt :=
  match mode with
  | .payload => copyM (ls + po) n' qsize
  | .whole => copyM ls n' qsize
  | .retag po' m =>
    .seq (.load .w8 RT (.slot BP) (UInt64.ofNat ls))
      (.seq (.bin .ult RX (.imm (UInt64.ofNat tag)) (.slot RT))
      (.seq (.bin .sub RT (.slot RT) (.slot RX))
      (.seq (.store .w8 (.slot BP) (UInt64.ofNat n') (.slot RT))
        (copyM (ls + po) (n' + po') m))))

/-- Compute a guard into the `Result Unit Unit` at `d`, whose tag byte is `1` for ok. -/
def guardCode {Γ : List Ty} : Guard Γ → List Loc → Nat → Stmt
  | .valid p _, ρ, d => .seq ((placeCheck p ρ).getD .skip)
      (.store .w8 (.slot BP) (UInt64.ofNat d) (.slot RY))

/-- The offset of the second field of a pair's shape. -/
abbrev sndOff (u t : Ty) : Nat := fieldOff (Data.shape (u.carrier × t.carrier)) 1

/-! ## Slot-resident variables -/

/-- The frame slot of a place that is a slot-resident variable. -/
def _root_.Millipede.Place.slotOf {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc) :
    Option Nat :=
  match p with
  | .var m => (ρ.getD m.idx default).slot?
  | _ => none

/-- The place is a whole-word field `x.f` of variable `i`: the field is at a multiple of 8 bytes
and of a slot-resident type of whole words, so a slot-resident `x` reads and writes it as slots. -/
def _root_.Millipede.Place.wordField {Γ : List Ty} {t : Ty} (i : Nat) : Place Γ t → Bool
  | .field (.var m) l => m.idx == i && lensOff l % 8 == 0 && t.size % 8 == 0 && t.slotTy
  | _ => false

/-- The slots of a whole-word field of a slot-resident variable: its first slot, and the number of
the variable's slots from there, which keeps the frame bound syntactic. -/
def _root_.Millipede.Place.slotField {Γ : List Ty} {t : Ty} (p : Place Γ t) (ρ : List Loc) :
    Option (Nat × Nat) :=
  match p with
  | .field (.var m) l =>
    match ρ.getD m.idx default with
    | .slot _ k n => if p.wordField m.idx then some (k + lensOff l / 8, n - lensOff l / 8) else none
    | _ => none
  | _ => none

/-- The variable that a tail mode hands back whole, in place, whose memory bytes are then the
value. The in-place components of a `split` may be in memory or in frame slots. -/
def Tl.vars : Tl → List Nat
  | .whole x => [x]
  | _ => []

/-- No slice of an extern call is rooted at variable `i`. -/
def _root_.Millipede.EArgs.noAddr {Γ : List Ty} (i : Nat) : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => true
  | _, .word _ as => as.noAddr i
  | _, .bufIn (.const _) as => as.noAddr i
  | _, .bufIn (.slice a _ _) as => a.root != i && as.noAddr i
  | _, .bufOut as => as.noAddr i
  | _, .sliceOut a _ _ as => a.root != i && as.noAddr i

/-- No reference argument of a call is rooted at variable `i`. -/
def _root_.Millipede.RArgs.noAddr {Γ : List Ty} (i : Nat) : {ps os : List Ty} → RArgs Γ ps os → Bool
  | _, _, .nil => true
  | _, _, .own _ as => as.noAddr i
  | _, _, .shr p as => p.root != i && as.noAddr i
  | _, _, .mut p as => p.root != i && as.noAddr i

/-- Variable `i` is never addressed in the term. No place is rooted at it, so it is not read
through a place, borrowed, passed by reference, sliced for an extern, or used by `put`, `take` or
`guard`, though it may be assigned whole and carried through a loop. It is not a scrutinee, except
of a `match` or `case` that is taken apart in its slots. Its uses are then atoms, whole assignments
and in-place hand-backs, which a frame slot serves. The test is syntactic and conservative, and
callee bodies are not examined because they are other activations. -/
def _root_.Millipede.Exp.noAddr : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat → Bool
  | _, _, .atom _, _ => true
  | _, _, .let_ e₁ e₂, i => e₁.noAddr i && e₂.noAddr (i + 1)
  | _, _, .ite _ e₁ e₂, i => e₁.noAddr i && e₂.noAddr i
  | _, _, .prim _ _, _ => true
  | _, _, .call _ _ _, _ => true
  | _, _, .ok _, _ => true
  | _, _, .err _, _ => true
  | _, _, .match_ (ε := ε) (α := α) s eE eO, i =>
    (!s.isVar i || Ty.slotSum ε α) && eE.noAddr (i + 1) && eO.noAddr (i + 1)
  | _, _, .ext _ args, i => args.noAddr i
  | _, _, .extMut _ args k, i => args.noAddr i && k.noAddr (i + 1)
  | _, _, .mk _ _, _ => true
  | _, _, .read p, i => p.root != i || p.wordField i
  | _, _, .assign p _ k, i => (p.root != i || p.isVarAt i || p.wordField i) && k.noAddr i
  | _, _, .case s sp eP eQ, i => (!s.isVar i || sp.slotOk) && eP.noAddr (i + 1) && eQ.noAddr (i + 1)
  | _, _, .put p _ _ k, i => p.root != i && k.noAddr i
  | _, _, .take (dflt := _) p _ k, i => p.root != i && k.noAddr (i + 1)
  | _, _, .borrowShr p body k, i => p.root != i && body.noAddr (i + 1) && k.noAddr (i + 1)
  | _, _, .borrowMut p body k, i => p.root != i && body.noAddr (i + 1) && k.noAddr (i + 1)
  | _, _, .callRef _ _ _ args k, i => args.noAddr i && k.noAddr (i + 1)
  | _, _, .guard (.valid p _), i => p.root != i
  | _, _, .loop _ _ _ c body k, i => c.noAddr (i + 2) && body.noAddr (i + 2) && k.noAddr (i + 1)

/-- Parameter `j` of a callee is passed as a word: it is a one-word scalar that the body never
addresses, among the first `FR - REXT` parameters, so its word passes through scratch slot
`REXT + j`. It lives in a frame slot of the callee's frame, and the caller passes its word in the
call's argument list and copies nothing. A parameter the body addresses stays in the callee's
region in memory. -/
def _root_.Millipede.Exp.wordParam {ps : List Ty} {t : Ty} (body : Exp ps t) (j : Nat) : Bool :=
  decide (j < FR - REXT) && (ps.getD j .unit).wordTy && body.noAddr j

/-- A whole-word field of variable `i` is read or assigned in the term. -/
def _root_.Millipede.Exp.fieldUse : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat → Bool
  | _, _, .let_ e₁ e₂, i => e₁.fieldUse i || e₂.fieldUse (i + 1)
  | _, _, .ite _ e₁ e₂, i => e₁.fieldUse i || e₂.fieldUse i
  | _, _, .match_ _ eE eO, i => eE.fieldUse (i + 1) || eO.fieldUse (i + 1)
  | _, _, .extMut _ _ k, i => k.fieldUse (i + 1)
  | _, _, .read p, i => p.wordField i
  | _, _, .assign p _ k, i => p.wordField i || k.fieldUse i
  | _, _, .case _ _ eP eQ, i => eP.fieldUse (i + 1) || eQ.fieldUse (i + 1)
  | _, _, .put _ _ _ k, i => k.fieldUse i
  | _, _, .take (dflt := _) _ _ k, i => k.fieldUse (i + 1)
  | _, _, .borrowShr _ body k, i => body.fieldUse (i + 1) || k.fieldUse (i + 1)
  | _, _, .borrowMut _ body k, i => body.fieldUse (i + 1) || k.fieldUse (i + 1)
  | _, _, .callRef _ _ _ _ k, i => k.fieldUse (i + 1)
  | _, _, .loop _ _ _ c body k, i => c.fieldUse (i + 2) || body.fieldUse (i + 2) || k.fieldUse (i + 1)
  | _, _, _, _ => false

/-- The binder of the scope `e₂` is slot-resident. The binder is that of a `let`, a `match` or
`case` arm, or the continuation of `take` or `extMut`. Its type is slot-resident, `e₂` never
addresses it, and `e₂` uses it as an atom or through a whole-word field. An unused binder stays at
its memory destination, since a slot would cost one more load and more frame slots. -/
def _root_.Millipede.Exp.slotBind {Γ : List Ty} {s t : Ty} (e₂ : Exp (s :: Γ) t) : Bool :=
  s.slotTy && e₂.noAddr 0 && (!e₂.VSafe 0 .none || e₂.fieldUse 0)

/-- The term makes no whole assignment `i := a` to variable `i` and carries it through no loop.
Together with `Exp.noAddr i`, the term does not write variable `i` at all. -/
def _root_.Millipede.Exp.noAsg : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat → Bool
  | _, _, .let_ e₁ e₂, i => e₁.noAsg i && e₂.noAsg (i + 1)
  | _, _, .ite _ e₁ e₂, i => e₁.noAsg i && e₂.noAsg i
  | _, _, .match_ _ eE eO, i => eE.noAsg (i + 1) && eO.noAsg (i + 1)
  | _, _, .extMut _ _ k, i => k.noAsg (i + 1)
  | _, _, .assign p _ k, i => !p.isVarAt i && !p.wordField i && k.noAsg i
  | _, _, .case _ _ eP eQ, i => eP.noAsg (i + 1) && eQ.noAsg (i + 1)
  | _, _, .put _ _ _ k, i => k.noAsg i
  | _, _, .take (dflt := _) _ _ k, i => k.noAsg (i + 1)
  | _, _, .borrowShr _ body k, i => body.noAsg (i + 1) && k.noAsg (i + 1)
  | _, _, .borrowMut _ body k, i => body.noAsg (i + 1) && k.noAsg (i + 1)
  | _, _, .callRef _ _ _ _ k, i => k.noAsg (i + 1)
  | _, _, .loop _ cs _ c body k, i =>
    !cs.idxs.contains i && c.noAsg (i + 2) && body.noAsg (i + 2) && k.noAsg (i + 1)
  | _, _, _, _ => true

/-- A loop's counter variable, variable `0` of the condition and the body, is slot-resident:
neither addresses it and the body does not assign it, so its frame slot is the loop's counter
itself and no copy is made per iteration. -/
def _root_.Millipede.Exp.cntSlot {Γ : List Ty} {s t : Ty} (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) t) : Bool :=
  c.noAddr 0 && body.noAddr 0 && body.noAsg 0

/-- A loop's accumulator, variable `1` of the condition and the body and variable `0` of the
continuation, is slot-resident: its type is slot-resident and none of them addresses it. -/
def _root_.Millipede.Exp.accSlot {Γ : List Ty} {s t u : Ty} (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) t) (k : Exp (s :: Γ) u) : Bool :=
  s.slotTy && c.noAddr 1 && body.noAddr 1 && k.noAddr 0

/-- The accumulator's location: the `w` frame slots from `FR + slotsIn ρ`, with its reserved bytes
at `n`, or memory at `n`. -/
def accLoc (b : Bool) (ρ : List Loc) (n w : Nat) : Loc :=
  if b then .slot n (FR + slotsIn ρ) w else .own n

/-- The counter variable's location: frame slot `FR + slotsIn ρ`, with its reserved bytes at
`a + 8`, or memory at `a + 8`, in which case the counter itself is the memory cell at `a` and is
copied in each iteration. -/
def cntLoc (b : Bool) (ρ : List Loc) (a : Nat) : Loc :=
  if b then .slot (a + 8) (FR + slotsIn ρ) 1 else .own (a + 8)

/-- The counter test `RX := counter < N`. -/
def cntTest (lc : Loc) (a N : Nat) : Stmt :=
  match lc with
  | .slot _ k _ => .bin .ult RX (.slot k) (.imm (UInt64.ofNat N))
  | _ => .seq (.load .w64 RX (.slot BP) (UInt64.ofNat a)) (.bin .ult RX (.slot RX) (.imm (UInt64.ofNat N)))

/-- Entering an iteration copies the counter into the counter variable's memory. A slot-resident
counter variable is the counter, so nothing is copied. -/
def cntEnter (lc : Loc) (a : Nat) : Stmt :=
  match lc with
  | .slot _ _ _ => .skip
  | _ => .seq (.load .w64 RT (.slot BP) (UInt64.ofNat a))
      (.store .w64 (.slot BP) (UInt64.ofNat (a + 8)) (.slot RT))

/-- Increment the counter. -/
def cntNext (lc : Loc) (a : Nat) : Stmt :=
  match lc with
  | .slot _ k _ => .bin .add k (.slot k) (.imm 1)
  | _ => .seq (.load .w64 RT (.slot BP) (UInt64.ofNat a))
      (.seq (.bin .add RT (.slot RT) (.imm 1)) (.store .w64 (.slot BP) (UInt64.ofNat a) (.slot RT)))

/-- Zero the counter. -/
def cntInit (lc : Loc) (a : Nat) : Stmt :=
  match lc with
  | .slot _ k _ => .mov k (.imm 0)
  | _ => .store .w64 (.slot BP) (UInt64.ofNat a) (.imm 0)

/-- After the body, move the new accumulator from `lb` to the accumulator. `lb` is the body's
destination `a + 17`, or the frame slots the body computed it into. -/
def accNext (la lb : Loc) (sz : Nat) : Stmt :=
  match la, lb with
  | .slot _ k n, .slot _ k' _ => movSlots k k' n
  | .slot _ k n, l => ldSlots (scalarWidth sz) k (.slot BP) l.off n
  | l, l' => copyM l'.off l.off sz

/-- A loop body that is computed into frame slots. The accumulator is slot-resident, no variable is
carried so the body's value is the new accumulator alone, and every tail of the body computes into
slots. The value goes to the slots after the loop variables' and is moved to the accumulator's, so
there is no store and load per iteration. -/
def _root_.Millipede.Exp.bodyW {Γ ts : List Ty} {s u : Ty} (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))) (k : Exp (s :: Γ) u) : Bool :=
  Exp.accSlot c body k && ts.isEmpty && decide ((Ty.pair s (.tup ts)).size = s.size) &&
    body.Conf (.word FR) &&
    -- no view the body may use is an argument of a constructor into slots
    (List.range Γ.length).all fun i => !body.VSafe (i + 2) (.split s.size []) || body.VSafe (i + 2) .none

/-- The tail mode of a loop body: into the slots from `T`, or the new accumulator at the
destination with the carried variables in place. -/
def bodyTl {Γ ts : List Ty} {s u : Ty} (cs : Carry Γ ts) (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))) (k : Exp (s :: Γ) u) (T : Nat) : Tl :=
  if Exp.bodyW c body k then .word T else loopTl s cs

/-- A loop body is charged as `split` exactly when the loop carries variables: a body computed
into slots carries none. -/
theorem bodyTl_hb {Γ ts : List Ty} {s u : Ty} (cs : Carry Γ ts) (c : Exp (.u64 :: s :: Γ) .bool)
    (body : Exp (.u64 :: s :: Γ) (.pair s (.tup ts))) (k : Exp (s :: Γ) u) (T : Nat) :
    (bodyTl cs c body k T).hb = Hb.of !ts.isEmpty := by
  unfold bodyTl
  split
  · rename_i h
    simp only [Exp.bodyW, Bool.and_eq_true] at h
    simpa [Hb.of] using h.1.1.1.2
  · exact loopTl_hb s cs

/-- Where a loop body leaves the new accumulator: the `w` slots from `T`, or its destination
`a + 17`. -/
def bodyLoc (tmb : Tl) (a w : Nat) : Loc :=
  match tmb with
  | .word T => .slot (a + 17) T w
  | _ => .own (a + 17)

/-- The tail mode of a loop condition: into frame slot `T` when its tails compute into slots, and
otherwise its byte at the destination `a + 16`. -/
def flagTl {Γ : List Ty} (c : Exp Γ .bool) (T : Nat) : Tl :=
  if c.Conf (.word FR) then .word T else .none

theorem flagTl_hb {Γ : List Ty} (c : Exp Γ .bool) (T : Nat) : (flagTl c T).hb = .copy := by
  unfold flagTl; split <;> rfl

/-- After the condition, load the flag into `RX` from frame slot `T` or from its byte at `a + 16`. -/
def flagLoad (tmc : Tl) (a : Nat) : Stmt :=
  match tmc with
  | .word k => .mov RX (.slot k)
  | _ => .load .w8 RX (.slot BP) (UInt64.ofNat (a + 16))

/-- The initial accumulator: the atom's bytes at the accumulator's bytes in memory, or its words
in the accumulator's slots. -/
def accInit {Γ : List Ty} {s : Ty} (la : Loc) (init : Atom Γ s) (ρ : List Loc) : Stmt :=
  match la with
  | .slot _ k n => atomSlots init ρ k n
  | l => atomTo init ρ l.off

/-- An arm's binder of type `p` at `n'` that takes a payload from memory at `b + o`, where `b` is a
base slot. The payload is loaded into the binder's frame slots from `K` when it is slot-resident,
and copied to its memory otherwise; then `rest` runs with the binder's location. -/
def memArm (sb : Bool) (p : Ty) (K b o n' : Nat) (rest : Loc → Stmt) : Stmt :=
  if sb then .seq (ldSlots (scalarWidth p.size) K (.slot b) o p.slotN) (rest (.slot n' K p.slotN))
  else .seq (copyB (.slot b) o (.slot BP) n' p.size) (rest (.own n'))

/-- An arm's binder of type `p` at `n'` that takes its value from a slot-resident scrutinee, in the
slots from `src`. The value is a `Result`'s or an enum's payload, or a `case`'s whole rest. It is
moved into the binder's slots from `K`, at most `cnt` of them to keep the frame bound syntactic, or
stored to its memory. -/
def slotArm (sb : Bool) (p : Ty) (K src cnt n' : Nat) (rest : Loc → Stmt) : Stmt :=
  if sb then .seq (movSlots K src (min p.slotN cnt)) (rest (.slot n' K p.slotN))
  else .seq (stSlots (scalarWidth p.size) (.slot BP) n' src (min p.slotN cnt))
    (rest (.own n'))

/-! ## Constructors computed into frame slots -/

/-- Move the words of a constructor's arguments into the `n` slots from `x`. Argument `j`, placed
at byte `o` of the value with `o` a multiple of 8, goes into the slots from `x + o / 8`, at most
up to the destination's last slot. An empty argument, or one whose slots already are those, needs
no code. -/
def argsSlots {Γ : List Ty} (ρ : List Loc) (x n : Nat) : {ps : List Ty} → Args Γ ps →
    List (List Nat) → Stmt
  | _, .cons (t := p) a as, os :: oss =>
    .seq (if p.slotTy && a.slotOf ρ != some (x + os.headD 0 / 8) then
        atomSlots a ρ (x + os.headD 0 / 8) (min p.slotN (n - os.headD 0 / 8)) else .skip)
      (argsSlots ρ x n as oss)
  | _, _, _ => .skip

/-- A constructor, given its arguments and its plan, into the `n` slots from `x`: the tag byte
zero-extended to a word, then the arguments' words. -/
def ctorSlots {Γ ps : List Ty} (args : Args Γ ps) (plan : List (List Nat) × Option Nat)
    (ρ : List Loc) (x n : Nat) : Stmt :=
  .seq (match plan.2 with
    | some i => .mov x (.imm (UInt64.ofNat (i % 256)))
    | none => .skip) (argsSlots ρ x n args plan.1)

/-- Every argument variable's slots lie wholly outside the `n` slots from `x`, or already are its
words' place there, so computing straight into them overwrites no argument before it is read. -/
def _root_.Millipede.Args.slotsAway {Γ : List Ty} (ρ : List Loc) (x n : Nat) :
    {ps : List Ty} → Args Γ ps → List (List Nat) → Bool
  | _, .cons a as, os :: oss =>
    (match a.slotOf ρ with
     | some k => k == x + os.headD 0 / 8 || decide (x + n ≤ k) || decide (k + a.slotNw ρ ≤ x)
     | none => true) && as.slotsAway ρ x n oss
  | _, _, _ => true

/-- A constructor into the `n` slots from `k`: straight into them, or, when an argument's slots
straddle them, into the scratch slots from `REXT` and then moved. -/
def ctorCode {Γ ps : List Ty} (args : Args Γ ps) (plan : List (List Nat) × Option Nat)
    (ρ : List Loc) (k n : Nat) : Stmt :=
  if args.slotsAway ρ k n plan.1 then ctorSlots args plan ρ k n
  else .seq (ctorSlots args plan ρ REXT n) (movSlots k REXT n)

/-- A `Result` constructor, `ok` with tag `1` or `err` with tag `0`, with payload atom `a`. In tail
mode `word k` it writes the tag word and the payload's words after it, and otherwise the tag byte
and the payload at the destination. -/
def resultCode {Γ : List Ty} {p : Ty} (ε α : Ty) (a : Atom Γ p) (tag : Nat) (tm : Tl)
    (ρ : List Loc) (d : Nat) : Stmt :=
  match tm with
  | .word k => if Ty.slotSum ε α then ctorCode (.cons a .nil)
      ([[payloadOff (Data.shape (Except ε.carrier α.carrier))]], some tag) ρ k (Ty.result ε α).slotN
    else .skip
  | _ => .seq (.store .w8 (.slot BP) (UInt64.ofNat d) (.imm (UInt64.ofNat tag)))
      (atomTo a ρ (d + payloadOff (Data.shape (Except ε.carrier α.carrier))))

/-- The frame slots beyond `FR` that the code of a term needs for its own slot-resident binders.
Callees are not counted, since they run in their own frames. -/
def _root_.Millipede.Exp.slotNeed : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat
  | _, _, .atom _ => 0
  | _, _, .let_ (s := s) e₁ e₂ => if e₂.slotBind then max e₁.slotNeed (e₂.slotNeed + s.slotN)
      else max e₁.slotNeed e₂.slotNeed
  | _, _, .ite _ e₁ e₂ => max e₁.slotNeed e₂.slotNeed
  | _, _, .prim _ _ => 0
  | _, _, .call _ _ _ => 0
  | _, _, .ok _ => 0
  | _, _, .err _ => 0
  | _, _, .match_ (ε := ε) (α := α) _ eE eO =>
    max (if eE.slotBind then eE.slotNeed + ε.slotN else eE.slotNeed)
      (if eO.slotBind then eO.slotNeed + α.slotN else eO.slotNeed)
  | _, _, .ext _ _ => 0
  | _, _, .extMut _ _ k => if k.slotBind then k.slotNeed + 1 else k.slotNeed
  | _, _, .mk _ _ => 0
  | _, _, .read _ => 0
  | _, _, .assign _ _ k => k.slotNeed
  | _, _, .case (p := pt) (q := qt) _ _ eP eQ =>
    max (if eP.slotBind then eP.slotNeed + pt.slotN else eP.slotNeed)
      (if eQ.slotBind then eQ.slotNeed + qt.slotN else eQ.slotNeed)
  | _, _, .put _ _ _ k => k.slotNeed
  | _, _, .take (t := t) (dflt := _) _ _ k => if k.slotBind then k.slotNeed + t.slotN else k.slotNeed
  | _, _, .borrowShr _ body k => max body.slotNeed k.slotNeed
  | _, _, .borrowMut _ body k => max body.slotNeed k.slotNeed
  | _, _, .callRef _ _ _ _ k => k.slotNeed
  | _, _, .guard _ => 0
  | _, _, .loop (s := s) _ _ _ c body k =>
    let A := if Exp.accSlot c body k then s.slotN else 0
    max (A + (if Exp.cntSlot c body then 1 else 0) +
        max (if c.Conf (.word FR) then max 1 c.slotNeed else c.slotNeed)
          (if Exp.bodyW c body k then max s.slotN body.slotNeed else body.slotNeed))
      (A + k.slotNeed)

/-- The memory lowering of a term in tail mode `tm`: write its value at offset `d` from the base
pointer, using memory from offset `n` up. -/
def lowerM : {Γ : List Ty} → {t : Ty} → Exp Γ t → Tl → List Loc → Nat → Nat → Stmt
  | _, _, .atom (t := t) a, tm, ρ, _, d =>
    .seq (.tick (.atom (tm.hb.atomW t)))
      (match tm with
       | .whole _ => .skip
       | .word k => atomSlots a ρ k t.slotN
       | _ => atomTo a ρ d)
  | _, _, .let_ (s := s) e₁ e₂, tm, ρ, n, d =>
    if e₂.slotBind then
      -- a slot-resident binder's value goes to its frame slots from `FR + slotsIn ρ`, computed
      -- straight into them when the bound term's tails allow it, and through memory and loads otherwise
      .seq (.tick .let_) (.seq (if e₁.Conf (.word (FR + slotsIn ρ)) then
          lowerM e₁ (.word (FR + slotsIn ρ)) ρ (n + s.size) n
        else .seq (lowerM e₁ .none ρ (n + s.size) n)
            (ldSlots (scalarWidth s.size) (FR + slotsIn ρ) (.slot BP) n s.slotN))
        (lowerM e₂ tm.up (.slot n (FR + slotsIn ρ) s.slotN :: ρ) (n + s.size) d))
    else
      .seq (.tick .let_) (.seq (lowerM e₁ .none ρ (n + s.size) n) (lowerM e₂ tm.up (.own n :: ρ) (n + s.size) d))
  | _, _, .ite c e₁ e₂, tm, ρ, n, d =>
    .seq (.tick .ite) (.seq (atomWord c ρ RT)
      (.ite (.slot RT) (lowerM e₁ tm ρ n d) (lowerM e₂ tm ρ n d)))
  | _, _, .prim (r := r) p args, tm, ρ, _, d =>
    let pc := primCode p [.slot RX, .slot RY]
    .seq (.tick pc.1) (.seq (primLoad args ρ)
      (match tm with
       | .word k => .bin pc.2.1 k pc.2.2.1 pc.2.2.2
       | _ => .seq (.bin pc.2.1 RT pc.2.2.1 pc.2.2.2)
          (.store (scalarWidth r.size) (.slot BP) (UInt64.ofNat d) (.slot RT))))
  | _, _, .call (ps := ps) (r := r) name body args, tm, ρ, n, d =>
    -- word parameters go in the callee's frame slots `FR, …, FR + q - 1`, the others in its region at
    -- the watermark
    let P := ctxSize ps
    let ρc := paramLocs body.wordParam ps 0 0
    let q := slotsIn ρc
    .seq (.tick (.call (ctxWords ps + width r)))
      (.seq (argsPass body.wordParam args ρ n 0)
      (.seq (.bin .add RX (.slot BP) (.imm (UInt64.ofNat n)))
      (if body.Conf (.word (FR + q)) then
        -- a result of slot-resident type is returned as words: the callee computes it into its slots from
        -- `FR + q`, and the return writes them to the destination slots, or to the scratch slots from
        -- `REXT` before they are stored
        .seq (.call name (FR + q + max r.slotN body.slotNeed)
            (lowerM body (.word (FR + q)) ρc (P + r.size) P) (retSlots (FR + q) r.slotN)
            (callOps body.wordParam ps) (match tm with | .word k => k | _ => REXT))
          (match tm with
           | .word _ => .skip
           | _ => stSlots (scalarWidth r.size) (.slot BP) d REXT r.slotN)
      else
        .seq (.call name (FR + q + body.slotNeed)
            (lowerM body .none ρc (P + r.size) P) [] (callOps body.wordParam ps) 0)
          (match tm with
           | .word k => ldSlots (scalarWidth r.size) k (.slot BP) (n + P) r.slotN
           | _ => copyM (n + P) d r.size))))
  | _, _, .ok (ε := ε) (α := α) a, tm, ρ, _, d =>
    .seq (.tick (.ctor (width (.result ε α)))) (resultCode ε α a 1 tm ρ d)
  | _, _, .err (ε := ε) (α := α) a, tm, ρ, _, d =>
    .seq (.tick (.ctor (width (.result ε α)))) (resultCode ε α a 0 tm ρ d)
  | _, _, .match_ (ε := ε) (α := α) (t := t) s eE eO, tm, ρ, n, d =>
    -- the scrutinee is at `ls`, after a literal or a reference is copied to `n`; the payload is copied
    -- to the arm's variable at `n'` or loaded into its frame slots
    let S := (Ty.result ε α).size
    let po := payloadOff (Data.shape (Except ε.carrier α.carrier))
    let ls := scrutLoc s ρ n
    let n' := n + S
    match s.slotOf ρ with
    | some k =>
      -- a slot-resident scrutinee: the tag is the low byte of its first word, the payload the words
      -- after it
      .seq (.tick (.match_ (width (.result ε α)))) (.seq (.bin .band RT (.slot k) (.imm 0xFF))
        (.ite (.slot RT)
          (slotArm eO.slotBind α (FR + slotsIn ρ) (k + 1) (s.slotNw ρ - 1) n'
            fun l => lowerM eO tm.up (l :: ρ) (n' + α.size) d)
          (slotArm eE.slotBind ε (FR + slotsIn ρ) (k + 1) (s.slotNw ρ - 1) n'
            fun l => lowerM eE tm.up (l :: ρ) (n' + ε.size) d)))
    | none =>
    .seq (.tick (.match_ (width (.result ε α)))) (.seq (scrutPre s ρ n) (.seq (.load .w8 RT (.slot BP) (UInt64.ofNat ls))
      (.ite (.slot RT)
        (memArm eO.slotBind α (FR + slotsIn ρ) BP (ls + po) n'
          fun l => lowerM eO tm.up (l :: ρ) (n' + α.size) d)
        (memArm eE.slotBind ε (FR + slotsIn ρ) BP (ls + po) n'
          fun l => lowerM eE tm.up (l :: ρ) (n' + ε.size) d))))
  | _, _, .ext sig args, tm, ρ, _, d =>
    let r := extArgs args ρ REXT
    .seq (.tick (.ext args.depth args.slices)) (.seq r.1
      (match tm with
       | .word k => .seq (.ext sig.sym sig.noreturn k r.2) .skip
       | _ => .seq (.ext sig.sym sig.noreturn RX r.2) (.store .w64 (.slot BP) (UInt64.ofNat d) (.slot RX))))
  | _, _, .extMut sig args k, tm, ρ, n, d =>
    -- the result word goes to `n`, the continuation's variable, or to its frame slot; the slice is
    -- written in place
    let r := extArgs args ρ REXT
    .seq (.tick (.ext args.depth args.slices)) (.seq r.1
      (if k.slotBind then
        .seq (.ext sig.sym sig.noreturn (FR + slotsIn ρ) r.2)
          (lowerM k tm.up (.slot n (FR + slotsIn ρ) 1 :: ρ) (n + 8) d)
      else .seq (.ext sig.sym sig.noreturn RX r.2)
        (.seq (.store .w64 (.slot BP) (UInt64.ofNat n) (.slot RX))
          (lowerM k tm.up (.own n :: ρ) (n + 8) d))))
  | _, _, .mk (ps := ps) (t := t) c args, tm, ρ, _, d =>
    match tm, mkCode? c args ρ d (tm.hb.mkW ps t) with
    | .none, some code => code
    | _, _ =>
    .seq (.tick (.ctor (tm.hb.mkW ps t)))
      (match tm with
       | .word k => if c.slotOk then ctorCode args c.plan ρ k t.slotN else .skip
       | _ => .seq (argsTo args
          (match tm with
           | .split _ _ => c.plan.1.take 1
           | _ => c.plan.1) ρ d)
        (match c.plan.2 with
         | some i => .store .w8 (.slot BP) (UInt64.ofNat d) (.imm (UInt64.ofNat i))
         | none => .skip))
  | _, _, .read (t := t) p, tm, ρ, _, d =>
    .seq (.tick (.mem p.depth (width t)))
      (match p.slotField ρ with
       | some (K, nw) =>
         -- a whole-word field of a slot-resident variable: its slots
         match tm with
         | .word k => movSlots k K (min t.slotN nw)
         | _ => stSlots (scalarWidth t.size) (.slot BP) d K (min t.slotN nw)
       | none =>
         match tm with
         | .word k => .seq (placeAddr p ρ) (ldSlots (scalarWidth t.size) k (.slot RA) 0 t.slotN)
         | _ => placeRead p ρ d)
  | _, _, .assign (t := t) p a k, tm, ρ, n, d =>
    match p.slotOf ρ with
    | some x => .seq (.tick (.mem p.depth (width t)))
      (.seq (atomSlots a ρ x (ρ.getD p.root default).nw) (lowerM k tm ρ n d))
    | none =>
      match p.slotField ρ with
      | some (K, nw) =>
        -- a whole-word field of a slot-resident variable: the atom's words into its slots
        .seq (.tick (.mem p.depth (width t))) (.seq (atomSlotsS a ρ K (min t.slotN nw))
          (lowerM k tm ρ n d))
      | none =>
        .seq (.tick (.mem p.depth (width t))) (.seq (atomTo a ρ n) (.seq (placeWrite p ρ n)
          (lowerM k tm ρ n d)))
  | _, _, .case (t := t) (p := pt) (q := qt) (u := u) s sp eP eQ, tm, ρ, n, d =>
    let po := payloadOff t.data.shape
    let ls := scrutLoc s ρ n
    let n' := n + t.size
    match s.slotOf ρ with
    | some k =>
      -- a slot-resident scrutinee: the tag is the low byte of its first word, the payload the words
      -- after it, and the rest either those words or the whole value's
      .seq (.tick (.match_ (width t))) (.seq (.bin .band RT (.slot k) (.imm 0xFF))
        (.seq (.bin .eq RX (.slot RT) (.imm (UInt64.ofNat sp.tag)))
        (.ite (.slot RX)
          (slotArm eP.slotBind pt (FR + slotsIn ρ) (k + 1) (s.slotNw ρ - 1) n'
            fun l => lowerM eP tm.up (l :: ρ) (n' + pt.size) d)
          (slotArm eQ.slotBind qt (FR + slotsIn ρ) (k + sp.restOff) (s.slotNw ρ - sp.restOff) n'
            fun l => lowerM eQ tm.up (l :: ρ) (n' + qt.size) d))))
    | none =>
    .seq (.tick (.match_ (width t))) (.seq (scrutPre s ρ n) (.seq (.load .w8 RT (.slot BP) (UInt64.ofNat ls))
      (.seq (.bin .eq RX (.slot RT) (.imm (UInt64.ofNat sp.tag)))
      (.ite (.slot RX)
        (memArm eP.slotBind pt (FR + slotsIn ρ) BP (ls + po) n'
          fun l => lowerM eP tm.up (l :: ρ) (n' + pt.size) d)
        (.seq (restCode sp.mode sp.tag ls po n' qt.size) (lowerM eQ tm.up (.own n' :: ρ) (n' + qt.size) d))))))
  | _, _, .put (t := t) p i a k, tm, ρ, n, d =>
    .seq (.tick (.mem (p.depth + 1) (width t))) (.seq (atomTo a ρ n)
      (.seq (placeAddr p ρ) (.seq (elemAddr i ρ t.size)
        (.seq (copyB (.slot BP) n (.slot RA) 0 t.size) (lowerM k tm ρ n d)))))
  | _, _, .take (t := t) (dflt := _) p i k, tm, ρ, n, d =>
    .seq (.tick (.mem (p.depth + 1) (width t)))
      (.seq (placeAddr p ρ) (.seq (elemAddr i ρ t.size)
        (memArm k.slotBind t (FR + slotsIn ρ) RA 0 n fun l => lowerM k tm.up (l :: ρ) (n + t.size) d)))
  | _, _, .borrowShr (u := u) p body k, tm, ρ, n, d =>
    .seq (.tick (.ref p.depth)) (.seq (placeAddr p ρ)
      (.seq (refStore p ρ n)
      (.seq (lowerM body .none (p.refLoc n :: ρ) (n + p.slotW + u.size) (n + p.slotW))
        (lowerM k tm.up (.own (n + p.slotW) :: ρ) (n + p.slotW + u.size) d))))
  | _, _, .borrowMut (t := t) (u := u) p body k, tm, ρ, n, d =>
    .seq (.tick (.ref p.depth)) (.seq (placeAddr p ρ)
      (.seq (refStore p ρ n)
      (.seq (lowerM body (borrowTl u t) (p.refLoc n :: ρ) (n + p.slotW + u.size) (n + p.slotW))
        (lowerM k tm.up (.own (n + p.slotW) :: ρ) (n + p.slotW + u.size) d))))
  | _, _, .callRef (r := r) name _ body args k, tm, ρ, n, d =>
    let P := args.frame
    .seq (.tick (.callR args.depth args.refs args.ownWords))
      (.seq (rargsPass args ρ n)
      (.seq (.bin .add RX (.slot BP) (.imm (UInt64.ofNat n)))
      (.seq (.call name (FR + body.slotNeed) (lowerM body (callTl r args) (args.locs 0) (P + r.size) P) [] [.slot RX] 0)
        (lowerM k tm.up (.own (n + P) :: ρ) (n + P + r.size) d))))
  | _, _, .guard g, _, ρ, _, d => .seq (.tick (.mem g.depth 0)) (guardCode g ρ d)
  | _, _, .loop (s := s) N cs init c body k, tm, ρ, n, d =>
    -- The accumulator is at `n`, which is the continuation's variable, so nothing is copied at the
    -- exit, or in frame slots. Above it are the loop's cells: the counter at `a` or in the counter
    -- variable's frame slot, the counter variable at `a + 8`, the condition at `a + 16` or in frame
    -- slot `T` after the loop variables', and the body's new accumulator at `a + 17` or in the slots
    -- from `T`. The body writes the carried variables and hands them back in place, so nothing is
    -- copied for them.
    let a := n + s.size
    let m := a + 17 + s.size
    let la := accLoc (Exp.accSlot c body k) ρ n s.slotN
    let lc := cntLoc (Exp.cntSlot c body) (la :: ρ) a
    let ρ' := lc :: la :: ρ
    let tmc := flagTl c (FR + slotsIn ρ')
    let tmb := bodyTl cs c body k (FR + slotsIn ρ')
    .seq (.tick (.loop (width s))) (.seq (accInit la init ρ)
      (.seq (cntInit lc a)
      (.seq (.while
        (.seq (cntTest lc a N)
            (.ite (.slot RX)
              (.seq (cntEnter lc a)
                (.seq (lowerM c tmc ρ' m (a + 16))
                  (.seq (flagLoad tmc a)
                    (.ite (.slot RX) .skip (.tick (.iter (width s)))))))
              .skip))
        (.slot RX)
        (.seq (.tick (.iter (width s))) (.seq (lowerM body tmb ρ' m (a + 17))
          (.seq (accNext la (bodyLoc tmb a s.slotN) s.size) (cntNext lc a)))))
        (lowerM k tm.up (la :: ρ) a d))))

/-- The bytes that a term needs above its watermark, callees included. -/
def _root_.Millipede.Exp.memNeed : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat
  | _, _, .atom _ => 0
  | _, _, .let_ (s := s) e₁ e₂ => s.size + max e₁.memNeed e₂.memNeed
  | _, _, .ite _ e₁ e₂ => max e₁.memNeed e₂.memNeed
  | _, _, .prim _ _ => 0
  | _, _, .call (ps := ps) (r := r) _ body _ => ctxSize ps + r.size + body.memNeed
  | _, _, .ok _ => 0
  | _, _, .err _ => 0
  | _, _, .match_ (ε := ε) (α := α) _ eE eO =>
    (Ty.result ε α).size + max (ε.size + eE.memNeed) (α.size + eO.memNeed)
  | _, _, .ext _ _ => 0
  | _, _, .extMut _ _ k => 8 + k.memNeed
  | _, _, .mk _ _ => 0
  | _, _, .read _ => 0
  | _, _, .assign (t := t) _ _ k => max t.size k.memNeed
  | _, _, .case (t := t) (p := pt) (q := qt) _ _ eP eQ =>
    t.size + max (pt.size + eP.memNeed) (qt.size + eQ.memNeed)
  | _, _, .put (t := t) _ _ _ k => max t.size k.memNeed
  | _, _, .take (t := t) (dflt := _) _ _ k => t.size + k.memNeed
  | _, _, .borrowShr (u := u) p body k => p.slotW + u.size + max body.memNeed k.memNeed
  | _, _, .borrowMut (u := u) p body k => p.slotW + u.size + max body.memNeed k.memNeed
  | _, _, .callRef (r := r) _ _ body args k => args.frame + r.size + max body.memNeed k.memNeed
  | _, _, .guard _ => 0
  | _, _, .loop (s := s) _ _ _ c body k =>
    s.size + max (17 + s.size + max c.memNeed body.memNeed) k.memNeed

/-- The place has no `Slots` cell selector. -/
def _root_.Millipede.Place.noSlot {Γ : List Ty} : {t : Ty} → Place Γ t → Bool
  | _, .var _ => true
  | _, .field p _ => p.noSlot
  | _, .index (dflt := _) p _ => p.noSlot
  | _, .slot (dflt := _) _ _ => false
  | _, .range p _ _ => p.noSlot
  | _, .pair2 (dflt := _) p _ _ => p.noSlot
  | _, .rangeS _ _ _ => false
  | _, .pair2S (dflt := _) _ _ _ => false

/-- The window of a place's occupancies within its root's. For a variable followed by certified
field lenses only, the place's components are the root's at `[o, o + n)`. The result is `none`
past an element or cell selector, or an uncertified lens. -/
def _root_.Millipede.Place.occWin {Γ : List Ty} : {t : Ty} → Place Γ t → Option (Nat × Nat)
  | _, .var (t := t) _ => some (0, Data.occsN t.carrier)
  | _, .field (s := s) (t := t) p l => match p.occWin with
    | some (o, _) => if l.law.isSome then some (o + Data.occsOff s.carrier l.index, Data.occsN t.carrier)
      else none
    | none => none
  | _, _ => none

/-- The window of the root's occupancies that a write to the place may change. It is the window of
the place's longest prefix of certified fields, or an empty window when that prefix is followed by
a `Slots` cell, because a write through a full cell keeps every cell's occupancy. -/
def _root_.Millipede.Place.setWin {Γ : List Ty} : {t : Ty} → Place Γ t → Nat × Nat
  | _, .var (t := t) _ => (0, Data.occsN t.carrier)
  | _, .field p l => ((Place.field p l).occWin).getD p.setWin
  | _, .index (dflt := _) p _ => p.setWin
  | _, .slot (dflt := _) p _ => match p.occWin with
    | some (o, _) => (o, 0)
    | none => p.setWin
  | _, .range p _ _ => p.setWin
  | _, .pair2 (dflt := _) p _ _ => p.setWin
  | _, .rangeS (t := t) (n := n) _ _ _ => (0, Data.occsN (Ty.slots t n).carrier)
  | _, .pair2S (t := t) (n := n) (dflt := _) _ _ _ => (0, Data.occsN (Ty.slots t n).carrier)

/-- Every `Slots` cell selector of the place is on a place whose occupancy window within its root's
is apart from `w`. -/
def _root_.Millipede.Place.slotsAway {Γ : List Ty} (w : Nat × Nat) : {t : Ty} → Place Γ t → Bool
  | _, .var _ => true
  | _, .field p _ => p.slotsAway w
  | _, .index (dflt := _) p _ => p.slotsAway w
  | _, .slot (dflt := _) p _ => p.slotsAway w && match p.occWin with
    | some (o, n) => decide (w.1 + w.2 ≤ o ∨ o + n ≤ w.1)
    | none => false
  | _, .range p _ _ => p.slotsAway w
  | _, .pair2 (dflt := _) p _ _ => p.slotsAway w
  | _, .rangeS _ _ _ => false
  | _, .pair2S (dflt := _) _ _ _ => false

/-- The `&mut` arguments of a reference call that go through `Slots` cells stay valid across the
earlier write-backs, where `prev` holds the roots and write windows of the earlier `&mut`
arguments. The value semantics writes the arguments back one after another, so the obligation of a
later place through a `Slots` cell, that the cell is full, is about the value after the earlier
write-backs, which the bytes cannot show because cells have no tags. The condition is decided on
occupancies instead. A later argument on the root of an earlier one may go through a cell when the
cell's `Slots` is reached from the root by certified fields only and its occupancies are apart from
the earlier argument's write window, as for `&mut pool.count` followed by `&mut pool.slots[k]`. -/
def _root_.Millipede.RArgs.mutOk {Γ : List Ty} (prev : List (Nat × (Nat × Nat))) :
    {ps os : List Ty} → RArgs Γ ps os → Bool
  | _, _, .nil => true
  | _, _, .own _ as => as.mutOk prev
  | _, _, .shr _ as => as.mutOk prev
  | _, _, .mut p as => prev.all (fun e => e.1 != p.root || p.slotsAway e.2) &&
    as.mutOk ((p.root, p.setWin) :: prev)

/-- The places of a reference call's arguments can be lowered: each is contiguous, or a slice of a
contiguous place. -/
def _root_.Millipede.RArgs.memOk {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Bool
  | _, _, .nil => true
  | _, _, .own _ as => as.memOk
  | _, _, .shr p as => p.refOk && as.memOk
  | _, _, .mut p as => p.refOk && as.memOk

/-- The slice arguments of a reference call, as the callee's parameter number, counted from `j`,
and whether the slice is passed `&mut`. -/
def _root_.Millipede.RArgs.views {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Nat →
    List (Nat × Bool)
  | _, _, .nil, _ => []
  | _, _, .own _ as, j => as.views (j + 1)
  | _, _, .shr p as, j => (if p.isRange then [(j, false)] else []) ++ as.views (j + 1)
  | _, _, .mut p as, j => (if p.isRange then [(j, true)] else []) ++ as.views (j + 1)

/-- The parameter numbers, counted from `j`, of the arguments that are the pair `p[i], p[j]`. Such
a callee parameter is two addresses and is used only through its fields. -/
def _root_.Millipede.RArgs.pairs {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Nat → List Nat
  | _, _, .nil, _ => []
  | _, _, .own _ as, j => as.pairs (j + 1)
  | _, _, .shr p as, j => (if p.isPair2 then [j] else []) ++ as.pairs (j + 1)
  | _, _, .mut p as, j => (if p.isPair2 then [j] else []) ++ as.pairs (j + 1)

/-- The callee's slice parameters are views, as in a slice borrow's body. Each is used only through
its elements, and a `&mut` one meets the hand-back condition, followed by the later `&mut`
parameters. A parameter for the pair `p[i], p[j]` is used only through its fields. -/
def _root_.Millipede.RArgs.viewsOk {Γ ps os : List Ty} {r : Ty} (args : RArgs Γ ps os)
    (body : Exp ps (.pair r (.tup os))) : Bool :=
  (args.views 0).all (fun (j, m) => body.VSafe j (callTl r args) &&
    (!m || body.HBv j ((args.mutIdx 0).filter (j < ·)))) &&
  (args.pairs 0).all fun j => body.VSafe j (callTl r args)

/-- The term is in the fragment that the memory lowering handles, callees included. The module doc
lists what is refused. -/
def _root_.Millipede.Exp.memOk : {Γ : List Ty} → {t : Ty} → Exp Γ t → Bool
  | _, _, .atom _ => true
  | _, _, .let_ e₁ e₂ => e₁.memOk && e₂.memOk
  | _, _, .ite _ e₁ e₂ => e₁.memOk && e₂.memOk
  | _, _, .prim _ _ => true
  | _, _, .call _ body _ => body.memOk
  | _, _, .ok _ => true
  | _, _, .err _ => true
  | _, _, .match_ _ eE eO => eE.memOk && eO.memOk
  | _, _, .ext _ args => args.noOut && args.memOk && decide (args.wordCount ≤ FR - REXT)
  | _, _, .extMut _ args k =>
    args.oneOut && args.memOk && decide (args.wordCount ≤ FR - REXT) && k.memOk
  | _, _, .mk _ _ => true
  | _, _, .read p => p.memOk
  | _, _, .assign p _ k => p.memOk && k.memOk
  | _, _, .case (t := t) _ _ eP eQ =>
    (match t.data.shape with
     | .sum vs => decide (vs.length ≤ 2 ^ 8)
     | _ => false) && eP.memOk && eQ.memOk
  | _, _, .put p _ _ k => p.contig && k.memOk
  | _, _, .take (dflt := _) p _ k => p.contig && k.memOk
  | _, _, .borrowShr p body k =>
    p.refOk && (p.contig || body.VSafe 0 .none) && body.memOk && k.memOk
  | _, _, .borrowMut (t := t) (u := u) p body k =>
    p.refOk && (p.contig || body.VSafe 0 (borrowTl u t) && (!p.isRange || body.HB 0)) &&
      body.Conf (borrowTl u t) &&
      body.memOk && k.memOk
  | _, _, .callRef (r := r) _ _ body args k =>
    args.memOk && args.mutOk [] && args.viewsOk body && body.Conf (callTl r args) && body.memOk &&
      k.memOk
  | _, _, .guard (.valid p _) => (placeCheck p []).isSome
  | _, _, .loop (s := s) N cs _ c body k =>
    decide (N < UInt64.size) && cs.distinct && body.Conf (loopTl s cs) && c.memOk && body.memOk &&
      k.memOk

/-! ## Refusal messages

`Exp.memWhy` names the first construct of a term that `Exp.memOk` refuses. It is used only for
`lower`'s error message, and no theorem depends on it. -/

/-- The first refused argument place of a reference call. -/
def _root_.Millipede.RArgs.memWhy {Γ : List Ty} : {ps os : List Ty} → RArgs Γ ps os → Option String
  | _, _, .nil => none
  | _, _, .own _ as => as.memWhy
  | _, _, .shr p as | _, _, .mut p as =>
    if p.refOk then as.memWhy
    else some "a reference argument that is a non-contiguous place (a selector under a slice or a \
        pair `p[i], p[j]`, or a slice or pair of one)"

/-- The first construct of a term that the pipeline refuses, or `none`. -/
def _root_.Millipede.Exp.memWhy : {Γ : List Ty} → {t : Ty} → Exp Γ t → Option String
  | _, _, .atom _ => none
  | _, _, .let_ e₁ e₂ => e₁.memWhy <|> e₂.memWhy
  | _, _, .ite _ e₁ e₂ => e₁.memWhy <|> e₂.memWhy
  | _, _, .prim _ _ => none
  | _, _, .call _ body _ => body.memWhy
  | _, _, .ok _ => none
  | _, _, .err _ => none
  | _, _, .match_ _ eE eO => eE.memWhy <|> eO.memWhy
  | _, _, .ext _ args =>
    if !args.noOut then some "a plain extern call with a mutable slice (use the extMut form)"
    else if !args.memOk then some "an extern buffer that is a slice of a non-contiguous place"
    else if !decide (args.wordCount ≤ FR - REXT) then
      some "an extern call with more argument words than the scratch frame holds (FR - REXT)"
    else none
  | _, _, .extMut _ args k =>
    if !args.oneOut then
      some "an extern call writing memory whose output buffers are not exactly one mutable slice"
    else if !args.memOk then some "an extern buffer that is a slice of a non-contiguous place"
    else if !decide (args.wordCount ≤ FR - REXT) then
      some "an extern call with more argument words than the scratch frame holds (FR - REXT)"
    else k.memWhy
  | _, _, .mk _ _ => none
  | _, _, .read p =>
    if p.memOk then none else some "a read of a non-contiguous place (a selector under a slice or a pair)"
  | _, _, .assign p _ k =>
    if p.memOk then k.memWhy
    else some "an assignment to a non-contiguous place (a selector under a slice or a pair)"
  | _, _, .case (t := t) _ _ eP eQ =>
    if (match t.data.shape with
     | .sum vs => decide (vs.length ≤ 2 ^ 8)
     | _ => false) then eP.memWhy <|> eQ.memWhy
    else some "a `case` on a sum with more than 256 variants (the tag is one byte)"
  | _, _, .put p _ _ k | _, _, .take (dflt := _) p _ k =>
    if p.contig then k.memWhy else some "`put`/`take` on a non-contiguous place"
  | _, _, .borrowShr p body k =>
    if !p.refOk then
      some "a borrow of a non-contiguous place (a selector under a slice or a pair, or a slice of one)"
    else if !p.contig && !body.VSafe 0 .none then
      some (if p.isRange then "a slice view used other than through its elements (copied, \
          assigned, passed as an owned argument or to a callee that does not use it through its \
          elements, re-borrowed whole)"
        else "a borrow of the pair `p[i], p[j]` used other than through its fields `r.fst`, \
          `r.snd` (copied, assigned or passed whole: it lives at two addresses)")
    else body.memWhy <|> k.memWhy
  | _, _, .borrowMut (t := t) (u := u) p body k =>
    if !p.refOk then
      some "a borrow of a non-contiguous place (a selector under a slice or a pair, or a slice of one)"
    else if !p.contig && !body.VSafe 0 (borrowTl u t) then
      some (if p.isRange then "a slice view used other than through its elements (copied, \
          assigned, passed as an owned argument or to a callee that does not use it through its \
          elements, re-borrowed whole)"
        else "a `&mut` borrow of the pair `p[i], p[j]` used other than through its fields `r.fst`, \
          `r.snd` (copied, assigned or passed whole: it lives at two addresses; a loop writing a \
          field carries the borrow whole)")
    else if p.isRange && !body.HB 0 then
      some "a `&mut` slice borrow whose body fails the hand-back condition Exp.HB (the view written \
        other than through its cells, or not handed back by a certified hand-back constructor)"
    else if !body.Conf (borrowTl u t) then
      some "a `&mut` borrow whose body does not hand back its reference in place (Exp.Conf)"
    else body.memWhy <|> k.memWhy
  | _, _, .callRef (r := r) _ _ body args k =>
    match args.memWhy with
    | some m => some m
    | none =>
      if !args.mutOk [] then
        some "a reference call with several `&mut` arguments on one root where a later one goes \
          through a `Slots` cell whose occupancies an earlier one may change (a cell not reached \
          from the root by certified fields only, or a field window overlapping the earlier \
          argument's, RArgs.mutOk)"
      else if !args.viewsOk body then
        some "a callee whose slice parameter is used other than through its elements (copied, \
          assigned, re-borrowed whole, or passed on whole by `&mut` to a callee that does not hand \
          it back exactly, Exp.HBx), or whose `&mut` slice parameter fails the hand-back condition \
          Exp.HBv, or whose parameter for a pair `p[i], p[j]` is used other than through its \
          fields (it lives at two addresses)"
      else if !body.Conf (callTl r args) then
        some "a callee that does not hand back its `&mut` parameters in place (Exp.Conf)"
      else body.memWhy <|> k.memWhy
  | _, _, .guard (.valid p _) =>
    if (placeCheck p []).isSome then none
    else some "a checked guard on a place that cannot be checked at run time"
  | _, _, .loop (s := s) N cs _ c body k =>
    if !decide (N < UInt64.size) then
      some "a loop bound of 2^64 or more (the counter is one machine word)"
    else if !cs.distinct then some "a loop whose carried variables are not distinct"
    else if !body.Conf (loopTl s cs) then
      some "a loop body that does not hand back its carried variables in place (Exp.Conf)"
    else c.memWhy <|> body.memWhy <|> k.memWhy

/-! ## Programs -/

/-- The bytes that a reactor step needs above the root before its own frame: none when it hands
back its root in place, and otherwise a temporary of the root's size. -/
def _root_.Millipede.Program.stepTmp (p : Program) : Nat :=
  if p.step.Conf (.whole 0) then 0 else p.State.size

/-- The bytes of static memory that a lowered program uses: the root's size plus the larger of
the needs of `init` and of `step`, the latter including its temporary. -/
def _root_.Millipede.Program.memBytes (p : Program) : Nat :=
  p.State.size + max p.init.memNeed (p.stepTmp + p.step.memNeed)

/-- The code of one reactor step. A step that hands back its root in place, as `mp def` steps that
take `&mut` state do, runs on the root and copies nothing. Any other step writes its result to a
temporary right above the root, because the step may read the old root until its end, and the
result is then copied over the root. -/
def stepCode (p : Program) : Stmt :=
  let S := p.State.size
  if p.step.Conf (.whole 0) then lowerM p.step (.whole 0) [.own 0] S 0
  else .seq (lowerM p.step .none [.own 0] (S + S) S) (copyM S 0 S)

/-- The main code of a lowered program. The main activation's base pointer is `0` and the root
lives at offset `0`; `init` builds it in place and each step updates it. -/
def lowerProg (p : Program) : Prog :=
  let S := p.State.size
  ⟨.seq (lowerM p.init .none [] S 0) (.while .skip (.imm 1) (stepCode p)),
    FR + max p.init.slotNeed p.step.slotNeed⟩

/-- The memory lowering pass. It refuses programs outside the lowered fragment and programs whose
memory does not fit the 64-bit address space. -/
def lower (p : Program) : Except String Prog :=
  if p.init.memOk && p.step.memOk && decide (p.memBytes < UInt64.size)
  then .ok (lowerProg p)
  else .error ("lower: " ++
    match p.init.memWhy <|> p.step.memWhy with
    | some m => m
    | none =>
      if !decide (p.memBytes < UInt64.size) then
        "static memory (the root and the larger frame need) beyond the 64-bit address space"
      else "outside the lowered fragment (Exp.memOk)")

end Millipede.Flat
