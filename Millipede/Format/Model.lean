/-!
# Format descriptions: the model

A format description is a value of the inductive type `Fmt`, which says how a value is laid out
as bytes. Its values are those of the plain inductive type `Val`, and `Fmt.ok f t v` says that `v`
is a value of `f`. The meaning of a description is three functions over byte lists, each defined
by structural recursion over the description:

- `Fmt.parse f bs` reads a value from the front of `bs` and returns it with the bytes left over,
  or `none`;
- `Fmt.write f v` gives the bytes of a value;
- `Fmt.check f bs` is the validator, which returns the bytes left over without building a value.

`Fmt.maxSize f` is a static bound on the bytes of every value, which may exceed the largest
encoding. The theorems that relate the three functions are in `Millipede/Format/Theorems.lean`.

The forms are fixed-width unsigned integers of either byte order (`uint k e`, `k` bytes), byte
arrays of a fixed length (`bytes n`), constants (`const l`), ignored bytes (`skip n`), the empty
record (`unit`), records as nested pairs (`pair a b`), byte strings with a length prefix and a
static bound (`lbytes k e max`), bounded repetitions with a count prefix (`array k e max f`), and
tagged unions (`union k e arms`). The arms of a union are a chain `arm t f (arm t' f' … noArm)`:
the union reads a tag of `k` bytes and then the format of the first arm with that tag, so when two
arms have the same tag the second is never used, in parsing, writing or `ok`.

The arms are constructors of `Fmt` itself, so that every function is one structural recursion over
one plain inductive type, which the kernel reduces. Each function therefore takes the selected tag
`t`, which only `arm` reads, and the plain forms `parse`, `write`, `check` and `ok` pass 0. Nothing
checks that a description is well formed: an `arm` outside a union reads as the arm for tag 0.
-/

namespace Millipede.Format

/-- The byte order of an integer. -/
inductive Endian where
  | big
  | little
deriving DecidableEq, Repr

/-- A format description. -/
inductive Fmt where
  /-- An unsigned integer of `k` bytes, in byte order `e`. -/
  | uint (k : Nat) (e : Endian)
  /-- `n` bytes. -/
  | bytes (n : Nat)
  /-- The bytes `l`, which must be present. -/
  | const (l : List UInt8)
  /-- `n` bytes that are ignored when read and written as zeros. -/
  | skip (n : Nat)
  /-- No bytes. -/
  | unit
  /-- `a` followed by `b`. -/
  | pair (a b : Fmt)
  /-- A length of `k` bytes in byte order `e`, at most `max`, then that many bytes. -/
  | lbytes (k : Nat) (e : Endian) (max : Nat)
  /-- A count of `k` bytes in byte order `e`, at most `max`, then that many values of `f`. -/
  | array (k : Nat) (e : Endian) (max : Nat) (f : Fmt)
  /-- A tag of `k` bytes in byte order `e`, then the format of the first arm with that tag. -/
  | union (k : Nat) (e : Endian) (arms : Fmt)
  /-- An arm of a union: the format `f` for tag `tag`, else the arms `rest`. -/
  | arm (tag : Nat) (f : Fmt) (rest : Fmt)
  /-- The end of the arms of a union, which matches no tag. -/
  | noArm
deriving Repr

/-- A value of a format. A repetition's elements are `pair v₁ (pair v₂ … unit)`. -/
inductive Val where
  | num (n : Nat)
  | bytes (l : List UInt8)
  | unit
  | pair (a b : Val)
  | tag (t : Nat) (v : Val)
deriving DecidableEq, Repr

/-! ## Integers -/

/-- The `k` low bytes of `n`, least significant first. -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: leBytes k (n / 256)

/-- The number whose bytes, least significant first, are `l`. -/
def leVal : List UInt8 → Nat
  | [] => 0
  | b :: l => b.toNat + 256 * leVal l

/-- The `k` low bytes of `n` in byte order `e`. -/
def encUint (k : Nat) (e : Endian) (n : Nat) : List UInt8 :=
  match e with
  | .little => leBytes k n
  | .big => (leBytes k n).reverse

/-- The number whose bytes in byte order `e` are `l`. -/
def decUint (e : Endian) (l : List UInt8) : Nat :=
  match e with
  | .little => leVal l
  | .big => leVal l.reverse

/-- Read an integer of `k` bytes from the front of `bs`. -/
def readUint (k : Nat) (e : Endian) (bs : List UInt8) : Option (Nat × List UInt8) :=
  if k ≤ bs.length then some (decUint e (bs.take k), bs.drop k) else none

/-! ## Repetitions -/

/-- The number of elements of a repetition's value. -/
def Val.count : Val → Nat
  | .pair _ b => b.count + 1
  | _ => 0

/-- Every element of a repetition's value satisfies `p`, and the chain ends in `unit`. -/
def Val.allItems (p : Val → Bool) : Val → Bool
  | .pair a b => p a && b.allItems p
  | .unit => true
  | _ => false

/-- The bytes of the elements, each by `w`. -/
def Val.writeItems (w : Val → List UInt8) : Val → List UInt8
  | .pair a b => w a ++ b.writeItems w
  | _ => []

/-- Read `c` elements, each by `p`. -/
def parseItems (p : List UInt8 → Option (Val × List UInt8)) :
    Nat → List UInt8 → Option (Val × List UInt8)
  | 0, bs => some (.unit, bs)
  | c + 1, bs => match p bs with
    | none => none
    | some (v, r) => match parseItems p c r with
      | none => none
      | some (vs, r') => some (.pair v vs, r')

/-- Skip `c` elements, each by `p`. -/
def checkItems (p : List UInt8 → Option (List UInt8)) : Nat → List UInt8 → Option (List UInt8)
  | 0, bs => some bs
  | c + 1, bs => match p bs with
    | none => none
    | some r => checkItems p c r

/-! ## The meaning of a description -/

namespace Fmt

/-- `v` is a value of `f` (in an arm chain, for the selected tag `t`). -/
def okT : Fmt → Nat → Val → Bool
  | uint k _, _, .num n => decide (n < 256 ^ k)
  | bytes n, _, .bytes l => decide (l.length = n)
  | const _, _, .unit => true
  | skip _, _, .unit => true
  | unit, _, .unit => true
  | pair a b, _, .pair v w => okT a 0 v && okT b 0 w
  | lbytes k _ m, _, .bytes l => decide (l.length ≤ m ∧ l.length < 256 ^ k)
  | array k _ m f, _, v => decide (v.count ≤ m ∧ v.count < 256 ^ k) && v.allItems (okT f 0)
  | union k _ arms, _, .tag t v => decide (t < 256 ^ k) && okT arms t v
  | arm tag f rest, t, v => if t = tag then okT f 0 v else okT rest t v
  | _, _, _ => false

/-- The bytes of `v` (in an arm chain, for the selected tag `t`). -/
def writeT : Fmt → Nat → Val → List UInt8
  | uint k e, _, .num n => encUint k e n
  | bytes _, _, .bytes l => l
  | const l, _, _ => l
  | skip n, _, _ => List.replicate n 0
  | pair a b, _, .pair v w => writeT a 0 v ++ writeT b 0 w
  | lbytes k e _, _, .bytes l => encUint k e l.length ++ l
  | array k e _ f, _, v => encUint k e v.count ++ v.writeItems (writeT f 0)
  | union k e arms, _, .tag t v => encUint k e t ++ writeT arms t v
  | arm tag f rest, t, v => if t = tag then writeT f 0 v else writeT rest t v
  | _, _, _ => []

/-- Read a value from the front of `bs` (in an arm chain, for the selected tag `t`). -/
def parseT : Fmt → Nat → List UInt8 → Option (Val × List UInt8)
  | uint k e, _, bs => (readUint k e bs).map fun (n, r) => (.num n, r)
  | bytes n, _, bs => if n ≤ bs.length then some (.bytes (bs.take n), bs.drop n) else none
  | const l, _, bs => if bs.take l.length = l then some (.unit, bs.drop l.length) else none
  | skip n, _, bs => if n ≤ bs.length then some (.unit, bs.drop n) else none
  | unit, _, bs => some (.unit, bs)
  | pair a b, _, bs => match parseT a 0 bs with
    | none => none
    | some (v, r) => match parseT b 0 r with
      | none => none
      | some (w, r') => some (.pair v w, r')
  | lbytes k e m, _, bs => match readUint k e bs with
    | none => none
    | some (n, r) => if n ≤ m ∧ n ≤ r.length then some (.bytes (r.take n), r.drop n) else none
  | array k e m f, _, bs => match readUint k e bs with
    | none => none
    | some (c, r) => if c ≤ m then parseItems (parseT f 0) c r else none
  | union k e arms, _, bs => match readUint k e bs with
    | none => none
    | some (t, r) => (parseT arms t r).map fun (v, r') => (.tag t v, r')
  | arm tag f rest, t, bs => if t = tag then parseT f 0 bs else parseT rest t bs
  | noArm, _, _ => none

/-- The validator: the bytes left after a value at the front of `bs`, without building the
value (in an arm chain, for the selected tag `t`). -/
def checkT : Fmt → Nat → List UInt8 → Option (List UInt8)
  | uint k _, _, bs => if k ≤ bs.length then some (bs.drop k) else none
  | bytes n, _, bs => if n ≤ bs.length then some (bs.drop n) else none
  | const l, _, bs => if bs.take l.length = l then some (bs.drop l.length) else none
  | skip n, _, bs => if n ≤ bs.length then some (bs.drop n) else none
  | unit, _, bs => some bs
  | pair a b, _, bs => match checkT a 0 bs with
    | none => none
    | some r => checkT b 0 r
  | lbytes k e m, _, bs => match readUint k e bs with
    | none => none
    | some (n, r) => if n ≤ m ∧ n ≤ r.length then some (r.drop n) else none
  | array k e m f, _, bs => match readUint k e bs with
    | none => none
    | some (c, r) => if c ≤ m then checkItems (checkT f 0) c r else none
  | union k e arms, _, bs => match readUint k e bs with
    | none => none
    | some (t, r) => checkT arms t r
  | arm tag f rest, t, bs => if t = tag then checkT f 0 bs else checkT rest t bs
  | noArm, _, _ => none

/-- The largest number of bytes of a value. -/
def maxSize : Fmt → Nat
  | uint k _ => k
  | bytes n => n
  | const l => l.length
  | skip n => n
  | unit => 0
  | pair a b => maxSize a + maxSize b
  | lbytes k _ m => k + m
  | array k _ m f => k + m * maxSize f
  | union k _ arms => k + maxSize arms
  | arm _ f rest => max (maxSize f) (maxSize rest)
  | noArm => 0

/-- A canonical description, in which each value has one encoding: no `skip`. A description with
`skip` is deliberately not canonical, because the skipped bytes may be anything. -/
def canonical : Fmt → Bool
  | skip _ => false
  | pair a b => canonical a && canonical b
  | array _ _ _ f => canonical f
  | union _ _ arms => canonical arms
  | arm _ f rest => canonical f && canonical rest
  | _ => true

/-- `v` is a value of `f`. -/
def ok (f : Fmt) (v : Val) : Bool := okT f 0 v
/-- The bytes of `v`. -/
def write (f : Fmt) (v : Val) : List UInt8 := writeT f 0 v
/-- Read a value from the front of `bs`. -/
def parse (f : Fmt) (bs : List UInt8) : Option (Val × List UInt8) := parseT f 0 bs
/-- The validator. -/
def check (f : Fmt) (bs : List UInt8) : Option (List UInt8) := checkT f 0 bs
/-- `bs` begins with a value of `f`. -/
def valid (f : Fmt) (bs : List UInt8) : Bool := (check f bs).isSome

end Fmt

end Millipede.Format
