import Millipede.Core.Data
import Millipede.Extern.Oracle

/-!
# Terms of the core language

A Core term `Exp Γ t` is an intrinsically typed de Bruijn term of type `t` whose free variables
have the types `Γ`, with index 0 for the head of `Γ`, the innermost binder. Ill-typed terms and
unbound variables cannot be built. Terms are in A-normal form, so the operands of primitives,
conditions, constructors, scrutinees and arguments are atoms. `Exp` is therefore a plain
inductive type, and its meaning is defined by structural recursion.

The scalar and control constructs are atoms, `let`, `if`, primitive application, a bounded loop,
calls, `ok` and `err` with a `match` on the linear `Result`, and extern calls. A call contains the
callee's body as a subterm, so recursion cannot be written. The memory constructs build values
from atoms, read, assign and borrow places, fill and empty `Slots` cells, take one step of an
exhaustive match on an enum, call functions with reference arguments, and test the obligations
of partial operations at run time. A place is a variable, a field, an element, a `Slots` cell, a
slice, or a pair of elements.

The value semantics has no pointers. A borrow binds the place's value, and an exclusive borrow's
body hands back the updated value with its result, which is written back to the place when the
borrow ends. A call with reference arguments writes the callee's handed-back values to the
argument places in the same way. Assignment changes a place for its continuation, which is the
rest of the enclosing block, and the checker rejects writes to variables bound outside the
current block. The exception is a loop's carried variables, which the body may assign and hands
back with its accumulator, so the loop passes them on to the next iteration and to its
continuation.

The design is described in doc/design/embedding.md.
-/

namespace Millipede

/-- A typed de Bruijn index. `Mem t Γ` is a position in `Γ` that holds the type `t`. -/
inductive Mem : Ty → List Ty → Type 1 where
  | here {t : Ty} {Γ : List Ty} : Mem t (t :: Γ)
  | there {t s : Ty} {Γ : List Ty} : Mem t Γ → Mem t (s :: Γ)

/-- The numeric de Bruijn index of a `Mem`. -/
def Mem.idx {t : Ty} : {Γ : List Ty} → Mem t Γ → Nat
  | _, .here => 0
  | _, .there m => m.idx + 1

/-- An environment, which holds one value for each type in `Γ`. It is an inductive type, so
`simp` sees through it. -/
inductive Env : List Ty → Type 1 where
  | nil : Env []
  | cons {t : Ty} {Γ : List Ty} : t.carrier → Env Γ → Env (t :: Γ)

/-- Look up a variable. -/
def Env.get {t : Ty} : {Γ : List Ty} → Env Γ → Mem t Γ → t.carrier
  | _, .cons v _, .here => v
  | _, .cons _ env, .there m => env.get m

@[simp] theorem Env.get_here {t : Ty} {Γ : List Ty} (v : t.carrier) (env : Env Γ) :
    (Env.cons v env).get .here = v := rfl
@[simp] theorem Env.get_there {t s : Ty} {Γ : List Ty} (v : s.carrier) (env : Env Γ)
    (m : Mem t Γ) : (Env.cons v env).get (.there m) = env.get m := rfl

/-- The occupancies of an environment's values, in order. They exist only in proofs. -/
def Env.occs : {Γ : List Ty} → Env Γ → List (Option (List Bool))
  | _, .nil => []
  | _, .cons v env => Data.occs v ++ env.occs

@[simp] theorem Env.occs_nil : (Env.nil).occs = [] := rfl
@[simp] theorem Env.occs_cons {t : Ty} {Γ : List Ty} (v : t.carrier) (env : Env Γ) :
    (Env.cons v env).occs = Data.occs v ++ env.occs := rfl

/-- An atom, which is a variable or a literal. -/
inductive Atom (Γ : List Ty) : Ty → Type 1 where
  | var {t : Ty} : Mem t Γ → Atom Γ t
  | lit {t : Ty} : t.carrier → Atom Γ t

/-- The value of an atom. -/
def Atom.denote {Γ : List Ty} {t : Ty} : Atom Γ t → Env Γ → t.carrier
  | .var m, env => env.get m
  | .lit v, _ => v

/-- A list of atoms, one per type in `ps`. -/
inductive Args (Γ : List Ty) : List Ty → Type 1 where
  | nil : Args Γ []
  | cons {t : Ty} {ts : List Ty} : Atom Γ t → Args Γ ts → Args Γ (t :: ts)

/-- The environment built from argument atoms, with the first argument at the head. -/
def Args.denote {Γ : List Ty} : {ps : List Ty} → Args Γ ps → Env Γ → Env ps
  | _, .nil, _ => .nil
  | _, .cons a as, env => .cons (a.denote env) (as.denote env)

/-! ## Primitives

A primitive is data rather than a constructor of `Exp`. Each has a name, a cost and a total
meaning that is exactly what the machine does, so `+`, `-` and `*` wrap, `x / 0 = 0`,
`x % 0 = x`, and shift amounts are taken modulo 64. Operands are in the order of `ps`, so `sub`
computes `x - y` with `x` first.

The primitives `add`, `sub`, `mul` and `trunc8` wrap. Each has a twin with the suffix `Nuw`, for
"no unsigned wrap", which denotes the same machine operation and carries the obligation that the
mathematical result fits the width. The twins are the meaning of the source operators `+!`, `-!`
and `*!`. -/

/-- The primitives on `U64` and `Bool`, and the conversions between `U8` and `U64`. `zext8` widens
a byte and `trunc8` keeps the low byte of a word, and the elaborator wraps the `U64` operations in
these conversions to compute on bytes. The machine loads a byte zero-extended and stores it with
a byte store, so `zext8` is a move and `trunc8` a mask. -/
inductive Prim : List Ty → Ty → Type 1 where
  | add : Prim [.u64, .u64] .u64
  | sub : Prim [.u64, .u64] .u64
  | mul : Prim [.u64, .u64] .u64
  | udiv : Prim [.u64, .u64] .u64
  | umod : Prim [.u64, .u64] .u64
  | band : Prim [.u64, .u64] .u64
  | bor : Prim [.u64, .u64] .u64
  | bxor : Prim [.u64, .u64] .u64
  | shl : Prim [.u64, .u64] .u64
  | shr : Prim [.u64, .u64] .u64
  | bnot : Prim [.u64] .u64
  | eq : Prim [.u64, .u64] .bool
  | ne : Prim [.u64, .u64] .bool
  | ult : Prim [.u64, .u64] .bool
  | ule : Prim [.u64, .u64] .bool
  | ugt : Prim [.u64, .u64] .bool
  | uge : Prim [.u64, .u64] .bool
  | not : Prim [.bool] .bool
  | and : Prim [.bool, .bool] .bool
  | or : Prim [.bool, .bool] .bool
  | beq : Prim [.bool, .bool] .bool
  | zext8 : Prim [.u8] .u64
  | trunc8 : Prim [.u64] .u8
  /-- `x + y` with the obligation `x + y < 2^64`, the source `+!` -/
  | addNuw : Prim [.u64, .u64] .u64
  /-- `x - y` with the obligation `y ≤ x` -/
  | subNuw : Prim [.u64, .u64] .u64
  /-- `x * y` with the obligation `x * y < 2^64` -/
  | mulNuw : Prim [.u64, .u64] .u64
  /-- the low byte of a word with the obligation `x < 2^8`, which narrows the word result of
  `+!`, `-!` or `*!` on `UInt8` -/
  | trunc8Nuw : Prim [.u64] .u8

/-- The source-level name of a primitive. -/
def Prim.name {ps : List Ty} {r : Ty} : Prim ps r → String
  | .add => "+" | .sub => "-" | .mul => "*" | .udiv => "/" | .umod => "%"
  | .band => "&&&" | .bor => "|||" | .bxor => "^^^" | .shl => "<<<" | .shr => ">>>"
  | .bnot => "~~~"
  | .eq => "==" | .ne => "!=" | .ult => "<" | .ule => "<=" | .ugt => ">" | .uge => ">="
  | .not => "!" | .and => "&&" | .or => "||" | .beq => "==b"
  | .zext8 => "toUInt64" | .trunc8 => "toUInt8"
  | .addNuw => "+!" | .subNuw => "-!" | .mulNuw => "*!" | .trunc8Nuw => "toUInt8!"

/-- The meaning of a primitive. It is total, because Lean's `UInt64` operations already wrap, give
`x / 0 = 0` and `x % 0 = x`, and take shift amounts modulo 64. -/
def Prim.denote : {ps : List Ty} → {r : Ty} → Prim ps r → Env ps → r.carrier
  | _, _, .add, env => (env.get .here : UInt64) + env.get (.there .here)
  | _, _, .sub, env => (env.get .here : UInt64) - env.get (.there .here)
  | _, _, .mul, env => (env.get .here : UInt64) * env.get (.there .here)
  | _, _, .udiv, .cons (x : UInt64) (.cons (y : UInt64) .nil) => x / y
  | _, _, .umod, .cons (x : UInt64) (.cons (y : UInt64) .nil) => x % y
  | _, _, .band, .cons (x : UInt64) (.cons (y : UInt64) .nil) => x &&& y
  | _, _, .bor, .cons (x : UInt64) (.cons (y : UInt64) .nil) => x ||| y
  | _, _, .bxor, .cons (x : UInt64) (.cons (y : UInt64) .nil) => x ^^^ y
  | _, _, .shl, .cons (x : UInt64) (.cons (y : UInt64) .nil) => x <<< y
  | _, _, .shr, .cons (x : UInt64) (.cons (y : UInt64) .nil) => x >>> y
  | _, _, .bnot, .cons (x : UInt64) .nil => ~~~x
  | _, _, .eq, .cons (x : UInt64) (.cons (y : UInt64) .nil) => decide (x = y)
  | _, _, .ne, .cons (x : UInt64) (.cons (y : UInt64) .nil) => decide (x ≠ y)
  | _, _, .ult, .cons (x : UInt64) (.cons (y : UInt64) .nil) => decide (x < y)
  | _, _, .ule, .cons (x : UInt64) (.cons (y : UInt64) .nil) => decide (x ≤ y)
  | _, _, .ugt, .cons (x : UInt64) (.cons (y : UInt64) .nil) => decide (y < x)
  | _, _, .uge, .cons (x : UInt64) (.cons (y : UInt64) .nil) => decide (y ≤ x)
  | _, _, .not, .cons (x : Bool) .nil => !x
  | _, _, .and, .cons (x : Bool) (.cons (y : Bool) .nil) => x && y
  | _, _, .or, .cons (x : Bool) (.cons (y : Bool) .nil) => x || y
  | _, _, .beq, .cons (x : Bool) (.cons (y : Bool) .nil) => x == y
  | _, _, .zext8, .cons (x : UInt8) .nil => x.toUInt64
  | _, _, .trunc8, env => (env.get .here : UInt64).toUInt8
  | _, _, .addNuw, env => (env.get .here : UInt64) + env.get (.there .here)
  | _, _, .subNuw, env => (env.get .here : UInt64) - env.get (.there .here)
  | _, _, .mulNuw, env => (env.get .here : UInt64) * env.get (.there .here)
  | _, _, .trunc8Nuw, env => (env.get .here : UInt64).toUInt8

-- `+ - *`, the narrowing and their `Nuw` twins read their operands with `Env.get` instead of
-- matching the environment, because `simp` unfolds that form several times faster in the normal
-- form of `mp def` and in `mp_safe`. The other primitives keep the matching form, in which the
-- normal forms of existing programs are stated.

/-- The obligation of a primitive, which says that the mathematical result of a `Nuw` primitive
fits its width and is `True` for every other primitive. -/
def Prim.ok : {ps : List Ty} → {r : Ty} → Prim ps r → Env ps → Prop
  | _, _, .addNuw, env =>
    (env.get .here : UInt64).toNat + (env.get (.there .here) : UInt64).toNat < 2 ^ 64
  | _, _, .subNuw, env => (env.get (.there .here) : UInt64).toNat ≤ (env.get .here : UInt64).toNat
  | _, _, .mulNuw, env =>
    (env.get .here : UInt64).toNat * (env.get (.there .here) : UInt64).toNat < 2 ^ 64
  | _, _, .trunc8Nuw, env => (env.get .here : UInt64).toNat < 2 ^ 8
  | _, _, _, _ => True

/-- Whether a primitive has no obligation, which holds for every primitive but the `Nuw` ones. -/
def Prim.total {ps : List Ty} {r : Ty} : Prim ps r → Bool
  | .addNuw | .subNuw | .mulNuw | .trunc8Nuw => false
  | _ => true

theorem Prim.ok_of_total {ps : List Ty} {r : Ty} (p : Prim ps r) (h : p.total = true)
    (env : Env ps) : p.ok env := by
  cases p <;> simp_all [Prim.total, Prim.ok]

/-- Masking a word to its low byte is the byte's zero extension, which is how the machine
computes `trunc8`. -/
theorem word_and_255 (x : UInt64) : x &&& 255 = x.toUInt8.toUInt64 := by
  rw [UInt64.toUInt64_toUInt8]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_and, UInt64.toNat_mod]
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

/-- Byte division computed through words, the normal form of a `UInt8` division in `mp def`. -/
theorem trunc8_div (a b : UInt8) : (a.toUInt64 / b.toUInt64).toUInt8 = a / b := by
  rw [← UInt8.toUInt64_div, UInt8.toUInt8_toUInt64]

/-- Byte remainder through words. -/
theorem trunc8_mod (a b : UInt8) : (a.toUInt64 % b.toUInt64).toUInt8 = a % b := by
  rw [← UInt8.toUInt64_mod, UInt8.toUInt8_toUInt64]

/-! ## Externs

An extern signature lists its parameters by kind. A word is passed as a word. An input buffer is
read by the extern and is either a constant byte string or a shared slice of a byte array. An
output buffer `bufOut cap` is written by the extern, up to `cap` bytes, and the program receives
the bytes through the call's value. A mutable slice of a byte array, `sliceOut`, receives up to
`cap` bytes chosen by the oracle, and the program receives the raw result word. Events record
word arguments and buffer contents, never addresses. -/

/-- The kinds of extern parameter. -/
inductive ExtParam where
  /-- a 64-bit word -/
  | word
  /-- a buffer the callee reads, passed as a pointer and a length -/
  | bufIn
  /-- a buffer of `cap` bytes the callee writes, passed as a pointer and a capacity; the program
  receives its contents through the call's value -/
  | bufOut (cap : Nat)
  /-- a mutable slice of bytes the callee writes, passed as a pointer and a capacity; the bytes
  land in the slice -/
  | sliceOut
deriving DecidableEq, Repr

/-- An extern's signature. Every extern returns one `U64` word, and a `noreturn` extern such as
`exit` halts the program, so its event is the last one. -/
structure ExtSig where
  sym : String
  params : List ExtParam
  noreturn : Bool := false
deriving DecidableEq, Repr

/-- `exit(code)`, which records its event and ends the trace. -/
def ExtSig.exit : ExtSig := { sym := "exit", params := [.word], noreturn := true }

/-- `write(fd, buf)`, where the callee reads `buf`, either constant bytes or a shared slice of a
byte array, and the oracle supplies the result word. -/
def ExtSig.write : ExtSig := { sym := "write", params := [.word, .bufIn] }

/-- `read(fd, buf, 1)`, where the callee writes at most one byte and the oracle supplies the
result and the byte. The value is the byte, or `2^64 - 1` at the end of input or on an error. -/
def ExtSig.read : ExtSig := { sym := "read", params := [.word, .bufOut 1] }

/-! ## Memory building blocks -/

/-- Binder modes are an owned value, a shared reference `&T` and an exclusive reference `&mut T`.
Modes appear in the checker and in call arguments but not in types. In the value semantics a
`shr` binder holds the value, and a `mut` binder holds the value that its scope hands back at its
end. -/
inductive Mode where
  | own
  | shr
  | mut
deriving DecidableEq, Repr

/-- How the memory lowering lays out the value that a constructor builds. -/
inductive CtorKind where
  /-- the arguments are the fields, in order -/
  | struct
  /-- variant number `i` of a sum; the single argument is the payload -/
  | variant (i : Nat)
  /-- the arguments are the elements, in order -/
  | array
  /-- every element or cell is the single argument, or every cell is empty -/
  | fill
  /-- the arguments are the components of the tuple `Ty.tup ps`, nested pairs ending in `Unit`;
  a function with `&mut` parameters hands back such a tuple of its result and the final values
  of its references, built at once -/
  | tuple
deriving DecidableEq, Repr

/-! ### Laws of the building blocks

A lens, constructor or split carries arbitrary Lean functions, which the memory lowering cannot
inspect. It compiles a field access to an offset, a constructor to byte copies and a split to a
tag test, all read off the layouts. The laws below say that the functions agree with those
layouts. Each building block carries an optional certificate of its law, and the compiler refuses
a program with an uncertified building block, so every program it compiles is lawful. The layout
helpers are defined here, in the namespace `Flat` where the memory lowering uses them, because
the laws need them. -/

namespace Flat

/-- Replaces the bytes of `bs` at `o` by `vb`. -/
def splice (bs : List UInt8) (o : Nat) (vb : List UInt8) : List UInt8 :=
  bs.take o ++ vb ++ bs.drop (o + vb.length)

/-- The byte ranges `[a, a+la)` and `[b, b+lb)` are disjoint. -/
def Disj (a la b lb : Nat) : Prop := a + la ≤ b ∨ b + lb ≤ a

instance (a la b lb : Nat) : Decidable (Disj a la b lb) := inferInstanceAs (Decidable (_ ∨ _))

/-- The offset of the payload of a sum shape, and 0 for other shapes. -/
def payloadOff : Shape → Nat
  | .sum vs => Shape.payloadOffset vs
  | _ => 0

/-- The offset of field `i` of a struct shape, and 0 for other shapes. -/
def fieldOff : Shape → Nat → Nat
  | .prod fs, i => Shape.fieldOffset fs i
  | _, _ => 0

/-- The offset of field number `i` of `s`. -/
def lensOffAt (s : Ty) (i : Nat) : Nat :=
  match s.data.shape with
  | .prod fs => Shape.fieldOffset fs i
  | _ => 0

/-- The offsets of the components of `tup os` inside a value at offset `o`, where `tup os` is
nested pairs ending in `Unit`. -/
def tupOffs : List Ty → Nat → List Nat
  | [], _ => []
  | t :: ts, o => o :: tupOffs ts (o + fieldOff (Data.shape (t.carrier × (Ty.tup ts).carrier)) 1)

/-- Where a constructor of kind `kind` from `ps` into `t` puts its arguments, and its tag. -/
def planOf (ps : List Ty) (t : Ty) (kind : CtorKind) : List (List Nat) × Option Nat :=
  match kind, t.data.shape with
  | .struct, .prod fs => ((Shape.prodOffsets 0 fs).map fun o => [o], none)
  | .variant i, .sum vs => ([[Shape.payloadOffset vs]], some i)
  | .array, .array _ s => ((List.range ps.length).map fun j => [j * s.size], none)
  | .fill, .array n s => ([(List.range n).map fun j => j * s.size], none)
  | .fill, .slots n s => ([(List.range n).map fun j => j * s.size], none)
  | .tuple, .prod [_, _] => ((tupOffs ps 0).map fun o => [o], none)
  | _, _ => ([], none)

/-- How the rest of a `case`, the `q` value, is built from the scrutinee's bytes. `payload` copies
the payload, for the last two variants of an enum, where `q` is the other payload. `retag po' m`
writes the renumbered tag at 0 and copies `m` payload bytes to `po'`, where `q` is a sum of the
remaining variants. `whole` copies the whole value with its tag, where `q` is the scrutinee's own
type, as in the split chain that `deriving Data` generates. -/
inductive RestMode where
  | payload
  | retag (po' m : Nat)
  | whole
deriving DecidableEq, Repr

/-- The rest mode of a split from `t` with rest `q`, read off the shapes. -/
def modeOf (t q : Ty) : RestMode :=
  match t.data.shape, q.data.shape with
  | .sum vs, .sum vs' => if vs.length ≤ 2 then .payload
      else if vs'.length = vs.length then .whole
      else .retag (Shape.payloadOffset vs') (Shape.sizeMax vs')
  | _, _ => .payload

/-- The placements of the arguments, an `(offset, size)` pair for every copy of every argument. -/
def placements : List Ty → List (List Nat) → List (Nat × Nat)
  | t :: ts, os :: oss => os.map (fun o => (o, t.size)) ++ placements ts oss
  | _, _ => []

/-- `bs` holds argument `j` at each of its offsets. -/
def ArgsAt : {ps : List Ty} → List (List Nat) → Env ps → List UInt8 → Prop
  | _, os :: oss, .cons (t := t) v env, bs =>
    (∀ o ∈ os, Data.reprBytes v (slice bs o t.size)) ∧ ArgsAt oss env bs
  | _, _, _, _ => True

/-- `bs` starts with the tag byte, if there is one. -/
def TagAt : Option Nat → List UInt8 → Prop
  | some i, bs => bs.head? = some (UInt64.ofNat i).toUInt8
  | none, _ => True

/-- The bytes that a `case`'s rest is built from, as described at `RestMode`. -/
def RestOk (mode : RestMode) (tag po qsize : Nat) (bs qb : List UInt8) : Prop :=
  match mode with
  | .payload => qb = slice bs po qsize
  | .whole => qb = bs
  | .retag po' m =>
    qb.head? = some ((bs.headD 0).toUInt64 -
        (if UInt64.ofNat tag < (bs.headD 0).toUInt64 then 1 else 0)).toUInt8 ∧
      slice qb po' m = slice bs po m

/-- The byte law of a lens of field number `index` of `s`, with projection `get` and update `set`.
The field lies at `lensOffAt s index` inside the struct, `get` reads its bytes and `set` splices
them. -/
def LensBytes (s t : Ty) (index : Nat) (get : s.carrier → t.carrier)
    (set : s.carrier → t.carrier → s.carrier) : Prop :=
  lensOffAt s index + t.size ≤ s.size ∧
  (∀ (x : s.carrier) (bs : List UInt8), Data.reprBytes x bs →
    Data.reprBytes (get x) (slice bs (lensOffAt s index) t.size)) ∧
  (∀ (x : s.carrier) (v : t.carrier) (bs vb : List UInt8), Data.reprBytes x bs →
    Data.reprBytes v vb → Data.reprBytes (set x v) (splice bs (lensOffAt s index) vb))

/-- The occupancy law of a lens. The field's occupancies are the struct's at
`Data.occsOff index`, and `set` replaces exactly those. Bytes do not show whether a `Slots` cell is
full, so the byte law alone does not say that updating one field leaves another field's cells
full, and this law does. -/
def LensOccs (s t : Ty) (index : Nat) (get : s.carrier → t.carrier)
    (set : s.carrier → t.carrier → s.carrier) : Prop :=
  Data.occsOff s.carrier index + Data.occsN t.carrier ≤ Data.occsN s.carrier ∧
  (∀ x : s.carrier, Data.occs (get x) =
    ((Data.occs x).drop (Data.occsOff s.carrier index)).take (Data.occsN t.carrier)) ∧
  (∀ (x : s.carrier) (v : t.carrier), Data.occs (set x v) =
    (Data.occs x).take (Data.occsOff s.carrier index) ++ Data.occs v ++
      (Data.occs x).drop (Data.occsOff s.carrier index + Data.occsN t.carrier))

/-- The law of a lens, which is its byte law and its occupancy law together. -/
def LensLaw (s t : Ty) (index : Nat) (get : s.carrier → t.carrier)
    (set : s.carrier → t.carrier → s.carrier) : Prop :=
  LensBytes s t index get set ∧ LensOccs s t index get set

/-- The law of a constructor of kind `kind` that builds `t` from `ps` with `build`. Its placements
are inside the value, pairwise disjoint and after the tag byte, and any bytes that hold the
arguments and the tag represent the built value. -/
def CtorLaw (ps : List Ty) (t : Ty) (kind : CtorKind) (build : Env ps → t.carrier) : Prop :=
  (∀ q ∈ placements ps (planOf ps t kind).1, q.1 + q.2 ≤ t.size ∧
    ((planOf ps t kind).2.isSome → 1 ≤ q.1)) ∧
  (placements ps (planOf ps t kind).1).Pairwise (fun a b => Disj a.1 a.2 b.1 b.2) ∧
  ((planOf ps t kind).2.isSome → 1 ≤ t.size) ∧
  ∀ (env : Env ps) (bs : List UInt8), bs.length = t.size → TagAt (planOf ps t kind).2 bs →
    ArgsAt (planOf ps t kind).1 env bs → Data.reprBytes (build env) bs

/-- The law of a split that tests variant `tag` of `t` with `split`. The tag byte decides the arm,
the payload of the tested variant is at the payload offset, and the rest is built as `RestOk`
says in the mode `modeOf t q`. -/
def SplitLaw (t p q : Ty) (tag : Nat) (split : t.carrier → p.carrier ⊕ q.carrier) : Prop :=
  payloadOff t.data.shape + p.size ≤ t.size ∧ 1 ≤ t.size ∧
  (match modeOf t q with
   | .payload => payloadOff t.data.shape + q.size ≤ t.size
   | .whole => q.size = t.size
   | .retag po' m => 1 ≤ po' ∧ po' + m ≤ q.size ∧ payloadOff t.data.shape + m ≤ t.size) ∧
  ∀ (x : t.carrier) (bs : List UInt8), Data.reprBytes x bs →
    (∀ a, split x = .inl a → (bs.headD 0).toUInt64 = UInt64.ofNat tag ∧
      Data.reprBytes a (slice bs (payloadOff t.data.shape) p.size)) ∧
    (∀ b, split x = .inr b → (bs.headD 0).toUInt64 ≠ UInt64.ofNat tag ∧
      ∀ qb, qb.length = q.size → RestOk (modeOf t q) tag (payloadOff t.data.shape) q.size bs qb →
        Data.reprBytes b qb)

end Flat

/-- A field of the struct `s` with type `t`. It has a name, a position `index` that fixes its
offset, a projection, an update, and an optional certificate that these agree with the layout,
which the compiler requires. The borrow checker relies on distinct indices of one struct being
disjoint fields. -/
structure Lens (s t : Ty) where
  name : String
  index : Nat
  get : s.carrier → t.carrier
  set : s.carrier → t.carrier → s.carrier
  law : Option (PLift (Flat.LensLaw s t index get set)) := none

/-- A constructor, a total function from argument values to a value of `t`, with an optional
certificate that it agrees with the layout. Structs, enum variants and arrays are all built by
`Exp.mk` with a `Ctor`. -/
structure Ctor (ps : List Ty) (t : Ty) where
  name : String
  kind : CtorKind
  build : Env ps → t.carrier
  law : Option (PLift (Flat.CtorLaw ps t kind build)) := none
  /-- an optional certificate that the built value hands back its arguments, which means that the
  occupancies of its components are those of its arguments, in order. The pair and tuple
  constructors that `mp def` uses for hand-backs carry it, and the hand-back condition requires
  it of the last constructor of a `&mut` slice borrow's body. -/
  occs : Option (PLift (∀ env, Data.occs (build env) = env.occs)) := none

/-- One step of an exhaustive match on `t`. Either the value is the variant with payload `p`, or
it is one of the other variants, given as a value of `q`. For the last two variants of an enum,
`q` is the last payload, and otherwise it is a smaller sum such as `Result`. A split has an
optional certificate that it agrees with the layout. -/
structure Split (t p q : Ty) where
  name : String
  /-- the variant tested -/
  tag : Nat
  split : t.carrier → p.carrier ⊕ q.carrier
  law : Option (PLift (Flat.SplitLaw t p q tag split)) := none

/-- A place is a variable, a field `p.f`, an element `p[i]`, a `Slots` cell `s[i]`, which is also
element `i` of a slice view, a slice `p[lo..lo+len]`, or the two elements `p[i], p[j]` borrowed
together. `rangeS` and `pair2S` are a sub-slice and a pair of elements of a view variable. A
reference binder is a variable whose value is the referenced value. Each partial selector carries
an `Inhabited` instance, so its meaning is total and returns `default` when its obligation
fails. -/
inductive Place (Γ : List Ty) : Ty → Type 1 where
  | var {t : Ty} : Mem t Γ → Place Γ t
  | field {s t : Ty} : Place Γ s → Lens s t → Place Γ t
  /-- `p[i]!`, with the obligation `i < n` -/
  | index {t : Ty} {n : Nat} [dflt : Inhabited t.carrier] : Place Γ (.arr t n) → Atom Γ .u64 → Place Γ t
  /-- the content of the `Slots` cell `s[i]`, with the obligation that `i < n` and the cell is
  full -/
  | slot {t : Ty} {n : Nat} [dflt : Inhabited t.carrier] : Place Γ (.slots t n) → Atom Γ .u64 →
      Place Γ t
  /-- the slice `p[lo..lo+len]`, with the obligation `lo + len ≤ n`; it is a view of `len`
  elements, which is only borrowed or passed by reference, and its elements are its full cells -/
  | range {t : Ty} {n : Nat} : Place Γ (.arr t n) → Atom Γ .u64 → Atom Γ .u64 →
      Place Γ (.view t n)
  /-- the elements `p[i]` and `p[j]` together, with the obligation that `i < n`, `j < n` and
  `i ≠ j` -/
  | pair2 {t : Ty} {n : Nat} [dflt : Inhabited t.carrier] : Place Γ (.arr t n) → Atom Γ .u64 →
      Atom Γ .u64 → Place Γ (.pair t t)
  /-- the sub-slice `s[lo..lo+len]` of a slice view or `Slots` variable `s`, a view of `len`
  elements whose cell `k` is `s`'s cell `lo + k`. Its obligation is `lo + len ≤ n` with the cells
  below `lo + len` full, and since a view's full cells are its first `s.len`, this means
  `lo + len ≤ s.len`. -/
  | rangeS {t : Ty} {n : Nat} : Mem (.slots t n) Γ → Atom Γ .u64 → Atom Γ .u64 →
      Place Γ (.view t n)
  /-- the cells `s[i]` and `s[j]` of a slice view or `Slots` variable together, with the
  obligation that both are full and `i ≠ j` -/
  | pair2S {t : Ty} {n : Nat} [dflt : Inhabited t.carrier] : Mem (.slots t n) Γ → Atom Γ .u64 →
      Atom Γ .u64 → Place Γ (.pair t t)

/-- Whether a place's obligations can be decided at run time. This holds for every selector but a
`Slots` cell, whose occupancy has no run-time representation, and the checked form
`Guard.valid` exists only for such places. -/
def Place.checkable {Γ : List Ty} : {t : Ty} → Place Γ t → Bool
  | _, .var _ => true
  | _, .field p _ => p.checkable
  | _, .index (dflt := _) p _ => p.checkable
  | _, .slot (dflt := _) _ _ => false
  | _, .range p _ _ => p.checkable
  | _, .pair2 (dflt := _) p _ _ => p.checkable
  | _, .rangeS _ _ _ => false
  | _, .pair2S (dflt := _) _ _ _ => false

/-- Call arguments with modes. `RArgs Γ ps os` has one argument per parameter in `ps`, and `os`
lists the types of the `mut` parameters, whose updated values the callee returns in order. -/
inductive RArgs (Γ : List Ty) : List Ty → List Ty → Type 1 where
  | nil : RArgs Γ [] []
  /-- an owned argument, moved when its type is linear and copied otherwise -/
  | own {t : Ty} {ps os : List Ty} : Atom Γ t → RArgs Γ ps os → RArgs Γ (t :: ps) os
  /-- `&p` -/
  | shr {t : Ty} {ps os : List Ty} : Place Γ t → RArgs Γ ps os → RArgs Γ (t :: ps) os
  /-- `&mut p` -/
  | mut {t : Ty} {ps os : List Ty} : Place Γ t → RArgs Γ ps os → RArgs Γ (t :: ps) (t :: os)

/-- The run-time conditions that the checked forms test. There is no guard on a `Slots` cell,
because its occupancy cannot be observed at run time. -/
inductive Guard (Γ : List Ty) : Type 1 where
  /-- the obligations of a checkable place hold, so its indices are in range and distinct -/
  | valid {t : Ty} (p : Place Γ t) (h : p.checkable = true) : Guard Γ

/-- A source of bytes for an input buffer, either constant bytes or the shared slice
`a[lo..lo+len]` of a byte array, with the obligation `lo + len ≤ n`. The slice is passed as a
pointer and a length. -/
inductive Buf (Γ : List Ty) : Type 1 where
  | const (bs : List UInt8)
  | slice {n : Nat} (a : Place Γ (.arr .u8 n)) (lo len : Atom Γ .u64)

/-- Extern arguments, matched to a parameter list. -/
inductive EArgs (Γ : List Ty) : List ExtParam → Type 1 where
  | nil : EArgs Γ []
  | word {ps : List ExtParam} : Atom Γ .u64 → EArgs Γ ps → EArgs Γ (.word :: ps)
  | bufIn {ps : List ExtParam} : Buf Γ → EArgs Γ ps → EArgs Γ (.bufIn :: ps)
  | bufOut {ps : List ExtParam} {cap : Nat} : EArgs Γ ps → EArgs Γ (.bufOut cap :: ps)
  /-- the mutable slice `a[lo..lo+cap]` of a byte array, with the obligation `lo + cap ≤ n` -/
  | sliceOut {ps : List ExtParam} {n : Nat} (a : Place Γ (.arr .u8 n)) (lo cap : Atom Γ .u64) :
      EArgs Γ ps → EArgs Γ (.sliceOut :: ps)

/-- The arguments contain no mutable slice, as for a plain `Exp.ext` call. -/
def EArgs.noOut {Γ : List Ty} : {ps : List ExtParam} → EArgs Γ ps → Bool
  | _, .nil => true
  | _, .word _ as => as.noOut
  | _, .bufIn _ as => as.noOut
  | _, .bufOut as => as.noOut
  | _, .sliceOut _ _ _ _ => false

/-- The loop-carried variables of `Exp.loop` are the outer binders, of types `ts` in order, that
a loop body may write, each as a whole variable. In the value semantics the body hands back their
updated values with the accumulator, so they pass through the iterations, while the machine
updates them in place. -/
inductive Carry (Γ : List Ty) : List Ty → Type 1 where
  | nil : Carry Γ []
  | cons {t : Ty} {ts : List Ty} : Mem t Γ → Carry Γ ts → Carry Γ (t :: ts)

/-- The de Bruijn indices of the carried variables, in order. -/
def Carry.idxs {Γ : List Ty} : {ts : List Ty} → Carry Γ ts → List Nat
  | _, .nil => []
  | _, .cons m cs => m.idx :: cs.idxs

/-- The carried variables are pairwise distinct. -/
def Carry.distinct {Γ : List Ty} : {ts : List Ty} → Carry Γ ts → Bool
  | _, .nil => true
  | _, .cons m cs => !cs.idxs.contains m.idx && cs.distinct

/-! ## Terms -/

/-- Core terms in A-normal form. -/
inductive Exp : List Ty → Ty → Type 1 where
  /-- return an atom -/
  | atom {Γ : List Ty} {t : Ty} : Atom Γ t → Exp Γ t
  /-- `let x := e₁; e₂`, where `x` is index 0 in `e₂` -/
  | let_ {Γ : List Ty} {s t : Ty} : Exp Γ s → Exp (s :: Γ) t → Exp Γ t
  /-- `if c then e₁ else e₂` -/
  | ite {Γ : List Ty} {t : Ty} : Atom Γ .bool → Exp Γ t → Exp Γ t → Exp Γ t
  /-- primitive application -/
  | prim {Γ ps : List Ty} {r : Ty} : Prim ps r → Args Γ ps → Exp Γ r
  /-- a call of a previously defined function, whose body is a closed subterm over its
  parameters `ps`, so there is no recursion -/
  | call {Γ ps : List Ty} {r : Ty} (name : String) : Exp ps r → Args Γ ps → Exp Γ r
  /-- `ok a : Result ε α` -/
  | ok {Γ : List Ty} {ε α : Ty} : Atom Γ α → Exp Γ (.result ε α)
  /-- `err e : Result ε α` -/
  | err {Γ : List Ty} {ε α : Ty} : Atom Γ ε → Exp Γ (.result ε α)
  /-- `match r with | err e => onErr | ok a => onOk`, where the payload is index 0 in each arm -/
  | match_ {Γ : List Ty} {ε α t : Ty} : Atom Γ (.result ε α) → Exp (ε :: Γ) t →
      Exp (α :: Γ) t → Exp Γ t
  /-- an extern call -/
  | ext {Γ : List Ty} (sig : ExtSig) : EArgs Γ sig.params → Exp Γ .u64
  /-- `let x := sig(args); k` for an extern that writes into mutable byte slices. The bytes the
  oracle supplies are written into the slices, and `x` is the raw result word, which for `read`
  is the count. -/
  | extMut {Γ : List Ty} {u : Ty} (sig : ExtSig) : EArgs Γ sig.params → Exp (.u64 :: Γ) u →
      Exp Γ u
  /-- builds a struct, an enum variant or an array from atoms -/
  | mk {Γ ps : List Ty} {t : Ty} : Ctor ps t → Args Γ ps → Exp Γ t
  /-- copies the value of a place -/
  | read {Γ : List Ty} {t : Ty} : Place Γ t → Exp Γ t
  /-- `p := a; k` -/
  | assign {Γ : List Ty} {t u : Ty} : Place Γ t → Atom Γ t → Exp Γ u → Exp Γ u
  /-- `match s with | P x => onP | rest y => onQ`, one step of an exhaustive match, where the
  payload is index 0 in each arm -/
  | case {Γ : List Ty} {t p q u : Ty} : Atom Γ t → Split t p q → Exp (p :: Γ) u →
      Exp (q :: Γ) u → Exp Γ u
  /-- `s.put! i a; k`, which fills the empty cell `i`, with the obligation that `i < n` and the
  cell is empty -/
  | put {Γ : List Ty} {t : Ty} {n : Nat} {u : Ty} : Place Γ (.slots t n) → Atom Γ .u64 →
      Atom Γ t → Exp Γ u → Exp Γ u
  /-- `let x := s.take! i; k`, which empties the full cell `i` and owns its value, with the
  obligation that `i < n` and the cell is full -/
  | take {Γ : List Ty} {t : Ty} {n : Nat} {u : Ty} [dflt : Inhabited t.carrier] :
      Place Γ (.slots t n) → Atom Γ .u64 → Exp (t :: Γ) u → Exp Γ u
  /-- `let x := { let r = &p; body }; k` -/
  | borrowShr {Γ : List Ty} {t u v : Ty} : Place Γ t → Exp (t :: Γ) u → Exp (u :: Γ) v → Exp Γ v
  /-- `let x := { let r = &mut p; body }; k`, where `body` returns its result and the final value
  of `*r`, which is written back to `p` -/
  | borrowMut {Γ : List Ty} {t u v : Ty} : Place Γ t → Exp (t :: Γ) (.pair u t) →
      Exp (u :: Γ) v → Exp Γ v
  /-- `let x := f(args); k` with reference arguments and the callee's `requires`, where the
  callee returns its result and the updated values of its `mut` parameters -/
  | callRef {Γ ps os : List Ty} {r u : Ty} (name : String) (req : Env ps → Prop) :
      Exp ps (.pair r (.tup os)) → RArgs Γ ps os → Exp (r :: Γ) u → Exp Γ u
  /-- the checked test of an obligation, which is `ok ()` when it holds and `err ()` otherwise -/
  | guard {Γ : List Ty} : Guard Γ → Exp Γ (.result .unit .unit)
  /-- `let x := (for i in 0...n do (if !c then break); acc := body); k`, which may write the
  loop-carried variables `cs`. In `c` and `body`, index 0 is `i : U64` and index 1 is `acc`. The
  body may assign the carried variables and hands back the new accumulator with their values,
  which they hold in the next iteration and, after the loop, in `k`, where index 0 is the final
  accumulator. The condition writes nothing. -/
  | loop {Γ ts : List Ty} {s u : Ty} (n : Nat) (cs : Carry Γ ts) : Atom Γ s →
      Exp (.u64 :: s :: Γ) .bool → Exp (.u64 :: s :: Γ) (.pair s (.tup ts)) →
      Exp (s :: Γ) u → Exp Γ u

/-- A function, with its name, parameter types `ps`, result type `r` and body. `ps` is the body's
context, so `ps[0]` is de Bruijn index 0, and call arguments are given in the same order. `mp def`
binds the last source parameter at index 0, so `clampAdd x y` has `ps = [y, x]`. -/
structure Fn (ps : List Ty) (r : Ty) where
  name : String
  body : Exp ps r
  /-- the precondition that callers must establish, under which the obligations of `f.body` are
  proved once -/
  requires : Env ps → Prop := fun _ => True

/-- A call to `f` with argument atoms. -/
abbrev Fn.call {Γ ps : List Ty} {r : Ty} (f : Fn ps r) (args : Args Γ ps) : Exp Γ r :=
  .call f.name f.body args

/-- A function with reference parameters `ps`, of which those passed `&mut` have the types `os`.
The body returns the result together with the final values of the `mut` parameters, which the
caller writes back. -/
structure FnRef (ps os : List Ty) (r : Ty) where
  name : String
  body : Exp ps (.pair r (.tup os))
  /-- the precondition that callers must establish -/
  requires : Env ps → Prop := fun _ => True

/-- `let x := f(args); k`. -/
abbrev FnRef.call {Γ ps os : List Ty} {r u : Ty} (f : FnRef ps os r) (args : RArgs Γ ps os)
    (k : Exp (r :: Γ) u) : Exp Γ u :=
  .callRef f.name f.requires f.body args k

end Millipede
