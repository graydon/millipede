import Lean
import Millipede.Meta.Basic

/-!
# Surface syntax of `mp def`

The body of an `mp def` is parsed with Lean's own term parser, so `let`, `if … then … else`,
operators, numerals, parentheses, `match`, type ascriptions, field access `p.f`, indexing such as
`a[i]`, `a[i]!`, `a[i]?` and `a[lo:hi]`, structure literals and updates, anonymous constructors
`⟨a, b⟩` and `#v[…]` look as they do in Lean. Statements are parsed with Lean's own `do` parser,
which covers `let mut x := v`, assignments to `x`, `p.f` and `a[i]`, `for i in lo...hi do`,
`break`, `continue` and `return`, but they are translated by `elabSeq` and never by Lean's `do`
elaborator.

This module adds term forms that mean something only inside `mp def`, and none of them is
elaborated as an ordinary Lean term.
- `&mut p` and `&p` pass references to calls and make scoped borrows `let r := &mut p; body`, and
  in parameter types they give the modes `(r : &mut T)` and `(r : &T)`.
- `a[lo..hi]` is the slice that Lean writes `a[lo:hi]`. The slice parameter types `&[T; n]` and
  `&mut [T; n]`, also written `Slice T n`, view `a[lo..hi]` for `a : Arr T n`, and a slice has the
  elements `s[i]` and `s[i]!` and the length `s.len`.
- `(a[i], a[j])` is a pair of places borrowed together, the place `a.pair! i j`.

It also declares the commands `mp def`, with an optional `requires` clause and, through
`Millipede.Meta.Contracts`, an optional `ensures` clause, `mp extern`, `mp program`, `mp prove`
and `#mp_cost`. `mp` is not a reserved keyword, so it stays usable as an identifier elsewhere.
The surface language is described in doc/design/language.md.
-/

namespace Millipede.Meta

/-- A group of parameters `(x y : T)`. -/
syntax mpBinder := "(" ident+ " : " term ")"

/-- `mp def f (x y : UInt64) (r : &mut Pt) requires P : T := body` defines `f.exp`, `f`,
`f.exp_denote`, `f.wf`, `f.safe` and related declarations. -/
syntax (name := mpDef) (docComment)? mpKw "def " ident (ppSpace mpBinder)*
  (&" requires " term)? " : " term " := " term : command

/-- `&mut p` is an exclusive reference to the place `p` inside `mp def`, or the mode of a
parameter type. -/
syntax (name := mpRefMut) "&mut " term : term

/-- `&p` is a shared reference to the place `p` inside `mp def`, or the mode of a parameter
type. -/
syntax (name := mpRefShr) "&" term : term

/-- `a[lo..hi]` is the slice of the elements `lo … hi-1` of an array, the same place as Lean's
`a[lo:hi]`. It is meaningful only inside `mp def`, where it is borrowed or passed by reference as
`&a[lo..hi]` or `&mut a[lo..hi]`. -/
syntax:max (name := mpRange) term noWs "[" withoutPosition(term " .. " term) "]" : term

/-- `[T; n]` is a slice of elements of type `T` viewing an array of `n` elements, the same type as
`Slice T n`. It is used only as the type of a reference parameter of `mp def`, as in
`(s : &[T; n])` or `(s : &mut [T; n])`. -/
syntax (name := mpSliceTy) "[" term "; " term "]" : term

/-- `mp program name (root : T) init f step g [invariant I]` declares the reactor whose root has
type `T`, built by `f`, which takes no parameters, and stepped by `g`, which takes one `&mut T`
parameter. `I : T → Prop` is an optional root invariant. -/
syntax (name := mpProgram) (docComment)? mpKw &"program " ident " (" &"root" " : " term ") "
  &"init " ident &"step " ident (&" invariant " term)? : command

/-- `mp prove f.safe := proof` proves the obligations of `f`, the goal `f.SafeGoal`, when `mp def`
could not discharge them automatically. -/
syntax (name := mpProve) (docComment)? mpKw &"prove " ident " := " term : command

/-- `mp extern [noreturn] "sym" name (p : UInt64) (buf : Bytes) : UInt64` declares an extern and
defines `name : ExtSig`. A parameter is a `UInt64` word, an input buffer `Bytes` or `&[U8]`, an
`OutByte` buffer, or an output buffer `&mut [U8]`. -/
syntax (name := mpExtern) (docComment)? mpKw &"extern " (&"noreturn ")? str ident
  (ppSpace mpBinder)* " : " term : command

/-- `#mp_cost f` prints the static cost bound `f.exp.cost κ hb` as a formula in the cost model `κ`,
and `#mp_cost f with κ` prints its value under the cost model `κ`. The mode `hb` is the one in
which a call charges the body: `split` for a function with `&mut` parameters, which hands them
back in place, and `copy` otherwise. -/
syntax (name := mpCost) "#mp_cost " ident (" with " term)? : command

end Millipede.Meta
