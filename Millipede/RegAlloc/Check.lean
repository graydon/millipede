import Millipede.RegAlloc.Lock

/-!
# The register allocation checker

Register allocation is validated after the fact. An untrusted allocator proposes, for a Lin
program `P`, a program `P'` with the same functions, code positions and instructions, except that
every slot is replaced by a location, which is a slot of the new frame. With register allocation
the locations below `k` are kept in machine registers by the selector. Along with `P'` the
allocator gives a location map for each code position, a list of pairs `(source slot, location)`
for the source slots whose values are still needed there. This module defines the checker
`check P P' maps`, and when it accepts, `P'` runs in lock-step with `P` with every mapped slot's
value in its location.

The checker works on one instruction at a time, in the manner of Rideau and Leroy's validator but
without moves. At position `pc` with map `M`, and with the map `M₁` of each successor, it requires
the following:

* every slot operand `y` of the source instruction is a target operand `l` with `(y, l) ∈ M`, and
  every immediate stays the same immediate;
* every entry `(y, l)` of a successor's map is justified, either because `y` is the slot that the
  instruction defines and `l` the target's destination, or because `(y, l) ∈ M` and the target
  instruction does not write `l` other than by the coalesced move `mov l l`;
* for every entry `(y, l)` of the callee's entry map, a call passes in position `l` of the target's
  argument list the operand that the source passes in position `y`, so a callee's parameters may
  be relocated as long as every call site follows;
* the remaining fields of each instruction are equal, the returned operands are related by the map
  at each `ret`, and `P'` is well formed.

The stack is checked apart, by `frameOk k c`: each target frame, counted in the words of a
selection with `k` preserved and `c` caller-saved register locations (`Sel.frameW`), is no
larger than the source frame. A register location may thus raise a frame's number of locations
as long as its words do not grow.

The checker checks no property of liveness. An entry missing from a map only means that the value
is not tracked, and if the value is used later, the check of its operand fails there.
-/

namespace Millipede.RegAlloc

open Flat (Operand ExtArg)
open Lin (Instr Prog)

/-- A location map, a list of pairs `(source slot, location)`. -/
abbrev LocMap := List (Nat × Nat)

/-- The map of function `i` at position `pc`, which is `[]` when absent. -/
def mapOf (maps : List (List LocMap)) (i pc : Nat) : LocMap := (maps.getD i []).getD pc []

/-- Whether a target operand stands for a source operand, as an equal immediate or as the location
of the slot. -/
def opOk (M : LocMap) : Operand → Operand → Bool
  | .imm w, .imm w' => w == w'
  | .slot y, .slot l => decide ((y, l) ∈ M)
  | _, _ => false

/-- `opOk` pointwise on two lists. -/
def opsOk (M : LocMap) : List Operand → List Operand → Bool
  | [], [] => true
  | o :: os, o' :: os' => opOk M o o' && opsOk M os os'
  | _, _ => false

/-- Whether a target extern argument stands for a source one. -/
def extOk (M : LocMap) : ExtArg → ExtArg → Bool
  | .word a, .word a' => opOk M a a'
  | .bytes bs, .bytes bs' => bs == bs'
  | .mem a n, .mem a' n' => opOk M a a' && opOk M n n'
  | .out c, .out c' => c == c'
  | .outMem a c, .outMem a' c' => opOk M a a' && opOk M c c'
  | _, _ => false

/-- `extOk` pointwise on two lists. -/
def extsOk (M : LocMap) : List ExtArg → List ExtArg → Bool
  | [], [] => true
  | a :: as, a' :: as' => extOk M a a' && extsOk M as as'
  | _, _ => false

/-- Every entry of `M₁` is carried from `M`, for an instruction that defines nothing. -/
def sub (M₁ M : LocMap) : Bool := M₁.all fun p => decide (p ∈ M)

/-- The entries of `M₁` after an instruction that defines slot `x` into location `x'`. Slot `x` is
at `x'`, and every other entry is carried from `M` with a location other than `x'`, unless `keep`
says that the target instruction writes `x'` with the value already there, as a coalesced move
does. -/
def defOk (M M₁ : LocMap) (x x' : Nat) (keep : Nat → Bool) : Bool :=
  M₁.all fun p => if p.1 = x then p.2 == x' else decide (p ∈ M) && (p.2 != x' || keep p.2)

/-- The entries after a call that writes its `n` results to `d, …`, and in the target to
`d', …`. -/
def resOk (M M₁ : LocMap) (d d' n : Nat) : Bool :=
  M₁.all fun p => if d ≤ p.1 ∧ p.1 < d + n then p.2 == d' + (p.1 - d)
    else decide (p ∈ M) && !(d' ≤ p.2 && p.2 < d' + n)

/-- The arguments serve the callee's entry map `E` when, for each entry `(y, l)`, position `l` of
the target's list holds what position `y` of the source's list holds. -/
def argsOk (M E : LocMap) (args args' : List Operand) : Bool :=
  E.all fun p => opOk M (args.getD p.1 (.imm 0)) (args'.getD p.2 (.imm 0))

/-- The number of words function `g` returns, which is `0` for a missing function. -/
def retLen (P : Prog) (g : Nat) : Nat := ((P.funs[g]?).map fun f => f.ret.length).getD 0

/-- The local check of instruction `ins` against its target `ins'` at position `pc` of function
`i`, whose returned operands are `ret` and in the target `ret'`. -/
def instrOk (P : Prog) (maps : List (List LocMap)) (i pc : Nat) (ret ret' : List Operand) :
    Instr → Instr → Bool
  | .mov x a, .mov x' a' =>
    opOk (mapOf maps i pc) a a' &&
      defOk (mapOf maps i pc) (mapOf maps i (pc + 1)) x x' (fun l => a' == .slot l)
  | .bin op x a b, .bin op' x' a' b' =>
    op == op' && opOk (mapOf maps i pc) a a' && opOk (mapOf maps i pc) b b' &&
      defOk (mapOf maps i pc) (mapOf maps i (pc + 1)) x x' (fun _ => false)
  | .load w x a off, .load w' x' a' off' =>
    w == w' && off == off' && opOk (mapOf maps i pc) a a' &&
      defOk (mapOf maps i pc) (mapOf maps i (pc + 1)) x x' (fun _ => false)
  | .store w a off b, .store w' a' off' b' =>
    w == w' && off == off' && opOk (mapOf maps i pc) a a' && opOk (mapOf maps i pc) b b' &&
      sub (mapOf maps i (pc + 1)) (mapOf maps i pc)
  | .jmp l, .jmp l' => l == l' && sub (mapOf maps i l) (mapOf maps i pc)
  | .jz c l, .jz c' l' =>
    l == l' && opOk (mapOf maps i pc) c c' && sub (mapOf maps i l) (mapOf maps i pc) &&
      sub (mapOf maps i (pc + 1)) (mapOf maps i pc)
  | .call g args d, .call g' args' d' =>
    g == g' && argsOk (mapOf maps i pc) (mapOf maps g 0) args args' &&
      resOk (mapOf maps i pc) (mapOf maps i (pc + 1)) d d' (retLen P g)
  | .ret, .ret => opsOk (mapOf maps i pc) ret ret'
  | .ext sym nr x args, .ext sym' nr' x' args' =>
    sym == sym' && nr == nr' && extsOk (mapOf maps i pc) args args' &&
      defOk (mapOf maps i pc) (mapOf maps i (pc + 1)) x x' (fun _ => false)
  | .tick t, .tick t' => t == t' && sub (mapOf maps i (pc + 1)) (mapOf maps i pc)
  | _, _ => false

/-- `f k a b` for the elements of two lists of equal length, with the first at index `k`. -/
def all2 {α β : Type} (f : Nat → α → β → Bool) : Nat → List α → List β → Bool
  | _, [], [] => true
  | k, a :: as, b :: bs => f k a b && all2 f (k + 1) as bs
  | _, _, _ => false

/-- The check of one function, which requires the same number of instructions and of returned
words and every instruction checked. -/
def fnOk (P : Prog) (maps : List (List LocMap)) (i : Nat) (fn fn' : Lin.Fn) : Bool :=
  fn.ret.length == fn'.ret.length &&
    all2 (fun pc ins ins' => instrOk P maps i pc fn.ret fn'.ret ins ins') 0 fn.code fn'.code

/-! ## Well-formedness, decided -/

/-- `Lin.OpsBelow`, decided. -/
def opsBelow (ops : List Operand) (n : Nat) : Bool :=
  ops.all fun o => match o with | .slot x => decide (x < n) | .imm _ => true

/-- `Lin.Instr.Wf`, decided. -/
def instrWf (P : Prog) (i fr len : Nat) : Instr → Bool
  | .mov x a => decide (x < fr) && opsBelow [a] fr
  | .bin _ x a b => decide (x < fr) && opsBelow [a, b] fr
  | .load _ x a _ => decide (x < fr) && opsBelow [a] fr
  | .store _ a _ b => opsBelow [a, b] fr
  | .jmp l => decide (l < len)
  | .jz c l => opsBelow [c] fr && decide (l < len)
  | .call g args d => decide (g < i) && opsBelow args fr &&
      match P.funs[g]? with
      | some gf => decide (args.length ≤ gf.frame) && decide (d + gf.ret.length ≤ fr)
      | none => false
  | .ret => true
  | .ext _ _ x args => decide (x < fr) && args.all fun a => match a with
      | .word o => opsBelow [o] fr
      | .mem a l => opsBelow [a, l] fr
      | .outMem a l => opsBelow [a, l] fr
      | _ => true
  | .tick _ => true

/-- `Lin.Prog.Wf`, decided. -/
def wfCheck (P : Prog) : Bool :=
  decide (P.main < P.funs.length) &&
    all2 (fun i fn _ => opsBelow fn.ret fn.frame &&
      fn.code.all (instrWf P i fn.frame fn.code.length)) 0 P.funs P.funs

/-- The checker, which requires the same entry function and data region, every function checked
against its target, and the target well formed. -/
def check (P P' : Prog) (maps : List (List LocMap)) : Bool :=
  P'.main == P.main && P'.mem == P.mem && all2 (fnOk P maps) 0 P.funs P'.funs && wfCheck P'

/-- The frame check: every frame of `P'`, counted in the words of a selection with `k` preserved
and `c` caller-saved register locations, is no larger than the frame of `P` it replaces. -/
def frameOk (k c : Nat) (P P' : Prog) : Bool :=
  all2 (fun _ fn fn' => decide (Sel.frameW k c fn'.frame ≤ fn.frame)) 0 P.funs P'.funs

end Millipede.RegAlloc
