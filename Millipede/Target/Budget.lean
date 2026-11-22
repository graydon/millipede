import Millipede.Compile.Lin

/-!
# The instruction budget of selected code

The resource clause of `compile_sound` bounds the machine instructions of reactor step `k` by
`p.stepCost k ω t.κ`. The Lin clock is the sum of the weights of the executed `tick`s, and every
other Lin instruction costs nothing on that clock but becomes machine instructions. An ISA states
how many in its `Counts`:

* `ins P g pc fn i` is the number of machine instructions one Lin step of `i` executes, at
  position `pc` of function `g` with code `fn`. It is the length of the selected block, except
  that a `call`'s count runs through the callee's entry sequence and stops before the result
  stores of the call block, a `ret`'s count includes the caller's result stores, one per
  returned word, and `exit`'s count stops at the system call.
* `entry` is the number of instructions of `main`'s entry sequence, which runs before Lin's first
  step.

The two clocks are related by a potential. A certificate `N` gives, for each code position, the
instructions that may still run from there before the credit of later ticks pays for them, or
`none` for an unreached position. `budgetOk C κ P N` checks locally that one Lin step pays for its
machine instructions out of the potential, `ins + N(next) ≤ N(here) + weight`, with the call and
return sequences split between the two frames. It also checks that the result stores after a
return never leave a negative potential behind, that every `jz` on a non-zero constant, the
reactor loop's test, has potential exactly 0, and that `main`'s entry plus the potential at its
first position is at most 0. These checks bound the instructions of every reactor step by the
advance of its Lin clock.

`potential C κ P` computes the least certificate by fixed-point iteration from `-∞`. It is not
trusted, because `compile` runs `budgetOk` on it and refuses the program when the check fails.
-/

namespace Millipede.Sel

/-- An ISA's instruction counts for each Lin step and for `main`'s entry sequence. -/
structure Counts where
  ins : Lin.Prog → Nat → Nat → Lin.Fn → Lin.Instr → Nat
  entry : Lin.Prog → Nat

/-- The frame size of Lin function `g`, or 0 when it is missing. -/
def calleeFrame (P : Lin.Prog) (g : Nat) : Nat := ((P.funs[g]?).map Lin.Fn.frame).getD 0

/-- The number of words function `g` returns, or 0 when it is missing. -/
def resLen (P : Lin.Prog) (g : Nat) : Nat := ((P.funs[g]?).map fun f => f.ret.length).getD 0

/-- A potential certificate, which gives `N i pc` for position `pc` of function `i`, or `none`
for an unreached position. -/
abbrev Cert := Nat → Nat → Option Int

/-- The successor `t` is certified and `c + N(t) ≤ v`. -/
def succOk (N : Cert) (i t : Nat) (v : Int) (c : Nat) : Bool :=
  match N i t with
  | some w => decide ((c : Int) + w ≤ v)
  | none => false

variable (C : Counts)

/-- The local check at position `pc` of function `i` (whose code is `fn`), certified with
potential `v`, for its instruction. -/
def instrOk (κ : CostModel) (P : Lin.Prog) (N : Cert) (i pc : Nat) (fn : Lin.Fn) (v : Int)
    (ins : Lin.Instr) : Bool :=
  match ins with
  | .jmp l => succOk N i l v (C.ins P i pc fn ins)
  | .jz (.imm u) l =>
    if u = 0 then succOk N i l v (C.ins P i pc fn ins)
    else succOk N i (pc + 1) v (C.ins P i pc fn ins) && decide (v = 0)
  | .jz (.slot _) l => succOk N i (pc + 1) v (C.ins P i pc fn ins) && succOk N i l v (C.ins P i pc fn ins)
  | .call g _ _ =>
    match N g 0, N i (pc + 1) with
    | some e, some w =>
      decide ((C.ins P i pc fn ins : Int) + e + (resLen P g : Int) + w ≤ v) &&
        decide (0 ≤ (resLen P g : Int) + w)
    | _, _ => false
  | .ret => decide ((C.ins P i pc fn ins : Int) ≤ v + fn.ret.length)
  | .ext _ nr _ _ =>
    if nr then decide ((C.ins P i pc fn ins : Int) ≤ v) else succOk N i (pc + 1) v (C.ins P i pc fn ins)
  | .tick t =>
    match N i (pc + 1) with
    | some w => decide ((C.ins P i pc fn ins : Int) + w ≤ v + (t.cost κ : Int))
    | none => false
  | _ => succOk N i (pc + 1) v (C.ins P i pc fn ins)

/-- The local checks along a code list, the first instruction at position `pc`. -/
def codeOk (κ : CostModel) (P : Lin.Prog) (N : Cert) (i : Nat) (fn : Lin.Fn) :
    Nat → List Lin.Instr → Bool
  | _, [] => true
  | pc, ins :: rest =>
    (match N i pc with
     | some v => instrOk C κ P N i pc fn v ins
     | none => true) && codeOk κ P N i fn (pc + 1) rest

/-- The local checks of the functions from number `i` on. -/
def funsOk (κ : CostModel) (P : Lin.Prog) (N : Cert) : Nat → List Lin.Fn → Bool
  | _, [] => true
  | i, fn :: fs => codeOk C κ P N i fn 0 fn.code && funsOk κ P N (i + 1) fs

/-- The budget check of certificate `N`. `main`'s entry of `C.entry P` instructions followed by
the potential `N main 0` fits in potential 0, and every certified position passes its local
check. -/
def budgetOk (κ : CostModel) (P : Lin.Prog) (N : Cert) : Bool :=
  (match N P.main 0 with
   | some v => decide ((C.entry P : Int) + v ≤ 0)
   | none => false) && funsOk C κ P N 0 P.funs

/-! ## Computing a certificate -/

/-- `a + b`, with `none` standing for `-∞`. -/
def addI (c : Int) : Option Int → Option Int
  | some w => some (c + w)
  | none => none

/-- `max`, with `none` standing for `-∞`. -/
def maxI : Option Int → Option Int → Option Int
  | some a, some b => some (max a b)
  | some a, none => some a
  | none, b => b

/-- The values computed so far. -/
abbrev Table := Array (Array (Option Int))

/-- Looks up a position in a table. -/
def Table.get (T : Table) (i pc : Nat) : Option Int := (T[i]?.bind fun r => r[pc]?).join

/-- The least potential that position `pc` of function `i` needs given the table, with `none`
standing for `-∞`. -/
def need (κ : CostModel) (P : Lin.Prog) (T : Table) (i pc : Nat) (fn : Lin.Fn)
    (ins : Lin.Instr) : Option Int :=
  match ins with
  | .jmp l => addI (C.ins P i pc fn ins) (T.get i l)
  | .jz (.imm u) l =>
    if u = 0 then addI (C.ins P i pc fn ins) (T.get i l) else addI (C.ins P i pc fn ins) (T.get i (pc + 1))
  | .jz (.slot _) l =>
    maxI (addI (C.ins P i pc fn ins) (T.get i (pc + 1))) (addI (C.ins P i pc fn ins) (T.get i l))
  | .call g _ _ =>
    match T.get g 0, T.get i (pc + 1) with
    | some e, some w => some ((C.ins P i pc fn ins : Int) + e + resLen P g + w)
    | _, _ => none
  | .ret => some ((C.ins P i pc fn ins : Int) - fn.ret.length)
  | .ext _ nr _ _ => if nr then some (C.ins P i pc fn ins) else addI (C.ins P i pc fn ins) (T.get i (pc + 1))
  | .tick t => addI ((C.ins P i pc fn ins : Int) - t.cost κ) (T.get i (pc + 1))
  | _ => addI (C.ins P i pc fn ins) (T.get i (pc + 1))

/-- The lower bound a position gets because it follows a `call`: the result stores after the
return must not leave a negative potential. -/
def afterCall (P : Lin.Prog) (code : Array Lin.Instr) (pc : Nat) : Option Int :=
  match pc with
  | 0 => none
  | q + 1 =>
    match code[q]? with
    | some (.call g _ _) => some (-(resLen P g : Int))
    | _ => none

/-- One backward sweep over the code of function `i`, from position `pc - 1` down to 0. -/
def sweepFn (κ : CostModel) (P : Lin.Prog) (i : Nat) (fn : Lin.Fn) (code : Array Lin.Instr) :
    Nat → Table → Table
  | 0, T => T
  | pc + 1, T =>
    let v := match code[pc]? with
      | some (.jz (.imm u) l) =>
        if u = 0 then need C κ P T i pc fn (.jz (.imm u) l)
        else match need C κ P T i pc fn (.jz (.imm u) l) with
          | some x => if x ≤ 0 then some 0 else some x
          | none => some 0
      | some ins => maxI (need C κ P T i pc fn ins) (afterCall P code pc)
      | none => none
    sweepFn κ P i fn code pc (T.modify i fun r => r.set! pc v)

/-- One sweep over all functions, taking callees first since they have smaller numbers. -/
def sweep (κ : CostModel) (P : Lin.Prog) (T : Table) : Table :=
  (P.funs.zipIdx).foldl (fun T (fn, i) => sweepFn C κ P i fn fn.code.toArray fn.code.length T) T

/-- Sweeps until nothing changes, at most `fuel` times. -/
def iterate (κ : CostModel) (P : Lin.Prog) : Nat → Table → Table
  | 0, T => T
  | fuel + 1, T =>
    let T' := sweep C κ P T
    if T' == T then T else iterate κ P fuel T'

/-- A certificate for `budgetOk`, the least solution of the local constraints, found by
iterating backward sweeps from `-∞`. Positions that stay `none` are unconstrained. -/
def potential (κ : CostModel) (P : Lin.Prog) : Table :=
  iterate C κ P (P.funs.length + 64)
    (P.funs.map fun fn => Array.replicate fn.code.length none).toArray

end Millipede.Sel
