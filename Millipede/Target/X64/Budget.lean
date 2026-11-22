import Millipede.Target.X64.Select
import Millipede.Target.Budget

/-!
# The instruction budget of x64 selected code

The check of a potential certificate is shared by both ISAs, and x64 supplies its instruction
counts with `k` preserved and `c` caller-saved register locations. `instrs k c P fn ins` is the number of machine instructions one
Lin step executes, and `main`'s entry is the single instruction `sub rsp`. `budgetOk` is the shared
check at these counts and their potential, and it is the check `compile` runs.
-/

namespace Millipede.X64

open Sel (calleeFrame resLen)

/-- The machine instructions executed for Lin instruction `ins` of the running function `fn`
with `k` register locations. It is the length of the selected block, except that a `call` also
runs the callee's entry `sub rsp` but not the result moves of its block, a `ret` runs those
moves after its own block, counted as at most `resFuel` of them, and `exit` does not run the store after its
`syscall`. -/
def instrs (k c : Nat) (mb : Bool) (lvo : Option RegAlloc.LiveSets) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn)
    (ins : Lin.Instr) : Nat :=
  match ins with
  | .call g args d =>
    (callOps k c (calleeFrame P g) args (RegAlloc.Live.callKeep lvo P i pc g d args)
      (RegAlloc.Live.liveIn lvo g 0)).length + 2
  | .ret => ((retLd k c fn.ret).getD [] ++ restores 0 (min k fn.frame) ++
      retTail (Sel.frameW k c fn.frame)).length +
      resFuel fn.ret.length
  | .ext "exit" true _ [.word a] => (ldTo k c .rdi a).length + 2
  | .ext "write" false x [.word a, .bytes _] =>
    (ldTo k c .rdi a).length + 1 + ([Instr.movRI .rdx 0, .movRI .rax 1, .syscall] ++ stTo k c x .rax).length
  | .ext "read" false x [.word a, .out 1] =>
    (ldTo k c .rdi a ++ rdPre (x - c) ++ [Instr.syscall] ++ rdFix (x - c) ++ stTo k c x .rcx).length
  | ins => match selInstr k c mb none P 0 0 fn ins with
    | .ok (b, _) => b.length
    | .error _ => 0

/-- x64's instruction counts with `k` preserved and `c` caller-saved register locations, which are `instrs k c` and one for
`main`'s entry `sub rsp, 8F`. -/
def counts (k c : Nat) (mb : Bool) (lvo : Option RegAlloc.LiveSets) : Sel.Counts :=
  ⟨fun P => instrs k c mb lvo P, fun _ => 1⟩

/-- A potential certificate. -/
abbrev Cert := Sel.Cert

/-- The budget check at x64's counts, with the register locations actually used and the cost
model `κ`. -/
def budgetOk (k c : Nat) (κ : CostModel) (P : Lin.Prog) (mb : Bool := true) : Bool :=
  let C := counts (kcUsed k c P mb).1 (kcUsed k c P mb).2 mb (RegAlloc.Live.of P)
  Sel.budgetOk C κ P (Sel.potential C κ P).get

end Millipede.X64
