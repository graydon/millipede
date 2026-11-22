import Millipede.Compile.Lin

/-!
# The pass from Flat to Lin

`linearize` replaces structured control with labels and jumps, and turns the inline callee of every
call site into a Lin function with its declared frame size. `Stmt.len s` is the number of Lin
instructions that `s` compiles to, which does not depend on where it is placed, so jump targets are
computed without looking at generated code.

`linS s pc fs = (code, fs')` compiles `s` to be placed at position `pc` of the current function,
given the functions `fs` created so far, and `fs'` extends `fs` with the callees of `s`. The
compiled forms are as follows:

- `ite c t e` at `pc` becomes `jz c Le; ⟦t⟧; jmp Lx; Le: ⟦e⟧; Lx:`.
- `while pre c body` at `L` becomes `L: ⟦pre⟧; jz c Lx; ⟦body⟧; jmp L; Lx:`.
- `call name fr body ret args d` compiles the body first, so that its own callees get smaller
  indices, as a function `⟨name, fr, ⟦body⟧ ++ [ret], ret⟩` appended at index `g`, and the call
  site becomes `call g args d`.

Callees therefore always have smaller indices than their callers, so there is no recursion, and
frame sizes are exactly the declared ones. `linearize fp M` appends `main`, with frame `fp.frame`
and code `⟦fp.main⟧ ++ [jmp self]`, and has the data region `[0, M)`. A Flat program that finishes
stutters, and so does its Lin image, on the self-jump. `Stmt.callBytes φ s` is the stack measure at
the Flat level, the maximum over call paths of the declared frames in bytes under `φ`, and the Lin
static stack bound equals it exactly.

See doc/design/compiler.md.
-/

namespace Millipede.Lin

open Flat (Stmt)

/-- The number of Lin instructions a Flat statement compiles to. -/
def Stmt.len : Stmt → Nat
  | .skip => 0
  | .seq a b => Stmt.len a + Stmt.len b
  | .ite _ t e => Stmt.len t + Stmt.len e + 2
  | .while pre _ body => Stmt.len pre + Stmt.len body + 2
  | .mov .. | .bin .. | .load .. | .store .. | .call .. | .ext .. | .tick _ => 1

/-- Compiles a Flat statement placed at position `pc`, given the functions created so far. -/
def linS : Stmt → Nat → List Fn → List Instr × List Fn
  | .skip, _, fs => ([], fs)
  | .seq a b, pc, fs =>
    let ra := linS a pc fs
    let rb := linS b (pc + Stmt.len a) ra.2
    (ra.1 ++ rb.1, rb.2)
  | .mov x a, _, fs => ([.mov x a], fs)
  | .bin op x a b, _, fs => ([.bin op x a b], fs)
  | .load w x a off, _, fs => ([.load w x a off], fs)
  | .store w a off b, _, fs => ([.store w a off b], fs)
  | .ite c t e, pc, fs =>
    let rt := linS t (pc + 1) fs
    let re := linS e (pc + Stmt.len t + 2) rt.2
    ([.jz c (pc + Stmt.len t + 2)] ++ rt.1 ++ [.jmp (pc + Stmt.len t + 2 + Stmt.len e)] ++ re.1,
      re.2)
  | .while pre c body, pc, fs =>
    let rp := linS pre pc fs
    let rb := linS body (pc + Stmt.len pre + 1) rp.2
    (rp.1 ++ [.jz c (pc + Stmt.len pre + Stmt.len body + 2)] ++ rb.1 ++ [.jmp pc], rb.2)
  | .call name fr body ret args d, _, fs =>
    let rb := linS body 0 fs
    ([.call rb.2.length args d], rb.2 ++ [⟨name, fr, rb.1 ++ [.ret], ret⟩])
  | .ext sym nr x args, _, fs => ([.ext sym nr x args], fs)
  | .tick t, _, fs => ([.tick t], fs)

/-- The `linearize` pass. It places all callees first, in creation order, and then `main`. Its
memory is the data region `[0, M)` of `M` bytes, and for a lowered program `M` is
`Program.memBytes`. -/
def linearize (fp : Flat.Prog) (M : Nat) : Prog :=
  let r := linS fp.main 0 []
  { funs := r.2 ++ [⟨"main", fp.frame, r.1 ++ [.jmp (Stmt.len fp.main)], []⟩]
    main := r.2.length
    mem := M }

/-- The stack measure at the Flat level, in bytes under `φ`, of the deepest chain of calls inside
`s`, where each call counts its declared frame. -/
def Stmt.callBytes (φ : FrameModel) : Stmt → Nat
  | .seq a b => max (Stmt.callBytes φ a) (Stmt.callBytes φ b)
  | .ite _ t e => max (Stmt.callBytes φ t) (Stmt.callBytes φ e)
  | .while pre _ body => max (Stmt.callBytes φ pre) (Stmt.callBytes φ body)
  | .call _ fr body _ _ _ => φ.frame fr + Stmt.callBytes φ body
  | _ => 0

/-- The generated code has exactly `Stmt.len s` instructions. -/
theorem linS_length : ∀ (s : Stmt) (pc : Nat) (fs : List Fn), (linS s pc fs).1.length = Stmt.len s
  | .skip, _, _ => rfl
  | .seq a b, pc, fs => by
    simp only [linS, List.length_append, linS_length a, linS_length b, Stmt.len]
  | .mov .., _, _ => rfl
  | .bin .., _, _ => rfl
  | .load .., _, _ => rfl
  | .store .., _, _ => rfl
  | .ite c t e, pc, fs => by
    simp only [linS, List.length_append, linS_length t, linS_length e, Stmt.len,
      List.length_singleton]
    omega
  | .while pre c body, pc, fs => by
    simp only [linS, List.length_append, linS_length pre, linS_length body, Stmt.len,
      List.length_singleton]
    omega
  | .call .., _, _ => rfl
  | .ext .., _, _ => rfl
  | .tick _, _, _ => rfl

/-- Compiling only appends functions. -/
theorem linS_prefix : ∀ (s : Stmt) (pc : Nat) (fs : List Fn), fs <+: (linS s pc fs).2
  | .skip, _, _ => List.prefix_refl _
  | .seq a b, pc, fs => (linS_prefix a pc fs).trans (linS_prefix b _ _)
  | .mov .., _, _ => List.prefix_refl _
  | .bin .., _, _ => List.prefix_refl _
  | .load .., _, _ => List.prefix_refl _
  | .store .., _, _ => List.prefix_refl _
  | .ite _ t e, _, fs => (linS_prefix t _ fs).trans (linS_prefix e _ _)
  | .while pre _ body, pc, fs => (linS_prefix pre pc fs).trans (linS_prefix body _ _)
  | .call _ _ body _ _ _, _, fs => (linS_prefix body 0 fs).trans (List.prefix_append _ _)
  | .ext .., _, _ => List.prefix_refl _
  | .tick _, _, _ => List.prefix_refl _

end Millipede.Lin
