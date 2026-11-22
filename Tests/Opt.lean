import Millipede

/-!
# Tests for the optimisation passes on Core

Each pass is run on a small term, and the result has fewer nodes, a lower cost under the targets'
cost models, and the same value, checked by `rfl` because the passes run in the kernel. The
passes' laws are theorems, and `scripts/opt-compare.sh` compares optimised and unoptimised images
over the whole differential suite. The suite also checks the switches that select the passes,
and that the soundness theorem holds for every configuration of them.
-/

namespace Millipede.Tests.Opt

open Millipede Opt

/-- The number of nodes of a term, callee bodies included. -/
def nodes : {Γ : List Ty} → {t : Ty} → Exp Γ t → Nat
  | _, _, .let_ e₁ e₂ => 1 + nodes e₁ + nodes e₂
  | _, _, .ite _ e₁ e₂ => 1 + nodes e₁ + nodes e₂
  | _, _, .call _ b _ => 1 + nodes b
  | _, _, .match_ _ e₁ e₂ => 1 + nodes e₁ + nodes e₂
  | _, _, .loop _ _ _ c b k => 1 + nodes c + nodes b + nodes k
  | _, _, _ => 1

abbrev lit (v : UInt64) {Γ : List Ty} : Atom Γ .u64 := .lit v
abbrev v0 {Γ : List Ty} {t : Ty} : Atom (t :: Γ) t := .var .here
abbrev v1 {Γ : List Ty} {s t : Ty} : Atom (s :: t :: Γ) t := .var (.there .here)

/-! ## `fold`: `let x := 2 + 3; if x < 9 then x * x else 0` is `25` -/

def foldIn : Exp [] .u64 :=
  .let_ (.prim .add (.cons (lit 2) (.cons (lit 3) .nil)))
    (.let_ (.prim .ult (.cons v0 (.cons (lit 9) .nil)))
      (.ite v0 (.prim .mul (.cons v1 (.cons v1 .nil))) (.atom (lit 0))))

example : nodes (foldPass.run foldIn) = 1 := by decide
example : nodes foldIn = 7 := by decide
example (ω : Oracle) : ((foldPass.run foldIn).denote ω .nil World.init).1 = 25 := rfl
example : (foldPass.run foldIn).cost X64.κ .copy < foldIn.cost X64.κ .copy := by decide
example : (foldPass.run foldIn).cost A64.κ .copy < foldIn.cost A64.κ .copy := by decide

/-! ## `dce`: an unused pure `let` goes; an extern call stays -/

def dceIn : Exp [.u64] .u64 :=
  .let_ (.prim .mul (.cons v0 (.cons v0 .nil)))
    (.let_ (.ext ExtSig.exit (.word v1 .nil)) (.atom (.var (.there (.there .here)))))

example : nodes (dcePass.run dceIn) = 3 := rfl
example : nodes dceIn = 5 := rfl

/-! ## `inline`: a call of `x + y` with arguments `a, 7` is `a + 7` -/

def addBody : Exp [.u64, .u64] .u64 := .prim .add (.cons v0 (.cons v1 .nil))

def inlineIn : Exp [.u64] .u64 := .call "add" addBody (.cons v0 (.cons (lit 7) .nil))

example : nodes (inlinePass.run inlineIn) = 1 := rfl
example (ω : Oracle) : ((inlinePass.run inlineIn).denote ω (.cons 5 .nil) World.init).1 = 12 := rfl
example : (inlinePass.run inlineIn).cost X64.κ .copy < inlineIn.cost X64.κ .copy := by decide

/-- A callee that writes its parameter is not inlined, because the parameter is the root of a
place. -/
def writesParam : Exp [.u64] .u64 := .assign (.var .here) (lit 1) (.atom v0)

example : nodes (inlinePass.run (.call "w" writesParam (.cons v0 .nil) : Exp [.u64] .u64)) = 2 := rfl

/-! ## `strength`: `x / 8` is `x >>> 3`, `x % 8` is `x &&& 7`, `x / 6` stays -/

def divIn (d : UInt64) : Exp [.u64] .u64 := .prim .udiv (.cons v0 (.cons (lit d) .nil))

example (ω : Oracle) : ((strengthPass.run (divIn 8)).denote ω (.cons 100 .nil) World.init).1 = 12 := rfl
example : (strengthPass.run (divIn 8)).cost X64.κ .copy < (divIn 8).cost X64.κ .copy := by decide
example : (strengthPass.run (divIn 6)).cost X64.κ .copy = (divIn 6).cost X64.κ .copy := by decide

/-! ## The switches -/

#guard Opt.names == ["inline", "fold", "dce", "strength"]
#guard (Opt.Config.parse "none").toOption == some Opt.Config.none
#guard (Opt.Config.parse "fold,dce").toOption.map (·.on) == some ["fold", "dce"]
#guard (Opt.Config.parse "-inline").toOption.map (·.on) == some ["fold", "dce", "strength"]
#guard !(Opt.Config.parse "nosuch").toBool
-- `mp.opt.<pass>` (`#mp_compile`) names every registered pass.
#guard Meta.optOn {} == Opt.names

/-! ## The weight of an extern call covers its result's store

`let _ := write(1, ".")` in `init` is a `mov`, the `write` sequence and the store of its result
word into the root's frame, which is 15 instructions on x64 and 17 on arm64, against
`κ.let_ + κ.ext`. The harnesses of the differential suite reduce to runs of such calls once
`inline` and `fold` have evaluated their arguments. Twenty calls in a row compile, unoptimised
and optimised, with no fallback. -/

/-- `n` calls `write(1, ".")` in a row, followed by `exit(0)`. -/
def writes : (k : Nat) → Nat → Exp (List.replicate k Ty.u64) Ty.unit
  | _, 0 => .let_ (.ext ExtSig.exit (.word (lit 0) .nil)) (.atom (.lit (t := Ty.unit) ()))
  | k, n + 1 => .let_ (.ext ExtSig.write (.word (lit 1) (.bufIn (.const [46]) .nil)))
      (writes (k + 1) n)

def writesProg (n : Nat) : Program := ⟨Ty.unit, writes 0 n, Examples.keepUnit.exp⟩

#guard (compileWith { opt := Opt.Config.none, fallback := false } (writesProg 20) x64Linux).toBool
#guard (compileWith { opt := Opt.Config.none, fallback := false } (writesProg 20) arm64Linux).toBool
#guard (compileWith { opt := Opt.Config.all, fallback := false } (writesProg 20) x64Linux).toBool
#guard (compileWith { opt := Opt.Config.all, fallback := false } (writesProg 20) arm64Linux).toBool

/-! ## The headline theorems hold for the compiler with every pass on -/

example : CompileSound.Statement compile x64Linux := compile_sound
example : CompileSound.Statement compile arm64Linux := compile_sound_arm64
/-- The soundness theorem holds for every configuration of the switches. -/
example (o : Compile.Options) : CompileSound.Statement (compileWith o) x64Linux :=
  compileWith_sound_of_backend o (x64Backend o) (x64Backend_laws o) rfl

end Millipede.Tests.Opt
