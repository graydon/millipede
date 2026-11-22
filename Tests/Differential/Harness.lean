import Tests.Differential.Funcs

/-!
# The harness that reads test cases from standard input

The pipeline expands every value to byte code, so a program with a hundred inlined calls is
large and slow to compile. The functions over memory are therefore tested by a reactor that
reads its cases from standard input, one byte per call of the `read` extern. Each step reads a
case, calls the function under test, compares the result with the expected value that came with
the case and writes `.` or `X`. At the end of input it calls `exit(0)`, so one ELF covers all the
cases of a function. The input file is fixed and biased towards edge values, and a truncated
file shows as `X`.

`wordHarness` builds the step in Core for a function of any number of words, so the compiler sees
an ordinary `Program` whose step calls the function.
-/

namespace Millipede.Tests.Differential

open Millipede

/-- Read one little-endian word whose first byte `b0` has been read already. A byte read as
`2^64-1`, at the end of input in the middle of a case, corrupts the word, so the case fails. The
reads are unrolled because a loop's copies of its accumulator would cost more instructions than
the cost model pays for, and `compile` would refuse the program. -/
mp def readWord (b0 : UInt64) : UInt64 :=
  let b1 := Examples.sysRead 0
  let b2 := Examples.sysRead 0
  let b3 := Examples.sysRead 0
  let b4 := Examples.sysRead 0
  let b5 := Examples.sysRead 0
  let b6 := Examples.sysRead 0
  let b7 := Examples.sysRead 0
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) |||
    (b6 <<< 48) ||| (b7 <<< 56)

mp def initUnit : Unit := ()

/-- The first byte of a case, or `2^64-1` at the end of input. -/
mp def readByte0 : UInt64 := Examples.sysRead 0

/-- A word of a case after its first. -/
mp def nextWord : UInt64 := readWord (Examples.sysRead 0)

/-- `Args` in a context with one more variable. -/
def shiftArgs {Γ : List Ty} {s : Ty} : {ps : List Ty} → Args Γ ps → Args (s :: Γ) ps
  | _, .nil => .nil
  | _, .cons a as => .cons a.shift (shiftArgs as)

/-- The `n` innermost variables of the context, the innermost first. -/
def innerArgs : (n : Nat) → (Γ : List Ty) → Args (List.replicate n Ty.u64 ++ Γ) (List.replicate n Ty.u64)
  | 0, _ => .nil
  | n + 1, Γ => .cons (.var .here) (shiftArgs (innerArgs n Γ))

/-- `k` words read in turn and bound in the context of `body`, the last one innermost. The first
word is read with its first byte, the variable `b0`, already read. -/
def readWords : (k : Nat) → {Γ : List Ty} → {t : Ty} → Mem Ty.u64 Γ →
    Exp (List.replicate k Ty.u64 ++ Γ) t → Exp Γ t
  | 0, _, _, _, body => body
  | k + 1, _, _, b0, body => readWords k b0 (.let_ (readAt k b0) body)
where
  /-- the read bound after `k` earlier words -/
  readAt {Γ : List Ty} : (k : Nat) → Mem Ty.u64 Γ → Exp (List.replicate k Ty.u64 ++ Γ) Ty.u64
    | 0, b0 => .call "readWord" readWord.exp (.cons (.var b0) .nil)
    | _ + 1, _ => .call "nextWord" nextWord.exp .nil

/-- `write(1, [b])`. -/
def writeByte {Γ : List Ty} (b : UInt8) : Exp Γ Ty.u64 :=
  .ext ExtSig.write (.word (.lit (t := Ty.u64) 1) (.bufIn (.const [b]) .nil))

/-- The harness step for a function `e` of `n` words, built in Core, also for functions whose
parameters are quantities. The step hands back its state, since the pipeline updates the root in
place and requires the step's tails to be the root. It reads the first byte of a case, and at the end of
input calls `exit(0)`. Otherwise it reads the `n` arguments and the expected value, calls the
function, and writes `.` or `X`. The arguments come from standard input, so the Core passes cannot
evaluate the call when the program is compiled. -/
def wordHarness (name : String) (n : Nat) (e : Exp (List.replicate n Ty.u64) Ty.u64) :
    Exp [Ty.unit] Ty.unit :=
  let Γ₁ : List Ty := [Ty.bool, Ty.u64, Ty.unit]
  let body : Exp (List.replicate (n + 1) Ty.u64 ++ Γ₁) Ty.u64 :=
    .let_ (.call name e (shiftArgs (innerArgs n Γ₁)))
      (.let_ (.prim .eq (.cons (.var .here) (.cons (.var (.there .here)) .nil)))
        (.ite (.var .here) (writeByte 46) (writeByte 88)))
  .let_
    (.let_ (.call "readByte0" readByte0.exp .nil)
      (.let_ (.prim .ult (.cons (.var .here) (.cons (.lit (t := Ty.u64) 256) .nil)))
        (.ite (.var .here) (readWords (n + 1) (.there .here) body)
          (.ext ExtSig.exit (.word (.lit (t := Ty.u64) 0) .nil)))))
    (.atom (.var (.there .here)))

/-- The program of a harness step. -/
def harnessProgram (step : Exp [Ty.unit] Ty.unit) : Program := ⟨Ty.unit, initUnit.exp, step⟩

/-- The input file of the harness, which holds for each case the arguments in source order and the
expected value, as little-endian words. -/
def harnessInput (ref : List UInt64 → UInt64) (ins : List (List UInt64)) : List UInt8 :=
  ins.flatMap fun xs => (xs ++ [ref xs]).flatMap fun w =>
    (List.range 8).map fun i => (w >>> (8 * i).toUInt64).toUInt8

end Millipede.Tests.Differential
