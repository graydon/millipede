import Tests.Lin
import Millipede.RegAlloc.Alloc
import Millipede.RegAlloc.Live
import Millipede.Target.PMove
import Millipede.RegAlloc.A64Reg
import Millipede.Target.X64.Select

/-!
# Tests for register allocation

The allocator proposes locations for lowered programs with calls, loops, externs and a reactor
loop, and the checker `RegAlloc.check` accepts each proposal, with 10 register locations and with
none, which only compacts the slots. The allocated programs run in the Lin interpreter with the
source's events and clock, as the checker's theorem promises for every accepted program.

Four seeded allocator bugs are each rejected by the checker, and those that change behaviour
are seen to change it, so a missing check would show. The bugs shift every location, put every
web in location 0, pass call arguments in the source's positions, and write a call's results
one location off.

The live sets computed for every program, before and after allocation, pass the checker against
the program itself. A Lin run that scrambles, at each call, the caller's locations that the call
does not keep has the plain run's events. Two seeded bugs in live sets are each rejected, and the
first, unchecked, changes the scrambled run's events.

With caller-saved classes (four registers after six preserved ones, all destroyed by a call, two
by a division), every allocation passes the clobber check `Live.clobOk`, and a Lin run that
scrambles, after each instruction, the locations it destroys and does not define has the plain
run's events. A seeded allocator bug that ignores the clobber sets is rejected by the check, and
its allocation, unchecked, changes the scrambled run's events.

The sequentialised parallel move `Sel.PMove.seq` with fuel `2 n + 1` accepts every parallel move of
four destinations among five registers and agrees with `par` on each (the theorem `seq_run` covers
accepted sequences only); a seeded bug that drops the cycle-breaking copy is caught. On arm64, a
`ret` whose two operands sit in each other's result register and a `write` of a buffer whose
descriptor and length sit in each other's argument register are selected as copies that exchange
the registers through the temporary, and the same copies in reverse order (mutant `areg-pmove`)
do not; so is an x64 `ret` whose operands sit in each other's result registers `rdx` and `rsi`
(mutant `xreg-pmove`).

The allocations with caller-saved classes pass the frame check `frameOk` in frame words
(`Sel.frameW`, a caller-saved location has none); frames that grow only by caller-saved
locations pass it and fail a check counting every location as a word.
-/

namespace Millipede.Tests.RegAlloc

open Millipede Millipede.Flat Millipede.Lin Millipede.RegAlloc Millipede.Tests.Lower
  Millipede.Tests.Lin Millipede.Tests.Core

/-- The events and clock after `fuel` Lin steps. -/
def runLin (P : Lin.Prog) (fuel : Nat) : Option (List Event × Nat) :=
  ((Lin.sem κ2 P).run ωc P.init fuel).map fun s => (s.world.events, s.clock)

def progs : List Lin.Prog :=
  [linearize (lowerProg callProg) callProg.memBytes, linearize (lowerProg counter) counter.memBytes,
   linearize (lowerProg hello) hello.memBytes, linearize (lowerProg resProg) resProg.memBytes,
   linOf clamp3, linOf (sumTo 10), linOf useDiv]

/-- Whether the allocator's proposal is accepted and runs as the source does. -/
def accepted (k : Nat) (P : Lin.Prog) : Bool :=
  let (P', maps, _) := Alloc.allocate { k } P
  check P P' maps && frameOk k 0 P P' && runLin P' 600 == runLin P 600 &&
    (Alloc.allocOrId { k } P).funs.length == P.funs.length

#guard progs.all (accepted 10)
#guard progs.all (accepted 0)

-- The allocation changes something, since some program's stack bound shrinks.
#guard progs.any fun P => (Alloc.allocOrId { k := 0 } P).stackBytes φ8 < P.stackBytes φ8

/-! ## Seeded allocator bugs -/

def mapOp (f : Nat → Nat) : Operand → Operand
  | .slot y => .slot (f y)
  | o => o

/-- Applies `f` to every location that the code uses or defines. -/
def mapInstr (f : Nat → Nat) : Instr → Instr
  | .mov x a => .mov (f x) (mapOp f a)
  | .bin op x a b => .bin op (f x) (mapOp f a) (mapOp f b)
  | .load w x a off => .load w (f x) (mapOp f a) off
  | .store w a off b => .store w (mapOp f a) off (mapOp f b)
  | .jz c l => .jz (mapOp f c) l
  | i => i

def mutFns (P : Lin.Prog) (g : Lin.Fn → Lin.Fn) : Lin.Prog := { P with funs := P.funs.map g }

/-- Bug 1 shifts every location by one and grows the frame to match. -/
def bugShift (P' : Lin.Prog) : Lin.Prog :=
  mutFns P' fun fn => { fn with frame := fn.frame + 1, code := fn.code.map (mapInstr (· + 1)) }

/-- Bug 2 ignores interference and puts every location at 0. -/
def bugZero (P' : Lin.Prog) : Lin.Prog :=
  mutFns P' fun fn => { fn with code := fn.code.map (mapInstr fun _ => 0) }

/-- Bug 3 passes call arguments in the source's positions, ignoring the callee's entry map. -/
def bugArgs (P P' : Lin.Prog) : Lin.Prog :=
  { P' with funs := (P'.funs.zip P.funs).map fun (fn', fn) =>
      { fn' with code := (fn'.code.zip fn.code).map fun
        | (.call g _ d', .call _ args _) => .call g args d'
        | (i, _) => i } }

/-- Bug 4 writes a call's results one location up. -/
def bugDst (P' : Lin.Prog) : Lin.Prog :=
  mutFns P' fun fn => { fn with code := fn.code.map fun
    | .call g args d => .call g args (d + 1)
    | i => i }

def rejects (bug : Lin.Prog → Lin.Prog → Lin.Prog) (P : Lin.Prog) : Bool :=
  let (P', maps, _) := Alloc.allocate { k := 10 } P
  !check P (bug P P') maps

-- Each bug is rejected on every program where it changes the code.
#guard progs.all (rejects fun _ P' => bugShift P')
#guard progs.all (rejects fun _ P' => bugZero P')
#guard [progs[0]!, progs[4]!].all (rejects bugArgs)
#guard [progs[0]!, progs[4]!].all (rejects fun _ P' => bugDst P')

/-- Whether a bug, unchecked, changes the behaviour of `P`, which shows that the checker is what
stops it. -/
def misbehaves (bug : Lin.Prog → Lin.Prog → Lin.Prog) (P : Lin.Prog) : Bool :=
  let (P', _, _) := Alloc.allocate { k := 10 } P
  runLin (bug P P') 600 != runLin P 600

#guard misbehaves (fun _ P' => bugZero P') progs[0]!
#guard misbehaves bugArgs progs[0]!
#guard misbehaves (fun _ P' => bugDst P') progs[0]!

/-! ## Live sets -/

def scramble (keep : Nat → Bool) (fr : Frame) : Frame := fun x => if keep x then fr x else 0xDEAD

/-- One Lin step that, at a call, scrambles the caller's locations the call does not keep, as a
selector that saves only those locations would do to a suspended frame. -/
def scrStep (P : Lin.Prog) (lvo : Option LiveSets) (s : Lin.State) : Option Lin.State :=
  match s.stack, (P.funs[s.fn]?).bind (·.code[s.pc]?), (P.funs[s.fn]?).map (·.frame) with
  | _, some (.call g args d), some F =>
    let keep := Live.keepCall lvo s.fn s.pc F d (retLen P g) args
    (Lin.step κ2 P ωc s).map fun t => match t.stack with
      | a :: st => { t with stack := { a with frame := scramble keep a.frame } :: st }
      | [] => t
  | _, _, _ => Lin.step κ2 P ωc s

def runScr (P : Lin.Prog) (lvo : Option LiveSets) : Nat → Lin.State → Option Lin.State
  | 0, s => some s
  | n + 1, s => (scrStep P lvo s).bind (runScr P lvo n)

def scrEvents (P : Lin.Prog) (lvo : Option LiveSets) (fuel : Nat) : Option (List Event × Nat) :=
  (runScr P lvo fuel P.init).map fun s => (s.world.events, s.clock)

def liveOk (P : Lin.Prog) : Bool :=
  (Live.of P).isSome && scrEvents P (Live.of P) 600 == runLin P 600

#guard progs.all liveOk
#guard progs.all fun P => liveOk (Alloc.allocOrId { k := 10 } P)

/-- A bug that marks every location dead after a call. -/
def bugAfterCall (P : Lin.Prog) (lv : LiveSets) : LiveSets :=
  (P.funs.zip lv).map fun (fn, l) => (List.range l.length).map fun pc =>
    match fn.code[pc - 1]? with
    | some (Lin.Instr.call ..) => if pc = 0 then l.getD pc [] else []
    | _ => l.getD pc []

/-- A bug that adds, at the target of a jump, a location the jump's set does not hold. -/
def bugJoin (P : Lin.Prog) (lv : LiveSets) : LiveSets :=
  (P.funs.zip lv).map fun (fn, l) =>
    let fresh := fn.frame
    (List.range l.length).map fun pc =>
      if fn.code.any (fun i => match i with | .jmp t => t == pc | _ => false) then
        fresh :: l.getD pc [] else l.getD pc []

def rejectsLive (bug : Lin.Prog → LiveSets → LiveSets) (P : Lin.Prog) : Bool :=
  !check P P (idMaps (bug P (Live.compute P)))

-- The bugs are rejected on the programs with calls, 0, 4 and 6, and on every program with a
-- jump.
#guard [progs[0]!, progs[4]!, progs[6]!].all (rejectsLive bugAfterCall)
#guard progs.all fun P => !(P.funs.any fun fn => fn.code.any fun | .jmp _ => true | _ => false) ||
  rejectsLive bugJoin P
#guard progs.any fun P => scrEvents P (some (bugAfterCall P (Live.compute P))) 600 != runLin P 600

/-! ## Caller-saved classes and the clobber check -/

/-- Six preserved registers and four caller-saved ones, all destroyed by a call and the first two
by a division. -/
def cls : Alloc.Classes := { k := 6, c := 4, kill := fun
  | .call .. => (List.range 4, [])
  | .bin .udiv .. => ([0, 1], [])
  | _ => ([], []) }

/-- The same classes as the allocator of seeded bug 5 sees them, with no register destroyed. -/
def clsBug : Alloc.Classes := { cls with kill := fun _ => ([], []) }

/-- One Lin step that scrambles, in the frame it reaches, the locations the instruction before
that position destroys and does not define, after a fall-through or a return. -/
def kilStep (P : Lin.Prog) (s : Lin.State) : Option Lin.State :=
  (Lin.step κ2 P ωc s).map fun t =>
    let back := (t.fn == s.fn && t.pc == s.pc + 1) || t.stack.length + 1 == s.stack.length
    match back, t.pc, (P.funs[t.fn]?).bind (·.code[t.pc - 1]?) with
    | true, _ + 1, some ins =>
      { t with frame := scramble (fun x => !cls.across ins x || Live.defs P ins x) t.frame }
    | _, _, _ => t

def runKil (P : Lin.Prog) : Nat → Lin.State → Option Lin.State
  | 0, s => some s
  | n + 1, s => (kilStep P s).bind (runKil P n)

def kilEvents (P : Lin.Prog) (fuel : Nat) : Option (List Event × Nat) :=
  (runKil P fuel P.init).map fun s => (s.world.events, s.clock)

def clobAccepted (cl : Alloc.Classes) (P : Lin.Prog) : Bool :=
  let P' := Alloc.allocOrId cl P
  Live.clobOk cls.across (Live.of P') P'

#guard progs.all fun P => clobAccepted cls P && kilEvents (Alloc.allocOrId cls P) 600 == runLin P 600
-- Caller-saved registers are used: some program has a location in `6 … 9`.
#guard progs.any fun P => (Alloc.allocOrId cls P).funs.any fun fn => fn.code.any fun
  | .mov x _ | .bin _ x _ _ => decide (6 ≤ x ∧ x < 10)
  | _ => false
-- Bug 5 is rejected on the programs with calls and changes the scrambled run of one of them.
#guard [progs[0]!, progs[4]!, progs[6]!].all fun P => !clobAccepted clsBug P
#guard progs.any fun P => kilEvents (Alloc.allocOrId clsBug P) 600 != runLin P 600

/-! ## Frames counted in words -/

-- A frame of 21 locations with 6 preserved and 14 caller-saved register locations has 7 words:
-- the 6 save words and the slot.
#guard Sel.frameW 6 14 21 = 7
-- The allocations with caller-saved classes pass the frame check in words, and their frames in
-- words are no larger than the source's.
#guard progs.all fun P => let (P', _, _) := Alloc.allocate cls P; frameOk cls.k cls.c P P'
#guard progs.all fun P => (Alloc.allocOrId cls P).stackBytes (φ8.words cls.k cls.c) ≤ P.stackBytes φ8
/-- A program whose functions all have frames of `F` locations. -/
def frames (F : Nat) : Lin.Prog := mutFns progs[0]! fun fn => { fn with frame := F }

-- Frames of 7 locations allocated into 21 (6 preserved, 14 caller-saved, one slot) pass in words
-- and fail when every location counts as a word, as before; frames of 6 fail in words too.
#guard frameOk 6 14 (frames 7) (frames 21) && !frameOk 6 0 (frames 7) (frames 21) &&
  !frameOk 6 14 (frames 6) (frames 21)

/-! ## Parallel moves -/

/-- Every parallel move of destinations `0 … 3` from sources among `0 … 4`, with `tmp = 9`. -/
def pmoves : List (List (Nat × Nat)) :=
  let srcs := List.range 5
  srcs.flatMap fun a => srcs.flatMap fun b => srcs.flatMap fun c => srcs.map fun d =>
    [(0, a), (1, b), (2, c), (3, d)]

def pmOk (sq : Nat → List (Nat × Nat) → Option (List (Nat × Nat))) (ms : List (Nat × Nat)) : Bool :=
  match sq (2 * ms.length + 1) ms with
  | some l => (List.range 9).all fun r => Sel.PMove.run id l r == Sel.PMove.par id ms r
  | none => false

#guard pmoves.all (pmOk (Sel.PMove.seq 9))

/-- Seeded bug 6: a cycle is broken by a move into its first destination instead of `tmp`. -/
def seqBug : Nat → List (Nat × Nat) → Option (List (Nat × Nat))
  | 0, _ => some []
  | n + 1, ms =>
    match Sel.PMove.pick 9 (ms.filter fun p => p.1 ≠ p.2) with
    | some ((d, s), rest) =>
      let mv := if d = 9 then ((ms.filter fun p => p.1 ≠ p.2).headD (0, 0)).1 else d
      ((mv, s) :: ·) <$> seqBug n rest
    | none => some []

#guard !pmoves.all (pmOk seqBug)

/-- The register file after the copies `mov d, s` of a code list; other instructions are
ignored. -/
def runMv (f : Nat → Nat) : List A64.Instr → Nat → Nat
  | [] => f
  | .logReg .orr true d 31 s :: is => runMv (fun r => if r = d.toNat then f s.toNat else f r) is
  | _ :: is => runMv f is

/-- `ret` of locations 11 and 10, which are `x1` and `x0` with 14 caller-saved locations. -/
def swapRet : List A64.Instr := (RegAlloc.A64Reg.retLd 0 14 [.slot 11, .slot 10]).getD []

#guard swapRet.length == 3
#guard runMv id swapRet 0 == 1 && runMv id swapRet 1 == 0
#guard !(runMv id swapRet.reverse 0 == 1 && runMv id swapRet.reverse 1 == 0)

/-- `write(x2, buf, x0)`: the descriptor in location 12 (`x2`) and the length in location 10
(`x0`), the address in `x16`. -/
def swapWrite : List A64.Instr :=
  (RegAlloc.A64Reg.memTail 0 14 64 20 (.slot 12) (.slot 10)).getD []

#guard runMv id swapWrite 0 == 2 && runMv id swapWrite 2 == 0 && runMv id swapWrite 1 == 16
#guard !(runMv id swapWrite.reverse 0 == 2 && runMv id swapWrite.reverse 2 == 0)

/-- The register file after the x64 copies `mov d, s` of a code list. -/
def runMvX (f : X64.Reg → Nat) : List X64.Instr → X64.Reg → Nat
  | [] => f
  | .movRR d s :: is => runMvX (fun r => if r = d then f s else f r) is
  | _ :: is => runMvX f is

def xId : X64.Reg → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3 | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13 | .r14 => 14
  | .r15 => 15

/-- x64 `ret` of three words whose operands are in `rsi`, `rdx` and `rdi` (locations 4, 5, 3 with
six caller-saved locations), results 2, 3, 4 being `rdx`, `rsi`, `rdi`: a cycle. -/
def swapRetX : List X64.Instr :=
  (X64.retLd 0 6 [.imm 7, .imm 8, .slot 4, .slot 5, .slot 3]).getD []

#guard runMvX xId swapRetX .rdx == xId .rsi && runMvX xId swapRetX .rsi == xId .rdx &&
  runMvX xId swapRetX .rdi == xId .rdi
#guard !(runMvX xId swapRetX.reverse .rdx == xId .rsi && runMvX xId swapRetX.reverse .rsi == xId .rdx)

end Millipede.Tests.RegAlloc
