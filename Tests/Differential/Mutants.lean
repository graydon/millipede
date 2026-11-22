import Tests.Differential.Harness

/-!
# Seeded compiler bugs

The self-test of `scripts/differential.sh` must show that the differential suite catches
miscompilations. This module runs the real passes of the x64 pipeline one by one and applies a
mutation to the output of one pass before the next pass consumes it, which has the effect of a
bug in that pass. The compiler itself is not modified, and the suite must fail for every mutant;
a mutant that every test passes is reported by the self-test.

The mutants act on three of the intermediate programs:
* On the Flat program, the lowering mutants invert `eq` tests, store bytes one byte off, widen
  byte loads to words, make `trunc8` keep 7 bits and make `zext8` set bit 8. They run on the byte
  functions of `ByteFuncs.lean`.
* Also on the Flat program, the pointer mutants add a field offset wrongly, read a reference's
  address from the wrong word of its slot, read or write through an address register one byte
  off, and record the wrong address for a borrow binder or reference argument. They run on the
  pointer functions of `PtrFuncs.lean`.
* The copy mutants replace the address stored for a reference by the address of a copy of the
  first 64 bytes of its lender, which reads correctly and loses the writes. `copy-borrow`,
  `copy-ref`, `copy-slice-borrow` and `copy-slice-arg` do this for a scoped borrow, a reference
  argument, a scoped slice borrow and a slice argument, and find each in the Flat code by its
  shape. `copy-loop-carried` copies the target of every store through the address register in a
  loop body, and `ptr-pair-alias` makes the second address of a pair reference equal the first.
  Such a bug shows only when the caller reads the lender afterwards, so `aliasFor` lists the
  harnesses that must fail for each.
* The slot mutants break variables that live in frame slots. They read from the next slot, drop
  an assignment's write, drop the writes of an `else` branch or of a loop's carried scalars, put
  a call's result or arguments in the wrong slots, step a loop counter by two, drop an
  accumulator's update, read one byte instead of a word, read a tag from the payload, store
  words as bytes, and copy overlapping slots forward. `slotFor` lists, for each, the functions
  of `SlotFuncs.lean` and `LoopFuncs.lean` that must each fail.
* The loop mutants stop the store loop of a large constructor one word early: `loop-fill-short`
  for a fill with a literal, `loop-copy-short` for a copied argument. `aliasFor` names `bFill`
  and `bCopy` of `ByteFuncs.lean`.
* On the Lin program, unsigned `<` becomes `≤`, and byte and word stores are swapped.
* On the Asm program, `setb` becomes `setbe`, `movzx` byte loads become word loads, byte and word
  stores are swapped, `shl` becomes `shr` and `sub` becomes `add`.
-/

namespace Millipede.Tests.Differential

open Millipede

/-! ## Mapping over the IRs -/

/-- Apply `f` to the leaves of a Flat statement. The function traverses `seq`, `ite`, `while` and
the bodies of calls, and applies `f` to every other statement. -/
def mapFlat (f : Flat.Stmt → Flat.Stmt) : Flat.Stmt → Flat.Stmt
  | .seq a b => .seq (mapFlat f a) (mapFlat f b)
  | .ite c t e => .ite c (mapFlat f t) (mapFlat f e)
  | .while pre c b => .while (mapFlat f pre) c (mapFlat f b)
  | .call n fr b ret args dst => f (.call n fr (mapFlat f b) ret args dst)
  | s => f s

/-- Apply `f` to every Lin instruction. -/
def mapLin (f : Lin.Instr → Lin.Instr) (P : Lin.Prog) : Lin.Prog :=
  { P with funs := P.funs.map fun fn => { fn with code := fn.code.map f } }

/-- Apply `f` to every x64 instruction of an Asm program, keeping its symbolic instructions. -/
def mapAsm (f : X64.Instr → X64.Instr) (A : Asm.Prog X64.arch) : Asm.Prog X64.arch :=
  let g : X64.SI → X64.SI
    | .op i => .op (f i)
    | s => s
  { A with funs := A.funs.map fun fn =>
      { fn with entry := fn.entry.map g, blocks := fn.blocks.map (·.map g) } }

/-! ## The mutants -/

/-- The seeded bugs. -/
inductive Mutant where
  | none
  | flatEq | flatStoreOff | flatLoadWide | flatTrunc8 | flatZext8
  | ptrFieldOff | ptrDerefLoad | ptrReadOff | ptrWriteOff | ptrStoreAddr
  | copyBorrow | copyRef | copySliceBorrow | copySliceArg
  | copyLoopCarried | ptrPairAlias
  | loopFillShort | loopCopyShort
  | slotReadOff | slotStale | slotBranch | slotCntStep | slotAccNext | slotReadNarrow
  | slotCarry | slotCallRes | slotArg | slotTag | slotAsgOff | slotChunkNarrow | slotStraddle
  | linUlt | linStoreWidth
  | selSetb | selMovzx | selStore8 | selShl | selSub
deriving DecidableEq

/-- The mutant's name on the command line. -/
def Mutant.name : Mutant → String
  | .none => "none" | .flatEq => "flat-eq" | .flatStoreOff => "flat-store-off"
  | .flatLoadWide => "flat-load-wide" | .flatTrunc8 => "flat-trunc8" | .flatZext8 => "flat-zext8"
  | .ptrFieldOff => "ptr-field-off" | .ptrDerefLoad => "ptr-deref-load"
  | .ptrReadOff => "ptr-read-off" | .ptrWriteOff => "ptr-write-off"
  | .ptrStoreAddr => "ptr-store-addr" | .copyBorrow => "copy-borrow" | .copyRef => "copy-ref"
  | .copySliceBorrow => "copy-slice-borrow" | .copySliceArg => "copy-slice-arg"
  | .copyLoopCarried => "copy-loop-carried" | .ptrPairAlias => "ptr-pair-alias"
  | .loopFillShort => "loop-fill-short" | .loopCopyShort => "loop-copy-short"
  | .slotReadOff => "slot-read-off" | .slotStale => "slot-stale" | .slotBranch => "slot-branch"
  | .slotCntStep => "slot-cnt-step" | .slotAccNext => "slot-acc-next"
  | .slotReadNarrow => "slot-read-narrow" | .slotCarry => "slot-carry"
  | .slotCallRes => "slot-call-res" | .slotArg => "slot-arg" | .slotTag => "slot-tag"
  | .slotAsgOff => "slot-asg-off" | .slotChunkNarrow => "slot-chunk-narrow"
  | .slotStraddle => "slot-straddle"
  | .linUlt => "lin-ult" | .linStoreWidth => "lin-store-width"
  | .selSetb => "sel-setb" | .selMovzx => "sel-movzx" | .selStore8 => "sel-store8"
  | .selShl => "sel-shl" | .selSub => "sel-sub"

/-- All seeded bugs. -/
def Mutant.all : List Mutant :=
  [.flatEq, .flatStoreOff, .flatLoadWide, .flatTrunc8, .flatZext8, .ptrFieldOff, .ptrDerefLoad, .ptrReadOff, .ptrWriteOff,
   .ptrStoreAddr, .copyBorrow, .copyRef, .copySliceBorrow, .copySliceArg, .copyLoopCarried,
   .ptrPairAlias, .loopFillShort, .loopCopyShort, .slotReadOff, .slotStale, .slotBranch, .slotCntStep, .slotAccNext,
   .slotReadNarrow, .slotCarry, .slotCallRes, .slotArg, .slotTag, .slotAsgOff,
   .slotChunkNarrow, .slotStraddle, .linUlt,
   .linStoreWidth, .selSetb, .selMovzx,
   .selStore8, .selShl, .selSub]

/-- The mutants aimed at references compiled as addresses. The self-test runs them on the pointer
functions of `PtrFuncs.lean` and on the memory functions. -/
def Mutant.isPtr : Mutant → Bool
  | .ptrFieldOff | .ptrDerefLoad | .ptrReadOff | .ptrWriteOff | .ptrStoreAddr => true
  | .copyBorrow | .copyRef | .copySliceBorrow | .copySliceArg => true
  | .copyLoopCarried | .ptrPairAlias => true
  | _ => false

def Mutant.ofName (s : String) : Option Mutant := Mutant.all.find? (·.name == s)

/-! ## Copy instead of pointer -/

open Flat in
/-- The statements of a nested `seq`, in order. -/
def flatten : Stmt → List Stmt
  | .seq a b => flatten a ++ flatten b
  | s => [s]

open Flat in
/-- A right-nested `seq` of the statements. -/
def rebuild : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: rest => .seq s (rebuild rest)

open Flat in
/-- Whether the statements continue, through straight-line code only, to the address of a callee
frame and the call, `RX := BP + n; call … [RX]`. When they do, the reference stores just seen are
a call's arguments and do not belong to a borrow. -/
def reachesCall : List Stmt → Bool
  | .bin .add x (.slot b) (.imm _) :: .call _ _ _ [] [.slot y] _ :: _ =>
    x == Flat.RX && b == Flat.BP && y == Flat.RX
  | .tick _ :: _ | .ite .. :: _ | .while .. :: _ | .call .. :: _ | .ext .. :: _ => false
  | _ :: rest => reachesCall rest
  | [] => false

open Flat in
/-- Whether a length is stored at `k + 8` right after the address, which marks a slice reference.
The search looks at most `fuel` statements ahead and stops at the next reference store. -/
def hasLenStore (k : UInt64) : Nat → List Stmt → Bool
  | 0, _ => false
  | _, [] => false
  | fuel + 1, s :: rest =>
    match s with
    | .store .w64 (.slot b) off (.slot x) =>
      if b == Flat.BP && x == Flat.RX && off == k + 8 then true
      else if b == Flat.BP && x == Flat.RA then false
      else hasLenStore k fuel rest
    | _ => hasLenStore k fuel rest

/-- The size of the scratch ring, which is a counter word at `M` followed by 0x4000 bytes of 64-byte
copies. -/
def scratchBytes : Nat := 0x4010

open Flat in
/-- Copy the 64 bytes at the address in `RA` into the next block of the scratch ring and put the
block's address in `RA`. The lender is not touched again, so writes through the reference are
lost. -/
def copyIn (M : Nat) : List Stmt :=
  [.mov Flat.RB (.imm (UInt64.ofNat M)),
   .load .w64 Flat.RX (.slot Flat.RB) 0,
   .bin .add Flat.RX (.slot Flat.RX) (.imm 64),
   .store .w64 (.slot Flat.RB) 0 (.slot Flat.RX),
   .bin .band Flat.RX (.slot Flat.RX) (.imm 0x3FC0),
   .bin .add Flat.RB (.slot Flat.RB) (.imm 8),
   .bin .add Flat.RB (.slot Flat.RB) (.slot Flat.RX)] ++
  (List.range 8).flatMap (fun j =>
    [.load .w64 Flat.RT (.slot Flat.RA) (UInt64.ofNat (8 * j)),
     .store .w64 (.slot Flat.RB) (UInt64.ofNat (8 * j)) (.slot Flat.RT)]) ++
  [.mov Flat.RA (.slot Flat.RB)]

open Flat in
/-- `copyIn` for a store inside a loop body. It uses only `RP` and slots 10 and 11, which no loop
body keeps live across a store, and leaves `RA` pointing at the copy. -/
def copyInLoop (M : Nat) : List Stmt :=
  [.mov Flat.RP (.imm (UInt64.ofNat M)),
   .load .w64 11 (.slot Flat.RP) 0,
   .bin .add 11 (.slot 11) (.imm 64),
   .store .w64 (.slot Flat.RP) 0 (.slot 11),
   .bin .band 11 (.slot 11) (.imm 0x3FC0),
   .bin .add Flat.RP (.slot Flat.RP) (.imm 8),
   .bin .add Flat.RP (.slot Flat.RP) (.slot 11)] ++
  (List.range 8).flatMap (fun j =>
    [.load .w64 10 (.slot Flat.RA) (UInt64.ofNat (8 * j)),
     .store .w64 (.slot Flat.RP) (UInt64.ofNat (8 * j)) (.slot 10)]) ++
  [.mov Flat.RA (.slot Flat.RP)]

open Flat in
/-- The effect of a loop that updates a copy of its carried binder instead of the binder. Inside
the body of a source loop, which is a `while` nested in the reactor's loop, every store through
the address register `RA` goes to a fresh copy of the 64 bytes at that address. Later reads of
the binder see the stale original. -/
partial def loopCopyGo (M : Nat) (depth : Nat) : Stmt → Stmt
  | .seq a b => .seq (loopCopyGo M depth a) (loopCopyGo M depth b)
  | .ite c t e => .ite c (loopCopyGo M depth t) (loopCopyGo M depth e)
  | .while pre c b => .while (loopCopyGo M (depth + 1) pre) c (loopCopyGo M (depth + 1) b)
  | .call n fr b ret args dst => .call n fr (loopCopyGo M depth b) ret args dst
  | .store w (.slot a) off v =>
    -- depth 1 is the reactor's own loop, which every program runs inside, and not a source loop
    if 2 ≤ depth && a == Flat.RA then rebuild (copyInLoop M ++ [.store w (.slot a) off v])
    else .store w (.slot a) off v
  | s => s

open Flat in
/-- Which reference stores a copy mutant rewrites, as the pair of whether the store is in a call's
arguments and whether it is a slice. -/
def copyKind : Mutant → Option (Bool × Bool)
  | .copyBorrow => some (false, false)
  | .copyRef => some (true, false)
  | .copySliceBorrow => some (false, true)
  | .copySliceArg => some (true, true)
  | _ => none

open Flat in
/-- Rewrite the reference stores of the kind the mutant selects. The code is flattened so that a
store can see what follows it. -/
partial def copyGo (m : Mutant) (M : Nat) (s : Stmt) : Stmt :=
  rebuild (goList (flatten s))
where
  goLeaf : Stmt → Stmt
    | .ite c t e => .ite c (copyGo m M t) (copyGo m M e)
    | .while pre c b => .while (copyGo m M pre) c (copyGo m M b)
    | .call n fr b ret args dst => .call n fr (copyGo m M b) ret args dst
    | s => s
  goList : List Stmt → List Stmt
    | [] => []
    | s :: rest =>
      match s with
      | .store .w64 (.slot b) k (.slot x) =>
        if b == Flat.BP && x == Flat.RA &&
            copyKind m == some (reachesCall rest, hasLenStore k 6 rest) then
          copyIn M ++ s :: goList rest
        else s :: goList rest
      | _ => goLeaf s :: goList rest

/-- The harnesses that must fail under a copy mutant. Each reads the lender after the borrow or the
callee whose writes the mutant loses. -/
def aliasFor : Mutant → List String
  | .copyBorrow => ["alBElem", "alBField", "alBWhole", "alBNest", "pBorrowFields"]
  | .copyRef => ["alRElem", "alRStruct", "alRTwo", "alAThenRef", "sScalar", "rPassWhole", "sPassMut",
      "lPt", "pSwapArg", "pBumpArg", "pBorrowFields", "iStruct", "iFindRep", "iSubSlice", "iTwo",
      "iPairPass", "iPairRev", "iSlotLoop", "iRoot", "svSort", "svRev", "iViewCellArg"]
  | .copySliceBorrow => ["alSBorrow", "alSTwo", "sSub", "svRev"]
  | .copySliceArg => ["alAFill", "alAScalar", "alAThenRef", "sFill", "sRev", "sCopy", "rPassWhole",
      "sPassMut", "lFill", "lRev", "lPrefix", "lCopy", "lFind",
      "iLibFill", "iLibRev", "iLibCopy", "iBubble", "iRot", "iSubSlice", "iTwo", "svSort", "svRev"]
  -- `lNest` is not listed, because its carried scalars live in slots and `slot-carry` covers them
  | .copyLoopCarried => ["lFill", "lRev", "lPrefix", "lCopy", "lFind", "lPt", "iLibFill", "iLibRev",
      "iLibCopy", "iBubble", "iStruct", "iFindRep", "iRot", "iSubSlice", "iTwo", "iPairPass",
      "iPairRev", "iSlotLoop", "iRoot"]
  | .ptrPairAlias => ["pSwapArg", "pBumpArg", "pSumArg", "pBorrowFields", "pBorrowShr",
      "iPairPass", "iPairRev", "svSort", "svRev"]
  | .loopFillShort => ["bFill"]
  | .loopCopyShort => ["bCopy"]
  | _ => []

/-- The functions of `SlotFuncs.lean` and `LoopFuncs.lean` that exercise the feature a slot mutant
breaks, each of which must fail under it. -/
def slotFor : Mutant → List String
  | .slotReadOff => ["slMix", "slLoop", "slAssign", "slBr", "slNest", "slRead", "slFlag", "slCarry",
      "slCall", "slArm", "slArgs", "slStruct", "slRes", "slSpan", "slStrOk", "slStrErr3", "slFld",
      "slCase", "slMk", "lNest"]
  | .slotStale => ["slAssign", "slCarry", "slStruct", "lNest"]
  | .slotBranch => ["slMix", "slBr", "slFlag", "slRes", "slFld"]
  | .slotCntStep => ["slLoop", "slBr", "slNest", "slRead", "slFlag", "slCarry", "slCall", "lNest"]
  | .slotAccNext => ["slLoop", "slBr", "slNest", "slRead", "slFlag", "slCall"]
  | .slotReadNarrow => ["slRead", "slStruct", "slSpan"]
  | .slotCarry => ["slCarry", "lNest"]
  | .slotCallRes => ["slCall", "slArgs", "slStruct", "slSpan", "slRet"]
  | .slotArg => ["slArgs"]
  | .slotTag => ["slArm", "slRes", "slStrErr3", "slFld", "slCase", "slMk"]
  | .slotAsgOff => ["slAssign", "slCarry", "slStruct"]
  -- `slStrOk` and `slStrErr3` are not listed, because their values never reach memory
  | .slotChunkNarrow => ["slStruct", "slSpan", "slRet"]
  | .slotStraddle => ["slStrOk", "slStrErr3", "slMk"]
  | _ => []

/-- Whether a slot lies beyond the scratch frame, where variables that live in slots are kept. -/
def isVarSlot (x : Nat) : Bool := Flat.FR ≤ x

-- every slot mutant names the functions of its feature
#guard Mutant.all.all fun m => !(m.name.startsWith "slot-") || !(slotFor m).isEmpty

open Flat in
/-- `slot-stale` drops the write to a slot variable right after an assignment's tick. An
assignment to a variable in memory stores instead and is not affected. -/
partial def staleGo (s : Stmt) : Stmt :=
  rebuild (goList (flatten s))
where
  goLeaf : Stmt → Stmt
    | .ite c t e => .ite c (staleGo t) (staleGo e)
    | .while pre c b => .while (staleGo pre) c (staleGo b)
    | .call n fr b ret args dst => .call n fr (staleGo b) ret args dst
    | s => s
  goList : List Stmt → List Stmt
    | [] => []
    | .tick (.mem d w) :: s :: rest =>
      match s with
      | .mov x _ | .load _ x _ _ =>
        if isVarSlot x then .tick (.mem d w) :: goList rest else .tick (.mem d w) :: goList (s :: rest)
      | _ => .tick (.mem d w) :: goList (s :: rest)
    | s :: rest => goLeaf s :: goList rest

open Flat in
/-- `slot-branch` drops the writes to slots beyond the scratch frame in the `else` branch of every
`if`. -/
def branchGo : Stmt → Stmt
  | .seq a b => .seq (branchGo a) (branchGo b)
  | .ite c t e => .ite c (branchGo t) (mapFlat (fun
      | .mov x o => if isVarSlot x then .skip else .mov x o
      | .bin op x a b => if isVarSlot x then .skip else .bin op x a b
      | .load w x a off => if isVarSlot x then .skip else .load w x a off
      | s => s) e)
  | .while pre c b => .while (branchGo pre) c (branchGo b)
  | .call n fr b ret args dst => .call n fr (branchGo b) ret args dst
  | s => s

open Flat in
/-- Drop the writes to slots beyond the scratch frame. -/
def dropVarWrites : Stmt → Stmt
  | .seq a b => .seq (dropVarWrites a) (dropVarWrites b)
  | .mov x o => if isVarSlot x then .skip else .mov x o
  | .load w x a o => if isVarSlot x then .skip else .load w x a o
  | s => s

open Flat in
/-- `slot-acc-next` drops, in every loop body, the accumulator's update at the end of the
iteration, right before the counter's increment. The accumulator then keeps its initial value. -/
def accNextGo (depth : Nat) : Stmt → Stmt
  | .seq a b => .seq (accNextGo depth a) (accNextGo depth b)
  | .ite c t e => .ite c (accNextGo depth t) (accNextGo depth e)
  | .while pre c b =>
    -- depth 0 is the reactor's own loop, which every program runs inside, and not a source loop
    match depth, b with
    | _ + 1, .seq t (.seq b (.seq an cn)) =>
      .while (accNextGo (depth + 1) pre) c (.seq t (.seq (accNextGo (depth + 1) b)
        (.seq (dropVarWrites an) cn)))
    | _, b => .while (accNextGo (depth + 1) pre) c (accNextGo (depth + 1) b)
  | .call n fr b ret args dst => .call n fr (accNextGo depth b) ret args dst
  | s => s

open Flat in
/-- The frame slots beyond the scratch frame that a statement writes. Call bodies are excluded,
since they write other frames. -/
def varWrites : Stmt → List Nat
  | .seq a b => varWrites a ++ varWrites b
  | .ite _ t e => varWrites t ++ varWrites e
  | .while p _ b => varWrites p ++ varWrites b
  | .mov x _ | .bin _ x _ _ | .load _ x _ _ | .ext _ _ x _ => if isVarSlot x then [x] else []
  | _ => []

open Flat in
/-- Drop the writes to the slots `xs`, except a loop counter's increment. -/
def dropWrites (xs : List Nat) : Stmt → Stmt
  | .seq a b => .seq (dropWrites xs a) (dropWrites xs b)
  | .ite c t e => .ite c (dropWrites xs t) (dropWrites xs e)
  | .while p c b => .while (dropWrites xs p) c (dropWrites xs b)
  | .mov x o => if xs.contains x then .skip else .mov x o
  | .bin op x a b =>
    if xs.contains x && !(op == .add && a == .slot x && b == .imm 1) then .skip else .bin op x a b
  | .load w x a o => if xs.contains x then .skip else .load w x a o
  | s => s

open Flat in
/-- `slot-carry` drops, inside every loop body, the writes to the slots written before the loop,
which is the effect of a loop that updates a copy of its carried scalars. It also returns the
slots written so far. -/
def carryGo (written : List Nat) : Stmt → Stmt × List Nat
  | .seq a b =>
    let r₁ := carryGo written a
    let r₂ := carryGo r₁.2 b
    (.seq r₁.1 r₂.1, r₂.2)
  | .ite c t e =>
    let r₁ := carryGo written t
    let r₂ := carryGo written e
    (.ite c r₁.1 r₂.1, r₁.2 ++ r₂.2)
  | .while p c b =>
    (.while p c (dropWrites written (carryGo written b).1), written ++ varWrites p ++ varWrites b)
  | .call n fr b ret args d => (.call n fr (carryGo [] b).1 ret args d, written)
  | s => (s, written ++ varWrites s)

open Flat in
/-- `slot-call-res` sends a call's result to the wrong slot. A word returned into a slot variable
goes to the next slot, and a result loaded into such a slot from the callee's destination right
after the call is loaded one byte off. -/
partial def callResGo (s : Stmt) : Stmt :=
  rebuild (go (flatten s))
where
  call (n : String) (fr : Nat) (b : Stmt) (ret : List Operand) (args : List Operand) (d : Nat) :
      Stmt :=
    .call n fr (callResGo b) ret args (if !ret.isEmpty && isVarSlot d then d + 1 else d)
  go : List Stmt → List Stmt
    | [] => []
    | .call n fr b ret args d :: .load w x (.slot a) off :: rest =>
      if isVarSlot x && a == Flat.BP then
        call n fr b ret args d :: .load w x (.slot a) (off + 1) :: go rest
      else call n fr b ret args d :: go (.load w x (.slot a) off :: rest)
    | .call n fr b ret args d :: rest => call n fr b ret args d :: go rest
    | .ite c t e :: rest => .ite c (callResGo t) (callResGo e) :: go rest
    | .while p c b :: rest => .while (callResGo p) c (callResGo b) :: go rest
    | s :: rest => s :: go rest

open Flat in
/-- `slot-arg` passes a call's argument words beyond the scratch frame, which hold its word
parameters, in reverse order. -/
def argGo : Stmt → Stmt
  | .seq a b => .seq (argGo a) (argGo b)
  | .ite c t e => .ite c (argGo t) (argGo e)
  | .while p c b => .while (argGo p) c (argGo b)
  | .call n fr b ret args d => .call n fr (argGo b) ret (args.take Flat.FR ++ (args.drop Flat.FR).reverse) d
  | s => s

open Flat in
/-- `slot-asg-off` sends an assignment's first write to a slot variable, right after its tick, to
the next slot. -/
partial def asgOffGo (s : Stmt) : Stmt :=
  rebuild (goList (flatten s))
where
  goLeaf : Stmt → Stmt
    | .ite c t e => .ite c (asgOffGo t) (asgOffGo e)
    | .while pre c b => .while (asgOffGo pre) c (asgOffGo b)
    | .call n fr b ret args dst => .call n fr (asgOffGo b) ret args dst
    | s => s
  goList : List Stmt → List Stmt
    | [] => []
    | .tick (.mem d w) :: s :: rest =>
      match s with
      | .mov x o => .tick (.mem d w) :: (if isVarSlot x then .mov (x + 1) o else .mov x o) :: goList rest
      | _ => .tick (.mem d w) :: goList (s :: rest)
    | s :: rest => goLeaf s :: goList rest

open Flat in
/-- `slot-straddle` breaks a copy between slot variables whose source straddles the destination from
below. Such a copy is staged through the scratch slots from `REXT` on, and the mutant reads the
sources from the variable's slots directly instead, so the forward copy overwrites the source's
later words before reading them. `stg` maps each scratch slot just written by a `mov` of the
staging to the variable's slot it came from. -/
partial def straddleGo (s : Stmt) : Stmt :=
  rebuild (goList [] (flatten s))
where
  goLeaf : Stmt → Stmt
    | .ite c t e => .ite c (straddleGo t) (straddleGo e)
    | .while pre c b => .while (straddleGo pre) c (straddleGo b)
    | .call n fr b ret args dst => .call n fr (straddleGo b) ret args dst
    | s => s
  goList (stg : List (Nat × Nat)) : List Stmt → List Stmt
    | [] => []
    | .mov y (.slot r) :: rest =>
      if Flat.REXT ≤ y && y < Flat.FR && isVarSlot r then
        .mov y (.slot r) :: goList ((y, r) :: stg) rest
      else
        match stg.lookup r with
        | some k => if isVarSlot y then .mov y (.slot k) :: goList stg rest
            else .mov y (.slot r) :: goList stg rest
        | none => .mov y (.slot r) :: goList stg rest
    | .skip :: rest => .skip :: goList stg rest
    | s :: rest => goLeaf s :: goList [] rest

/-- A word loop of a large constructor (`Flat.wordLoop`) that runs one iteration less: a fill's
when `fill` holds, a copy's otherwise. -/
def loopShortGo (fill : Bool) : Flat.Stmt → Flat.Stmt
  | .seq a b => .seq (loopShortGo fill a) (loopShortGo fill b)
  | .ite c t e => .ite c (loopShortGo fill t) (loopShortGo fill e)
  | .call n fr b ret args dst => .call n fr (loopShortGo fill b) ret args dst
  | .while (.bin .ult x (.slot r) (.imm v)) (.slot x') b =>
    let isFill := match b with
      | .seq (.tick (.words _)) (.seq _ (.seq (.store _ _ _ (.imm _)) _)) => some true
      | .seq (.tick (.words _)) (.seq _ (.seq (.seq (.load _ _ _ _) _) _)) => some false
      | _ => none
    if isFill = some fill ∧ x = Flat.RX ∧ r = Flat.RA ∧ 8 ≤ v then
      .while (.bin .ult x (.slot r) (.imm (v - 8))) (.slot x') b
    else .while (.bin .ult x (.slot r) (.imm v)) (.slot x') (loopShortGo fill b)
  | .while p c b => .while (loopShortGo fill p) c (loopShortGo fill b)
  | s => s

/-- The mutation of the Flat program. -/
def Mutant.flat (m : Mutant) (M : Nat) (s : Flat.Stmt) : Flat.Stmt :=
  match m with
  | .flatEq => mapFlat (fun
      | .bin .eq x a b => .bin .ne x a b
      | s => s) s
  | .flatStoreOff => mapFlat (fun
      | .store .w8 a off b => .store .w8 a (off + 1) b
      | s => s) s
  | .flatLoadWide => mapFlat (fun
      | .load .w8 x a off => .load .w64 x a off
      | s => s) s
  -- `trunc8` keeps 7 bits instead of 8, its mask `0xFF` made `0x7F`
  | .flatTrunc8 => mapFlat (fun
      | .bin .band x a (.imm k) => .bin .band x a (.imm (if k = 0xFF then 0x7F else k))
      | s => s) s
  -- `zext8` sets bit 8, its move `x ||| 0` made `x ||| 0x100`
  | .flatZext8 => mapFlat (fun
      | .bin .bor x a (.imm k) => .bin .bor x a (.imm (if k = 0 then 0x100 else k))
      | s => s) s
  -- a field offset added wrongly to a place's address, in a reference's target or anywhere else
  | .ptrFieldOff => mapFlat (fun
      | .bin .add x (.slot a) (.imm k) =>
        if x = Flat.RA ∧ a = Flat.RA then .bin .add x (.slot a) (.imm (k + 8)) else .bin .add x (.slot a) (.imm k)
      | s => s) s
  -- a dereference reads the reference's address from the wrong word of its slot
  | .ptrDerefLoad => mapFlat (fun
      | .load .w64 x (.slot a) off =>
        if x = Flat.RA ∧ a = Flat.BP then .load .w64 x (.slot a) (off + 8) else .load .w64 x (.slot a) off
      | s => s) s
  -- bytes read / written through an address register one byte off
  | .ptrReadOff => mapFlat (fun
      | .load w x (.slot a) off =>
        if a = Flat.RA ∨ a = Flat.RB then .load w x (.slot a) (off + 1) else .load w x (.slot a) off
      | s => s) s
  | .ptrWriteOff => mapFlat (fun
      | .store w (.slot a) off b =>
        if a = Flat.RA ∨ a = Flat.RB then .store w (.slot a) (off + 1) b else .store w (.slot a) off b
      | s => s) s
  -- a borrow binder records the stale address in the second address register
  | .ptrStoreAddr => mapFlat (fun
      | .store .w64 (.slot a) off (.slot b) =>
        if a = Flat.BP ∧ b = Flat.RA then .store .w64 (.slot a) off (.slot Flat.RB)
        else .store .w64 (.slot a) off (.slot b)
      | s => s) s
  | .copyBorrow | .copyRef | .copySliceBorrow | .copySliceArg => copyGo m M s
  | .copyLoopCarried => loopCopyGo M 0 s
  | .loopFillShort => loopShortGo true s
  | .loopCopyShort => loopShortGo false s
  -- a slot-resident variable is read from the next slot
  | .slotReadOff => mapFlat (fun
      | .mov x (.slot k) => if isVarSlot k then .mov x (.slot (k + 1)) else .mov x (.slot k)
      | .store w a off (.slot k) =>
        if isVarSlot k then .store w a off (.slot (k + 1)) else .store w a off (.slot k)
      | s => s) s
  | .slotStale => staleGo s
  | .slotBranch => branchGo s
  -- a slot-resident loop counter steps by two
  | .slotCntStep => mapFlat (fun
      | .bin .add x (.slot y) (.imm 1) =>
        if isVarSlot x && x == y then .bin .add x (.slot y) (.imm 2) else .bin .add x (.slot y) (.imm 1)
      | s => s) s
  | .slotAccNext => accNextGo 0 s
  | .slotCarry => (carryGo [] s).1
  | .slotCallRes => callResGo s
  -- the word parameters' words in the callee's frame in the wrong order
  | .slotArg => argGo s
  -- a `match` or `case` on a slot-resident sum reads its tag from the payload's word
  | .slotTag => mapFlat (fun
      | .bin .band x (.slot k) (.imm 0xFF) =>
        if isVarSlot k then .bin .band x (.slot (k + 1)) (.imm 0xFF) else .bin .band x (.slot k) (.imm 0xFF)
      | s => s) s
  | .slotAsgOff => asgOffGo s
  | .slotStraddle => straddleGo s
  -- a slot value's whole-word chunks are stored to memory as one byte each
  | .slotChunkNarrow => mapFlat (fun
      | .store .w64 a off (.slot k) =>
        if isVarSlot k then .store .w8 a off (.slot k) else .store .w64 a off (.slot k)
      | s => s) s
  -- a place read straight into a slot reads one byte
  | .slotReadNarrow => mapFlat (fun
      | .load w x (.slot a) off =>
        if isVarSlot x && a == Flat.RA then .load .w8 x (.slot a) off else .load w x (.slot a) off
      | s => s) s
  -- the second address of a pair reference is stored as the first, so the pair's elements alias
  | .ptrPairAlias => mapFlat (fun
      | .store .w64 (.slot a) off (.slot b) =>
        if a = Flat.BP ∧ b = Flat.RB then .store .w64 (.slot a) off (.slot Flat.RA)
        else .store .w64 (.slot a) off (.slot b)
      | s => s) s
  | _ => s

/-- The mutation of the Lin program. -/
def Mutant.lin (m : Mutant) (P : Lin.Prog) : Lin.Prog :=
  match m with
  | .linUlt => mapLin (fun
      | .bin .ult x a b => .bin .ule x a b
      | i => i) P
  | .linStoreWidth => mapLin (fun
      | .store .w8 a off b => .store .w64 a off b
      | .store .w64 a off b => .store .w8 a off b
      | i => i) P
  | _ => P

/-- The mutation of the Asm program. -/
def Mutant.asm (m : Mutant) (A : Asm.Prog X64.arch) : Asm.Prog X64.arch :=
  match m with
  | .selSetb => mapAsm (fun
      | .setcc .b d => .setcc .be d
      | i => i) A
  | .selMovzx => mapAsm (fun
      | .load8 d mem => .load d mem
      | i => i) A
  | .selStore8 => mapAsm (fun
      | .store8 mem s => .store mem s
      | .store mem s => .store8 mem s
      | i => i) A
  | .selShl => mapAsm (fun
      | .shiftCL .shl d => .shiftCL .shr d
      | i => i) A
  | .selSub => mapAsm (fun
      | .aluRR .sub d s => .aluRR .add d s
      | i => i) A
  | _ => A

/-- The image that the x64 backend produces, with the mutant's bug seeded between the passes. The
checks of `image` and the budget check are left out, so that the mutant reaches the machine. -/
def imageMut (m : Mutant) (p : Program) (o : Compile.Options := {}) : Except String Image := do
  let fp ← Flat.lower p
  let fp := { fp with main := m.flat p.memBytes fp.main }
  let P := Lin.linearize fp (p.memBytes + scratchBytes)
  let P := Compile.x64Prep o (m.lin P)
  let A ← X64.selectFb (Compile.x64K o) (Compile.x64C o) P o.memBase
  let A := m.asm A
  let obj ← X64.assemble A
  Link.link (Compile.linkConfig P) [obj]

/-- `compile` with a seeded bug. -/
def compileMut (m : Mutant) (p : Program) (o : Compile.Options := {}) : Except String ByteArray := do
  let img ← imageMut m p o
  let bs ← x64Linux.fmt.write img
  pure ⟨bs.toArray⟩

end Millipede.Tests.Differential
