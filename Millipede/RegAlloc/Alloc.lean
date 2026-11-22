import Millipede.RegAlloc.Check

/-!
# The register allocator

The allocator is ordinary Lean code with no proof. Whatever it proposes is validated by the
proved checker `check`, and `allocOrId` keeps the unallocated program when the check fails, so a
bug in the allocator can cost performance but never correctness.

The allocator handles one function at a time in index order, because a call site needs the
entry map of its callee. For each function it takes the following steps:

1. It computes the live slots of each position by backward iteration to a fixed point. A call
   uses only the argument positions that are live at the callee's entry.
2. It joins the live points `(pc, y)` and the definitions `(pc, x)` along control flow into webs
   with union-find. Every web gets one location for its whole life, so no move is ever inserted
   and code positions do not change.
3. Two webs interfere when they are live at the same point, or when one is defined at a position
   that the other is carried across. The source of a move is exempt, so that it may share the
   location of the move's destination.
4. It colours the webs greedily by weight, counting uses and definitions eight times over for
   each enclosing loop up to three, and prefers the colour of a move's other end. Locations
   `0 … k-1` are the preserved register locations and `k … k+c-1` the caller-saved ones, which
   the selector places in machine registers, so `k = c = 0` only compacts the slots. A web live
   across an instruction that destroys a caller-saved register (a call destroys them all) does
   not get that register; a web live across none tries the caller-saved registers first. The results of a call get consecutive locations, and the
   destination of a one-byte `read`, whose buffer is its slot, never gets a register location.
5. It rewrites every instruction through the maps, and a call passes its arguments in the
   positions of the callee's entry map.

A function whose result groups cannot be coloured, or whose colouring needs more frame words
(`Sel.frameW`: a caller-saved location has none) than its frame has locations, is coloured again
without caller-saved registers, and if that fails too it keeps its slots unchanged.
-/

namespace Millipede.RegAlloc.Alloc

open Flat (Operand ExtArg)
open Lin (Instr Prog)

def opSlots : Operand → List Nat
  | .slot y => [y]
  | .imm _ => []

def extSlots : ExtArg → List Nat
  | .word a => opSlots a
  | .mem a n => opSlots a ++ opSlots n
  | .outMem a c => opSlots a ++ opSlots c
  | _ => []

/-- The union of two strictly increasing lists, with their total length as fuel. -/
def merge : Nat → List Nat → List Nat → List Nat
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a, [] => a
  | f + 1, x :: a, y :: b =>
    if x < y then x :: merge f a (y :: b)
    else if y < x then y :: merge f (x :: a) b
    else x :: merge f a b

/-- The union of two sets of slots, each a strictly increasing list. -/
def uni (a b : List Nat) : List Nat := merge (a.length + b.length) a b

/-- The merge of two lists sorted by `le`, taking from the first on ties, with their total length
as fuel. -/
def mergeBy {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a, [] => a
  | f + 1, x :: a, y :: b =>
    if le x y then x :: mergeBy le f a (y :: b) else y :: mergeBy le f (x :: a) b

/-- A stable merge sort by `le`, structurally recursive on the fuel `n` (the length suffices), so
the kernel reduces it. -/
def sortBy {α : Type} (le : α → α → Bool) : Nat → List α → List α
  | 0, l => l
  | n + 1, l =>
    if l.length ≤ 1 then l
    else mergeBy le l.length (sortBy le n (l.take (l.length / 2))) (sortBy le n (l.drop (l.length / 2)))

/-- The set of a list. -/
def toSet (l : List Nat) : List Nat := l.foldl (fun acc x => uni [x] acc) []

/-- The uses, definitions and successors of the instruction at `pc`, where `entry g` gives the
slots live at the entry of function `g`. -/
def info (P : Prog) (fn : Lin.Fn) (entry : Nat → List Nat) (pc : Nat) :
    Instr → List Nat × List Nat × List Nat
  | .mov x a => (opSlots a, [x], [pc + 1])
  | .bin _ x a b => (opSlots a ++ opSlots b, [x], [pc + 1])
  | .load _ x a _ => (opSlots a, [x], [pc + 1])
  | .store _ a _ b => (opSlots a ++ opSlots b, [], [pc + 1])
  | .jmp l => ([], [], [l])
  | .jz c l => (opSlots c, [], [pc + 1, l])
  | .call g args d => ((entry g).flatMap (fun y => opSlots (args.getD y (.imm 0))),
      (List.range (retLen P g)).map (d + ·), [pc + 1])
  | .ret => (fn.ret.flatMap opSlots, [], [])
  | .ext _ _ x args => (args.flatMap extSlots, [x], [pc + 1])
  | .tick _ => ([], [], [pc + 1])

/-- The live-in slots of every position, by backward iteration in which the sets only grow. -/
def liveness (infos : Array (List Nat × List Nat × List Nat)) : Array (List Nat) := Id.run do
  let n := infos.size
  let mut live : Array (List Nat) := Array.replicate n []
  let mut changed := true
  for _ in [0:10000] do
    if !changed then break
    changed := false
    for idx in [0:n] do
      let pc := n - 1 - idx
      let (u, d, ss) := infos[pc]!
      let out := ss.foldl (fun acc s => uni (live.getD s []) acc) []
      let inn := uni (toSet u) (out.filter fun y => !d.contains y)
      if inn.length != (live[pc]!).length then
        live := live.set! pc inn
        changed := true
  return live

/-- The root of `x` in the union-find forest `par`. -/
def find (par : Array Nat) (x : Nat) : Nat := Id.run do
  let mut y := x
  for _ in [0:par.size] do
    let p := par.getD y y
    if p == y then break
    y := p
  return y

def link (par : Array Nat) (a b : Nat) : Array Nat :=
  let ra := find par a
  let rb := find par b
  if ra == rb then par else par.set! ra rb

def lookup (M : List (Nat × Nat)) (y : Nat) : Option Nat := (M.find? (·.1 == y)).map (·.2)

def ren (M : List (Nat × Nat)) : Operand → Operand
  | .slot y => .slot ((lookup M y).getD y)
  | .imm w => .imm w

def renExt (M : List (Nat × Nat)) : ExtArg → ExtArg
  | .word a => .word (ren M a)
  | .mem a n => .mem (ren M a) (ren M n)
  | .outMem a c => .outMem (ren M a) (ren M c)
  | a => a

/-- Whether `ins` is a one-byte `read` whose buffer is its destination slot. -/
def isReadOut : Instr → Bool
  | .ext "read" false _ [.word _, .out 1] => true
  | _ => false

/-- The result of allocating one function. -/
structure FnRes where
  fn : Lin.Fn
  maps : List LocMap
  /-- The number of webs in register locations, kept with `inSlots` for statistics only. -/
  inRegs : Nat
  inSlots : Nat
  fallback : Bool

/-- Rewrite function `fn` given its maps and the location `defLoc pc x` of each definition, where
`entryMaps g` is the entry map of function `g`. -/
def rewrite (P : Prog) (fn : Lin.Fn) (frame : Nat) (maps : Array LocMap)
    (defLoc : Nat → Nat → Nat) (entryMaps : Nat → LocMap) (retPc : Nat) : Lin.Fn :=
  let M := fun pc => maps.getD pc []
  let code := (fn.code.zipIdx).map fun (i, pc) => match i with
    | .mov x a => .mov (defLoc pc x) (ren (M pc) a)
    | .bin op x a b => .bin op (defLoc pc x) (ren (M pc) a) (ren (M pc) b)
    | .load w x a off => .load w (defLoc pc x) (ren (M pc) a) off
    | .store w a off b => .store w (ren (M pc) a) off (ren (M pc) b)
    | .jz c l => .jz (ren (M pc) c) l
    | .call g args d =>
      let E := entryMaps g
      let len := E.foldl (fun m p => max m (p.2 + 1)) 0
      let args' := (List.range len).map fun l =>
        match E.find? (·.2 == l) with
        | some (y, _) => ren (M pc) (args.getD y (.imm 0))
        | none => .imm 0
      .call g args' (if retLen P g = 0 then 0 else defLoc pc d)
    | .ext sym nr x args => .ext sym nr (defLoc pc x) (args.map (renExt (M pc)))
    | i => i
  { fn with frame := frame, code := code, ret := fn.ret.map (ren (M retPc)) }

/-- The register classes the allocator colours with. Locations `0 … k-1` are preserved registers,
which keep their value across everything; locations `k … k+c-1` are caller-saved registers; the
rest are frame slots. `kill ins` lists, by their index `0 … c-1`, the caller-saved registers that
`ins` destroys for a value live across it, and those a value live into it may not take; the
selectors' classes leave the second list empty, and the clobber mutants of the differential tests
use it to steer values into particular registers. By default a web live
across no instruction that destroys a caller-saved register tries the caller-saved registers
first and every other web the preserved ones first; `callerFirst := some b` puts the
caller-saved registers first for every web (`b`) or for none (`!b`). Before either, a web tries
the register its value is next used or defined in: the `i`-th returned word of `ret` or of a
call (`resReg i`) or the `i`-th argument of an extern call (`argReg i`), so that no move is needed
there. -/
structure Classes where
  k : Nat
  c : Nat := 0
  kill : Instr → List Nat × List Nat := fun _ => ([], [])
  callerFirst : Option Bool := none
  /-- The caller-saved register, by index, that holds the `i`-th returned word, if any. -/
  resReg : Nat → Option Nat := fun _ => none
  /-- The caller-saved register, by index, that holds the `i`-th system-call argument, if any. -/
  argReg : Nat → Option Nat := fun _ => none

/-- The locations instruction `ins` destroys for a value live across it, which is the clobber set
the selectors declare and `Live.clobOk` checks. -/
def Classes.across (cl : Classes) (ins : Instr) (x : Nat) : Bool :=
  decide (cl.k ≤ x) && decide (x < cl.k + cl.c) && (cl.kill ins).1.contains (x - cl.k)

/-- Allocate one function with the register classes `cl`, and with no caller-saved register when
`noC`. -/
def allocFn (P : Prog) (cl : Classes) (noC : Bool) (fn : Lin.Fn) (entryLive : Nat → List Nat)
    (entryMaps : Nat → LocMap) : FnRes := Id.run do
  let k := cl.k
  let K := cl.k + cl.c
  let code := fn.code.toArray
  let n := code.size
  let infos := (Array.range n).map fun pc => info P fn entryLive pc code[pc]!
  let live := liveness infos
  -- The identity allocation, which is always valid, keeps every slot in itself.
  let idMaps := live.map fun l => l.map fun y => (y, y)
  let retPcs := (List.range n).filter fun pc => match code[pc]! with | .ret => true | _ => false
  let identity : FnRes :=
    ⟨rewrite P fn fn.frame idMaps (fun _ x => x) entryMaps (retPcs.headD 0), idMaps.toList, 0, 0, true⟩
  -- Number the nodes, live points first and then definitions.
  let mut nodeOf : Array (List (Nat × Nat)) := Array.replicate n []
  let mut defOf : Array (List (Nat × Nat)) := Array.replicate n []
  let mut cnt := 0
  for pc in [0:n] do
    let mut l := []
    for y in live[pc]! do
      l := (y, cnt) :: l
      cnt := cnt + 1
    nodeOf := nodeOf.set! pc l
    let mut dl := []
    for x in (infos[pc]!).2.1 do
      dl := (x, cnt) :: dl
      cnt := cnt + 1
    defOf := defOf.set! pc dl
  let node := fun (pc y : Nat) => lookup (nodeOf.getD pc []) y
  let dnode := fun (pc x : Nat) => lookup (defOf.getD pc []) x
  let mut par : Array Nat := Array.range cnt
  -- Join nodes along control flow.
  for pc in [0:n] do
    let (_, ds, ss) := infos[pc]!
    for s in ss do
      for y in live.getD s [] do
        match node s y, (if ds.contains y then dnode pc y else node pc y) with
        | some a, some b => par := link par a b
        | _, _ => pure ()
  -- Every `ret` reads its words from the same locations.
  match retPcs with
  | r :: rs =>
    for r' in rs do
      for o in fn.ret do
        for y in opSlots o do
          match node r y, node r' y with
          | some a, some b => par := link par a b
          | _, _ => pure ()
  | [] => pure ()
  let roots : Array Nat := (Array.range cnt).map (find par)
  let root := fun x => roots.getD x x
  -- Interference and weights.
  let mut adj : Array (List Nat) := Array.replicate cnt []
  let mut weight : Array Nat := Array.replicate cnt 0
  let mut noReg : Array Bool := Array.replicate cnt false
  let mut pref : Array (List Nat) := Array.replicate cnt []
  -- The registers a web's value is next used or defined in, by location.
  let mut hint : Array (List Nat) := Array.replicate cnt []
  let hintOf := fun (q : Option Nat) => match q with
    | some i => if i < cl.c then [k + i] else []
    | none => []
  -- The caller-saved registers a web may not take, and whether it is live across a destroying
  -- instruction.
  let mut forbid : Array (List Nat) := Array.replicate cnt []
  let mut crosses : Array Bool := Array.replicate cnt false
  -- The loop depth of a position counts the back edges `l ≤ pc` around it.
  let mut depth : Array Nat := Array.replicate n 0
  for pc in [0:n] do
    let l? := match code[pc]! with | .jmp l => some l | .jz _ l => some l | _ => none
    if let some l := l? then
      if l ≤ pc then
        for q in [l:pc + 1] do depth := depth.set! q (depth[q]! + 1)
  for pc in [0:n] do
    let w := 8 ^ (min (depth[pc]!) 3)
    let (us, ds, ss) := infos[pc]!
    let here := (nodeOf.getD pc []).map fun p => root p.2
    let (cross, inn) := cl.kill code[pc]!
    for a in here do
      if !inn.isEmpty then forbid := forbid.set! a (inn ++ forbid[a]!)
      for b in here do
        if a != b then adj := adj.modify a (uni [b] ·)
    if !cross.isEmpty then
      for s in ss do
        for y in live.getD s [] do
          if !ds.contains y then
            if let some b := node s y then
              forbid := forbid.set! (root b) (cross ++ forbid[root b]!)
              crosses := crosses.set! (root b) true
    for y in us do
      if let some a := node pc y then weight := weight.set! (root a) (weight[root a]! + w)
    let uses : List (Nat × Option Nat) := match code[pc]! with
      | .ret => fn.ret.zipIdx.filterMap fun (o, i) => match o with
        | .slot y => some (y, cl.resReg i)
        | _ => none
      | .ext _ _ _ args => (args.zipIdx.map fun (a, i) => match a with
        | .word (.slot y) => [(y, cl.argReg i)]
        | .mem _ (.slot y) => [(y, cl.argReg (i + 1))]
        | .outMem _ (.slot y) => [(y, cl.argReg (i + 1))]
        | _ => []).flatten
      | _ => []
    for (y, q) in uses do
      if let some a := node pc y then
        hint := hint.set! (root a) (hint[root a]! ++ hintOf q)
    let coal : Option (Nat × Nat) := match code[pc]! with
      | .mov x (.slot a) => some (x, a)
      | _ => none
    for x in ds do
      if let some dn := dnode pc x then
        let r := root dn
        if let .call _ _ d := code[pc]! then
          if d ≤ x then hint := hint.set! r (hint[r]! ++ hintOf (cl.resReg (x - d)))
        weight := weight.set! r (weight[r]! + w)
        if isReadOut code[pc]! then noReg := noReg.set! r true
        for s in ss do
          for y in live.getD s [] do
            if !ds.contains y && coal != some (x, y) then
              if let some b := node s y then
                let rb := root b
                if rb != r then
                  adj := adj.modify r (uni [rb] ·)
                  adj := adj.modify rb (uni [r] ·)
        if let some (_, a) := coal then
          if let some b := node pc a then
            pref := pref.set! r (root b :: pref[r]!)
            pref := pref.set! (root b) (r :: pref[root b]!)
  -- The results of each call form a group of consecutive locations.
  let mut groups : List (List Nat) := []
  for pc in [0:n] do
    match code[pc]! with
    | .call g _ d =>
      let m := retLen P g
      if m ≥ 2 then
        groups := ((List.range m).filterMap fun j => (dnode pc (d + j)).map root) :: groups
    | _ => pure ()
  -- Colouring.
  let allowed (r c : Nat) : Bool :=
    if c < k then !noReg[r]!
    else if c < K then !noC && !noReg[r]! && !(forbid[r]!).contains (c - k)
    else true
  let rootList := ((List.range cnt).filter fun x => root x == x)
  let order := sortBy (fun a b => weight[a]! ≥ weight[b]!) rootList.length rootList
  let mut col : Array (Option Nat) := Array.replicate cnt none
  let mut ok := true
  let forbidden (col : Array (Option Nat)) (r : Nat) : List Nat :=
    (adj[r]!).foldl (fun acc b => match col[b]! with | some c => uni [c] acc | none => acc) []
  for grp in groups do
    if grp.any fun r => (col[r]!).isSome then ok := false
    else
      let fits := fun (c : Nat) => (grp.zipIdx).all fun (r, j) =>
        !(forbidden col r).contains (c + j) && allowed r (c + j)
      -- The start that puts some result in its result register, if it fits.
      let starts := (grp.zipIdx).flatMap fun (r, j) => (hint[r]!).filterMap fun h =>
        if j ≤ h then some (h - j) else none
      let mut c := 0
      let mut found := false
      if let some h := starts.find? fits then
        c := h
        found := true
      for _ in [0:fn.frame + 1] do
        if !found then
          if fits c then found := true else c := c + 1
      if found then
        for (r, j) in grp.zipIdx do col := col.set! r (some (c + j))
      else ok := false
  for r in order do
    if (col[r]!).isNone then
      let fb := forbidden col r
      let prefs := (pref[r]!).filterMap fun b => col[root b]!
      let regs := if cl.callerFirst.getD !crosses[r]! then (List.range cl.c).map (k + ·) ++ List.range k
        else List.range k ++ (List.range cl.c).map (k + ·)
      match (hint[r]! ++ prefs ++ regs).find? fun c => allowed r c && !fb.contains c with
      | some c => col := col.set! r (some c)
      | none =>
        let mut c := K
        for _ in [0:fb.length + 1] do
          if fb.contains c then c := c + 1
        col := col.set! r (some c)
  if !ok then return identity
  let colOf := fun x => (col[root x]!).getD 0
  let maps : Array LocMap := (Array.range n).map fun pc =>
    (nodeOf.getD pc []).reverse.map fun (y, nd) => (y, colOf nd)
  let defLoc := fun pc x => match dnode pc x with | some d => colOf d | none => 0
  let used := (List.range cnt).foldl (fun m x => max m (colOf x + 1)) 0
  -- A call writes its results at `d', …` even when they are dead, so the frame covers them.
  let frame := (List.range n).foldl (fun m pc => match code[pc]! with
    | .call g _ d => if retLen P g = 0 then m else max m (defLoc pc d + retLen P g)
    | _ => m) used
  if Sel.frameW k cl.c frame > fn.frame then return identity
  let fn' := rewrite P fn frame maps defLoc entryMaps (retPcs.headD 0)
  let rs := rootList.map colOf
  return ⟨fn', maps.toList, (rs.filter (· < K)).length, (rs.filter (· ≥ K)).length, false⟩

/-- Allocate a program with the register classes `cl` in every function. The result is the target
program, the maps for the checker and the statistics of each function. -/
def allocate (cl : Classes) (P : Prog) : Prog × List (List LocMap) × List FnRes := Id.run do
  let mut res : Array FnRes := #[]
  for fn in P.funs do
    let entryLive := fun g => ((res[g]?).map fun r => (r.maps.headD []).map (·.1)).getD []
    let entryMaps := fun g => ((res[g]?).map fun r => r.maps.headD []).getD []
    -- The hints put values in caller-saved registers, which can lengthen a frame that would
    -- otherwise hold only preserved locations by the save words of all of them: keep the
    -- allocation without hints when its frame is shorter.
    let rh := allocFn P cl false fn entryLive entryMaps
    let rn := allocFn P { cl with resReg := fun _ => none, argReg := fun _ => none } false fn
      entryLive entryMaps
    let r := if cl.c != 0 && Sel.frameW cl.k cl.c rn.fn.frame < Sel.frameW cl.k cl.c rh.fn.frame
      then rn else rh
    -- A function that keeps its slots would have some of them in caller-saved registers, which
    -- the selector refuses when they are live across a call: try it without those first.
    res := res.push (if r.fallback && cl.c != 0 then allocFn P cl true fn entryLive entryMaps else r)
  let P' : Prog := { P with funs := res.toList.map (·.fn) }
  return (P', res.toList.map (·.maps), res.toList)

/-- The allocation pass, which returns the allocated program if the checker and the frame check
at `cl`'s register locations accept it and `P` itself otherwise. -/
def allocOrId (cl : Classes) (P : Prog) : Prog :=
  let (P', maps, _) := allocate cl P
  if check P P' maps && frameOk cl.k cl.c P P' then P' else P

end Millipede.RegAlloc.Alloc
