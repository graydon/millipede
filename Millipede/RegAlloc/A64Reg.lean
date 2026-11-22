import Millipede.Target.A64.Select
import Millipede.RegAlloc.Live
import Millipede.Target.PMove

/-!
# arm64 instruction selection with register locations

The selector `selector k c` places the register locations of an allocated Lin program in machine
registers: locations `0 … k-1` in the preserved registers `x19 … x(18+k)` (`k ≤ 10`), locations
`k … k+c-1` in the caller-saved registers `x4 … x7, x10 … x14, x8, x0, x1, x2, x3` (`c ≤ 14`,
`loc`), and every other location in its frame word, so `k = c = 0` selects with slot locations
only. Nothing else touches `x19` to `x28`, because the scratch registers are `x9` and `x15` to
`x17` and Linux preserves the rest. A caller-saved register may also have a fixed role at some
instructions: a call destroys every caller-saved register, and an extern call destroys `x8`, into
which it loads the system-call number, and `x0 … x2`, its arguments and result. The selector
refuses a program in which a location live after an instruction is in a register the instruction
destroys and does not define (`Live.clobOk` of the clobber set `(cls k c).across`). With
caller-saved locations a function returns at most four words, in `x0 … x3`. The registers that
`ret` loads, that the caller reads the results from and that a `write` or `read` of a buffer
loads are each set by one parallel move (`Sel.PMove.seq` through `x16` or `x17`), so an operand
may sit in any of them and a result may stay in the register it arrives in.

The frame word of a preserved location is free, so it serves as the save area of its register.
Before `bl g`, where `g` has a frame of `G` words, the caller stores each register `x(19+j)` with
`j < min k G` that `Live.callKeep` names into word `j` of `g`'s frame. It then writes the memory
arguments while its registers still hold its own values, then the preserved register arguments,
reading an argument whose register it has already overwritten back from its save word, and then
the caller-saved register arguments: those in caller-saved registers by a parallel move through
`x9` (`cSeq`, `Sel.PMove.seq`), the others after it. Of `g`'s locations it writes only those live
at `g`'s entry. The `ret` of `g` moves the returned words into `x0, …` (`retLd`), reloads the
saved registers from its own frame and returns, so every activation sees its preserved registers as Lin sees its
slots and frames do not grow.

With the option `mb` (`Options.memBase`), every function's entry sequence ends with
`adrp x29, mp_mem; add x29, x29, :lo12:mp_mem`, and nothing else writes `x29`, so it holds the
data region's address throughout (`conv`'s `regOk`). A `load` or `store` of `a + off` is then
`ldr d, [x29, a]` when `off = 0` and `a` is in a register, and otherwise
`add x16, a, #off; ldr d, [x29, x16]` (`memIx`, `memX`, `memAd`); without `mb` it computes the
full address into `x16` (`memAddrR`).

Each other block has the shape of `A64.selInstr`, except that an operand in a register location
is used in place, a result whose location is a register is computed into it, an addition or
subtraction of an immediate below 4096 is `add`/`sub` with that immediate, a move of a
location to itself is empty, and a zero is stored from `xzr`. The selector refuses `k > 10`,
`c > 14` and a one-byte `read` into a register location, whose buffer would be its frame word. On
a refusal `compile` allocates again without caller-saved locations (`Compile.prep`) and selects
at the first of `(k, c)`, `(k, 0)` and slot locations that the selector accepts, through
`selectFb` and `kcUsed`.

The convention is described in doc/design/targets.md.
-/

namespace Millipede.RegAlloc.A64Reg

open Flat (Operand BinOp ExtArg)
open Sel (fnSym dataSym memSym)
export Sel (isC cArgs cArgs_length cArgs_val cArgs_below cArgs_slot pad_drop pad_take slot_of_pad)
open A64

/-- The register of location `x < k`. -/
def preg (x : Nat) : Reg := BitVec.ofNat 5 (19 + x)

/-- The register of caller-saved location `k + i`, for `i < 14`: `x4 … x7`, then `x10 … x14`,
then `x8`, the register of the system-call number, then `x0 … x3`, the registers of the results
and of the system-call arguments, in order, so that consecutive locations can hold consecutive
results in place. -/
def creg (i : Nat) : Reg :=
  BitVec.ofNat 5 (if i < 4 then 4 + i else if i < 9 then 6 + i else if i < 10 then 8 else i - 10)

/-- The register of location `x < k + c`: `x(19+x)` below `k`, a caller-saved register above. -/
def loc (k x : Nat) : Reg := if x < k then preg x else creg (x - k)

/-- `mov d, s` (`orr d, xzr, s`). -/
def mv (d s : Reg) : Instr := .logReg .orr true d 31 s

/-- Load an operand into register `r`, where slot `y` is the frame word `y - c`. -/
def ldIsC (c : Nat) (r : Reg) : Operand → List Instr
  | .slot y => ldIs r (.slot (y - c))
  | o => ldIs r o

/-- An operand in some register: in place for a register location, else loaded into `r`. -/
def src (k c : Nat) (r : Reg) : Operand → List Instr × Reg
  | .slot y => if y < k + c then ([], loc k y) else (ldIsC c r (.slot y), r)
  | o => (ldIsC c r o, r)

/-- An operand into register `r`. -/
def ldTo (k c : Nat) (r : Reg) : Operand → List Instr
  | .slot y =>
    if y < k + c then (if loc k y == r then [] else [mv r (loc k y)]) else ldIsC c r (.slot y)
  | o => ldIsC c r o

/-- Store register `r` into location `x`. -/
def stTo (k c : Nat) (x : Nat) (r : Reg) : List Instr :=
  if x < k + c then (if loc k x == r then [] else [mv (loc k x) r]) else stIs (x - c) r

/-- The register in which a result for location `x` is computed, which is `t` when `x` is a slot. -/
def dreg (k c : Nat) (x : Nat) (t : Reg) : Reg := if x < k + c then loc k x else t

/-- After computing into `dreg k c x t`: nothing, or the store of `t` into slot `x`. -/
def fin (k c : Nat) (x : Nat) (t : Reg) : List Instr := if x < k + c then [] else stIs (x - c) t

/-- `cset d, c` after `cmp n, m`. -/
def cmpSetR (c : Cond) (d n m : Reg) : List Instr :=
  [.addReg true true true 31 n m, .csel .csinc true d 31 31 c.invert]

/-- A binary operation `d := n op m`. -/
def binR (d n m : Reg) : BinOp → List Instr
  | .add => [addR d n m]
  | .sub => [.addReg true true false d n m]
  | .mul => [.madd true false d n m 31]
  | .band => [.logReg .and true d n m]
  | .bor => [.logReg .orr true d n m]
  | .bxor => [.logReg .eor true d n m]
  | .shl => [.shiftV .lsl true d n m]
  | .shr => [.shiftV .lsr true d n m]
  | .udiv => [.div true false d n m]
  | .umod => [.div true false 9 n m, .madd true true d 9 m n]
  | .eq => cmpSetR .eq d n m
  | .ne => cmpSetR .ne d n m
  | .ult => cmpSetR .cc d n m
  | .ule => cmpSetR .ls d n m

/-- `d := n + w` or `d := n - w` by `add`/`sub` of an immediate, for `w < 4096`. -/
def binImm (op : BinOp) (d n : Reg) (w : UInt64) : Option (List Instr) :=
  if w.toNat < 4096 then
    match op with
    | .add => some [.addImm true false false d n (BitVec.ofNat 12 w.toNat) false]
    | .sub => some [.addImm true true false d n (BitVec.ofNat 12 w.toNat) false]
    | _ => none
  else none

/-- `d := n op o`, by `binImm` when it applies, and otherwise with `o` in some register. -/
def binOps (k c : Nat) (op : BinOp) (d n : Reg) : Operand → List Instr
  | .imm w => (binImm op d n w).getD ((src k c 17 (.imm w)).1 ++ binR d n (src k c 17 (.imm w)).2 op)
  | o => (src k c 17 o).1 ++ binR d n (src k c 17 o).2 op

/-- The store of a zero to `ad`, from `xzr`. -/
def stImm (w : Flat.Width) (ad : Addr) (v : UInt64) : Option (List Instr) :=
  if v = 0 then some [.str (size w) 31 ad] else none

/-- The store of `b` to `ad`, a zero from `xzr`. -/
def storeOps (k c : Nat) (w : Flat.Width) (ad : Addr) : Operand → List Instr
  | .imm v => (stImm w ad v).getD ((src k c 17 (.imm v)).1 ++ [.str (size w) (src k c 17 (.imm v)).2 ad])
  | b => (src k c 17 b).1 ++ [.str (size w) (src k c 17 b).2 ad]

/-- The index of a data access of `a + off` with the data region's address in `x29`: the code and
the register that holds `a + off`, which is `a`'s own register when `off = 0`, and otherwise
`x16 := a + off`. -/
def memIx (k c : Nat) (a : Operand) (off : UInt64) : List Instr × Reg :=
  if off = 0 then src k c 16 a
  else ((src k c 16 a).1 ++ binOps k c .add 16 (src k c 16 a).2 (.imm off), 16)

/-- The address of a `load` or `store` of `a + off` after `memX`. -/
def memAd (k c : Nat) (mb : Bool) (a : Operand) (off : UInt64) : Addr :=
  if mb then .reg 29 (memIx k c a off).2 else .uimm 16 0

/-- The data address `mp_mem + a + off` into `x16`. -/
def memAddrR (k c : Nat) (a : Operand) (off : UInt64) : List SI :=
  let (ca, ra) := src k c 16 a
  ops (ca ++ binOps k c .add 16 ra (.imm off)) ++ symAddr 17 memSym ++ [.op (addR 16 16 17)]

/-- The address code of a `load` or `store` of `a + off`: with the option `mb`, the index
(`memIx`), and the access is `[x29, index]`; otherwise `memAddrR`, and the access is `[x16]`. -/
def memX (k c : Nat) (mb : Bool) (a : Operand) (off : UInt64) : List SI :=
  if mb then ops (memIx k c a off).1 else memAddrR k c a off

/-- An operand for a store, which is `xzr` for a zero and otherwise `src` into `x16`. -/
def srcZ (k c : Nat) : Operand → List Instr × Reg
  | .imm 0 => ([], 31)
  | o => src k c 16 o

/-- Store operand `o` into location `j` of the callee frame at `x17`, a slot and so word
`j - c`, a zero from `xzr`. -/
def argMem (k c : Nat) (j : Nat) (o : Operand) : List Instr :=
  (srcZ k c o).1 ++ farPre 15 17 (j - c) ++ [.str .x (srcZ k c o).2 (farA 15 17 (j - c))]

/-- Load operand `o` into the register of location `j`. The preserved registers of the locations
below `n` are already overwritten, so an operand in one of them is read back from its save word
in the callee frame at `x17`. -/
def argReg (k c : Nat) (n j : Nat) (o : Operand) : List Instr :=
  match o with
  | .slot y =>
    if y < k then
      if y < n then [.ldr .x (loc k j) (.uimm 17 (BitVec.ofNat 12 y))]
      else if y = j then [] else [mv (loc k j) (preg y)]
    else if y < k + c then [mv (loc k j) (loc k y)]
    else ldIsC c (loc k j) (.slot y)
  | .imm w => immIs (loc k j) w

/-- The memory arguments `j, j+1, …`, each only when `ent` names its word. -/
def argMems (k c : Nat) (ent : Nat → Bool) : Nat → List Operand → List Instr
  | _, [] => []
  | j, o :: os => (if ent j then argMem k c j o else []) ++ argMems k c ent (j + 1) os

/-- The preserved register arguments `j, j+1, …`, each only when `ent` names its location. -/
def argRegs (k c : Nat) (ent : Nat → Bool) : Nat → List Operand → List Instr
  | _, [] => []
  | j, o :: os => (if ent j then argReg k c j j o else []) ++ argRegs k c ent (j + 1) os

/-- The other caller-saved register arguments `j, j+1, …` that `ent` names, after the preserved
registers below `n` are overwritten. -/
def cLoads (k c n : Nat) (ent : Nat → Bool) : Nat → List Operand → List Instr
  | _, [] => []
  | j, o :: os => (if ent j && !isC k c o then argReg k c n j o else []) ++ cLoads k c n ent (j + 1) os

/-- The parallel move of the caller-saved register arguments in caller-saved registers. -/
abbrev cMoves (k c G : Nat) (args : List Operand) (ent : Nat → Bool) : List (Reg × Reg) :=
  Sel.cMoves (loc k) 31 k c ent k (cArgs k c G args)

/-- The sequential moves of the caller-saved register arguments, through `x9`. -/
def cSeq (k c G : Nat) (args : List Operand) (ent : Nat → Bool) : Option (List (Reg × Reg)) :=
  Sel.PMove.seq 9 (2 * c + 1) (cMoves k c G args ent)

/-- A place a parallel move reads or writes: a register, or an operand in no register. -/
abbrev Place := Sel.Place Reg

/-- The place of operand `o`: its register for a register location. -/
abbrev place (k c : Nat) : Operand → Place := Sel.place (loc k) (k + c)

/-- The code of one move into a register: a copy, or a load of a slot or an immediate. -/
def emit (k c : Nat) : Place × Place → List Instr
  | (.inl d, .inl r) => [mv d r]
  | (.inl d, .inr o) => ldTo k c d o
  | (.inr _, _) => []

/-- The code of one move after a call: a copy into a register, or the store of a register into
slot `x`, word `x - c`, which is word `x - c - bs` above the base `b`. -/
def emitW (c : Nat) (b : Reg) (bs : Nat) : Place × Place → List Instr
  | (.inl d, .inl r) => [mv d r]
  | (.inr (.slot x), .inl r) => [.str .x r (.uimm b (BitVec.ofNat 12 (x - c - bs)))]
  | _ => []

/-- The moves of `ret`: operand `i` into `x_i`. -/
abbrev retMoves (k c : Nat) (os : List Operand) : List (Place × Place) :=
  Sel.retMoves (fun i => BitVec.ofNat 5 i) (place k c) 0 os

/-- The moves after a call: `x_i` into location `d + i`, for `i < n`. -/
abbrev resMoves (k c d n : Nat) : List (Place × Place) :=
  Sel.resMoves (fun i => BitVec.ofNat 5 i) (place k c) d 0 n

/-- The fuel of the result moves, which bounds their number: `n` moves and one more for each
cycle, of which there are at most `n / 2`. -/
def resFuel (n : Nat) : Nat := n + n / 2

/-- The caller's moves of the returned words `x0, …` into the locations `d, …`, sequentialised
through `x16`. In a program with a frame of more than 4,096 slots the slot words are addressed
through `x15 := sp + 4096 ⌊(d - c) / 512⌋`. -/
def retR (k c : Nat) (P : Lin.Prog) (d n : Nat) : Option (List Instr) :=
  (Sel.PMove.seq (.inl 16) (resFuel n) (resMoves k c d n)).map fun l =>
    if farProg P then
      .addImm true false false 15 31 (BitVec.ofNat 12 ((d - c) / 512)) true ::
        l.flatMap (emitW c 15 (512 * ((d - c) / 512)))
    else l.flatMap (emitW c 31 0)

/-- The moves of the returned operands into `x0, x1, …`, sequentialised through `x16`. -/
def retLd (k c : Nat) (os : List Operand) : Option (List Instr) :=
  (Sel.PMove.seq (.inl 16) (2 * os.length + 1) (retMoves k c os)).map (·.flatMap (emit k c))

/-- The moves of a `write` or `read` of a buffer: the address from `x16` into `x1`, the
descriptor `a` into `x0`, the length `l` into `x2` and the number into `x8`. -/
abbrev memMoves (k c : Nat) (nr : UInt64) (a l : Operand) : List (Place × Place) :=
  [(.inl 1, .inl 16), (.inl 0, place k c a), (.inl 2, place k c l), (.inl 8, .inr (.imm nr))]

/-- The rest of a `write` or `read` of a buffer at the address in `x16`: the moves of `memMoves`
through `x17`, `svc` and the store of the result into location `x`. -/
def memTail (k c : Nat) (nr : UInt64) (x : Nat) (a l : Operand) : Option (List Instr) :=
  (Sel.PMove.seq (.inl 17) 9 (memMoves k c nr a l)).map fun ms =>
    ms.flatMap (emit k c) ++ [.svc 0] ++ stTo k c x 0

/-- Load the `n` registers `x_r, …` from the words `o, o+1, …` above the base `b`. -/
def ldWords (b : Reg) (o : Nat) : Nat → Nat → List Instr
  | _, 0 => []
  | r, n + 1 => .ldr .x (BitVec.ofNat 5 r) (.uimm b (BitVec.ofNat 12 o)) :: ldWords b (o + 1) (r + 1) n

/-- The saves of the location registers `x, x+1, …` (`n` of them) that `keep` names, each into
word `x` of the callee frame at `x17`. -/
def saves (keep : Nat → Bool) : Nat → Nat → List Instr
  | _, 0 => []
  | x, n + 1 => (if keep x then [.str .x (preg x) (.uimm 17 (BitVec.ofNat 12 x))] else []) ++
      saves keep (x + 1) n

/-- The call sequence before `bl`: the callee frame's address into `x17` (its `frameW k c G`
words), the saves of the
registers `x19, …` (`x < min k G`) that `keep` names, the memory arguments, the preserved
register arguments, and the caller-saved register arguments, by the parallel move of those in
caller-saved registers and then the others. Of the callee's locations it writes only those that
`ent` names. -/
def callOps (k c G : Nat) (args : List Operand) (keep ent : Nat → Bool) : List Instr :=
  frameI true 17 31 (Sel.frameW k c G) :: saves keep 0 (min k G) ++
    argMems k c ent (min (k + c) G) ((padArgs G args).drop (min (k + c) G)) ++
    argRegs k c ent 0 ((padArgs G args).take (min k G)) ++
    ((cSeq k c G args ent).getD []).map (fun p => mv p.1 p.2) ++
    cLoads k c (min k G) ent k (cArgs k c G args)

/-- The call sequence up to and including `bl g`. -/
def callIs (k c : Nat) (g G : Nat) (args : List Operand) (keep ent : Nat → Bool) : List SI :=
  ops (callOps k c G args keep ent) ++ [.fix .branch26 (.b true 0) (.sym (fnSym g))]

/-- The block of one Lin instruction, with the data it adds to the image. -/
def selInstr (k c : Nat) (mb : Bool) (lvo : Option LiveSets) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn) :
    Lin.Instr → Except String (List SI × List (String × List UInt8))
  | .mov x a =>
    if x < k + c then .ok (ops (ldTo k c (loc k x) a), [])
    else if a = .slot x then .ok ([], [])
    else let (r, q) := src k c 16 a; .ok (ops (r ++ stIs (x - c) q), [])
  | .bin op x a b =>
    let (ca, ra) := src k c 16 a
    .ok (ops (ca ++ binOps k c op (dreg k c x 16) ra b ++ fin k c x 16), [])
  | .load w x a off =>
    .ok (memX k c mb a off ++ ops (.ldr (size w) (dreg k c x 16) (memAd k c mb a off) :: fin k c x 16), [])
  | .store w a off b => .ok (memX k c mb a off ++ ops (storeOps k c w (memAd k c mb a off) b), [])
  | .jmp l => .ok ([.fix .branch26 (.b false 0) (.label l)], [])
  | .jz o l =>
    let (cc, rc) := src k c 16 o
    .ok (ops cc ++ [.fix .cond19 (.cbz true false rc 0) (.label l)], [])
  | .call g args d =>
    match P.funs[g]? with
    | none => .error "select: call to a missing function"
    | some gf =>
      if args.length ≤ gf.frame then
        match (cSeq k c gf.frame args (Live.liveIn lvo g 0)).isSome, retR k c P d gf.ret.length with
        | true, some rr =>
          .ok (callIs k c g gf.frame args (Live.callKeep lvo P i pc g d args) (Live.liveIn lvo g 0) ++
            ops rr, [])
        | _, _ => .error "select: no sequence for a parallel move of the arguments or results"
      else .error "select: more arguments than the callee's frame"
  | .ret =>
    match retLd k c fn.ret with
    | none => .error "select: no sequence for the parallel move of the returned words"
    | some rl =>
      .ok (ops (rl ++ ldWords 31 0 19 (min k fn.frame) ++
        ldIs 30 (.slot (Sel.frameW k c fn.frame)) ++ [frameI false 31 31 (Sel.frameW k c fn.frame),
        .ret 30]), [])
  | .ext sym nr x args =>
    match sym, nr, args with
    | "exit", true, [.word a] => .ok (ops (ldTo k c 0 a ++ immIs 8 93 ++ [.svc 0] ++ stTo k c x 0), [])
    | "write", false, [.word a, .bytes bs] =>
      if bs.length < 2 ^ 32 then
        .ok (ops (ldTo k c 0 a) ++ symAddr 1 (dataSym i pc) ++
          ops (immIs 2 (UInt64.ofNat bs.length) ++ immIs 8 64 ++ [.svc 0] ++ stTo k c x 0),
          [(dataSym i pc, bs)])
      else .error "select: constant buffer too large"
    | "write", false, [.word a, .mem p l] =>
      match memTail k c 64 x a l with
      | some tl => .ok (memAddrR k c p 0 ++ ops tl, [])
      | none => .error "select: no sequence for the parallel move of the arguments"
    | "read", false, [.word a, .out 1] =>
      if x < k + c then .error "select: read into a register location"
      else .ok (ops (ldTo k c 0 a ++ stIs (x - c) 31 ++ slotAddr 1 (x - c) ++ immIs 2 1 ++
        immIs 8 63 ++ [.svc 0] ++ ldIs 16 (.slot (x - c)) ++
        [.addImm true true true 31 0 1 false, .csel .csinv true 16 16 31 .eq] ++ stIs (x - c) 16),
        [])
    | "read", false, [.word a, .outMem p l] =>
      match memTail k c 63 x a l with
      | some tl => .ok (memAddrR k c p 0 ++ ops tl, [])
      | none => .error "select: no sequence for the parallel move of the arguments"
    | _, _, _ => .error ("select: unsupported extern " ++ sym)
  | .tick _ => .ok ([], [])

/-- The arm64 selector with `k` preserved and `c` caller-saved register locations and the live
sets `lvo`. With caller-saved locations a function returns at most four words, in `x0 … x3`,
which are no location's registers. -/
def selector (k c : Nat) (mb : Bool) (lvo : Option LiveSets) : Sel.Selector arch where
  instr := selInstr k c mb lvo
  entry fn := ops (entryIs (Sel.frameW k c fn.frame)) ++ (if mb then symAddr 29 memSym else [])
  fnOk fn := A64.fnOk fn && k ≤ 10 && c ≤ 14 && (c == 0 || fn.ret.length ≤ 4)

/-- The register classes of arm64 for the allocator. A call destroys every caller-saved
register, and an extern call destroys `x8` (caller-saved register 9), into which it loads the
system-call number, and `x0 … x2` (registers 10, 11, 12), its arguments and result. Linux system
calls preserve the other registers. The `i`-th result and the `i`-th system-call argument are in
`x_i`, caller-saved register `10 + i`, which the allocator tries first for such a value. -/
def cls (k c : Nat) : Alloc.Classes :=
  { k, c, kill := fun
      | .call .. => (List.range c, [])
      | .ext .. => ([9, 10, 11, 12].filter (· < c), [])
      | _ => ([], [])
    resReg := fun i => if i < 4 then some (10 + i) else none
    argReg := fun i => if i < 3 then some (10 + i) else none }

/-- Selection with `k` preserved and `c` caller-saved register locations. With caller-saved
locations it refuses a program in which a location live after a call is a caller-saved one that
the call does not define (`Live.clobOk`). -/
def select (k c : Nat) (P : Lin.Prog) (mb : Bool := true) : Except String (Asm.Prog arch) :=
  if c = 0 ∨ Live.clobOk (cls k c).across (Live.of P) P = true then
    Sel.select (selector k c mb (Live.of P)) P
  else .error "select: a caller-saved location is live across a call"

/-! ## Instruction counts -/

/-- The machine instructions of one Lin step, which the budget check counts. A call runs through
`bl` and the callee's entry, a `ret` includes the caller's result stores, and `exit` stops at its
`svc`. -/
def instrs (k c : Nat) (mb : Bool) (lvo : Option LiveSets) (P : Lin.Prog) (i pc : Nat) (fn : Lin.Fn)
    (ins : Lin.Instr) : Nat :=
  match ins with
  | .call g args d =>
    (callIs k c g (Sel.calleeFrame P g) args (Live.callKeep lvo P i pc g d args)
      (Live.liveIn lvo g 0)).length +
      entryLen (Sel.frameW k c (Sel.calleeFrame P g)) + (if mb then 2 else 0)
  | .ret => (match selInstr k c mb none P 0 0 fn .ret with | .ok (b, _) => b.length | .error _ => 0) +
      resFuel fn.ret.length + (if farProg P then 1 else 0)
  | .ext "exit" true _ [.word a] => (ldTo k c 0 a).length + 2
  | .ext "write" false x [.word a, .bytes bs] => (ldTo k c 0 a).length + 2 +
      (immIs 2 (UInt64.ofNat bs.length) ++ immIs 8 64 ++ [Instr.svc 0] ++ stTo k c x 0).length
  | .ext "read" false x [.word a, .out 1] => (ldTo k c 0 a ++ (stIs (x - c) 31 ++
      slotAddr 1 (x - c) ++ immIs 2 1 ++ immIs 8 63) ++ [Instr.svc 0] ++ (ldIs 16 (.slot (x - c)) ++
      [Instr.addImm true true true 31 0 1 false, Instr.csel .csinv true 16 16 31 .eq]) ++ stTo k c x 16).length
  | ins => match selInstr k c mb none P 0 0 fn ins with | .ok (b, _) => b.length | .error _ => 0

/-- The counts at the live sets `lvo`, which the caller computes once as `Live.of P`. -/
def counts (k c : Nat) (mb : Bool) (lvo : Option LiveSets) : Sel.Counts :=
  ⟨fun P => instrs k c mb lvo P,
    fun P => entryLen (Sel.frameW k c (Sel.calleeFrame P P.main)) + (if mb then 2 else 0)⟩

/-! ## The backend's selection -/

/-- The number of register locations `compile` uses on arm64 by default. -/
def kDefault : Nat := 6

/-- The number of caller-saved register locations `compile` uses on arm64 by default, all 14:
`x4 … x7, x10 … x14`, `x8` and `x0 … x3`. -/
def cDefault : Nat := 14

/-- The numbers of preserved and caller-saved register locations used for `P`: `(k, c)`, or
`(k, 0)` when the selector refuses that, or `(0, 0)` when it refuses both. With caller-saved
locations the selector refuses a program in which one is live across an instruction that destroys
it, which happens when allocation fell back to the unallocated program; `compile` then allocates
again without caller-saved locations (`Compile.prep`), and `(k, 0)` refuses only a one-byte `read`
into a register location, which happens likewise. -/
def kcUsed (k c : Nat) (P : Lin.Prog) (mb : Bool := true) : Nat × Nat :=
  match select k c P mb with
  | .ok _ => (k, c)
  | .error _ => match select k 0 P mb with
    | .ok _ => (k, 0)
    | .error _ => (0, 0)

/-- The arm64 selection of `compile`, which is `select` at `kcUsed k c P`. -/
def selectFb (k c : Nat) (P : Lin.Prog) (mb : Bool := true) : Except String (Asm.Prog arch) :=
  select (kcUsed k c P mb).1 (kcUsed k c P mb).2 P mb

/-- The budget check at the counts of `kcUsed k c P` and the cost model `A64.κ`. -/
def budgetOk (k c : Nat) (P : Lin.Prog) (mb : Bool := true) : Bool :=
  let C := counts (kcUsed k c P mb).1 (kcUsed k c P mb).2 mb (Live.of P)
  Sel.budgetOk C A64.κ P (Sel.potential C A64.κ P).get

theorem kcUsed_le (k c : Nat) (P : Lin.Prog) (mb : Bool) :
    (kcUsed k c P mb).1 ≤ k ∧ (kcUsed k c P mb).2 ≤ c := by
  unfold kcUsed; split
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · split <;> exact ⟨by omega, by omega⟩

theorem kcUsed_of_ok {k c : Nat} {P : Lin.Prog} {mb : Bool} (h : (select k c P mb).isOk = true) :
    kcUsed k c P mb = (k, c) := by
  unfold kcUsed; split
  · rfl
  · rename_i e he; rw [he] at h; cases h

end Millipede.RegAlloc.A64Reg
