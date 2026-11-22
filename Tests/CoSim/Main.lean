import Millipede.Top.Compile
import Tests.Rand

/-!
# Co-simulation of the x64 model against qemu

`lake exe cosim` checks the x64 encoder and execution model against qemu-x86_64, which stands in
for hardware. It generates random short instruction sequences from the modelled subset, encodes
them with the project's own encoder and links them into a harness ELF. Every sequence stores
random words in the 8 scratch slots below `rsp`, loads random values into every register but
`rsp` and sets the flags by a `cmp`. It then runs the random body and may make up to two `read`
system calls on a fixed pseudo-random standard input. Last, it dumps the 15 registers, the flags
`o b e s` and the 8 scratch slots into a 216-byte buffer and writes the buffer to standard
output.

The body uses moves, byte and word loads and stores at `[rsp - d]`, at `[rsp + d]` inside a pair
of `lea` that lowers and restores `rsp`, and through another register set by `lea` from `rsp`, `lea`, the two-operand
arithmetic and logic instructions with registers and immediates, `imul`, `div` with a valid
quotient, shifts by `cl`, `setcc`, `movzx`, forward jumps, balanced `push` and `pop`, and
`call +0; pop`. It never touches `rsp` and never reads a flag whose value the architecture leaves
undefined. The generator tracks which flags `imul`, `div` and shifts leave undefined, and before
the dump it redefines all flags by a `cmp` when any is undefined.

The model side runs the intended instructions with `X64.exec` instead of the bytes, following
`rip` through a table from addresses to instructions until the dump is written. Its oracle answers
`read` as Linux does. Comparing the model's dump with what qemu does with the bytes tests the
encoder and the execution model at once, and the decoder is tied to the encoder by a proved law.
`cosim gen <dir> <seed> <chunks> <per-chunk> [bug]` writes `<dir>/cosim.<k>.elf` and the
expected output `<dir>/cosim.<k>.expect`, which `scripts/cosim.sh` compares with qemu's output.
`cosim show <seed> <chunk> <index> <per-chunk>` prints one sequence.

The `bug` argument seeds a bug, and `scripts/cosim.sh --selftest` requires each to be caught.
Bug 1 makes the encoder swap the two registers of `aluRR`, bug 2 encodes the condition `b` of
`setcc` as `ae`, bug 3 encodes `shl` as `shr`, and bug 4 clears the sign bit of `lea`
displacements. Bug 9 encodes a SIB byte with scale 2 instead of 1, bug 10 the immediate of `store8I` one too
large. Bug 5 drops the first byte of the model's standard input, which the `read` part
of the co-simulation must notice. Bugs 6, 7 and 8 are errors in the model's semantics (`execBug`):
a wrong carry after `sub` and `cmp`, a shift count masked to 7 bits, and a wrong `div` remainder.
The default `0` is the real encoder and model.

`cosim gen` also checks that every addressing form that the selector emits occurs in the
generated sequences (`selectorForms`), and fails when one is missing.
-/

namespace Millipede.Tests.CoSim

open Millipede Millipede.X64

/-! ## Random generation -/

/-- The generator monad, whose state is the SplitMix state. -/
abbrev G := StateM UInt64

def next : G UInt64 := modifyGet fun s => let (s', z) := splitmix s; (z, s')

/-- A number below `n`, which must be positive. -/
def below (n : Nat) : G Nat := do
  let w ← next
  pure (w.toNat % n)

/-- A random element. -/
def pick {α : Type} [Inhabited α] (xs : List α) : G α := do
  let i ← below xs.length
  pure (xs[i]!)

/-- Edge values for immediates and register contents. -/
def edgeWords : List UInt64 :=
  [0, 1, 2, 3, 7, 8, 63, 64, 255, 256, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x100000000,
   0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0x8000000000000001, 0xFFFFFFFFFFFFFFFE,
   0xFFFFFFFFFFFFFFFF]

/-- A random 64-bit word, which is an edge value plus or minus a small number, a random word, or a
word of random magnitude. -/
def word : G UInt64 := do
  let k ← below 5
  let a ← next
  match k with
  | 0 => do let e ← pick edgeWords; pure (e + (a % 3) - 1)
  | 1 => pure a
  | 2 => do let s ← below 64; pure (a >>> s.toUInt64)
  | 3 => do let e ← pick edgeWords; pure e
  | _ => do let s ← below 64; pure (a <<< s.toUInt64)

/-- A random 32-bit immediate, possibly negative. -/
def imm32 : G UInt32 := do
  let k ← below 4
  let a ← next
  match k with
  | 0 => pure 0
  | 1 => do let e ← pick [1, 2, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFFE, 255, 256, 0xFFFFFF00]; pure (UInt32.ofNat e)
  | _ => pure a.toUInt32

/-- The registers the generator may use, which are all but `rsp`. -/
def regs : List Reg := Reg.all.filter (· ≠ .rsp)

def reg : G Reg := pick regs

/-- The displacement of `[rsp - n]` for `n ∈ [8, 64]`, inside the initialised scratch slots. -/
def slotDisp : G UInt32 := do
  let n ← below 57
  pure (0 - UInt32.ofNat (n + 8))

/-- Which of the flags `cf`, `zf`, `sf` and `of` are tainted, because the architecture leaves their
value undefined. -/
structure Taint where
  cf : Bool := false
  zf : Bool := false
  sf : Bool := false
  of : Bool := false
deriving Repr

def Taint.union (a b : Taint) : Taint := ⟨a.cf || b.cf, a.zf || b.zf, a.sf || b.sf, a.of || b.of⟩

/-- Whether a condition may be read, which holds when none of the flags it depends on is tainted. -/
def Cond.ok (t : Taint) : Cond → Bool
  | .o | .no => !t.of
  | .b | .ae => !t.cf
  | .e | .ne => !t.zf
  | .be | .a => !t.cf && !t.zf
  | .s | .ns => !t.sf
  | .l | .ge => !t.sf && !t.of
  | .le | .g => !t.zf && !t.sf && !t.of

def Taint.any (t : Taint) : Bool := t.cf || t.zf || t.sf || t.of

/-- A random readable condition, or `none` when every condition reads a tainted flag. -/
def cond (t : Taint) : G (Option Cond) := do
  match Cond.all.filter (Cond.ok t) with
  | [] => pure none
  | cs => pure (some (← pick cs))

/-- Fix up `setcc` steps by replacing a condition that reads a tainted flag with a readable one. -/
def fixSetcc (t : Taint) : List Instr → List Instr
  | [.setcc c d] =>
    if Cond.ok t c then [.setcc c d]
    else match Cond.all.filter (Cond.ok t) with
      | c' :: _ => [.setcc c' d]
      | [] => [.movzx d d]
  | is => is

/-- One generator step, which returns its instructions and the taint after them. `simple` forbids
jumps. -/
partial def step (simple : Bool) (t : Taint) : G (List Instr × Taint) := do
  let k ← below (if simple then 20 else 26)
  match k with
  | 0 | 1 => do pure ([.movRR (← reg) (← reg)], t)
  | 2 => do pure ([.movRI (← reg) (← word)], t)
  | 3 => do
    if (← below 3) = 0 then pure ([.load8 (← reg) (.base .rsp (← slotDisp))], t)
    else pure ([.load (← reg) (.base .rsp (← slotDisp))], t)
  | 4 => do
    if (← below 3) = 0 then pure ([.store8 (.base .rsp (← slotDisp)) (← reg)], t)
    else pure ([.store (.base .rsp (← slotDisp)) (← reg)], t)
  | 5 =>
    if (← below 4) = 0 then do
      let d ← below 2001
      pure ([.lea (← reg) (.rip (UInt32.ofInt ((d : Int) - 1000)))], t)
    else do
      let b ← reg
      pure ([.lea (← reg) (.base b (← imm32))], t)
  | 6 | 7 | 8 | 9 | 10 => do
    pure ([.aluRR (← pick Alu.all) (← reg) (← reg)], {})
  | 11 | 12 | 13 => do
    pure ([.aluRI (← pick Alu.all) (← reg) (← imm32)], {})
  | 14 => do pure ([.imul (← reg) (← reg)], { cf := false, of := false, zf := true, sf := true })
  | 15 => do
    -- div with a valid quotient, since rdx := d % v < v
    let s ← pick (regs.filter fun r => r ≠ .rax && r ≠ .rdx)
    let v ← word
    let v := if v = 0 then 1 else v
    let d ← word
    let a ← word
    pure ([.movRI s v, .movRI .rdx (d % v), .movRI .rax a, .div s], ⟨true, true, true, true⟩)
  | 16 => do pure ([.shiftCL (← pick [Shift.shl, Shift.shr]) (← reg)], { t with of := true })
  | 17 => do pure ([.setcc ((← pick Cond.all)) (← reg)], t)   -- flags are read below
  | 18 => do pure ([.movzx (← reg) (← reg)], t)
  | 19 => do
    let a ← reg
    let b ← reg
    pure ([.push a, .pop b], t)
  | 20 => do
    -- jcc / jmp over a few simple steps
    let m ← below 3
    let mut body : List Instr := []
    let mut tb := t
    for _ in [0:m + 1] do
      let (is, t') ← step true tb
      body := body ++ fixSetcc tb is
      tb := t'
    let rel := UInt32.ofNat (body.flatMap encode).length
    let tAfter := t.union tb
    match ← cond t with
    | some c => do pure ((Instr.jcc c rel) :: body, tAfter)
    | none => pure (body, tb)
  | 21 => do
    let m ← below 3
    let mut body : List Instr := []
    let mut tb := t
    for _ in [0:m + 1] do
      let (is, t') ← step true tb
      body := body ++ fixSetcc tb is
      tb := t'
    let rel := UInt32.ofNat (body.flatMap encode).length
    pure ((Instr.jmp rel) :: body, t)  -- the body is skipped: taint unchanged
  | 22 => do pure ([.call 0, .pop (← reg)], t)
  | 23 => do
    -- an access `[b + e]` through a register `b` set by `lea b, [rsp - n - e]`, as the selector
    -- addresses the data region through `rax` or `r11` and a displacement; `b` holds a stack
    -- address, which differs under qemu, so it is overwritten afterwards
    let n ← below 57
    let e ← pick [0, 0, 8, 16, 0xFFFFFFF8, 4089, 0x7FFFFF00]
    let b ← reg
    let r ← pick (regs.filter (· ≠ b))
    let a := X64.Mem.base b e
    let acc ← pick [Instr.load r a, .load8 r a, .store a r, .store8 a r]
    pure ([.lea b (.base .rsp (0 - UInt32.ofNat (n + 8) - e)), acc, .movRI b 0], t)
  | 24 => do
    -- an access `[b + i + e]`, as the selector addresses the data region through `r11` (the
    -- region) and the address's register as the index; `b` is set to `rsp - n - 8 - x - e` and
    -- `i` to `x`, and both are overwritten afterwards
    let n ← below 57
    let e ← pick [0, 0, 8, 16, 0xFFFFFFF8, 4089, 0x7FFFFF00]
    let x ← below 192
    let b ← reg
    let i ← pick (regs.filter (· ≠ b))
    let r ← pick (regs.filter fun q => q ≠ b && q ≠ i)
    if h : i = .rsp then pure ([], t) else
    let a := X64.Mem.sib b ⟨i, h⟩ e
    let v ← imm32
    let acc ← pick [Instr.load r a, .load8 r a, .store a r, .store8 a r, .storeI a v,
      .store8I a v.toUInt8]
    pure ([.lea b (.base .rsp (0 - UInt32.ofNat (n + 8 + x) - e)), .movRI i (UInt64.ofNat x), acc,
      .movRI b 0, .movRI i 0], t)
  | _ => do
    -- an access `[rsp + d]` with `d ≥ 0`, as to the selector's frame slots, inside
    -- `lea rsp, [rsp - 64]` … `lea rsp, [rsp + 64]`, so that it reaches the scratch slots
    let d := UInt32.ofNat (← below 57)
    let r ← reg
    let a := X64.Mem.base .rsp d
    let acc ← pick [Instr.load r a, .load8 r a, .store a r, .store8 a r]
    pure ([.lea .rsp (.base .rsp (0 - 64)), acc, .lea .rsp (.base .rsp 64)], t)

/-- The body, which is `n` steps. -/
def body : Nat → Taint → G (List Instr × Taint)
  | 0, t => pure ([], t)
  | n + 1, t => do
    let (is, t') ← step false t
    let is := fixSetcc t is
    let (rest, t'') ← body n t'
    pure (is ++ rest, t'')

/-- The prelude, which sets the scratch slots, then the registers, then the flags. -/
def prelude : G (List Instr) := do
  let mut out : List Instr := []
  for k in [1:9] do
    out := out ++ [.movRI .rax (← word), .store (.base .rsp (0 - UInt32.ofNat (8 * k))) .rax]
  for r in regs do
    out := out ++ [.movRI r (← word)]
  out := out ++ [.aluRR .cmp (← reg) (← reg)]
  pure out

/-- The address of word `j` of the dump area, which starts at `[rsp - 1024]`. -/
def dumpMem (j : Nat) : X64.Mem := .base .rsp (0 - UInt32.ofNat (1024 - 8 * j))

/-- The number of words in the dump, for 15 registers, 4 flags and 8 slots. -/
def dumpWords : Nat := 27

/-- The dump and `write(1, buf, 216)`. When the taint `t` marks any flag, a `cmp` first redefines
all flags. -/
def dump (t : Taint) : G (List Instr) := do
  let fl ← (if t.any then do pure [Instr.aluRR .cmp (← reg) (← reg)] else pure [])
  let mut out : List Instr := fl
  let mut j := 0
  for r in regs do
    out := out ++ [.store (dumpMem j) r]
    j := j + 1
  for c in [Cond.o, Cond.b, Cond.e, Cond.s] do
    out := out ++ [.setcc c .rax, .movzx .rax .rax, .store (dumpMem j) .rax]
    j := j + 1
  for k in [1:9] do
    out := out ++ [.load .rax (.base .rsp (0 - UInt32.ofNat (8 * k))), .store (dumpMem j) .rax]
    j := j + 1
  out := out ++ [.movRI .rax 1, .movRI .rdi 1, .lea .rsi (.base .rsp (0 - 1024)),
    .movRI .rdx (UInt64.ofNat (8 * dumpWords)), .syscall]
  pure out

/-- Between zero and two `read` system calls at the end of a sequence, which are always executed.
Each is `read(fd, [rsp - n], cap)` with `fd ∈ {0, 3, 9999}` and `cap ∈ {0, 1, 2, 3}`. Afterwards
`rcx`, `r11` and `rsi` are zeroed. The hardware and the model clobber `rcx` and `r11` with the
return address and the flag image, but qemu-user leaves them alone, and `rsi` holds a stack
address that differs under qemu, so none of the three can be compared. A `cmp` first redefines
tainted flags. The result is the instructions and the taint after them. -/
def readBlock (t : Taint) : G (List Instr × Taint) := do
  let n ← below 3
  if n = 0 then pure ([], t)
  else
    let fl ← (if t.any then do pure [Instr.aluRR .cmp (← reg) (← reg)] else pure [])
    let mut out : List Instr := fl
    for _ in [0:n] do
      let fd ← pick [0, 0, 0, 0, 3, 9999]
      let cap ← pick [1, 1, 1, 2, 3, 0]
      let off ← below 53
      out := out ++ [.movRI .rax 0, .movRI .rdi fd, .lea .rsi (.base .rsp (0 - UInt32.ofNat (off + 8))),
        .movRI .rdx cap, .syscall, .movRI .rcx 0, .movRI .r11 0, .movRI .rsi 0]
    pure (out, {})

/-- One sequence, which is the prelude, a body of `len` steps, the reads and the dump. -/
def sequence (len : Nat) : G (List Instr) := do
  let p ← prelude
  let (b, t) ← body len {}
  let (r, t) ← readBlock t
  let d ← dump t
  pure (p ++ b ++ r ++ d)

/-- The sequences of a chunk, generated from the seed of the chunk. -/
def chunkSeqs (seed : UInt64) (k : Nat) (count : Nat) : List (List Instr) :=
  let init := (splitmix (seed + (UInt64.ofNat k) * 0x1234567)).2
  let g : G (List (List Instr)) := do
    let mut out := []
    for _ in [0:count] do
      let len ← below 24
      out := out ++ [← sequence (len + 4)]
    pure out
  (g.run init).1

/-! ## Addressing forms

The selector (Millipede/Target/X64/Select.lean, SelectCall.lean) addresses memory in these forms:
loads and stores of a word or a byte at `[rsp + d]` with `d` negative (the words below the stack
pointer, `belowMem`) or not (frame slots, `slotMem`), at `[rax]` and at `[r11 + i + d]` (`ldWR`,
`stWR` with `memM`, an index register `i`), and `lea` of `[rsp + d]` and of `[rip + d]` (a
symbol). Every one of them must occur in the generated sequences, with any base register in place
of `rax` or `r11`. -/

/-- The addressing forms of an instruction, named as in `selectorForms`. -/
def forms : Instr → List String
  | .load _ m => form "load" m
  | .load8 _ m => form "load8" m
  | .store m _ => form "store" m
  | .store8 m _ => form "store8" m
  | .storeI m _ => form "storeI" m
  | .store8I m _ => form "store8I" m
  | .lea _ m => form "lea" m
  | _ => []
where
  form (op : String) : X64.Mem → List String
    | .rip _ => [s!"{op} [rip+d]"]
    | .base .rsp d => [if d.toNat ≥ 2 ^ 31 then s!"{op} [rsp-d]" else s!"{op} [rsp+d]"]
    | .base _ d => [if d = 0 then s!"{op} [r]" else s!"{op} [r+d]"]
    | .sib _ _ d => [if d = 0 then s!"{op} [r+r]" else s!"{op} [r+r+d]"]

/-- The forms that the selector emits. -/
def selectorForms : List String :=
  ["load", "load8", "store", "store8"].flatMap (fun op =>
    [s!"{op} [rsp-d]", s!"{op} [rsp+d]", s!"{op} [r]", s!"{op} [r+r]", s!"{op} [r+r+d]"]) ++
    ["lea [rsp+d]", "lea [rip+d]", "storeI [r+r]", "storeI [r+r+d]", "store8I [r+r]",
      "store8I [r+r+d]"]

/-- The selector's forms that do not occur in the sequences. -/
def missingForms (seqs : List (List Instr)) : List String :=
  let seen := seqs.flatten.flatMap forms
  selectorForms.filter (!seen.contains ·)

/-! ## Harness ELF and model run -/

/-- The encoder the harness ELF is built with, which is the real one when `bug = 0` and otherwise
has the seeded bug. -/
def enc (bug : Nat) : Instr → List UInt8
  | .aluRR op d s => if bug = 1 then encode (.aluRR op s d) else encode (.aluRR op d s)
  | .setcc .b d => if bug = 2 then encode (.setcc .ae d) else encode (.setcc .b d)
  | .shiftCL .shl d => if bug = 3 then encode (.shiftCL .shr d) else encode (.shiftCL .shl d)
  | .lea d (.base b disp) =>
    if bug = 4 then encode (.lea d (.base b (disp &&& 0x7FFFFFFF))) else encode (.lea d (.base b disp))
  | i =>
    -- bug 9: a SIB byte with scale 2 instead of 1 (the SIB byte precedes the 32-bit displacement);
    -- bug 10: the immediate of a byte store one too large
    match i with
    | .store8I m v => if bug = 10 then encode (.store8I m (v + 1)) else encode i
    | .storeI m v => if bug = 9 then sibBug (encode i) 9 else encode i
    | _ => let bs := encode i
      if bug = 9 && hasSib i then bs.set (bs.length - 5) (bs[bs.length - 5]! ||| 0x40) else bs
where
  /-- The SIB byte of a `storeI`, which precedes the displacement and the immediate. -/
  sibBug (bs : List UInt8) (k : Nat) : List UInt8 :=
    if bs.length ≥ k then bs.set (bs.length - k) (bs[bs.length - k]! ||| 0x40) else bs
  hasSib : Instr → Bool
    | .load _ (.sib ..) | .load8 _ (.sib ..) | .store (.sib ..) _ | .store8 (.sib ..) _
    | .lea _ (.sib ..) => true
    | _ => false

/-- The program, which is all the sequences followed by `exit(0)`. -/
def program (seqs : List (List Instr)) : List Instr :=
  seqs.flatten ++ [.movRI .rax 60, .movRI .rdi 0, .syscall]

/-- The linked image of a program, built with encoder `bug`, whose entry `_start` is at offset 0. -/
def image (bug : Nat) (is : List Instr) : Except String Image :=
  let bytes := is.flatMap (enc bug)
  let obj : Obj := ⟨[⟨".text", .text, 16, bytes, 0⟩], [⟨"_start", 0, 0, true⟩], []⟩
  Link.link (Link.Config.x64Linux "_start" 8192) [obj]

/-- The addresses of the instructions of a sequence that starts at `a`, with the lengths of their
canonical encodings, which are what the model sees. -/
def layout : UInt64 → List Instr → List (UInt64 × Instr × Nat)
  | _, [] => []
  | a, i :: rest => (a, i, (encode i).length) :: layout (a + UInt64.ofNat (encode i).length) rest

/-- The byte offsets of the sequences, by the lengths of their canonical encodings. -/
def offsets : Nat → List (List Instr) → List Nat
  | _, [] => []
  | o, s :: rest => o :: offsets (o + (s.flatMap encode).length) rest

/-- The bytes on standard input in chunk `k`, a fixed pseudo-random file of `40 + (97 k mod 300)`
bytes. It is short enough that some reads meet the end of input. -/
def stdinBytes (seed : UInt64) (k : Nat) : List UInt8 :=
  let len := 40 + (97 * k) % 300
  let rec go : Nat → UInt64 → List UInt8
    | 0, _ => []
    | n + 1, st => let (st', z) := splitmix st; z.toUInt8 :: go n st'
  go len (seed + UInt64.ofNat k * 0x51ED27)

/-- What Linux does with `read(fd, buf, cap)` on a pipe or file holding `inp`, of which `base` bytes
have been consumed before. For `fd = 0` it returns the next `min cap remaining` bytes and their
count. For an unopened descriptor it returns `-EBADF` and writes nothing. The kernel uses only
the low 32 bits of `fd`, but the generator never produces a value where that matters. -/
def stdinOracle (inp : List UInt8) (base : Nat) : Oracle :=
  ⟨fun hist c =>
    if c.sym = "read" ∧ c.args = [0] then
      let used := base + (hist.filter fun e => e.sym = "read" ∧ e.args = [0]).foldl
        (fun a e => a + e.result.toNat) 0
      let cap := c.outCaps.headD 0
      let bs := (inp.drop used).take cap
      ⟨UInt64.ofNat bs.length, [bs]⟩
    else if c.sym = "read" then ⟨0xFFFFFFFFFFFFFFF7, []⟩
    else ⟨0, []⟩⟩

/-- The number of bytes of standard input that the `read` events of a world consumed. -/
def consumed (evs : List Event) : Nat :=
  (evs.filter fun e => e.sym = "read" ∧ e.args = [0]).foldl (fun a e => a + e.result.toNat) 0

/-- `X64.exec`, or with `bug` one of three seeded errors in the model's semantics. Bug 6 inverts
the carry flag after `sub` and `cmp`. Bug 7 masks the count of a shift by `cl` to 7 bits instead
of 6, so that a count with bit 6 set shifts out every bit. Bug 8 adds one to the remainder of
`div`. -/
def execBug (bug : Nat) (trap : X64.State → Option X64.State) (i : Instr) (n : Nat) (s : X64.State) :
    Option X64.State :=
  (X64.exec trap i n s).map fun s' =>
    match bug, i with
    | 6, .aluRR op _ _ | 6, .aluRI op _ _ =>
      if op = .sub || op = .cmp then
        { s' with regs := { s'.regs with flags := { s'.regs.flags with cf := !s'.regs.flags.cf } } }
      else s'
    | 7, .shiftCL _ d =>
      if s.regs.gpr .rcx &&& 0x40 != 0 then { s' with regs := s'.regs.set d 0 } else s'
    | 8, .div _ => { s' with regs := s'.regs.set .rdx (s'.regs.gpr .rdx + 1) }
    | _, _ => s'

/-- The model run of a sequence. It executes the instructions of a table from addresses to
instructions, from the sequence's first address until the `write` of the dump, and returns the
dumped bytes and the bytes of standard input consumed. -/
def runModel (bug : Nat) (inp : List UInt8) (base : Nat) (img : Image)
    (tbl : List (UInt64 × Instr × Nat)) (start : UInt64) : Option (List UInt8 × Nat) :=
  let s₀ := img.init X64.linux
  let ω := stdinOracle inp base
  let rec go : Nat → X64.State → Option (List UInt8 × Nat)
    | 0, _ => none
    | fuel + 1, s =>
      match s.world.events.getLast? with
      | some e =>
        if e.sym = "write" then e.bytesIn.head?.map fun d => (d, consumed s.world.events)
        else
          match tbl.find? (·.1 == s.regs.rip) with
          | none => none
          | some (_, i, n) =>
            match execBug bug (X64.linux.trap ω) i n s with
            | none => none
            | some s' => go fuel s'
      | none =>
        match tbl.find? (·.1 == s.regs.rip) with
        | none => none
        | some (_, i, n) =>
          match execBug bug (X64.linux.trap ω) i n s with
          | none => none
          | some s' => go fuel s'
  go 5000 { s₀ with regs := { s₀.regs with rip := start } }

/-- Generate chunk `k` by writing the ELF and the model's expected output. -/
def genChunk (dir : String) (seed : UInt64) (count bug k : Nat) : IO Bool := do
  let seqs := chunkSeqs seed k count
  let is := program seqs
  match image bug is with
  | .error e => IO.eprintln s!"cosim: link failed: {e}"; return false
  | .ok img =>
    match x64Linux.fmt.write img with
    | .error e => IO.eprintln s!"cosim: write failed: {e}"; return false
    | .ok file =>
      -- the model sees the canonical encodings at the image's entry address
      let mut expect : List UInt8 := []
      let mut i := 0
      -- seeded bug 5: the model's standard input lacks its first byte
      let inp := if bug = 5 then (stdinBytes seed k).drop 1 else stdinBytes seed k
      let mut base := 0
      for (o, sq) in (offsets 0 seqs).zip seqs do
        let start := img.entry + UInt64.ofNat o
        match runModel bug inp base img (layout start sq) start with
        | some (out, used) =>
          expect := expect ++ out
          base := base + used
        | none =>
          IO.eprintln s!"cosim: the model got stuck or did not write in sequence {i} of chunk {k}"
          return false
        i := i + 1
      let path := s!"{dir}/cosim.{k}.elf"
      IO.FS.writeBinFile path ⟨file.toArray⟩
      IO.setAccessRights path
        { user := { read := true, write := true, execution := true },
          group := { read := true, execution := true },
          other := { read := true, execution := true } }
      IO.FS.writeBinFile s!"{dir}/cosim.{k}.expect" ⟨expect.toArray⟩
      IO.FS.writeBinFile s!"{dir}/cosim.{k}.in" ⟨(stdinBytes seed k).toArray⟩
      return true

/-- Print sequence `i` of chunk `k`. -/
def showSeq (seed : UInt64) (count k i : Nat) : IO Unit := do
  match (chunkSeqs seed k count)[i]? with
  | none => IO.eprintln "no such sequence"
  | some is =>
    for ins in is do IO.println (repr ins).pretty

def main (args : List String) : IO UInt32 := do
  match args with
  | "gen" :: dir :: seed :: chunks :: count :: rest =>
    IO.FS.createDirAll dir
    let bug := match rest with | b :: _ => b.toNat! | [] => 0
    let mut ok := true
    let mut seqs := []
    for k in [0:chunks.toNat!] do
      if !(← genChunk dir seed.toNat!.toUInt64 count.toNat! bug k) then ok := false
      seqs := seqs ++ chunkSeqs seed.toNat!.toUInt64 k count.toNat!
    -- the coverage of the selector's forms is checked on the real run, whose many chunks reach
    -- every form; a seeded bug's run has one chunk of 100 sequences, which may miss one
    match if bug = 0 then missingForms seqs else [] with
    | [] => pure ()
    | ms => IO.eprintln s!"cosim: addressing forms of the selector not generated: {ms}"; ok := false
    return if ok then 0 else 1
  | ["show", seed, k, i, count] =>
    showSeq seed.toNat!.toUInt64 count.toNat! k.toNat! i.toNat!
    return 0
  | _ =>
    IO.eprintln "usage: cosim gen <dir> <seed> <chunks> <per-chunk> [bug] | cosim show <seed> <chunk> <index> <per-chunk>"
    return 2

end Millipede.Tests.CoSim

def main : List String → IO UInt32 := Millipede.Tests.CoSim.main
