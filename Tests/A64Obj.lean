import Millipede.Target.A64.Select
import Millipede.Object.LinkProof
import Millipede.Object.Elf.Laws

/-!
# arm64 object layer tests

These tests take real arm64 instructions through the arm64 word assembler and its fixups, the
linker and the ELF writer for AArch64 Linux. Each fixup's field for a known distance gives the
word that `llvm-mc` emits, and targets out of range or misaligned are refused. The Linux
system-call model on arm64 registers maps `x8 = 64` to `write` and is stuck on the x64 numbers,
and the x64 model is shown to be the x64 instance of the same builder.

A small program goes through assembly, linking and the ELF writer and back through the loader
model, next to the refusals of a misaligned base, a `page21` fixup to a local label, a branch out
of reach, an `ldr :lo12:` fixup and the x64 page size. `emit dir` writes `echo.elf`, the program of
`scripts/a64/echo.s`, which writes a greeting, echoes what `read` returns, runs a `cbnz` loop,
calls a function 1.25 MiB away and exits with a word loaded through `adrp`. It also writes the
section addresses, every instruction's word with its assembly, the file offsets of the fixups
and the loader model's verdict on the file and on corruptions of it, which
`scripts/a64-elf-check.sh` checks against `llvm-mc` and the reference tools.
-/

namespace Millipede.Tests.A64Obj

open Millipede Asm A64

abbrev RA : Arch := A64.arch

/-! ## Fixups against `llvm-mc`

The expected words come from `llvm-mc -triple=aarch64 -show-encoding`. -/

-- `bl #0x100` = 0x94000040; `bl #-0x7fffffc` = 0x96000001
example : Fixup.branch26.apply 0x400100 0x400000 0x94000000 = some 0x94000040 := by decide
example : Fixup.branch26.apply 0x400004 0x8400000 0x94000000 = some 0x96000001 := by decide
-- `cbnz x9, #-8` = 0xb5ffffc9
example : Fixup.cond19.apply 0x400000 0x400008 0xb5000009 = some 0xb5ffffc9 := by decide
-- `adr x5, #-12` = 0x10ffffa5; `adr x5, #0xfffff` = 0x707fffe5
example : Fixup.adr21.apply 0x400000 0x40000c 0x10000005 = some 0x10ffffa5 := by decide
example : Fixup.adr21.apply 0x4fffff 0x400000 0x10000005 = some 0x707fffe5 := by decide
-- `adrp x1, #0x130000` = 0x90000981; `adrp x1, #-0x1000` = 0xf0ffffe1; the arithmetic is on
-- pages, so the low 12 bits of both addresses are ignored
example : Fixup.page21.apply 0x530fff 0x400ffc 0x90000001 = some 0x90000981 := by decide
example : Fixup.page21.apply 0x400000 0x401abc 0x90000001 = some 0xf0ffffe1 := by decide
-- `add x1, x1, #6` = 0x91001821; `ldr x0, [x3, #8]` = 0xf9400460; `ldr x0, [x3, #4088]` = 0xf947fc60
example : (Fixup.lo12 0).apply 0x530006 0 0x91000021 = some 0x91001821 := by decide
example : (Fixup.lo12 3).apply 0x530008 0 0xf9400060 = some 0xf9400460 := by decide
example : (Fixup.lo12 3).apply 0x531ff8 0 0xf9400060 = some 0xf947fc60 := by decide
-- targets out of reach and misaligned targets are refused
example : Fixup.branch26.apply 0x8400000 0x400000 0x94000000 = none := by decide
example : Fixup.branch26.apply 0x400002 0x400000 0x94000000 = none := by decide
example : Fixup.cond19.apply 0x500000 0x400000 0xb5000009 = none := by decide
example : Fixup.adr21.apply 0x500000 0x400000 0x10000005 = none := by decide
example : (Fixup.lo12 3).apply 0x530004 0 0xf9400060 = none := by decide
-- the relocation patches exactly the instruction's field, reading the template word
example : RelocKind.patch (.word .branch26) 0x400100 0x400000 0 [0x00, 0x00, 0x00, 0x94] =
    some [0x40, 0x00, 0x00, 0x94] := by decide

/-! ## The Linux system-call model on arm64 registers -/

/-- A state with `x8 = nr`, `x0 = 1`, `x1 = 0x10`, `x2 = 2` and two readable bytes at `0x10`. -/
def sysState (nr : UInt64) : MState Regs where
  regs := ⟨fun j => if j = 8 then nr else if j = 0 then 1 else if j = 1 then 0x10 else if j = 2 then 2 else 0,
    0, ⟨false, false, false, false⟩⟩
  mem := { pageBits := 12, bytes := fun a => if a = 0x10 then 104 else if a = 0x11 then 105 else 0,
           perm := fun _ => Perm.r_ }
  world := World.init

-- `x8 = 64` is `write(1, "hi")`; `x8 = 93` is `exit(1)`; `x8 = 63` is `read`
example : (A64.linux.sysCall (sysState 64)) = some (⟨"write", [1], [[104, 105]], []⟩, false) := by
  decide +kernel
example : (A64.linux.sysCall (sysState 93)).map (·.1.sym) = some "exit" := by decide +kernel
example : (A64.linux.sysCall (sysState 63)).map (·.1) = some ⟨"read", [1], [], [2]⟩ := by
  decide +kernel
-- the x64 numbers mean nothing here, so a wrong system-call number is stuck
example : A64.linux.sysCall (sysState 1) = none := by decide +kernel
example : A64.linux.sysCall (sysState 60) = none := by decide +kernel

/-- The x64 Linux model is the x64 instance of the same builder. -/
theorem x64_linux_eq : X64.linux = Abi.linux 12 0x7ffffffff000 X64.linux.entryRegs LinuxNums.x64
    ⟨fun r => r.gpr .rax, fun i r => r.gpr ([X64.Reg.rdi, .rsi, .rdx].getD i .rdi),
      fun v r => r.set .rax v⟩ := rfl

/-! ## A small program, end to end

These tests use compiled evaluation, since the program's pages are 64 KiB. -/

/-- A program whose `_start` is `b skip; ret; skip: adrp x1, msg; add x1, :lo12:msg; bl f; svc`,
where `skip` is label 1, and whose function `f` is `ret`. Its data is `msg`. -/
def small : Asm.Prog RA where
  funs := [{ name := "_start", entry := [],
             blocks := [[.fix .branch26 (.b false 0) (.label 1), .op (.ret 30)],
                        [.fix .page21 (.adr true 1 0) (.sym "msg"), .fix (.lo12 0) (lo12I 1 0) (.sym "msg"),
                         .fix .branch26 (.b true 0) (.sym "f"), .op (.svc 0)]] },
           { name := "f", entry := [.op (.ret 30)], blocks := [] }]
  data := [("msg", [104, 105, 10])]
  main := 0

def smallCfg : Link.Config := Link.Config.a64Linux "_start" 4096

def smallImg : Except String Image := do
  let obj ← assemble A64.asm small
  Link.link smallCfg [obj]

def smallBytes : Except String (List UInt8) := do
  Elf.write Elf.Config.a64Linux 16 Abi.a64LinuxStackTop (← smallImg)

-- the text segment: `b +8`, `ret`, `adrp x1, (0x410000 - 0x400000) >> 12`, `add x1, x1, #0`,
-- `bl +8`, `svc`, `ret`; then rodata at the next 64 KiB page
#guard smallImg.toOption.map (fun img => (img.segments.map fun sg => (sg.vaddr, sg.bytes.take 28))) ==
    some [(0x400000, natBytes 4 0x14000002 ++ natBytes 4 0xd65f03c0 ++
            natBytes 4 0x90000081 ++ natBytes 4 0x91000021 ++ natBytes 4 0x94000002 ++
            natBytes 4 0xd4000001 ++ natBytes 4 0xd65f03c0),
         (0x410000, [104, 105, 10] ++ List.replicate 25 0)]
-- the writer accepts it, and the loader model reads back exactly the linked image
#guard (do let img ← smallImg; let bs ← smallBytes
           pure (Elf.parse Elf.Config.a64Linux 16 Abi.a64LinuxStackTop bs == some img)).toOption ==
    some true
-- `e_machine` is 183, which is EM_AARCH64, and the first `PT_LOAD` is 64 KiB-aligned
#guard smallBytes.toOption.map (fun bs => (natOfBytes ((bs.drop 18).take 2),
    natOfBytes ((bs.drop (64 + 48)).take 8))) == some (183, 0x10000)

-- a base address that is 4 KiB-aligned but not 64 KiB-aligned is refused
#guard (do let obj ← assemble A64.asm small
           Link.link { smallCfg with base := 0x401000 } [obj]).toBool == false
-- laid out with 4 KiB pages, the arm64 writer refuses (its page is 64 KiB)
#guard (do let obj ← assemble A64.asm small
           let img ← Link.link { smallCfg with pageBits := 12 } [obj]
           Elf.write Elf.Config.a64Linux 12 Abi.a64LinuxStackTop img).toBool == false
-- `adrp` of a local label is refused, since its value depends on the absolute address
#guard (assemble A64.asm { small with
    funs := [{ name := "_start", entry := [], blocks := [[.fix .page21 (.adr true 1 0) (.label 0)]] }] }
    ).toBool == false
-- a `cbz` to a label just over 1 MiB away is out of reach …
#guard (assemble A64.asm { small with
    funs := [{ name := "_start", entry := [], blocks := [[.fix .cond19 (.cbz true false 0 0) (.label 2)],
      List.replicate (2 ^ 18) (.op (.ret 30))] }] }).toBool == false
-- … and one 1 MiB - 4 away is in reach
#guard (assemble A64.asm { small with
    funs := [{ name := "_start", entry := [], blocks := [[.fix .cond19 (.cbz true false 0 0) (.label 2)],
      List.replicate (2 ^ 18 - 2) (.op (.ret 30))] }] }).toBool == true
-- an `ldr :lo12:` cannot carry a fixup on arm64, since selection uses `add :lo12:`, and neither
-- can a template whose field is not zero
#guard (assemble A64.asm { small with
    funs := [{ name := "_start", entry := [], blocks := [[.fix (.lo12 3) (.ldr .x 0 (.uimm 3 0)) (.sym "msg")]] }] }
    ).toBool == false
#guard (assemble A64.asm { small with
    funs := [{ name := "_start", entry := [], blocks := [[.fix .page21 (.adr true 1 1) (.sym "msg")]] }] }
    ).toBool == false
-- a wrong `e_machine` (x86-64) is refused by the arm64 loader model
#guard smallBytes.toOption.map (fun bs =>
    (Elf.parse Elf.Config.a64Linux 16 Abi.a64LinuxStackTop (patchBytes bs 18 (natBytes 2 62))).isNone) ==
    some true

/-! ## The echo program of `scripts/a64/echo.s` -/

/-- The instructions with their assembly and the word that `llvm-mc` assembles it to. The script
checks the text against `llvm-mc`, and the guard below checks `A64.encode` against the word. -/
def W : List (String × Instr × Nat) :=
  [ ("mov x0, #1", .mov .z true 0 1 0, 0xd2800020), ("mov x0, #0", .mov .z true 0 0 0, 0xd2800000),
    ("mov x2, #6", .mov .z true 2 6 0, 0xd28000c2), ("mov x2, #4", .mov .z true 2 4 0, 0xd2800082),
    ("mov x2, #64", .mov .z true 2 64 0, 0xd2800802), ("mov x8, #64", .mov .z true 8 64 0, 0xd2800808),
    ("mov x8, #63", .mov .z true 8 63 0, 0xd28007e8), ("mov x8, #93", .mov .z true 8 93 0, 0xd2800ba8),
    ("svc #0", .svc 0, 0xd4000001), ("orr x2, xzr, x0", .logReg .orr true 2 31 0, 0xaa0003e2),
    ("mov x9, #3", .mov .z true 9 3 0, 0xd2800069),
    ("sub x9, x9, #1", .addImm true true false 9 9 1 false, 0xd1000529),
    ("cbnz x9, #0", .cbz true true 9 0, 0xb5000009), ("b #0", .b false 0, 0x14000000),
    ("bl #0", .b true 0, 0x94000000), ("adr x5, #0", .adr false 5 0, 0x10000005),
    ("adrp x1, #0", .adr true 1 0, 0x90000001), ("add x1, x1, #0", lo12I 1 0, 0x91000021),
    ("adrp x3, #0", .adr true 3 0, 0x90000003), ("add x3, x3, #0", lo12I 3 0, 0x91000063),
    ("ldr x0, [x3]", .ldr .x 0 (.uimm 3 0), 0xf9400060), ("ret", .ret 30, 0xd65f03c0),
    ("orr x10, xzr, xzr", .logReg .orr true 10 31 31, 0xaa1f03ea) ]

-- the encoder agrees with every literal word
#guard W.all fun (_, i, n) => i.valid && (A64.encode i).toNat == n

/-- The instruction of an assembly line of `W`. -/
def w (s : String) : Instr := ((W.find? (·.1 == s)).map (·.2.1)).getD (.ret 30)

def o (s : String) : WSI Instr := .op (w s)
def fx (k : Fixup) (s : String) (r : Ref) : WSI Instr := .fix k (w s) r

/-- `write(1, sym, n)` with `x2` set by `len`. -/
def writeSym (sym : String) (len : String) : List (WSI Instr) :=
  [o "mov x0, #1", fx .page21 "adrp x1, #0" (.sym sym), fx (.lo12 0) "add x1, x1, #0" (.sym sym),
   o len, o "mov x8, #64", o "svc #0"]

/-- `_start`: block 0 writes the greeting and echoes; block 1 is a 3-iteration `cbnz` loop
then `b` to block 2; block 2 takes an `adr` of block 1, calls `far`, and exits with the word
at `val`. -/
def startFn : Asm.Fn RA where
  name := "_start"
  entry := []
  blocks :=
    [ writeSym "hello" "mov x2, #6" ++
      [o "mov x0, #0", fx .page21 "adrp x1, #0" (.sym "buf"), fx (.lo12 0) "add x1, x1, #0" (.sym "buf"),
       o "mov x2, #64", o "mov x8, #63", o "svc #0", o "orr x2, xzr, x0",
       o "mov x0, #1", fx .page21 "adrp x1, #0" (.sym "buf"), fx (.lo12 0) "add x1, x1, #0" (.sym "buf"),
       o "mov x8, #64", o "svc #0", o "mov x9, #3"],
      [o "sub x9, x9, #1", fx .cond19 "cbnz x9, #0" (.label 1), fx .branch26 "b #0" (.label 2),
       o "ret"],
      [fx .adr21 "adr x5, #0" (.label 1), fx .branch26 "bl #0" (.sym "far"),
       fx .page21 "adrp x3, #0" (.sym "val"), fx (.lo12 0) "add x3, x3, #0" (.sym "val"),
       o "ldr x0, [x3]", o "mov x8, #93", o "svc #0"] ]

/-- `far`: writes `far\n` and returns. -/
def farFn : Asm.Fn RA := { name := "far", entry := writeSym "farmsg" "mov x2, #4" ++ [o "ret"], blocks := [] }

/-- The number of padding functions between `_start` and `far`. Each is 1000 instructions
`orr x10, xzr, xzr`, so together they span 1.25 MiB. -/
def padFns : Nat := 320

def padFn (i : Nat) : Asm.Fn RA :=
  { name := s!"pad{i}", entry := List.replicate 1000 (o "orr x10, xzr, xzr"), blocks := [] }

def echo : Asm.Prog RA where
  funs := startFn :: (List.range padFns).map padFn ++ [farFn]
  data := [("val", natBytes 8 42), ("hello", "hello\n".toUTF8.toList), ("farmsg", "far\n".toUTF8.toList)]
  main := 0
  bss := [("buf", 64)]

def echoCfg : Link.Config := Link.Config.a64Linux "_start" 65536

/-- The file offset of an address in the text segment, after the headers' 64 KiB page. -/
def fileOff (a : Nat) : Nat := a - 0x400000 + 0x10000

def emit (dir : System.FilePath) : IO UInt32 := do
  let obj ← IO.ofExcept (assemble A64.asm echo)
  let img ← IO.ofExcept (Link.link echoCfg [obj])
  let bs ← IO.ofExcept (Elf.write Elf.Config.a64Linux 16 Abi.a64LinuxStackTop img)
  IO.FS.writeBinFile (dir / "echo.elf") ⟨bs.toArray⟩
  let L := Link.layout echoCfg [obj]
  let σ := Link.resolve L [obj] 0
  let addr (s : String) : Nat := ((σ s).map (·.toNat)).getD 0
  let text := (obj.sections.headD default).bytes.length
  IO.FS.writeFile (dir / "layout.txt")
    s!"text {L.textBase} {text}\nrodata {L.roBase}\nbss {L.rwBase}\n"
  IO.FS.writeFile (dir / "words.txt") (String.join (W.map fun (s, i, _) => s!"{s}\t{(A64.encode i).toNat}\n"))
  -- instruction indices in `_start`: block 0 has 19 instructions, block 1 four
  let start := addr "_start"
  IO.FS.writeFile (dir / "sites.txt") (String.join
    [ s!"bl {fileOff (start + 4 * 24)}\n", s!"adrp {fileOff (start + 4 * 1)}\n",
      s!"svcnr {fileOff (start + 4 * 4)}\n", s!"far {addr "far" - start}\n" ])
  let mut bad : UInt32 := 0
  let ok := Elf.parse Elf.Config.a64Linux 16 Abi.a64LinuxStackTop bs == some img
  IO.println s!"lean-loader echo.elf: {if ok then "loads (round trip)" else "WRONG"}"
  if !ok then bad := bad + 1
  for (name, f) in [("machine", patchBytes bs 18 (natBytes 2 62)),
                    ("misaligned", patchBytes bs (64 + 56 + 16) (natBytes 8 (L.roBase + 0x1000)))] do
    let refused := (Elf.parse Elf.Config.a64Linux 16 Abi.a64LinuxStackTop f).isNone
    IO.println s!"lean-loader bad-{name}: {if refused then "refused" else "ACCEPTED"}"
    if !refused then bad := bad + 1
  return bad

end Millipede.Tests.A64Obj
