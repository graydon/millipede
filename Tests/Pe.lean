import Millipede.Object.Pe.Laws
import Millipede.Target.X64.Isa

/-!
# Tests for the PE32+ writer and loader model

Three hand-assembled images at the base `0x140000000`:

* `ret42`: `mov eax, 42; ret`, which returns to the loader's thread start, so the process exits
  with status 42;
* `exit42`: `sub rsp, 40; mov ecx, 42; call [ExitProcess]`, exit status 42 through the import
  address table;
* `hello`: code, the read-only string `hello\n` and 8 bytes of zero-initialised data. It calls
  `GetStdHandle(-11)`, `WriteFile(h, msg, 6, &written, 0)` and `ExitProcess(7)`.

Each is written, loaded by the general theorem `load_write` (`ret42`, `hello`), parsed back by
evaluation and compared with the image the writer was given, with the import list and the import
address table as the writer laid them out. Each call in the hand-assembled code reads the slot of
the function it names, and the fixed header fields hold the values of the PE/COFF specification at
its offsets. The writer refuses invalid images, and each corrupted file is refused by the loader
model and differs from the valid file. `emit` writes the files and the model's description of each for
`scripts/pe-check.sh`.
-/

namespace Millipede.Pe.Tests

open Millipede Millipede.Pe

abbrev cfg : Config := Config.win64
/-- The stack top of the tests. -/
def top : UInt64 := 0x7ffffffe0000

def base : Nat := 0x140000000

/-- An x64 ABI with 4 KiB pages and the stack at `top`, which makes no system calls: Windows
programs reach the system through imported functions. -/
def abi : Abi X64.isa where
  pageBits := 12
  stackTop := top
  stackAlign := 16
  entryRegs entry sp := ⟨fun r => if r = .rsp then sp else 0, entry, ⟨false, false, false, false⟩⟩
  sysCall _ := none
  sysRet _ r := r

def retCode : List UInt8 := [0xb8, 0x2a, 0x00, 0x00, 0x00, 0xc3]

/-- `sub rsp, 40; mov ecx, 42; call [rip + 0x1041]` (the slot of `ExitProcess` at
`0x140002050`); `int3`. -/
def exitCode : List UInt8 :=
  [0x48, 0x83, 0xec, 0x28, 0xb9, 0x2a, 0x00, 0x00, 0x00, 0xff, 0x15, 0x41, 0x10, 0x00, 0x00, 0xcc]

/-- The `hello` program; the import section is at `0x140004000`, its slots at `0x...4050`
(`ExitProcess`), `…58` (`GetStdHandle`), `…60` (`WriteFile`). -/
def helloCode : List UInt8 :=
  [0x48, 0x83, 0xec, 0x38,                         -- sub rsp, 56
   0xb9, 0xf5, 0xff, 0xff, 0xff,                   -- mov ecx, -11
   0xff, 0x15, 0x49, 0x30, 0x00, 0x00,             -- call [GetStdHandle]
   0x48, 0x89, 0xc1,                               -- mov rcx, rax
   0x48, 0x8d, 0x15, 0xe7, 0x0f, 0x00, 0x00,       -- lea rdx, [msg]
   0x41, 0xb8, 0x06, 0x00, 0x00, 0x00,             -- mov r8d, 6
   0x4c, 0x8d, 0x0d, 0xda, 0x1f, 0x00, 0x00,       -- lea r9, [written]
   0x48, 0xc7, 0x44, 0x24, 0x20, 0, 0, 0, 0,       -- mov qword [rsp + 32], 0
   0xff, 0x15, 0x2b, 0x30, 0x00, 0x00,             -- call [WriteFile]
   0xb9, 0x07, 0x00, 0x00, 0x00,                   -- mov ecx, 7
   0xff, 0x15, 0x10, 0x30, 0x00, 0x00,             -- call [ExitProcess]
   0xcc]                                           -- int3

def ret42 : Image where
  segments := [{ vaddr := 0x140001000, bytes := retCode, memSize := 6, perm := Perm.rx }]
  entry := 0x140001000
  stackSize := 8192

def exit42 : Image where
  segments := [{ vaddr := 0x140001000, bytes := exitCode, memSize := 16, perm := Perm.rx }]
  entry := 0x140001000
  stackSize := 8192

def hello : Image where
  segments := [{ vaddr := 0x140001000, bytes := helloCode, memSize := helloCode.length,
                 perm := Perm.rx },
               { vaddr := 0x140002000, bytes := ascii "hello\n", memSize := 6, perm := Perm.r_ },
               { vaddr := 0x140003000, bytes := [], memSize := 8, perm := Perm.rw }]
  entry := 0x140001000
  stackSize := 0x10000

/-- The bytes of a written image, or none when the writer refuses it. -/
def bytesOf (img : Image) : List UInt8 :=
  match write cfg 12 top img with
  | .ok bs => bs
  | .error _ => []

def ret42Bytes : List UInt8 := bytesOf ret42
def exit42Bytes : List UInt8 := bytesOf exit42
def helloBytes : List UInt8 := bytesOf hello

#guard ret42Bytes.length = 1536
#guard exit42Bytes.length = 1536
#guard helloBytes.length = 2048
#guard idataRva hello = 0x4000
#guard idataRva exit42 = 0x2000
#guard base + idataRva hello + iatOff 4 = 0x140004050

/-- What the loader model reads, compared with the image the writer was given: the image itself
up to the zero padding of each section's bytes, the base, and the imports. -/
def readsBack (img : Image) (bs : List UInt8) : Bool :=
  match parse cfg 12 top bs with
  | none => false
  | some p =>
    p.img.entry == img.entry && p.img.stackSize == img.stackSize && p.base == base &&
      p.img.segments.length == img.segments.length &&
      (p.img.segments.zip img.segments).all (fun (a, b) =>
        a.vaddr == b.vaddr && a.memSize == b.memSize && a.perm == b.perm &&
          a.bytes.take b.bytes.length == b.bytes &&
          (a.bytes.drop b.bytes.length).all (· == 0)) &&
      p.imports == { dll := cfg.dll, funcs := cfg.funcs, iat := idataRva img + iatOff 4 }

set_option maxRecDepth 100000 in
theorem ret42_write : write cfg 12 top ret42 = .ok ret42Bytes := by rfl
set_option maxRecDepth 100000 in
theorem hello_write : write cfg 12 top hello = .ok helloBytes := by rfl

/-- The round trip by the general theorems. -/
theorem ret42_load : load cfg abi ret42Bytes = some (ret42.init abi) := load_write ret42_write
theorem hello_load : load cfg abi helloBytes = some (hello.init abi) := load_write hello_write

#guard readsBack ret42 ret42Bytes
#guard readsBack exit42 exit42Bytes
#guard readsBack hello helloBytes

/-- The address table slot `k` after loading with a resolver that maps function `k` of
`kernel32.dll` to `0x7ff800000000 + k`. -/
def resolver (dll f : List UInt8) : Option UInt64 :=
  if dll = cfg.dll then (cfg.funcs.idxOf? f).map (fun k => 0x7ff800000000 + k.toUInt64) else none

#guard (loadWith cfg abi resolver helloBytes).isSome
#guard match loadWith cfg abi resolver helloBytes with
  | some s => (List.range 4).all fun k =>
      (List.range 8).map (fun i => s.mem.bytes (0x140004050 + UInt64.ofNat (8 * k + i))) =
        natBytes 8 (0x7ff800000000 + k)
  | none => false
-- The import section and the headers are read-only in the fuller model, unmapped in `load`.
#guard match loadWith cfg abi resolver helloBytes, load cfg abi helloBytes with
  | some s, some s₀ => s.mem.perm 0x140004 == Perm.r_ && s.mem.perm 0x140000 == Perm.r_ &&
      s₀.mem.perm 0x140004 == Perm.none && s₀.mem.perm 0x140000 == Perm.none &&
      s₀.mem.perm 0x140001 == Perm.rx && s₀.mem.perm 0x140003 == Perm.rw
  | _, _ => false
-- A missing function makes the fuller model refuse the file.
#guard (loadWith cfg abi (fun _ f => if f = ascii "ReadFile" then none else some 1)
  helloBytes).isNone

/-- The address that the `call [rip + disp]` ending at offset `e` of a program's code reads. -/
def callSlot (code : List UInt8) (e : Nat) : Nat :=
  0x140001000 + e + natOfBytes ((code.drop (e - 4)).take 4)

/-- The address table slot of function `f` in the file of `img`. -/
def slotOf (img : Image) (f : String) : Nat :=
  base + idataRva img + iatOff cfg.funcs.length + 8 * cfg.funcs.idxOf (ascii f)

-- Each call in the hand-assembled code goes through the slot of the function it means.
#guard callSlot exitCode 15 = slotOf exit42 "ExitProcess"
#guard callSlot helloCode 15 = slotOf hello "GetStdHandle"
#guard callSlot helloCode 53 = slotOf hello "WriteFile"
#guard callSlot helloCode 64 = slotOf hello "ExitProcess"

/-- The fixed header fields that Windows checks, as offset, width and value, taken from the
PE/COFF specification's layout rather than from `hdrFields`, so that a wrong constant there fails
here. -/
def specFields : List (Nat × Nat × Nat) :=
  [ (0, 2, 0x5a4d), (60, 4, 64), (64, 4, 0x4550),     -- "MZ", e_lfanew, "PE\0\0"
    (68, 2, 0x8664), (84, 2, 240), (86, 2, 0x22),     -- AMD64, optional header size, flags
    (88, 2, 0x20b), (120, 4, 4096), (124, 4, 512),    -- PE32+, section and file alignment
    (128, 2, 6), (136, 2, 6), (156, 2, 3),            -- OS and subsystem version, console
    (158, 2, 0x8160), (196, 4, 16) ]                  -- DLL characteristics, 16 directories

#guard [ret42Bytes, exit42Bytes, helloBytes].all fun bs =>
  specFields.all fun (off, w, v) => natOfBytes ((bs.drop off).take w) = v

/-! ### The writer refuses invalid images -/

/-- A writable and executable segment. -/
def wx : Image :=
  { ret42 with segments := [{ vaddr := 0x140001000, bytes := retCode, memSize := 6,
                              perm := ⟨true, true, true⟩ }] }
/-- A base that is not 64 KiB-aligned. -/
def unaligned : Image :=
  { ret42 with segments := [{ vaddr := 0x140002000, bytes := retCode, memSize := 6,
                              perm := Perm.rx }] }
/-- A gap between sections. -/
def gap : Image :=
  { hello with segments := [{ vaddr := 0x140001000, bytes := helloCode,
                              memSize := helloCode.length, perm := Perm.rx },
                            { vaddr := 0x140003000, bytes := ascii "hello\n", memSize := 6,
                              perm := Perm.r_ }] }

#guard (write cfg 12 top wx).toBool = false
#guard (write cfg 12 top unaligned).toBool = false
#guard (write cfg 12 top gap).toBool = false
-- no segments, 64 KiB pages, a stack too large, an empty import list, a name with a zero byte
#guard (write cfg 12 top { ret42 with segments := [] }).toBool = false
#guard (write cfg 16 top ret42).toBool = false
#guard (write cfg 12 top { ret42 with stackSize := 2 ^ 23 }).toBool = false
#guard (write { cfg with funcs := [] } 12 top ret42).toBool = false
#guard (write { cfg with funcs := [[0x41, 0]] } 12 top ret42).toBool = false

/-! ### Corrupted files -/

/-- The `k` little-endian bytes of `n`. -/
abbrev le (n k : Nat) : List UInt8 := natBytes k n

/-- File offsets in `hello`: section header `k`, and the import section. -/
def sh (k : Nat) : Nat := HDR_LEN + SHDR_LEN * k
def idOff : Nat := 1536

/-- The corruptions, each a name and a patched file. -/
def corruptions : List (String × List UInt8) :=
  [ ("bad-mz",            patchBytes helloBytes 0 [0x4e]),
    ("lfanew",            patchBytes helloBytes 60 (le 0x80 4)),
    ("pe-signature",      patchBytes helloBytes 64 [0x50, 0x45, 0x01]),
    ("machine-arm64",     patchBytes helloBytes 68 (le 0xaa64 2)),
    ("nsec-plus-one",     patchBytes helloBytes 70 (le 5 2)),
    ("dll-characteristic", patchBytes helloBytes 86 (le 0x2022 2)),
    ("pe32-magic",        patchBytes helloBytes 88 (le 0x10b 2)),
    ("section-align",     patchBytes helloBytes 120 (le 0x200 4)),
    ("file-align",        patchBytes helloBytes 124 (le 0x1000 4)),
    ("size-of-image",     patchBytes helloBytes 144 (le 0x6000 4)),
    ("size-of-headers",   patchBytes helloBytes 148 (le 0x300 4)),
    ("subsystem-gui",     patchBytes helloBytes 156 (le 2 2)),
    ("no-nx",             patchBytes helloBytes 158 (le 0x8060 2)),
    ("stack-big",         patchBytes helloBytes 160 (le (2 ^ 24) 8)),
    ("stack-commit",      patchBytes helloBytes 168 (le 0x1000 8)),
    ("import-dir",        patchBytes helloBytes 208 (le 0x4008 4)),
    ("reloc-dir",         patchBytes helloBytes 240 (le 0x5000 4)),
    ("tls-dir",           patchBytes helloBytes 272 (le 0x2000 4)),
    ("iat-size",          patchBytes helloBytes 300 (le 0x10 4)),
    ("text-wx",           patchBytes helloBytes (sh 0 + 36) (le 0xe0000020 4)),
    ("text-chars",        patchBytes helloBytes (sh 0 + 36) (le 0x60000021 4)),
    ("text-rva",          patchBytes helloBytes (sh 0 + 12) (le 0x2000 4)),
    ("gap",               patchBytes helloBytes (sh 1 + 12) (le 0x3000 4)),
    ("raw-misaligned",    patchBytes helloBytes (sh 0 + 20) (le 0x210 4)),
    ("raw-outside",       patchBytes helloBytes (sh 3 + 16) (le 0x400 4)),
    ("raw-in-headers",    patchBytes helloBytes (sh 2 + 20) (le 0 4)),
    ("relocations",       patchBytes helloBytes (sh 0 + 24) (le 0x200 4)),
    ("text-tail",         patchBytes helloBytes (512 + 100) [0x90]),
    ("idata-writable",    patchBytes helloBytes (sh 3 + 36) (le 0xc0000040 4)),
    ("idata-short",       patchBytes helloBytes (sh 3 + 8) (le 100 4)),
    ("time-stamp",        patchBytes helloBytes (idOff + 4) (le 1 4)),
    ("two-descriptors",   patchBytes helloBytes (idOff + 20) (le 0x4028 4)),
    ("by-ordinal",        patchBytes helloBytes (idOff + 40 + 7) [0x80]),
    ("iat-overlaps-ilt",  patchBytes helloBytes (idOff + 16) (le 0x4040 4)),
    ("dll-name-outside",  patchBytes helloBytes (idOff + 12) (le 0x5000 4)),
    ("truncated",         helloBytes.take 1800) ]

#guard corruptions.all (fun c => (parse cfg 12 top c.2).isNone)
#guard corruptions.all (fun c => c.2 != helloBytes)

/-! ### Files for `scripts/pe-check.sh` -/

/-- A permission as the three letters `r`, `w`, `x` or dashes. -/
def permStr (p : Perm) : String :=
  (if p.r then "r" else "-") ++ (if p.w then "w" else "-") ++ (if p.x then "x" else "-")

/-- The loader model's description of a file: base, entry, stack, each section (address, size,
permission), the import section and the imports. -/
def describe (p : Parsed) : String :=
  let seg (tag : String) (sg : Segment) :=
    s!"{tag} {sg.vaddr.toNat - p.base} {sg.memSize} {permStr sg.perm}\n"
  s!"base {p.base}\nentry {p.img.entry.toNat - p.base}\nstack {p.img.stackSize}\n" ++
    String.join (p.img.segments.map (seg "section")) ++ seg "idata" p.idata ++
    s!"dll {String.ofList (p.imports.dll.map (fun b => Char.ofNat b.toNat))}\n" ++
    s!"iat {p.imports.iat}\n" ++
    String.join (p.imports.funcs.map fun f => s!"import {String.ofList (f.map (fun b => Char.ofNat b.toNat))}\n")

/-- Writes `<name>.exe` and `<name>.model` for the three images, and `bad-<name>.exe` for each
corruption, into `dir`; prints the loader model's verdict on each and returns the number of
unexpected verdicts. -/
def emit (dir : System.FilePath) : IO UInt32 := do
  let mut bad : UInt32 := 0
  for (name, img, bs) in [("ret42", ret42, ret42Bytes), ("exit42", exit42, exit42Bytes),
      ("hello", hello, helloBytes)] do
    IO.FS.writeBinFile (dir / s!"{name}.exe") ⟨bs.toArray⟩
    match parse cfg 12 top bs with
    | some p => IO.FS.writeFile (dir / s!"{name}.model") (describe p)
    | none => pure ()
    let ok := readsBack img bs
    IO.println s!"lean-loader {name}: {if ok then "loads (round trip)" else "WRONG"}"
    if !ok then bad := bad + 1
  for (name, bs) in corruptions do
    IO.FS.writeBinFile (dir / s!"bad-{name}.exe") ⟨bs.toArray⟩
    let refused := (parse cfg 12 top bs).isNone
    if !refused then
      IO.println s!"lean-loader bad-{name}: ACCEPTED"
      bad := bad + 1
  IO.println s!"lean-loader: {corruptions.length} corrupted files, {bad} unexpected verdicts"
  return bad

/-- Prints the loader model's verdict on each file, `accepted` or `refused`. -/
def verdicts (files : List String) : IO UInt32 := do
  for f in files do
    let bs ← IO.FS.readBinFile f
    IO.println s!"{f} {if (parse cfg 12 top bs.toList).isSome then "accepted" else "refused"}"
  return 0

end Millipede.Pe.Tests
