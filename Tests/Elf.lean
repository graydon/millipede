import Millipede.Object.Elf.Laws
import Millipede.Object.Obj

/-!
# Tests for the ELF64 writer and loader model

This suite writes a hand-assembled `exit(42)` image, checks its layout, and parses it back both
by the general round-trip theorem and by evaluation. A two-segment image with code and read-only
data round-trips too, and the writer refuses invalid images. Each of twenty corrupted files is
refused by the loader model, and each differs from the valid file, so the test is not vacuous.
The corruptions include a bad magic number, a wrong class or machine, a missing or executable
stack header, a segment both writable and executable, misaligned offsets, a truncated file and
overlapping segments.

For arm64 Linux, with 64 KiB pages and whole-page segments, an `exit(42)` image round-trips,
and images and files that break an arm64 rule are refused. `emit` writes the x64 files for
`scripts/elf-check.sh`, which checks them with `readelf` and runs them under `qemu-x86_64`. The
x64 checks are kernel evaluations, and the arm64 checks run by compiled evaluation with `#guard`.
-/

namespace Millipede.Elf.Tests

open Millipede Millipede.Elf

/-- The ELF settings of x86-64 Linux. -/
abbrev cfg : Config := Config.x64Linux
/-- The stack top used by the tests, the highest value that `Config.x64Linux` allows. -/
def top : UInt64 := 0x7ffffffff000

/-- `exit(42)` as `mov eax, 60; mov edi, 42; syscall`. -/
def exitCode : List UInt8 :=
  [0xb8, 0x3c, 0x00, 0x00, 0x00, 0xbf, 0x2a, 0x00, 0x00, 0x00, 0x0f, 0x05]

/-- One read-execute page at `0x400000` with the entry at its start and 8 KiB of stack. -/
def hello : Image where
  segments := [{ vaddr := 0x400000, bytes := exitCode, memSize := 12, perm := Perm.rx }]
  entry := 0x400000
  stackSize := 8192

/-- Code plus a read-only page with 16 bytes initialised and 4 KiB more of zeros. -/
def two : Image where
  segments := [{ vaddr := 0x400000, bytes := exitCode, memSize := 12, perm := Perm.rx },
               { vaddr := 0x401000, bytes := List.replicate 16 0xab, memSize := 4096 + 16,
                 perm := Perm.r_ }]
  entry := 0x400000
  stackSize := 4096

/-- The bytes of a written image, or none when the writer refuses it. -/
def bytesOf (img : Image) : List UInt8 :=
  match write cfg 12 top img with
  | .ok bs => bs
  | .error _ => []

def helloBytes : List UInt8 := bytesOf hello
def twoBytes : List UInt8 := bytesOf two

theorem hello_write : write cfg 12 top hello = .ok helloBytes := by rfl
theorem two_write : write cfg 12 top two = .ok twoBytes := by rfl

/-- The layout is the headers padded to one page, followed by the code page. -/
theorem hello_length : helloBytes.length = 8192 := by decide +kernel
theorem hello_magic : helloBytes.take 4 = [0x7f, 0x45, 0x4c, 0x46] := by decide +kernel
theorem hello_code : (helloBytes.drop 4096).take 12 = exitCode := by decide +kernel
theorem hello_phnum : natOfBytes ((helloBytes.drop 56).take 2) = 2 := by decide +kernel
theorem two_length : twoBytes.length = 4096 * 3 := by decide +kernel

/-- The round trip by the general theorem. -/
theorem hello_parse : parse cfg 12 top helloBytes = some hello := parse_write hello_write
theorem two_parse : parse cfg 12 top twoBytes = some two := parse_write two_write
/-- The round trip by evaluation. -/
theorem hello_parse_eval : parse cfg 12 top helloBytes = some hello := by decide +kernel

/-- The writer refuses invalid images. -/
theorem refuse_wx : (write cfg 12 top { hello with
    segments := [{ vaddr := 0x400000, bytes := exitCode, memSize := 12,
                   perm := ⟨true, true, true⟩ }] }).toBool = false := by decide +kernel
theorem refuse_unaligned : (write cfg 12 top { hello with
    segments := [{ vaddr := 0x400010, bytes := exitCode, memSize := 12, perm := Perm.rx }] }
    ).toBool = false := by decide +kernel
theorem refuse_low : (write cfg 12 top { hello with
    segments := [{ vaddr := 0x1000, bytes := exitCode, memSize := 12, perm := Perm.rx }] }
    ).toBool = false := by decide +kernel
theorem refuse_pagesize : (write cfg 16 top hello).toBool = false := by decide +kernel

/-! ### Corrupted files -/

/-- The `k` little-endian bytes of `n`. -/
abbrev le (n k : Nat) : List UInt8 := natBytes k n

/-- The corruptions, each a name and a patched file. -/
def corruptions : List (String × List UInt8) :=
  [ ("bad-magic",      patchBytes helloBytes 0 [0x7e]),
    ("class32",        patchBytes helloBytes 4 [1]),
    ("big-endian",     patchBytes helloBytes 5 [2]),
    ("et-dyn",         patchBytes helloBytes 16 (le 3 2)),
    ("machine-arm64",  patchBytes helloBytes 18 (le 183 2)),
    ("phentsize",      patchBytes helloBytes 54 (le 32 2)),
    ("no-gnu-stack",   patchBytes helloBytes 56 (le 1 2)),
    ("phoff-outside",  patchBytes helloBytes 32 (le 0xffff 8)),
    ("load-wx",        patchBytes helloBytes (64 + 4) (le 7 4)),
    ("load-flags",     patchBytes helloBytes (64 + 4) (le 13 4)),
    ("offset-misalign", patchBytes helloBytes (64 + 8) (le 0x1001 8)),
    ("align",          patchBytes helloBytes (64 + 48) (le 0x200000 8)),
    ("vaddr-low",      patchBytes helloBytes (64 + 16) (le 0x1000 8)),
    ("filesz-gt-memsz", patchBytes helloBytes (64 + 32) (le 13 8)),
    ("exec-stack",     patchBytes helloBytes (64 + 56 + 4) (le 7 4)),
    ("stack-big",      patchBytes helloBytes (64 + 56 + 40) (le (2 ^ 23) 8)),
    ("truncated",      helloBytes.take 4100),
    ("tail-nonzero",   patchBytes helloBytes (4096 + 12) [0x90]),
    ("overlap",        patchBytes twoBytes (64 + 56 + 16) (le 0x400000 8)),
    ("stack-first", patchBytes helloBytes 64 (le PT_GNU_STACK 4)) ]

/-- Every corruption is refused by the loader model. -/
theorem corruptions_refused :
    corruptions.all (fun c => (parse cfg 12 top c.2).isNone) = true := by decide +kernel

/-- Each corruption really changes the file, so the test is not vacuous. -/
theorem corruptions_differ :
    corruptions.all (fun c => c.2 != helloBytes && c.2 != twoBytes) = true := by decide +kernel

/-! ### arm64 Linux -/

/-- The arm64 stack top. -/
def a64top : UInt64 := 0x7fffff0000

/-- `exit(42)` as `movz x0, #42; movz x8, #93; svc #0`. -/
def a64Exit : List UInt8 :=
  [0x40, 0x05, 0x80, 0xd2, 0xa8, 0x0b, 0x80, 0xd2, 0x01, 0x00, 0x00, 0xd4]

/-- One read-execute 64 KiB page at `0x400000`, with 12 bytes of code and the rest zero. -/
def a64Hello : Image where
  segments := [{ vaddr := 0x400000, bytes := a64Exit, memSize := 65536, perm := Perm.rx }]
  entry := 0x400000
  stackSize := 8192

/-- The bytes of an image written for arm64 Linux, or none when the writer refuses it. -/
def a64BytesOf (img : Image) : List UInt8 :=
  match write Config.a64Linux 16 a64top img with
  | .ok bs => bs
  | .error _ => []

def a64HelloBytes : List UInt8 := a64BytesOf a64Hello

#guard a64HelloBytes.length = 2 * 65536
#guard natOfBytes ((a64HelloBytes.drop 18).take 2) = 183
#guard parse Config.a64Linux 16 a64top a64HelloBytes == some a64Hello

-- The writer refuses a segment that is not whole 64 KiB pages, and a layout with 4 KiB pages.
#guard (write Config.a64Linux 16 a64top { a64Hello with
  segments := [{ vaddr := 0x400000, bytes := a64Exit, memSize := 4096, perm := Perm.rx }] }).toBool = false
#guard (write Config.a64Linux 12 a64top a64Hello).toBool = false

/-- arm64 corruptions, each refused by the loader model and each a real change. -/
def a64Corruptions : List (String × List UInt8) :=
  [ ("machine-x64", patchBytes a64HelloBytes 18 (le 62 2)),
    ("tail-nonzero", patchBytes a64HelloBytes (65536 + 12) [0x90]),
    ("filesz-gt-memsz", patchBytes a64HelloBytes (64 + 32) (le 65537 8)),
    ("memsz-part-page", patchBytes a64HelloBytes (64 + 40) (le 4096 8)),
    ("offset-4k", patchBytes a64HelloBytes (64 + 8) (le 0x1000 8)) ]

#guard a64Corruptions.all fun c => (parse Config.a64Linux 16 a64top c.2).isNone
#guard a64Corruptions.all fun c => c.2 != a64HelloBytes

/-! ### Files for `scripts/elf-check.sh` -/

/-- Writes `hello.elf`, `two.elf` and `bad-<name>.elf` into `dir`, prints the loader model's
verdict on each, and returns the number of unexpected verdicts. -/
def emit (dir : System.FilePath) : IO UInt32 := do
  let mut bad : UInt32 := 0
  for (name, img, bs) in [("hello", hello, helloBytes), ("two", two, twoBytes)] do
    IO.FS.writeBinFile (dir / s!"{name}.elf") ⟨bs.toArray⟩
    let ok := parse cfg 12 top bs == some img
    IO.println s!"lean-loader {name}: {if ok then "loads (round trip)" else "WRONG"}"
    if !ok then bad := bad + 1
  for (name, bs) in corruptions do
    IO.FS.writeBinFile (dir / s!"bad-{name}.elf") ⟨bs.toArray⟩
    let refused := (parse cfg 12 top bs).isNone
    IO.println s!"lean-loader bad-{name}: {if refused then "refused" else "ACCEPTED"}"
    if !refused then bad := bad + 1
  return bad

end Millipede.Elf.Tests
