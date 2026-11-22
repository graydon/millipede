import Millipede.Object.MachO.Laws
import Millipede.Object.Obj

/-!
# Tests for the Mach-O writer and loader model

SHA-256 agrees with `sha256sum` on fixed inputs around the block boundaries. Three images are
written for arm64 macOS: `exit(42)`; a program that writes "hi\n" from a read-only segment and
exits with 7; and one that also loads a word from initialised data, stores it in the zero-filled
part and exits with it (5). Each round-trips through the loader model, by the general theorem and
by evaluation. The writer refuses images that break a rule of the platform, and the loader model
refuses each of a list of corrupted files, each of which differs from the valid file.

`emit` writes the files, the model's description of each and the corruptions for
scripts/macho-check.sh, which compares them with `llvm-readobj`, `llvm-objdump`, an independent
check of the signature and a file linked by `ld64.lld`. The checks run by compiled evaluation
with `#guard`, because the kernel cannot evaluate SHA-256 over a whole file in reasonable time.
-/

namespace Millipede.MachO.Tests

open Millipede Millipede.MachO

/-! ### SHA-256 -/

/-- Lowercase hexadecimal. -/
def hex (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let d := Nat.toDigits 16 b.toNat
    String.ofList (if d.length = 1 then '0' :: d else d))

/-- The test input of `n` bytes, byte `i` being `7 i + 3` modulo 256. -/
def pattern (n : Nat) : List UInt8 := (List.range n).map fun i => UInt8.ofNat (7 * i + 3)

-- the expected digests come from `sha256sum`
#guard hex (Sha256.hash []) = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard hex (Sha256.hash [0x61, 0x62, 0x63]) =
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard hex (Sha256.hash (pattern 55)) =
  "e7313d333c272e639f790978283f9eb392e843d0f29b7016828bb1daa4aac70b"
#guard hex (Sha256.hash (pattern 56)) =
  "4324d65f3c103567f5589c710bc08f8523f929a9272e3af36fc968e52abc6c27"
#guard hex (Sha256.hash (pattern 63)) =
  "81c80242132f230c3bd41b3e63bbcff16107339549214a99614ff26664625055"
#guard hex (Sha256.hash (pattern 64)) =
  "39e3d7b6b5d075d37d053ad89b24b41bef4f3c29760c84447cab3f3be1882241"
#guard hex (Sha256.hash (pattern 65)) =
  "aacca6ff74fdbb296d165a45cecfa04e5127bc008770fbbdd48006f2d2fae95e"
#guard hex (Sha256.hash (pattern 119)) =
  "9ce7368e4daf32341631b492e80359dc9f594b48453cd0dd5bf0b19279cc177e"
#guard hex (Sha256.hash (pattern 120)) =
  "7836b787757e95e58b3ca5aec90b1b004e8deba1e50e9675af9cabf1a13a04b5"
#guard hex (Sha256.hash (pattern 128)) =
  "d2742f1f4ac6bb7ca2b239ee18402ba8b3f9f8e652d2a72973c2b9ba11c08cf6"
#guard hex (Sha256.hash (pattern 1000)) =
  "1e9bc38cbf860b9ec31918b065f9b52476c549a782e0e7990bed8ce3868d2371"

/-! ### Images -/

/-- The settings of arm64 macOS. -/
abbrev cfg : Config := Config.a64Macos
/-- The stack top used by the tests. -/
def top : UInt64 := 0x7ff000000000

/-- The code segment's address, one 16 KiB page above `__PAGEZERO` and the header page. -/
def textBase : UInt64 := 0x100004000

/-- `exit(42)`: `mov x0, #42; mov x16, #1; svc #0x80`. -/
def helloCode : List UInt8 :=
  [0x40, 0x05, 0x80, 0xd2, 0x30, 0x00, 0x80, 0xd2, 0x01, 0x10, 0x00, 0xd4]

/-- `write(1, msg, 3); exit(7)`, with `msg` at the start of the read-only segment, four 4 KiB
pages after the code: `mov x0, #1; adrp x1, #0x4000; add x1, x1, #0; mov x2, #3; mov x16, #4;
svc #0x80; mov x0, #7; mov x16, #1; svc #0x80`. -/
def twoCode : List UInt8 :=
  [0x20, 0x00, 0x80, 0xd2, 0x21, 0x00, 0x00, 0x90, 0x21, 0x00, 0x00, 0x91, 0x62, 0x00, 0x80, 0xd2,
   0x90, 0x00, 0x80, 0xd2, 0x01, 0x10, 0x00, 0xd4, 0xe0, 0x00, 0x80, 0xd2, 0x30, 0x00, 0x80, 0xd2,
   0x01, 0x10, 0x00, 0xd4]

/-- As `twoCode` up to the first `svc`, then loads the word at the start of the data segment,
stores it 4 KiB further on in the zero-filled part, loads it back and exits with it:
`…; svc #0x80; adrp x1, #0x8000; add x1, x1, #0; ldr x0, [x1]; add x3, x1, #0x1000;
str x0, [x3]; ldr x0, [x3]; mov x16, #1; svc #0x80`. -/
def threeCode : List UInt8 :=
  [0x20, 0x00, 0x80, 0xd2, 0x21, 0x00, 0x00, 0x90, 0x21, 0x00, 0x00, 0x91, 0x62, 0x00, 0x80, 0xd2,
   0x90, 0x00, 0x80, 0xd2, 0x01, 0x10, 0x00, 0xd4, 0x41, 0x00, 0x00, 0x90, 0x21, 0x00, 0x00, 0x91,
   0x20, 0x00, 0x40, 0xf9, 0x23, 0x04, 0x40, 0x91, 0x60, 0x00, 0x00, 0xf9, 0x60, 0x00, 0x40, 0xf9,
   0x30, 0x00, 0x80, 0xd2, 0x01, 0x10, 0x00, 0xd4]

/-- "hi\n". -/
def msg : List UInt8 := [0x68, 0x69, 0x0a]

def hello : Image where
  segments := [{ vaddr := textBase, bytes := helloCode, memSize := 16384, perm := Perm.rx }]
  entry := textBase
  stackSize := 16384

def two : Image where
  segments := [{ vaddr := textBase, bytes := twoCode, memSize := 16384, perm := Perm.rx },
               { vaddr := 0x100008000, bytes := msg, memSize := 16384, perm := Perm.r_ }]
  entry := textBase
  stackSize := 65536

def three : Image where
  segments := [{ vaddr := textBase, bytes := threeCode, memSize := 16384, perm := Perm.rx },
               { vaddr := 0x100008000, bytes := msg, memSize := 16384, perm := Perm.r_ },
               { vaddr := 0x10000c000, bytes := [5, 0, 0, 0, 0, 0, 0, 0], memSize := 32768,
                 perm := Perm.rw }]
  entry := textBase
  stackSize := 65536

/-- The bytes of a written image, or none when the writer refuses it. -/
def bytesOf (img : Image) : List UInt8 :=
  match write cfg 14 top img with
  | .ok bs => bs
  | .error _ => []

def helloBytes : List UInt8 := bytesOf hello
def twoBytes : List UInt8 := bytesOf two
def threeBytes : List UInt8 := bytesOf three

/-- The round trip by the general theorem. -/
theorem hello_parse (h : write cfg 14 top hello = .ok helloBytes) :
    parse cfg 14 top helloBytes = some (padImage (2 ^ 14) hello) := parse_write h

-- the round trip by evaluation
#guard (write cfg 14 top hello).toBool
#guard parse cfg 14 top helloBytes == some (padImage (2 ^ 14) hello)
#guard parse cfg 14 top twoBytes == some (padImage (2 ^ 14) two)
#guard parse cfg 14 top threeBytes == some (padImage (2 ^ 14) three)
-- the layout: a header page, one page per segment, `__LINKEDIT`
#guard helloBytes.take 4 = [0xcf, 0xfa, 0xed, 0xfe]
#guard (helloBytes.drop 16384).take 12 = helloCode
#guard helloBytes.length = 2 * 16384 + 16 + sigSize (2 * 16384 + 16)
#guard threeBytes.length = 4 * 16384 + 16 + sigSize (4 * 16384 + 16)

/-! ### The writer refuses what the platform cannot load -/

def withSeg (img : Image) (sg : Segment) : Image := { img with segments := [sg] }

-- below `__PAGEZERO` and the header page
#guard !(write cfg 14 top (withSeg hello
  { vaddr := 0x100000000, bytes := helloCode, memSize := 16384, perm := Perm.rx })).toBool
-- a part page of memory
#guard !(write cfg 14 top (withSeg hello
  { vaddr := textBase, bytes := helloCode, memSize := 4096, perm := Perm.rx })).toBool
-- writable and executable
#guard !(write cfg 14 top (withSeg hello
  { vaddr := textBase, bytes := helloCode, memSize := 16384, perm := ⟨true, true, true⟩ })).toBool
-- the first segment is not code
#guard !(write cfg 14 top (withSeg hello
  { vaddr := textBase, bytes := helloCode, memSize := 16384, perm := Perm.r_ })).toBool
-- an entry point outside the code
#guard !(write cfg 14 top { hello with entry := 0x100008000 }).toBool
-- 4 KiB pages
#guard !(write cfg 12 top hello).toBool
-- a stack of part of a page, or too large
#guard !(write cfg 14 top { hello with stackSize := 1000 }).toBool
#guard !(write cfg 14 top { hello with stackSize := 2 ^ 26 }).toBool

/-! ### Corrupted files -/

/-- The `k` little-endian bytes of `n`. -/
abbrev le (n k : Nat) : List UInt8 := natBytes k n

/-- Offsets of load commands in `threeBytes`: the header is 32 bytes, `__PAGEZERO` 72, each
image segment 152, `__LINKEDIT` 72. -/
def textCmd : Nat := 32 + 72
def roCmd : Nat := textCmd + 152
def dataCmd : Nat := roCmd + 152
def linkeditCmd : Nat := dataCmd + 152
def dyldInfoAt : Nat := linkeditCmd + 72
def mainAt : Nat := dyldInfoAt + 48 + 24 + 80 + 32 + 24 + 24

/-- The corruptions, each a name and a patched file. Each except the last four also breaks the
code signature, and `resigned` repairs it. -/
def corruptions : List (String × List UInt8) :=
  [ ("bad-magic",       patchBytes threeBytes 0 [0xce]),
    ("cpu-x86_64",      patchBytes threeBytes 4 (le 0x01000007 4)),
    ("not-pie",         patchBytes threeBytes 24 (le 0x85 4)),
    ("ncmds",           patchBytes threeBytes 16 (le 13 4)),
    ("sizeofcmds",      patchBytes threeBytes 20 (le (linkeditCmd + 72 + 336 - 32) 4)),
    ("pagezero-small",  patchBytes threeBytes (32 + 32) (le 0x1000 8)),
    ("text-fileoff",    patchBytes threeBytes (textCmd + 40) (le 0x4000 8)),
    ("text-wx",         patchBytes threeBytes (textCmd + 60) (le 7 4)),
    ("rodata-exec",     patchBytes threeBytes (roCmd + 56) (le 5 4) |> (patchBytes · (roCmd + 60) (le 5 4))),
    ("data-overlap",    patchBytes threeBytes (dataCmd + 24) (le 0x100008000 8)),
    ("data-misaligned", patchBytes threeBytes (dataCmd + 40) (le 0xc001 8)),
    ("sect-zerofill",   patchBytes threeBytes (dataCmd + 72 + 64) (le 1 4)),
    ("sect-addr",       patchBytes threeBytes (dataCmd + 72 + 32) (le 0x100020000 8)),
    ("sect-size",       patchBytes threeBytes (dataCmd + 72 + 40) (le 0x8000 8)),
    ("dylinker",        patchBytes threeBytes (dyldInfoAt + 48 + 24 + 80 + 12) [0x2e]),
    ("main-entry",      patchBytes threeBytes (mainAt + 8) (le 0x5000 8)),
    ("stack-small",     patchBytes threeBytes (mainAt + 16) (le 0x4000 8)),
    ("code-byte",       patchBytes threeBytes 16384 [0x41]),
    ("data-byte",       patchBytes threeBytes (3 * 16384) [6]),
    ("sig-hash",        patchBytes threeBytes (threeBytes.length - 1)
                          [threeBytes.getD (threeBytes.length - 1) 0 + 1]),
    ("last-page-hash",  patchBytes threeBytes (threeBytes.length - 32) [0]),
    ("truncated",       threeBytes.take (threeBytes.length - 32)),
    ("extended",        threeBytes ++ [0]) ]

#guard corruptions.all fun c => (parse cfg 14 top c.2).isNone
#guard corruptions.all fun c => c.2 != threeBytes

/-- The file offset of `three`'s signature, after the segments and 16 bytes of `__LINKEDIT`. -/
def sigAt : Nat := 4 * 16384 + 16

/-- `three` with its signature recomputed, so that a corruption before the signature leaves a
correctly signed file. -/
def resign (bs : List UInt8) : List UInt8 :=
  bs.take sigAt ++ codeSignature (bs.take sigAt) (2 * 16384)

#guard resign threeBytes == threeBytes

/-- The corruptions that break a rule other than the signature, re-signed, so that only that
rule can refuse them. The changes to code, data, the entry point within the code and the
signature itself make valid files once re-signed, and are left out. -/
def resigned : List (String × List UInt8) :=
  (corruptions.filter fun c => !["main-entry", "code-byte", "data-byte", "sig-hash",
      "last-page-hash", "truncated", "extended"].contains c.1).map
    fun c => (c.1 ++ "-resigned", resign c.2)

#guard resigned.length = 16
#guard resigned.all fun c => (parse cfg 14 top c.2).isNone
-- the re-signed files that are not refused for their own rule would load
#guard ["main-entry", "code-byte", "data-byte"].all fun n =>
  ((corruptions.lookup n).map (parse cfg 14 top ∘ resign)).join.isSome

/-! ### Files for `scripts/macho-check.sh` -/

/-- The model's description of a parsed image, one line per segment with its address, memory
size, bytes in the file and protection, then the entry point and the stack size. -/
def describe (img : Image) : String :=
  let segs := img.segments.map fun sg =>
    s!"segment 0x{String.ofList (Nat.toDigits 16 sg.vaddr.toNat)} {sg.memSize} {sg.bytes.length} " ++
      s!"{protOf sg.perm}\n"
  String.join segs ++ s!"entry 0x{String.ofList (Nat.toDigits 16 img.entry.toNat)}\n" ++
    s!"stack {img.stackSize}\n"

/-- Writes `<name>.macho` and `<name>.model` for the three images and `bad-<name>.macho` for
the corruptions into `dir`, prints the loader model's verdict on each, and returns the number of
unexpected verdicts. -/
def emit (dir : System.FilePath) : IO UInt32 := do
  let mut bad : UInt32 := 0
  for (name, img, bs) in [("hello", hello, helloBytes), ("two", two, twoBytes),
      ("three", three, threeBytes)] do
    IO.FS.writeBinFile (dir / s!"{name}.macho") ⟨bs.toArray⟩
    match parse cfg 14 top bs with
    | some i =>
      IO.FS.writeFile (dir / s!"{name}.model") (describe i)
      let ok := i == padImage (2 ^ 14) img
      IO.println s!"lean-loader {name}: {if ok then "loads (round trip)" else "WRONG"}"
      if !ok then bad := bad + 1
    | none =>
      IO.println s!"lean-loader {name}: REFUSED"
      bad := bad + 1
  for (name, bs) in corruptions ++ resigned do
    IO.FS.writeBinFile (dir / s!"bad-{name}.macho") ⟨bs.toArray⟩
    let refused := (parse cfg 14 top bs).isNone
    IO.println s!"lean-loader bad-{name}: {if refused then "refused" else "ACCEPTED"}"
    if !refused then bad := bad + 1
  return bad

/-- Prints the SHA-256 of each file, as `sha256sum` does. -/
def hashFiles (files : List String) : IO Unit := do
  for f in files do
    let b ← IO.FS.readBinFile f
    IO.println s!"{hex (Sha256.hash b.toList)}  {f}"

end Millipede.MachO.Tests
