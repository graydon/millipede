import Millipede.Object.ElfRel.Laws

/-!
# Tests for the ELF64 relocatable-object writer and reader model

Four hand-made objects, two per machine:

* `mixX64` and `mixA64` have a `text`, `rodata`, `data` and `bss` section, global symbols listed
  before local ones, relocations in `text` and in `data`, a negative and a positive addend, and a
  reference to `ext_fn`, which no symbol defines.
* `cX64` and `cA64` are `_start: c_add(40, 2); exit(result)`, the code calling the C function
  `c_add`, which scripts/elfrel-check.sh links against a C object.

Each is written and read back by evaluation and compared with the object with its local symbols
first, as `read_write` states. The fixed header fields and relocation types of a written file
hold the numbers of the gABI and the processor supplements at their offsets (`specFields`,
`specRelocs`). The writer refuses objects it cannot represent, the reader refuses 29 corrupted
files, each different from the valid file, and it accepts 5 variants that the writer never makes
but the specification allows, such as `R_X86_64_PLT32` in place of `R_X86_64_PC32`. Two seeded
bugs, a machine table that writes `pc32` as `R_X86_64_64` and a writer that drops the addends,
are caught by these checks. `describe` gives the reader model's view of a file for the script.
-/

namespace Millipede.ElfRel.Tests

open Millipede Millipede.ElfRel

/-- Two objects are equal. -/
def objEq (a b : Obj) : Bool := a.sections == b.sections && a.symbols == b.symbols && a.relocs == b.relocs

/-- The file reads back as the object with its local symbols first. -/
def roundTrip (wm rm : Mach) (o : Obj) : Bool :=
  match write wm o with
  | .ok bs => match read rm bs with
    | some o' => objEq o' o.norm
    | none => false
  | .error _ => false

/-! ### Hand-made objects -/

/-- An object with every kind of section, for x86-64. -/
def mixX64 : Obj where
  sections := [⟨".text", .text, 16, [0x48, 0x8d, 0x05, 0, 0, 0, 0, 0xe8, 0, 0, 0, 0, 0xe8, 0, 0, 0, 0,
                0xc3], 0⟩,
               ⟨".rodata", .rodata, 8, [104, 105, 10], 0⟩,
               ⟨".data", .data, 8, List.replicate 16 0, 0⟩,
               ⟨".bss", .bss, 16, [], 32⟩]
  symbols := [⟨"g_main", 0, 0, true⟩, ⟨"l_str", 1, 0, false⟩, ⟨"g_data", 2, 0, true⟩,
              ⟨"l_buf", 3, 0, false⟩]
  relocs := [⟨0, 3, .pc32, "l_str", -4⟩, ⟨0, 8, .pc32, "ext_fn", -4⟩, ⟨0, 13, .pc32, "ext_fn", -4⟩,
             ⟨2, 0, .abs64, "l_buf", 8⟩, ⟨2, 8, .abs64, "g_main", 0⟩]

/-- An object with every kind of section and every fixup the arm64 assembler emits, for AArch64. -/
def mixA64 : Obj where
  sections := [⟨".text", .text, 16, [0x00, 0x00, 0x00, 0x90, 0x00, 0x00, 0x00, 0x91,
                0x00, 0x00, 0x40, 0xf9, 0x00, 0x00, 0x00, 0x94, 0xc0, 0x03, 0x5f, 0xd6], 0⟩,
               ⟨".rodata", .rodata, 8, [104, 105, 10, 0, 0, 0, 0, 0], 0⟩,
               ⟨".data", .data, 8, List.replicate 16 0, 0⟩,
               ⟨".bss", .bss, 16, [], 32⟩]
  symbols := [⟨"g_main", 0, 0, true⟩, ⟨"l_str", 1, 0, false⟩, ⟨"g_data", 2, 0, true⟩,
              ⟨"l_buf", 3, 0, false⟩]
  relocs := [⟨0, 0, .word .page21, "l_str", 0⟩, ⟨0, 4, .word (.lo12 0), "l_str", 0⟩,
             ⟨0, 8, .word (.lo12 3), "l_str", 0⟩, ⟨0, 12, .word .branch26, "ext_fn", 0⟩,
             ⟨2, 0, .abs64, "l_buf", 8⟩, ⟨2, 8, .abs64, "g_main", -16⟩]

/-- `_start: c_add(40, 2); exit(result)` for x86-64. -/
def cX64 : Obj where
  sections := [⟨".text", .text, 16, [0xbf, 40, 0, 0, 0, 0xbe, 2, 0, 0, 0, 0xe8, 0, 0, 0, 0,
                0x89, 0xc7, 0xb8, 60, 0, 0, 0, 0x0f, 0x05], 0⟩]
  symbols := [⟨"_start", 0, 0, true⟩]
  relocs := [⟨0, 11, .pc32, "c_add", -4⟩]

/-- `_start: c_add(40, 2); exit(result)` for AArch64: `mov w0, #40; mov w1, #2; bl c_add;
mov x8, #93; svc #0`. -/
def cA64 : Obj where
  sections := [⟨".text", .text, 16, natBytes 4 0x52800500 ++ natBytes 4 0x52800041 ++
                natBytes 4 0x94000000 ++ natBytes 4 0xd2800ba8 ++ natBytes 4 0xd4000001, 0⟩]
  symbols := [⟨"_start", 0, 0, true⟩]
  relocs := [⟨0, 8, .word .branch26, "c_add", 0⟩]

#guard roundTrip x64 x64 mixX64
#guard roundTrip a64 a64 mixA64
#guard roundTrip x64 x64 cX64
#guard roundTrip a64 a64 cA64
-- the symbols come back with the local ones first
#guard ((write x64 mixX64).toOption.bind (read x64)).map (·.symbols.map (·.name)) =
  some ["l_str", "l_buf", "g_main", "g_data"]
-- a file of one machine is refused by the reader of the other
#guard ((write x64 mixX64).toOption.bind (read a64)).isNone
#guard ((write a64 mixA64).toOption.bind (read x64)).isNone

/-- The bytes of a written object. -/
def bytesOf (m : Mach) (o : Obj) : List UInt8 := ((write m o).toOption).getD []

def mixX64Bytes : List UInt8 := bytesOf x64 mixX64
def mixA64Bytes : List UInt8 := bytesOf a64 mixA64

/-! ### Fixed values against the specification -/

/-- Little-endian field at an offset. -/
def fieldAt (bs : List UInt8) (off w : Nat) : Nat := natOfBytes ((bs.drop off).take w)

/-- The fixed ELF header fields of an x86-64 relocatable object, as offset, width and value, from
the gABI's layout of `Elf64_Ehdr`: the magic, `ELFCLASS64`, `ELFDATA2LSB`, `EV_CURRENT`,
`ELFOSABI_SYSV`, then `e_type = ET_REL`, `e_machine = EM_X86_64`, `e_version`, `e_entry`,
`e_phoff`, `e_flags`, `e_ehsize`, `e_phnum` and `e_shentsize`. -/
def specFields (machine : Nat) : List (Nat × Nat × Nat) :=
  [ (0, 4, 0x464c457f), (4, 1, 2), (5, 1, 1), (6, 1, 1), (7, 1, 0),
    (16, 2, 1), (18, 2, machine), (20, 4, 1), (24, 8, 0), (32, 8, 0), (48, 4, 0), (52, 2, 64),
    (56, 2, 0), (58, 2, 64) ]

#guard (specFields 62).all fun (off, w, v) => fieldAt mixX64Bytes off w = v
#guard (specFields 183).all fun (off, w, v) => fieldAt mixA64Bytes off w = v

/-- Section header `k` of a file, from `e_shoff` at offset 40 and 64-byte headers. -/
def shdrAt (bs : List UInt8) (k : Nat) (field w : Nat) : Nat :=
  fieldAt bs (fieldAt bs 40 8 + 64 * k + field) w

/-- The section headers of `mixX64`, by the gABI's `Elf64_Shdr` offsets: `sh_type` at 4,
`sh_flags` at 8, `sh_link` at 40, `sh_info` at 44, `sh_addralign` at 48 and `sh_entsize` at 56.
`.text` is `SHT_PROGBITS` with `SHF_ALLOC | SHF_EXECINSTR`, `.rodata` has `SHF_ALLOC`, `.data`
`SHF_ALLOC | SHF_WRITE`, `.bss` is `SHT_NOBITS`, `.symtab` is `SHT_SYMTAB` with 24-byte entries,
the string tables are `SHT_STRTAB`, and `.rela.text` is `SHT_RELA` with `SHF_INFO_LINK`, 24-byte
entries, the symbol table as link and `.text` as info. -/
def specShdrs : List (Nat × Nat × Nat × Nat) :=
  [ (1, 4, 4, 1), (1, 8, 8, 6), (1, 48, 8, 16), (2, 4, 4, 1), (2, 8, 8, 2), (3, 4, 4, 1),
    (3, 8, 8, 3), (4, 4, 4, 8), (4, 8, 8, 3), (6, 4, 4, 2), (6, 56, 8, 24), (6, 40, 4, 7),
    (7, 4, 4, 3), (8, 4, 4, 3), (9, 4, 4, 4), (9, 8, 8, 0x40), (9, 56, 8, 24), (9, 40, 4, 6),
    (9, 44, 4, 1) ]

#guard specShdrs.all fun (k, f, w, v) => shdrAt mixX64Bytes k f w = v
-- e_shstrndx names the section-name table, section 8
#guard fieldAt mixX64Bytes 62 2 = 8

/-- The first relocation entry of `.rela.text`: `r_info` at offset 8 holds the symbol index in its
high 32 bits and the type in its low 32 bits, and `r_addend` at 16 is signed. -/
def relaAt (bs : List UInt8) (k field w : Nat) : Nat :=
  fieldAt bs (shdrAt bs 9 24 8 + 24 * k + field) w

-- `lea rax, [rip + l_str]` is `R_X86_64_PC32` against symbol 1 with addend -4
#guard relaAt mixX64Bytes 0 0 8 = 3
#guard relaAt mixX64Bytes 0 8 8 = 1 * 2 ^ 32 + 2
#guard relaAt mixX64Bytes 0 16 8 = 2 ^ 64 - 4
-- `g_main` is a global function, `st_info = STB_GLOBAL << 4 | STT_FUNC`, in section 1
#guard fieldAt mixX64Bytes (shdrAt mixX64Bytes 6 24 8 + 24 * 3 + 4) 1 = 0x12
#guard fieldAt mixX64Bytes (shdrAt mixX64Bytes 6 24 8 + 24 * 3 + 6) 2 = 1

/-- The relocation types of the processor supplements for each kind the assembler emits: the
x86-64 psABI's `R_X86_64_PC32` (2) and `R_X86_64_64` (1), and ARM IHI 0056's `R_AARCH64_ABS64`
(257), `PREL32` (261), `ADR_PREL_LO21` (274), `ADR_PREL_PG_HI21` (275), `ADD_ABS_LO12_NC`
(277), `CONDBR19` (280), `CALL26` (283) and `LDST16`, `LDST32`, `LDST64` and `LDST128_ABS_LO12_NC`
(284, 285, 286, 299). -/
def specRelocs : List (Bool × RelocKind × Nat) :=
  [ (true, .pc32, 2), (true, .abs64, 1),
    (false, .abs64, 257), (false, .pc32, 261), (false, .word .adr21, 274),
    (false, .word .page21, 275), (false, .word (.lo12 0), 277), (false, .word .cond19, 280),
    (false, .word .branch26, 283), (false, .word (.lo12 1), 284), (false, .word (.lo12 2), 285),
    (false, .word (.lo12 3), 286), (false, .word (.lo12 4), 299) ]

/-- The machine tables give the specification's numbers. -/
def specRelocsOk (mx ma : Mach) : Bool :=
  mx.em == 62 && ma.em == 183 &&
  specRelocs.all fun (isX, k, t) => (if isX then mx else ma).relType k == some t

#guard specRelocsOk x64 a64
-- the aliases the reader accepts, from the same tables
#guard x64.relKind 4 = some .pc32
#guard a64.relKind 282 = some (.word .branch26)
#guard a64.relKind 273 = some (.word .cond19)
#guard a64.relKind 278 = some (.word (.lo12 0))
-- an x86-64 type the format does not use, `R_X86_64_GOTPCREL`, and an arm64 fixup with no type
#guard x64.relKind 9 = none
#guard a64.relType (.word (.lo12 5)) = none

/-! ### Seeded bugs -/

/-- A machine table that writes `pc32` as `R_X86_64_64`. -/
def x64Bad : Mach := { x64 with relType := fun k => if k = .pc32 then some 1 else x64.relType k }

#guard !roundTrip x64Bad x64 mixX64
#guard !specRelocsOk x64Bad a64

/-- A writer that drops the addends. -/
def dropAddends (o : Obj) : Obj := { o with relocs := o.relocs.map fun r => { r with addend := 0 } }

#guard !(match write x64 (dropAddends mixX64) with
  | .ok bs => (read x64 bs).map (objEq · mixX64.norm) == some true
  | .error _ => false)

/-! ### The writer refuses what the format cannot represent -/

def refused (m : Mach) (o : Obj) : Bool := (write m o).toBool = false

-- a `bss` section with bytes, and a `data` section with a zero-filled tail
#guard refused x64 { mixX64 with sections := mixX64.sections.set 3 ⟨".bss", .bss, 16, [1], 32⟩ }
#guard refused x64 { mixX64 with sections := mixX64.sections.set 2 ⟨".data", .data, 8, [1], 8⟩ }
-- a `data` section named `.text`, which GNU ld would place with the code, and a name that is
-- no standard one
#guard refused x64 { mixX64 with sections := mixX64.sections.set 2 ⟨".text", .data, 8, [1], 0⟩ }
#guard refused x64 { mixX64 with sections := mixX64.sections.set 2 ⟨".tdata", .data, 8, [1], 0⟩ }
#guard roundTrip x64 x64
  { mixX64 with sections := mixX64.sections.set 0 { mixX64.sections[0]! with name := ".text.hot" } }
-- an alignment of 3
#guard refused x64 { mixX64 with sections := mixX64.sections.set 1 ⟨".rodata", .rodata, 3, [1], 0⟩ }
-- two symbols named alike, an empty name, a name with a NUL byte
#guard refused x64 { mixX64 with symbols := ⟨"g_main", 1, 0, false⟩ :: mixX64.symbols }
#guard refused x64 { mixX64 with symbols := ⟨"", 1, 0, false⟩ :: mixX64.symbols }
#guard refused x64 { mixX64 with symbols := ⟨"a\x00b", 1, 0, false⟩ :: mixX64.symbols }
#guard refused x64 { mixX64 with sections := ⟨".te\x00xt", .text, 1, [], 0⟩ :: mixX64.sections.tail }
-- a symbol and a relocation in a missing section
#guard refused x64 { mixX64 with symbols := ⟨"x", 4, 0, false⟩ :: mixX64.symbols }
#guard refused x64 { mixX64 with relocs := ⟨4, 0, .abs64, "x", 0⟩ :: mixX64.relocs }
-- an arm64 fixup in an x86-64 object, and an arm64 fixup with no relocation type
#guard refused x64 { mixX64 with relocs := ⟨0, 0, .word .branch26, "g_main", 0⟩ :: mixX64.relocs }
#guard refused a64 { mixA64 with relocs := ⟨0, 0, .word (.lo12 5), "g_main", 0⟩ :: mixA64.relocs }
-- relocations of `.text` in two runs, and an addend outside 64 bits
#guard refused x64 { mixX64 with relocs := mixX64.relocs ++ [⟨0, 3, .pc32, "l_str", -4⟩] }
#guard refused x64 { mixX64 with relocs := ⟨0, 3, .pc32, "l_str", 2 ^ 63⟩ :: mixX64.relocs.tail }
-- but an object with no symbols, no relocations or no sections is written
#guard roundTrip x64 x64 ⟨[], [], []⟩
#guard roundTrip x64 x64 { mixX64 with relocs := [] }

/-! ### The reader -/

/-- `bs` with the `w`-byte field at `off` set to `v`. -/
def setField (bs : List UInt8) (off w v : Nat) : List UInt8 := patchBytes bs off (natBytes w v)

/-- Offsets in `mixX64Bytes`: section header `k`'s field, symbol `k`'s field and relocation
`k`'s field. -/
def shOff (k field : Nat) : Nat := fieldAt mixX64Bytes 40 8 + 64 * k + field
def symOff (k field : Nat) : Nat := shdrAt mixX64Bytes 6 24 8 + 24 * k + field
def relOff (k field : Nat) : Nat := shdrAt mixX64Bytes 9 24 8 + 24 * k + field

/-- Corrupted files, each breaking one rule of the reader. The symbol table of `mixX64` holds the
null symbol, `l_str`, `l_buf`, `g_main`, `g_data` and the undefined `ext_fn`. -/
def corruptions : List (String × List UInt8) :=
  let bs := mixX64Bytes
  [ ("type-exec", setField bs 16 2 2),
    ("machine", setField bs 18 2 183),
    ("class32", setField bs 4 1 1),
    ("version", setField bs 20 4 2),
    ("phnum", setField bs 56 2 1),
    ("shstrndx", setField bs 62 2 1),
    ("shnum-zero", setField bs 60 2 0),
    ("truncated", bs.take (bs.length - 10)),
    ("null-header", setField bs (shOff 0 4) 4 1),
    ("text-merge", setField bs (shOff 1 8) 8 0x16),
    ("text-writable", setField bs (shOff 1 8) 8 3),
    ("nobits-exec", setField bs (shOff 4 8) 8 7),
    ("align3", setField bs (shOff 2 48) 8 3),
    ("rel-not-rela", setField bs (shOff 9 4) 4 9),
    ("two-symtabs", setField bs (shOff 5 4) 4 2),
    ("symtab-info", setField bs (shOff 6 44) 4 1),
    ("symtab-entsize", setField bs (shOff 6 56) 8 16),
    ("strtab-cut", setField bs (shOff 7 32) 8 (shdrAt bs 7 32 8 - 1)),
    ("rela-info", setField bs (shOff 9 44) 4 6),
    ("rela-link", setField bs (shOff 9 40) 4 7),
    ("sym-hidden", setField bs (symOff 3 5) 1 2),
    ("sym-weak", setField bs (symOff 4 4) 1 0x21),
    ("sym-abs", setField bs (symOff 3 6) 2 0xfff1),
    ("undef-local", setField (setField bs (symOff 5 4) 1 0) (shOff 6 44) 4 6),
    ("undef-clash", setField bs (symOff 5 0) 4 (fieldAt bs (symOff 3 0) 4)),
    ("rel-type", setField bs (relOff 0 8) 4 9),
    ("rel-sym0", setField bs (relOff 0 12) 4 0),
    ("rel-sym-range", setField bs (relOff 0 12) 4 99),
    ("rel-section-sym", setField (setField bs (symOff 2 4) 1 3) (symOff 2 0) 4 0) ]

#guard corruptions.all fun (_, c) => c != mixX64Bytes && (read x64 c).isNone

/-- Variants that the writer never makes and the specification allows, each read as `mixX64`:
`R_X86_64_PLT32`, a relocation section without `SHF_INFO_LINK`, `.note.GNU-stack` with the
flags of `.comment`, and a function symbol of type `STT_NOTYPE`. -/
def variants : List (String × List UInt8) :=
  let bs := mixX64Bytes
  [ ("plt32", setField bs (relOff 1 8) 4 4),
    ("no-info-link", setField bs (shOff 9 8) 8 0),
    ("note-merge", setField bs (shOff 5 8) 8 0x30),
    ("notype", setField bs (symOff 3 4) 1 0x10) ]

#guard variants.all fun (_, c) => c != mixX64Bytes &&
  (read x64 c).map (objEq · mixX64.norm) == some true

-- `R_AARCH64_JUMP26` reads as `CALL26`
#guard (read a64 (setField mixA64Bytes (fieldAt mixA64Bytes 40 8 + 64 * 9 + 0 |> fun h =>
    fieldAt mixA64Bytes (h + 24) 8 + 24 * 3 + 8) 4 282)).map (objEq · mixA64.norm) == some true

/-! ### Descriptions for the script -/

def hexBytes (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let d := fun (n : Nat) => "0123456789abcdef".toList.getD n '0'
    String.ofList [d (b.toNat / 16), d (b.toNat % 16)])

def kindName : SecKind → String
  | .text => "text" | .rodata => "rodata" | .data => "data" | .bss => "bss"

def relocName : RelocKind → String
  | .pc32 => "pc32"
  | .abs64 => "abs64"
  | .word .branch26 => "branch26"
  | .word .cond19 => "cond19"
  | .word .adr21 => "adr21"
  | .word .page21 => "page21"
  | .word (.lo12 s) => s!"lo12.{s}"

/-- One line per section, symbol and relocation, in the reader model's order. -/
def describe (o : Obj) : String :=
  String.join (o.sections.map fun s =>
    s!"section {s.name} {kindName s.kind} {s.align} {s.size} {hexBytes s.bytes}\n") ++
  String.join (o.symbols.map fun s =>
    s!"symbol {s.name} {s.sec} {s.offset} {if s.global then "global" else "local"}\n") ++
  String.join (o.relocs.map fun r =>
    s!"reloc {r.sec} {r.offset} {relocName r.kind} {r.sym} {r.addend}\n")

end Millipede.ElfRel.Tests
