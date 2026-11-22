import Tests.ElfRel
import Millipede.Object.ElfRel.Objects
import Millipede.Top.Examples

/-!
# Files for scripts/elfrel-check.sh

`emit dir` writes, for each object, its relocatable file `NAME.o`, the description `NAME.desc`
of the object the file should hold, which is the object with its local symbols first, and the
reader model's description of the file `NAME.model`, or `refused`. The script compares both the
model's and an independent reader's view of the file with `NAME.desc`, so a writer bug that both
readers see alike is still caught. The objects are the four hand-made ones of
Tests/ElfRel.lean and those of the programs `hello`, `sum` and `revchunks` for both targets, from
`Compile.objLink`, and the emitter checks that `Compile.objects` writes the same bytes. For each
program it also writes the entry symbol `NAME.entry` and the executable `NAME.mp` that
Millipede's own linker and ELF writer make from the same object, so the script can compare it
with what the system linker makes. `consts.txt` lists the constants and relocation types the
writer uses, by their names in `<elf.h>`.

With `--seeds`, it writes the same files once per seeded bug into `dir/SEED/`, where `none` is no
bug. The seeds are the following:

* `reltype` writes x86-64 `pc32` as `R_X86_64_32` and arm64 `page21` as `R_AARCH64_ADR_PREL_LO21`;
* `addend` drops every addend;
* `textflags` writes `.text` without `SHF_EXECINSTR`;
* `machine` writes `e_machine = EM_386` in x86-64 files;
* `symorder` writes the symbol table's `sh_info` as 1, which claims that only the null symbol is
  local;
* `symglobal` makes every relocation against a global symbol name the next symbol instead;
* `bssndx` gives every symbol of a `bss` section the section number of the section before it.
-/

namespace Millipede.ElfRel.Emit

open Millipede Millipede.ElfRel Millipede.ElfRel.Tests

/-- The seeded bugs, as a machine table, a change to the object and a change to the bytes. -/
structure Seed where
  name : String
  mach : Mach → Mach := id
  obj : Obj → Obj := id
  bytes : Mach → List UInt8 → List UInt8 := fun _ bs => bs

/-- The relocation types of seed `reltype`. -/
def badRelType (m : Mach) : RelocKind → Option Nat
  | .pc32 => if m.em = EM_X86_64 then some 10 else m.relType .pc32
  | .word .page21 => some R_AARCH64_ADR_PREL_LO21
  | k => m.relType k

/-- The section header table as `(type, offset)` for each header. -/
def shdrsOf (bs : List UInt8) : List (Nat × Nat) :=
  let shoff := fieldAt bs 40 8
  (List.range (fieldAt bs 60 2)).map fun k =>
    (fieldAt bs (shoff + 64 * k + 4) 4, fieldAt bs (shoff + 64 * k + 24) 8)

/-- The file offset of the symbol table, and its number of entries. -/
def symtabOf (bs : List UInt8) : Nat × Nat :=
  let shoff := fieldAt bs 40 8
  match (List.range (fieldAt bs 60 2)).find? (fun k => fieldAt bs (shoff + 64 * k + 4) 4 == SHT_SYMTAB) with
  | some k => (fieldAt bs (shoff + 64 * k + 24) 8, fieldAt bs (shoff + 64 * k + 32) 8 / 24)
  | none => (0, 0)

/-- Seed `symglobal`: each relocation entry whose symbol is global names the next symbol. -/
def bumpGlobalRefs (bs : List UInt8) : List UInt8 :=
  let (st, _) := symtabOf bs
  let shoff := fieldAt bs 40 8
  (List.range (fieldAt bs 60 2)).foldl (fun bs k =>
    if fieldAt bs (shoff + 64 * k + 4) 4 == SHT_RELA then
      let off := fieldAt bs (shoff + 64 * k + 24) 8
      (List.range (fieldAt bs (shoff + 64 * k + 32) 8 / 24)).foldl (fun bs i =>
        let e := off + 24 * i
        let sym := fieldAt bs (e + 12) 4
        if fieldAt bs (st + 24 * sym + 4) 1 / 16 == STB_GLOBAL then setField bs (e + 12) 4 (sym + 1)
        else bs) bs
    else bs) bs

/-- Seed `bssndx`: each symbol in a `SHT_NOBITS` section gets the number of the section before. -/
def lowerBssNdx (bs : List UInt8) : List UInt8 :=
  let (st, n) := symtabOf bs
  let types := (shdrsOf bs).map (·.1)
  (List.range n).foldl (fun bs i =>
    let ndx := fieldAt bs (st + 24 * i + 6) 2
    if 0 < ndx && types[ndx]? == some SHT_NOBITS then setField bs (st + 24 * i + 6) 2 (ndx - 1)
    else bs) bs

def seeds : List Seed :=
  [ { name := "none" },
    { name := "reltype", mach := fun m => { m with relType := badRelType m } },
    { name := "addend", obj := fun o => { o with relocs := o.relocs.map ({ · with addend := 0 }) } },
    { name := "textflags", bytes := fun _ bs => setField bs (fieldAt bs 40 8 + 64 + 8) 8 SHF_ALLOC },
    { name := "machine",
      bytes := fun m bs => if m.em = EM_X86_64 then setField bs 18 2 3 else bs },
    { name := "symorder", bytes := fun _ bs =>
      -- the symbol table is the only section of type 2; find its header
      let shoff := fieldAt bs 40 8
      let n := fieldAt bs 60 2
      match (List.range n).find? (fun k => fieldAt bs (shoff + 64 * k + 4) 4 == SHT_SYMTAB) with
      | some k => setField bs (shoff + 64 * k + 44) 4 1
      | none => bs },
    { name := "symglobal", bytes := fun _ bs => bumpGlobalRefs bs },
    { name := "bssndx", bytes := fun _ bs => lowerBssNdx bs } ]

def writeObj (dir : System.FilePath) (s : Seed) (m : Mach) (name : String) (o : Obj) :
    IO Bool := do
  match write (s.mach m) (s.obj o) with
  | .error e =>
    IO.println s!"emit {s.name}/{name}: writer refused: {e}"
    return false
  | .ok bs =>
    let bs := s.bytes m bs
    IO.FS.writeBinFile (dir / s!"{name}.o") ⟨bs.toArray⟩
    IO.FS.writeFile (dir / s!"{name}.desc") (describe o.norm)
    IO.FS.writeFile (dir / s!"{name}.model") (match read m bs with
      | some o' => describe o'
      | none => "refused\n")
    return true

def consts : List (String × Nat) :=
  [ ("ET_REL", ET_REL), ("EM_X86_64", x64.em), ("EM_AARCH64", a64.em),
    ("SHT_PROGBITS", SHT_PROGBITS), ("SHT_SYMTAB", SHT_SYMTAB), ("SHT_STRTAB", SHT_STRTAB),
    ("SHT_RELA", SHT_RELA), ("SHT_NOBITS", SHT_NOBITS), ("SHF_WRITE", SHF_WRITE),
    ("SHF_ALLOC", SHF_ALLOC), ("SHF_EXECINSTR", SHF_EXECINSTR), ("SHF_INFO_LINK", SHF_INFO_LINK),
    ("STB_LOCAL", STB_LOCAL), ("STB_GLOBAL", STB_GLOBAL), ("STT_NOTYPE", STT_NOTYPE),
    ("STT_OBJECT", STT_OBJECT), ("STT_FUNC", STT_FUNC), ("STT_SECTION", STT_SECTION),
    ("STT_FILE", STT_FILE),
    ("R_X86_64_PC32", (x64.relType .pc32).getD 0), ("R_X86_64_64", (x64.relType .abs64).getD 0),
    ("R_X86_64_PLT32", R_X86_64_PLT32),
    ("R_AARCH64_ABS64", (a64.relType .abs64).getD 0),
    ("R_AARCH64_PREL32", (a64.relType .pc32).getD 0),
    ("R_AARCH64_CALL26", (a64.relType (.word .branch26)).getD 0),
    ("R_AARCH64_JUMP26", R_AARCH64_JUMP26),
    ("R_AARCH64_CONDBR19", (a64.relType (.word .cond19)).getD 0),
    ("R_AARCH64_LD_PREL_LO19", R_AARCH64_LD_PREL_LO19),
    ("R_AARCH64_ADR_PREL_LO21", (a64.relType (.word .adr21)).getD 0),
    ("R_AARCH64_ADR_PREL_PG_HI21", (a64.relType (.word .page21)).getD 0),
    ("R_AARCH64_ADD_ABS_LO12_NC", (a64.relType (.word (.lo12 0))).getD 0),
    ("R_AARCH64_LDST8_ABS_LO12_NC", R_AARCH64_LDST8_ABS_LO12_NC),
    ("R_AARCH64_LDST16_ABS_LO12_NC", (a64.relType (.word (.lo12 1))).getD 0),
    ("R_AARCH64_LDST32_ABS_LO12_NC", (a64.relType (.word (.lo12 2))).getD 0),
    ("R_AARCH64_LDST64_ABS_LO12_NC", (a64.relType (.word (.lo12 3))).getD 0),
    ("R_AARCH64_LDST128_ABS_LO12_NC", (a64.relType (.word (.lo12 4))).getD 0) ]

/-- The programs whose objects the script links with the system linker. -/
def programs : List String := ["hello", "sum", "revchunks"]

/-- Writes the files of every object with seed `s` into `dir`, given the programs' objects. -/
def emitWith (dir : System.FilePath) (s : Seed)
    (progs : List (String × Mach × Obj × String × Except String (List UInt8))) : IO UInt32 := do
  IO.FS.createDirAll dir
  let mut bad : UInt32 := 0
  for (name, m, o) in [("mix-x64", x64, mixX64), ("mix-a64", a64, mixA64), ("c-x64", x64, cX64),
      ("c-a64", a64, cA64)] do
    unless ← writeObj dir s m name o do bad := bad + 1
  for (name, m, o, entry, exe) in progs do
    unless ← writeObj dir s m name o do bad := bad + 1
    IO.FS.writeFile (dir / s!"{name}.entry") (entry ++ "\n")
    match exe with
    | .ok bs =>
      IO.FS.writeBinFile (dir / s!"{name}.mp") ⟨bs.toArray⟩
      IO.setAccessRights (dir / s!"{name}.mp")
        { user := { read := true, write := true, execution := true } }
    | .error e => IO.println s!"emit {name}: {e}"; bad := bad + 1
  return bad

def emit (args : List String) : IO UInt32 := do
  match args with
  | dir :: rest =>
    let dir : System.FilePath := dir
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / "consts.txt")
      (String.join (consts.map fun (n, v) => s!"{n} {v}\n"))
    let mut progs := []
    for p in programs do
      for (t, m, a) in [(x64Linux, x64, "x64"), (arm64Linux, a64, "a64")] do
        match Examples.registry.find? (·.name == p) with
        | none => IO.println s!"emit: no program {p}"; return 1
        | some e =>
          match Compile.objLink e.prog t, Compile.objects e.prog t with
          | .ok (o, cfg), .ok [("prog.o", b)] =>
            -- `Compile.objects` writes exactly the object that `objLink` gives
            unless b.data.toList == ((write m o).toOption.getD []) do
              IO.println s!"emit {p}-{a}: Compile.objects differs from the written object"
              return 1
            progs := progs ++ [(s!"{p}-{a}", m, o, cfg.entry, (Link.link cfg [o]).bind t.fmt.write)]
          | .error err, _ | _, .error err => IO.println s!"emit {p}-{a}: {err}"; return 1
          | _, _ => IO.println s!"emit {p}-{a}: Compile.objects gave other files"; return 1
    let mut bad : UInt32 := 0
    if rest = ["--seeds"] then
      for s in seeds do
        bad := bad + (← emitWith (dir / s.name) s progs)
    else
      bad := bad + (← emitWith dir {name := "none"} progs)
    return bad
  | [] => return 2

end Millipede.ElfRel.Emit
