import Millipede.Object.ElfRel.Format

/-!
# The ELF64 relocatable-object writer

`ElfRel.write m o` serialises an `Obj` as an ELF64 relocatable object (`ET_REL`) for machine `m`,
laid out as follows:

```
offset 0      ELF header (64 bytes), no program headers
offset 64     the contents of the sections below, each at an offset aligned to its alignment
              (NOBITS sections take no file space)
then          the section-header table, at an offset aligned to 8
```

The section-header table holds, in this order, the null header; one header per section of the
`Obj`, in order, so section `i` of the `Obj` is ELF section `i + 1`; `.note.GNU-stack`, which is
empty and tells the linker that the code needs no executable stack; `.symtab`; `.strtab`;
`.shstrtab`, which holds the section names; and one `.rela<name>` section per run of
relocations of the same section, in the order of the `Obj`'s relocation list.

A `text` section is `SHT_PROGBITS` with the flags `SHF_ALLOC | SHF_EXECINSTR`, `rodata` has
`SHF_ALLOC` only and `data` has `SHF_ALLOC | SHF_WRITE`. A `bss` section is `SHT_NOBITS` with
`SHF_ALLOC | SHF_WRITE` and its `bssSize` as its size. A section's alignment is its
`sh_addralign`.

The symbol table holds the null symbol, the local symbols of the `Obj`, its global symbols, and
then one undefined global symbol for each name that a relocation refers to and no symbol of the
`Obj` defines, in the order of first reference. `sh_info` is one more than the number of local
symbols, as the gABI requires. A defined symbol's `st_value` is its offset in its section, and its
type is `STT_FUNC` in a `text` section and `STT_OBJECT` elsewhere. A relocation entry names the
symbol of its name, its type is the machine's type for its kind, and its addend is the `Obj`'s.

The writer refuses an `Obj` that the format cannot represent exactly. These are the following:

* a relocation kind that the machine has no type for, such as an arm64 fixup in an x86-64 object;
* a `bss` section with bytes, or a section of another kind with a zero-filled tail;
* a section whose name does not fit its kind, such as a `data` section named `.text`, because a
  system linker places a section by its name;
* an alignment that is neither 0 nor a power of 2;
* two symbols with the same name, or a symbol with an empty name, since ELF resolves a
  relocation by the symbol's index while an `Obj` resolves it by its name;
* a name that contains a NUL byte;
* a symbol or relocation in a section that does not exist;
* two runs of relocations of the same section, since a section has at most one relocation
  section;
* an addend outside the signed 64-bit range, and any field that does not fit its width.
-/

namespace Millipede.ElfRel

open Elf (fits zeros)
open Link (alignUp)

/-- One section of the output, with its contents in the file. -/
structure Out where
  name : String
  type : Nat
  flags : Nat
  link : Nat := 0
  info : Nat := 0
  align : Nat
  entsize : Nat := 0
  bytes : List UInt8
  /-- `sh_size`, which is `bytes.length` except for `SHT_NOBITS` -/
  size : Nat

/-- The header of `o` with its name at offset `n` of `.shstrtab` and its contents at file offset
`off`. -/
def Out.hdr (o : Out) (n off : Nat) : Shdr :=
  ⟨n, o.type, o.flags, 0, off, o.size, o.link, o.info, o.align, o.entsize⟩

/-- The contents of the sections placed from file offset `cur`, each at an offset aligned to its
alignment, with zeros in the gaps. -/
def lay : Nat → List Out → List UInt8
  | _, [] => []
  | cur, o :: os =>
    zeros (alignUp cur o.align - cur) ++ o.bytes ++ lay (alignUp cur o.align + o.bytes.length) os

/-- The file offset just after the contents placed from `cur`. -/
def layEnd : Nat → List Out → Nat
  | cur, [] => cur
  | cur, o :: os => layEnd (alignUp cur o.align + o.bytes.length) os

/-- The section headers of the sections placed from `cur`, with their names at the offsets `ns`. -/
def mkHdrs : Nat → List Nat → List Out → List Shdr
  | cur, n :: ns, o :: os =>
    o.hdr n (alignUp cur o.align) :: mkHdrs (alignUp cur o.align + o.bytes.length) ns os
  | _, _, _ => []

/-- The output section of an `Obj` section. -/
def secOut (s : Section) : Out :=
  match s.kind with
  | .text => { name := s.name, type := SHT_PROGBITS, flags := SHF_ALLOC + SHF_EXECINSTR,
               align := s.align, bytes := s.bytes, size := s.bytes.length }
  | .rodata => { name := s.name, type := SHT_PROGBITS, flags := SHF_ALLOC,
                 align := s.align, bytes := s.bytes, size := s.bytes.length }
  | .data => { name := s.name, type := SHT_PROGBITS, flags := SHF_ALLOC + SHF_WRITE,
               align := s.align, bytes := s.bytes, size := s.bytes.length }
  | .bss => { name := s.name, type := SHT_NOBITS, flags := SHF_ALLOC + SHF_WRITE,
              align := s.align, bytes := [], size := s.bssSize }

/-- A section the format represents exactly. -/
def secOk (s : Section) : Bool :=
  (match s.kind with
   | .bss => s.bytes.isEmpty
   | _ => s.bssSize == 0) && isAlign s.align && nameFits s.kind s.name

/-- The list without later repetitions. -/
def dedup : List String → List String
  | [] => []
  | x :: xs => x :: (dedup xs).filter (· != x)

/-- The local symbols, in order. -/
def locals (o : Obj) : List Symbol := o.symbols.filter (!·.global)
/-- The global symbols, in order. -/
def globals (o : Obj) : List Symbol := o.symbols.filter (·.global)

/-- The names that relocations refer to and no symbol defines, in the order of first reference. -/
def undefs (o : Obj) : List String :=
  dedup ((o.relocs.map (·.sym)).filter (fun n => !(o.symbols.map (·.name)).contains n))

/-- The defined symbols in the order of the symbol table. -/
def defSyms (o : Obj) : List Symbol := locals o ++ globals o

/-- The names of the symbol table after the null symbol. -/
def symNames (o : Obj) : List String := (defSyms o).map (·.name) ++ undefs o

/-- The offsets of the symbol names in `.strtab`. -/
def symOffs (o : Obj) : List Nat := strOffs 1 ((symNames o).map strBytes)

/-- The symbol-table entry of a defined symbol whose name is at offset `n`. -/
def symEnt (o : Obj) (n : Nat) (s : Symbol) : Sym :=
  ⟨n, (if s.global then STB_GLOBAL * 16 else STB_LOCAL * 16) +
      (if (o.sections[s.sec]?.map (·.kind)) = some .text then STT_FUNC else STT_OBJECT),
    0, s.sec + 1, s.offset, 0⟩

/-- The symbol-table entry of an undefined symbol whose name is at offset `n`. -/
def undefEnt (n : Nat) : Sym := ⟨n, STB_GLOBAL * 16 + STT_NOTYPE, 0, 0, 0, 0⟩

def Sym.null : Sym := ⟨0, 0, 0, 0, 0, 0⟩

/-- The symbol table. -/
def symEnts (o : Obj) : List Sym :=
  Sym.null :: (List.zipWith (symEnt o) (symOffs o) (defSyms o) ++
    List.zipWith (fun n _ => undefEnt n) ((symOffs o).drop (defSyms o).length) (undefs o))

/-- The runs of consecutive relocations of the same section, each with its section. -/
def runs : List Reloc → List (Nat × List Reloc)
  | [] => []
  | r :: rs =>
    match runs rs with
    | (s, g) :: tl => if s = r.sec then (s, r :: g) :: tl else (r.sec, [r]) :: (s, g) :: tl
    | [] => [(r.sec, [r])]

/-- The index of the symbol named `n` in the symbol table. -/
def symIdx (o : Obj) (n : String) : Nat := (symNames o).idxOf n + 1

/-- An addend as the bits of `r_addend`. -/
def addendBits (a : Int) : Nat := (a % 2 ^ 64).toNat

/-- The relocation entry of `r`. -/
def relaEnt (m : Mach) (o : Obj) (r : Reloc) : List Nat :=
  [r.offset, symIdx o r.sym * 2 ^ 32 + (m.relType r.kind).getD 0, addendBits r.addend]

/-- The contents of `.symtab`. -/
def symtabBytes (o : Obj) : List UInt8 := encodeTab symW ((symEnts o).map Sym.toList)

/-- The contents of `.strtab`. -/
def strtabBytes (o : Obj) : List UInt8 := strtab ((symNames o).map strBytes)

/-- `.note.GNU-stack`, which is empty and says that the code needs no executable stack. -/
def noteOut : Out :=
  { name := ".note.GNU-stack", type := SHT_PROGBITS, flags := 0, align := 1, bytes := [],
    size := 0 }

/-- `.symtab`, whose string table is section `n + 3` when the `Obj` has `n` sections. -/
def symOut (o : Obj) : Out :=
  { name := ".symtab", type := SHT_SYMTAB, flags := 0, link := o.sections.length + 3,
    info := (locals o).length + 1, align := 8, entsize := SYM_SIZE, bytes := symtabBytes o,
    size := (symtabBytes o).length }

/-- `.strtab`. -/
def strOut (o : Obj) : Out :=
  { name := ".strtab", type := SHT_STRTAB, flags := 0, align := 1, bytes := strtabBytes o,
    size := (strtabBytes o).length }

/-- `.shstrtab` with contents `shstr`. -/
def shstrOut (shstr : List UInt8) : Out :=
  { name := ".shstrtab", type := SHT_STRTAB, flags := 0, align := 1, bytes := shstr,
    size := shstr.length }

/-- The sections after those of the `Obj`. -/
def fixedOuts (o : Obj) (shstr : List UInt8) : List Out :=
  [noteOut, symOut o, strOut o, shstrOut shstr]

/-- The relocation section of a run of relocations of section `p.1`. -/
def relaOut (m : Mach) (o : Obj) (p : Nat × List Reloc) : Out :=
  let b := encodeTab relaW (p.2.map (relaEnt m o))
  { name := ".rela" ++ ((o.sections[p.1]?).map (·.name)).getD "", type := SHT_RELA,
    flags := SHF_INFO_LINK, link := o.sections.length + 2, info := p.1 + 1, align := 8,
    entsize := RELA_SIZE, bytes := b, size := b.length }

/-- The sections of the output, with `shstr` as the contents of `.shstrtab`. -/
def outsWith (m : Mach) (o : Obj) (shstr : List UInt8) : List Out :=
  o.sections.map secOut ++ fixedOuts o shstr ++ (runs o.relocs).map (relaOut m o)

/-- The section names, in header order after the null header. -/
def secNames (m : Mach) (o : Obj) : List String := (outsWith m o []).map (·.name)

/-- The contents of `.shstrtab`. -/
def shstrtab (m : Mach) (o : Obj) : List UInt8 := strtab ((secNames m o).map strBytes)

/-- The sections of the output. -/
def outs (m : Mach) (o : Obj) : List Out := outsWith m o (shstrtab m o)

/-- The offset of the section-header table. -/
def shoff (m : Mach) (o : Obj) : Nat := alignUp (layEnd 64 (outs m o)) 8

/-- The section-header table. -/
def hdrs (m : Mach) (o : Obj) : List Shdr :=
  Shdr.null :: mkHdrs 64 (strOffs 1 ((secNames m o).map strBytes)) (outs m o)

/-- The ELF header. -/
def ehdr (m : Mach) (o : Obj) : Elf.Ehdr where
  type := ET_REL
  machine := m.em
  version := Elf.EV_CURRENT
  entry := 0
  phoff := 0
  shoff := shoff m o
  flags := 0
  ehsize := Elf.EHDR_SIZE
  phentsize := 0
  phnum := 0
  shentsize := SHDR_SIZE
  shnum := (outs m o).length + 1
  shstrndx := o.sections.length + 4

/-- The file, assuming that the checks passed. -/
def fileBytes (m : Mach) (o : Obj) : List UInt8 :=
  Elf.encodeEhdr (ehdr m o) ++ lay 64 (outs m o) ++ zeros (shoff m o - layEnd 64 (outs m o)) ++
    encodeTab shdrW ((hdrs m o).map Shdr.toList)

/-- No NUL byte in a name. -/
def noNul (s : String) : Bool := !(strBytes s).contains 0

/-- The checks of the writer, as the module documentation lists them. -/
def objOk (m : Mach) (o : Obj) : Bool :=
  let n := o.sections.length
  o.relocs.all (fun r => (m.relType r.kind).isSome && decide (r.sec < n) &&
    decide (-2 ^ 63 ≤ r.addend ∧ r.addend < 2 ^ 63)) &&
  o.sections.all secOk &&
  o.symbols.all (fun s => decide (s.sec < n)) &&
  decide ((o.symbols.map (·.name)).Nodup) &&
  decide (((runs o.relocs).map (·.1)).Nodup) &&
  (secNames m o).all noNul && (symNames o).all (fun s => noNul s && s != "")

/-- Every field of the file fits its width, and the section count stays below the reserved
indices. -/
def fieldsOk (m : Mach) (o : Obj) : Bool :=
  (ehdr m o).fits && decide ((outs m o).length + 1 < SHN_LORESERVE) &&
  (hdrs m o).all (fun h => fitsW shdrW h.toList) &&
  (symEnts o).all (fun s => fitsW symW s.toList) &&
  o.relocs.all (fun r => fitsW relaW (relaEnt m o r))

/-- The writer, which refuses an object the format cannot represent exactly. -/
def write (m : Mach) (o : Obj) : Except String (List UInt8) :=
  if objOk m o = false then .error "elfrel: object not representable as ELF"
  else if fieldsOk m o = false then .error "elfrel: field out of range"
  else .ok (fileBytes m o)

/-- The writer with a `ByteArray` result. -/
def writeByteArray (m : Mach) (o : Obj) : Except String ByteArray :=
  (write m o).map (fun bs => ⟨bs.toArray⟩)

end Millipede.ElfRel
