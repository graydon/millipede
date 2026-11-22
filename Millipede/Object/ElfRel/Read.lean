import Millipede.Object.ElfRel.Format

/-!
# The ELF64 relocatable-object reader

`ElfRel.read m bs` reads an ELF64 relocatable object for machine `m` into the `Obj` that
Millipede's linker would link in its place, or returns `none`. It is written from the gABI and the
processor supplements and accepts any file of the subset described here, whatever produced it.
It reads the following:

1. The ELF header has the `e_ident` of `Elf.ident` (`ELFCLASS64`, little-endian, `EV_CURRENT`,
   the System V ABI), `e_type = ET_REL`, `e_machine = m.em`, `e_version = 1`, no entry point, no
   program headers, `e_flags = 0`, `e_ehsize = 64` and `e_shentsize = 64`. The section-header
   table lies inside the file and has between 1 and `SHN_LORESERVE - 1` entries, so extended
   section numbering is not used, and `e_shstrndx` names a string table.
2. Section header 0 is all zero, as the gABI reserves it. Every other header is classified by its
   type and flags. An `SHT_PROGBITS` header with exactly the flags `SHF_ALLOC | SHF_EXECINSTR`,
   `SHF_ALLOC`, or `SHF_ALLOC | SHF_WRITE` is a `text`, `rodata` or `data` section, and an
   `SHT_NOBITS` header with `SHF_ALLOC | SHF_WRITE` is a `bss` section. These become the sections
   of the `Obj`, in header order, with their names from `.shstrtab`. Each must have address 0, an
   alignment of 0 or a power of 2, a name that `nameFits` its kind and, unless it is `SHT_NOBITS`,
   its contents inside the file. The name matters because a system linker places a section by its
   name while this model classifies it by its flags, so a writable section named `.text` would be
   data here and code to GNU ld.
   An `SHT_PROGBITS` header without `SHF_ALLOC`, such as `.note.GNU-stack` or `.comment`, and an
   `SHT_NULL` header occupy no memory and are ignored. `SHT_SYMTAB`, `SHT_STRTAB` and `SHT_RELA`
   are read as described next, and any other header refuses the file, so a file with `SHT_REL`
   relocations, section groups, initialiser arrays or merged strings is refused.
3. There is exactly one symbol table, with entries of 24 bytes inside the file. Its `sh_link`
   names its string table, and `sh_info`, one more than the index of the last local symbol, lies
   between 1 and the number of entries. Entry 0 is all zero. Every entry has `st_other = 0`, the
   binding `STB_LOCAL` below `sh_info` and `STB_GLOBAL` from there on, so weak symbols are
   refused, and a type of `STT_NOTYPE`, `STT_OBJECT`, `STT_FUNC`, or, for local entries only,
   `STT_SECTION` or `STT_FILE`. Section and file symbols and symbols without a name define no
   name and are skipped. A named symbol whose `st_shndx` is `SHN_UNDEF` must be global, and it is
   a reference to a symbol of another object. Any other named symbol becomes a symbol of the
   `Obj`, at offset `st_value` of the section `st_shndx`, which must be one of the `Obj`'s, so
   absolute and common symbols are refused. A name that an undefined symbol and a defined symbol
   share refuses the file, because the `Obj` resolves a relocation by its name and would find the
   defined one.
4. Each `SHT_RELA` section, in header order, has entries of 24 bytes inside the file, the flags 0
   or `SHF_INFO_LINK`, an `sh_link` that names the symbol table, and an `sh_info` that names a
   section of the `Obj`. Each entry becomes a relocation of that section at `r_offset`, with the
   kind that `m.relKind` gives the type `ELF64_R_TYPE(r_info)`, the name of the symbol
   `ELF64_R_SYM(r_info)`, which must be a named symbol, and the addend `r_addend` read as a signed
   64-bit number.

Strings are NUL-terminated inside their table, and names must be valid UTF-8. A relocation
against a section symbol is refused, because an `Obj` relocation names a symbol and cannot name a
section, so the reader refuses most objects that GNU as and C compilers make, which refer to local
labels through section symbols. The reader does not
check that symbols lie inside their sections, that relocation fields lie inside theirs, or that
names are unique, because Millipede's linker refuses objects that break these.
-/

namespace Millipede.ElfRel

/-- What a section header is, by its type and flags. -/
inductive Cls where
  /-- a section of the `Obj`, of the given kind -/
  | sec (k : SecKind)
  /-- a section that occupies no memory, or an inactive header -/
  | ignored
  | symtab
  | strtab
  | rela
  | bad
deriving DecidableEq, Repr

/-- The class of a section header, as item 2 of the module documentation describes. -/
def clsOf (type flags : Nat) : Cls :=
  if type = SHT_NULL then .ignored
  else if type = SHT_PROGBITS then
    if flags = SHF_ALLOC + SHF_EXECINSTR then .sec .text
    else if flags = SHF_ALLOC then .sec .rodata
    else if flags = SHF_ALLOC + SHF_WRITE then .sec .data
    else if flags / SHF_ALLOC % 2 = 0 then .ignored
    else .bad
  else if type = SHT_NOBITS then
    if flags = SHF_ALLOC + SHF_WRITE then .sec .bss else .bad
  else if type = SHT_SYMTAB then .symtab
  else if type = SHT_STRTAB then .strtab
  else if type = SHT_RELA then .rela
  else .bad

def Shdr.cls (h : Shdr) : Cls := clsOf h.type h.flags

/-- The header is a section of the `Obj`. -/
def Shdr.isSec (h : Shdr) : Bool := match h.cls with
  | .sec _ => true
  | _ => false

/-- The index in the `Obj` of ELF section `k`, which is the number of `Obj` sections before it. -/
def secIdx (shs : List Shdr) (k : Nat) : Option Nat :=
  match shs[k]? with
  | some h => if h.isSec then some ((shs.take k).countP Shdr.isSec) else none
  | none => none

/-- The contents of a section, if they lie inside the file. -/
def contents (bs : List UInt8) (h : Shdr) : Option (List UInt8) :=
  if h.offset + h.size ≤ bs.length then some ((bs.drop h.offset).take h.size) else none

/-- The contents of string table `k`. -/
def strSec (bs : List UInt8) (shs : List Shdr) (k : Nat) : Option (List UInt8) :=
  match shs[k]? with
  | some h => if h.type = SHT_STRTAB then contents bs h else none
  | none => none

/-- The section of a header of class `.sec k`, named from the table `shstr`. -/
def loadSec (bs shstr : List UInt8) (k : SecKind) (h : Shdr) : Option Section :=
  if h.addr = 0 ∧ isAlign h.addralign = true then
    match strAt shstr h.name with
    | none => none
    | some name =>
      if nameFits k name then
        match k with
        | .bss => some { name, kind := .bss, align := h.addralign, bytes := [], bssSize := h.size }
        | k => (contents bs h).map fun b => { name, kind := k, align := h.addralign, bytes := b }
      else none
  else none

/-- The sections of the `Obj`, in header order. -/
def loadSecs (bs shstr : List UInt8) : List Shdr → Option (List Section)
  | [] => some []
  | h :: hs =>
    match h.cls with
    | .sec k =>
      match loadSec bs shstr k h, loadSecs bs shstr hs with
      | some s, some ss => some (s :: ss)
      | _, _ => none
    | _ => loadSecs bs shstr hs

/-- What a symbol-table entry says. -/
inductive RSym where
  /-- no name: a section or file symbol, or an unnamed one -/
  | anon
  /-- an undefined global symbol -/
  | undef (n : String)
  /-- a symbol of the `Obj` -/
  | defn (s : Symbol)
deriving DecidableEq, Repr

def RSym.name? : RSym → Option String
  | .anon => none
  | .undef n => some n
  | .defn s => some s.name

def RSym.sym? : RSym → Option Symbol
  | .defn s => some s
  | _ => none

def RSym.undef? : RSym → Option String
  | .undef n => some n
  | _ => none

/-- Reads one symbol-table entry, local or global, as item 3 of the module documentation
describes. -/
def readSym (shs : List Shdr) (strs : List UInt8) (loc : Bool) (e : Sym) : Option RSym :=
  if e.other = 0 ∧ e.bind = (if loc then STB_LOCAL else STB_GLOBAL) then
    if e.type = STT_SECTION ∨ e.type = STT_FILE then
      if loc then some .anon else none
    else if e.type ≤ STT_FUNC then
      if e.name = 0 then some .anon
      else
        match strAt strs e.name with
        | none => none
        | some n =>
          if e.shndx = 0 then
            if loc then none else some (.undef n)
          else (secIdx shs e.shndx).map fun sec => .defn ⟨n, sec, e.value, !loc⟩
    else none
  else none

/-- Reads the entries after the null one, of which the first `k` are local. -/
def readSyms (shs : List Shdr) (strs : List UInt8) : Nat → List Sym → Option (List RSym)
  | _, [] => some []
  | k, e :: es =>
    match readSym shs strs (k != 0) e, readSyms shs strs (k - 1) es with
    | some r, some rs => some (r :: rs)
    | _, _ => none

/-- The signed value of 64 bits. -/
def signed64 (n : Nat) : Int := if n < 2 ^ 63 then n else (n : Int) - 2 ^ 64

/-- Reads one relocation entry of `Obj` section `sec`. -/
def readRel (m : Mach) (rsyms : List RSym) (sec : Nat) (e : List Nat) : Option Reloc :=
  match e with
  | [off, info, add] =>
    match m.relKind (info % 2 ^ 32), (rsyms[info / 2 ^ 32 - 1]?).bind RSym.name? with
    | some k, some n => if info / 2 ^ 32 = 0 then none else some ⟨sec, off, k, n, signed64 add⟩
    | _, _ => none
  | _ => none

def readRels (m : Mach) (rsyms : List RSym) (sec : Nat) : List (List Nat) → Option (List Reloc)
  | [] => some []
  | e :: es =>
    match readRel m rsyms sec e, readRels m rsyms sec es with
    | some r, some rs => some (r :: rs)
    | _, _ => none

/-- A table of `w`-byte entries inside the file: its entries, or `none`. -/
def table (bs : List UInt8) (ws : List Nat) (h : Shdr) : Option (List (List Nat)) :=
  if h.entsize = ws.sum ∧ h.size % ws.sum = 0 ∧ h.offset + h.size ≤ bs.length then
    some (decodeTab ws (h.size / ws.sum) (bs.drop h.offset))
  else none

/-- The relocations of one `SHT_RELA` section. -/
def readRela (m : Mach) (bs : List UInt8) (shs : List Shdr) (rsyms : List RSym) (h : Shdr) :
    Option (List Reloc) :=
  if (h.flags = 0 ∨ h.flags = SHF_INFO_LINK) ∧ (shs[h.link]?.map Shdr.type) = some SHT_SYMTAB then
    match secIdx shs h.info, table bs relaW h with
    | some sec, some es => readRels m rsyms sec es
    | _, _ => none
  else none

/-- The relocations of all `SHT_RELA` sections, in header order. -/
def readRelas (m : Mach) (bs : List UInt8) (shs : List Shdr) (rsyms : List RSym) :
    List Shdr → Option (List Reloc)
  | [] => some []
  | h :: hs =>
    if h.cls = .rela then
      match readRela m bs shs rsyms h, readRelas m bs shs rsyms hs with
      | some r, some rs => some (r ++ rs)
      | _, _ => none
    else readRelas m bs shs rsyms hs

/-- The header checks of item 1 of the module documentation. -/
def ehdrOk (m : Mach) (h : Elf.Ehdr) (len : Nat) : Bool :=
  h.type == ET_REL && h.machine == m.em && h.version == Elf.EV_CURRENT && h.entry == 0 &&
    h.phoff == 0 && h.phnum == 0 && h.flags == 0 && h.ehsize == Elf.EHDR_SIZE &&
    h.shentsize == SHDR_SIZE && decide (0 < h.shnum) && decide (h.shnum < SHN_LORESERVE) &&
    decide (h.shoff + SHDR_SIZE * h.shnum ≤ len)

/-- The symbol-table checks of item 3 of the module documentation, given its entry count. -/
def symtabOk (st : Shdr) (n : Nat) : Bool := decide (1 ≤ st.info) && decide (st.info ≤ n)

/-- No name is both undefined and defined. -/
def namesOk (rs : List RSym) : Bool :=
  (rs.filterMap RSym.undef?).all fun n => !((rs.filterMap RSym.sym?).map (·.name)).contains n

/-- Reads the symbols and relocations, given the sections. -/
def readRest (m : Mach) (bs : List UInt8) (shs : List Shdr) (secs : List Section) : Option Obj :=
  match shs.filter (·.cls = .symtab) with
  | [st] =>
    match strSec bs shs st.link, table bs symW st with
    | some strs, some (e0 :: es) =>
      if symtabOk st (es.length + 1) ∧ Sym.ofList e0 = ⟨0, 0, 0, 0, 0, 0⟩ then
        match readSyms shs strs (st.info - 1) (es.map Sym.ofList) with
        | some rsyms =>
          if namesOk rsyms then
            (readRelas m bs shs rsyms shs).map fun relocs =>
              { sections := secs, symbols := rsyms.filterMap RSym.sym?, relocs }
          else none
        | none => none
      else none
    | _, _ => none
  | _ => none

/-- The reader. -/
def read (m : Mach) (bs : List UInt8) : Option Obj :=
  match Elf.decodeEhdr bs with
  | none => none
  | some h =>
    if ehdrOk m h bs.length then
      let shs := (decodeTab shdrW h.shnum (bs.drop h.shoff)).map Shdr.ofList
      if shs.head? = some Shdr.null ∧ shs.all (·.cls != .bad) then
        match strSec bs shs h.shstrndx with
        | none => none
        | some shstr =>
          match loadSecs bs shstr shs with
          | none => none
          | some secs => readRest m bs shs secs
      else none
    else none

end Millipede.ElfRel
