import Millipede.Object.Image
import Millipede.Object.Obj

/-!
# The linker

`link cfg objs` turns relocatable objects into a loadable image, in the following steps:

1. It merges the sections into three groups, in object order and section order. `text` is read
   and execute, `rodata` is read only, and `rw`, which holds `data` and `bss`, is read and write.
   Each section is placed at the next address aligned to its `align`, the gaps are zero bytes, and
   a section's contents in memory are its `bytes` followed by `bssSize` zero bytes.
2. It assigns addresses. The text group starts at `cfg.base`, and each later group at the next
   page boundary after the previous one. Each non-empty group becomes one page-aligned segment
   with the group's permissions, so code is never writable.
3. It resolves symbols. A name is looked up first among the symbols of the referring object,
   local or global, and then among the global symbols of all objects. A symbol's address is its
   section's address plus its offset.
4. It applies the relocations, patching the field at the section's address plus the
   relocation's offset.
5. It sets the entry to the address of the global symbol `cfg.entry`, and sets the stack size.

The linker refuses a duplicate symbol name within an object, a duplicate global symbol across
objects, a symbol or relocation that names a section that does not exist, and a relocation whose
field does not lie inside its section's bytes. It also refuses an unresolved symbol, a relocation
value out of reach, such as a `pc32` value beyond ±2 GiB, an undefined entry symbol, a base
address that is not page-aligned, an empty stack, a stack top that is not page-aligned or is too
small for the stack, and an image that does not end below the stack. It never emits anything
else in place of a refusal. Its laws are proved in `LinkProof.lean`.
-/

namespace Millipede.Link

/-- The linker's parameters, whose page size and stack top must be the ABI's. -/
structure Config where
  /-- the base-2 logarithm of the page size -/
  pageBits : Nat
  /-- the address just above the stack -/
  stackTop : UInt64
  /-- the address of the first segment, the text segment, which must be page-aligned -/
  base : Nat
  /-- the name of the global symbol where execution starts -/
  entry : String
  /-- the bytes of stack the program needs -/
  stackSize : Nat
  /-- whether every segment extends with zero bytes to the end of its last page. This is needed
  when the layout page is larger than the kernel's, as on arm64 Linux, which lays out in 64 KiB
  pages for kernels with 4, 16 or 64 KiB pages, so that the kernel maps exactly the pages that
  the model's segments cover. -/
  fullPages : Bool := false
deriving Repr, Inhabited

/-- Rounds `a` up to a multiple of `k`, where `k = 0` leaves `a` unchanged. -/
def alignUp (a k : Nat) : Nat := if k = 0 then a else (a + k - 1) / k * k

/-- The output groups, each of which becomes at most one segment. -/
inductive Group where
  | text
  | rodata
  | rw
deriving DecidableEq, Repr, Inhabited

/-- The group a section kind goes to. -/
def _root_.Millipede.SecKind.group : SecKind → Group
  | .text => .text
  | .rodata => .rodata
  | .data => .rw
  | .bss => .rw

/-- The permissions of a group's segment. -/
def Group.perm : Group → Perm
  | .text => Perm.rx
  | .rodata => Perm.r_
  | .rw => Perm.rw

theorem group_perm (k : SecKind) : k.group.perm = k.perm := by cases k <;> rfl

/-- A section tagged with its object index, its section index and its object's relocations. -/
structure Item where
  obj : Nat
  idx : Nat
  sec : Section
  relocs : List Reloc

/-- The sections of object `j`, numbered from `i`. -/
def secItems (j : Nat) (rs : List Reloc) : Nat → List Section → List Item
  | _, [] => []
  | i, s :: ss => ⟨j, i, s, rs⟩ :: secItems j rs (i + 1) ss

/-- All sections of the objects numbered from `j`, in order. -/
def items : Nat → List Obj → List Item
  | _, [] => []
  | j, o :: os => secItems j o.relocs 0 o.sections ++ items (j + 1) os

/-- The sections of one group, in order. -/
def groupItems (g : Group) (objs : List Obj) : List Item :=
  (items 0 objs).filter (fun it => it.sec.kind.group == g)

/-- Places sections one after the other from address `cur`, each aligned, and pairs each section
with its address. -/
def place : Nat → List Item → List (Item × Nat)
  | _, [] => []
  | cur, it :: its =>
    let a := alignUp cur it.sec.align
    (it, a) :: place (a + it.sec.size) its

/-- The address just after the last section placed from `cur`. -/
def placeEnd : Nat → List Item → Nat
  | cur, [] => cur
  | cur, it :: its => placeEnd (alignUp cur it.sec.align + it.sec.size) its

/-- The address layout, which holds the group bases and ends and every section's address. -/
structure Layout where
  textBase : Nat
  textEnd : Nat
  roBase : Nat
  roEnd : Nat
  rwBase : Nat
  rwEnd : Nat
  placed : List (Item × Nat)

/-- Computes the layout, with text from `cfg.base` and each later group from the next page
boundary. -/
def layout (cfg : Config) (objs : List Obj) : Layout :=
  let P := 2 ^ cfg.pageBits
  let tb := cfg.base
  let te := placeEnd tb (groupItems .text objs)
  let rb := alignUp te P
  let re := placeEnd rb (groupItems .rodata objs)
  let wb := alignUp re P
  let we := placeEnd wb (groupItems .rw objs)
  { textBase := tb, textEnd := te, roBase := rb, roEnd := re, rwBase := wb, rwEnd := we
    placed := place tb (groupItems .text objs) ++ place rb (groupItems .rodata objs) ++
      place wb (groupItems .rw objs) }

/-- The address of section `i` of object `j`. -/
def secAddr (L : Layout) (j i : Nat) : Option Nat :=
  (L.placed.find? (fun p => p.1.obj == j && p.1.idx == i)).map (·.2)

/-- The address of a symbol of object `j`. -/
def symAddr (L : Layout) (j : Nat) (s : Symbol) : Option Nat :=
  (secAddr L j s.sec).map (· + s.offset)

/-- The first global symbol named `n` among the objects numbered from `j`. -/
def globalSym (n : String) : Nat → List Obj → Option (Nat × Symbol)
  | _, [] => none
  | j, o :: os =>
    match o.symbols.find? (fun s => s.global && s.name == n) with
    | some s => some (j, s)
    | none => globalSym n (j + 1) os

/-- The address of the global symbol `n`. -/
def globalAddr (L : Layout) (objs : List Obj) (n : String) : Option UInt64 :=
  match globalSym n 0 objs with
  | some (j, s) => (symAddr L j s).map UInt64.ofNat
  | none => none

/-- Symbol resolution for references from object `j`, which looks among its own symbols first
and then among the global symbols of all objects. -/
def resolve (L : Layout) (objs : List Obj) (j : Nat) (n : String) : Option UInt64 :=
  match (objs[j]?).bind (fun o => o.symbols.find? (fun s => s.name == n)) with
  | some s => (symAddr L j s).map UInt64.ofNat
  | none => globalAddr L objs n

/-! ### Fast evaluation of `applyRelocs` and `relocsOk`

The model patches a list once per relocation, which takes time quadratic in the code size because
every memory access of the compiled code carries a relocation to `mp_mem`. The compiled linker
instead patches one array in place and checks relocation fields against precomputed section
lengths, and `@[csimp]` lemmas prove both equal to the model. -/

/-- `patchBytes` on an array, with one `setIfInBounds` per byte. -/
def patchArr (a : Array UInt8) (off : Nat) : List UInt8 → Array UInt8
  | [] => a
  | n :: ns => patchArr (a.setIfInBounds off n) (off + 1) ns

@[simp] theorem patchBytes_nil (bs : List UInt8) (off : Nat) : patchBytes bs off [] = bs := by
  cases bs <;> rfl

theorem patchBytes_succ (b : UInt8) (bs : List UInt8) (off : Nat) (ns : List UInt8) :
    patchBytes (b :: bs) (off + 1) ns = b :: patchBytes bs off ns := by
  cases ns <;> simp [patchBytes]

theorem patchBytes_cons : ∀ (bs : List UInt8) (off : Nat) (n : UInt8) (ns : List UInt8),
    patchBytes bs off (n :: ns) = patchBytes (bs.set off n) (off + 1) ns
  | [], _, _, _ => by simp [patchBytes]
  | _ :: bs, 0, n, ns => by simp [patchBytes, patchBytes_succ]
  | b :: bs, off + 1, n, ns => by
    simp only [patchBytes, List.set_cons_succ, patchBytes_succ, patchBytes_cons bs off n ns]

theorem patchArr_toList : ∀ (a : Array UInt8) (off : Nat) (ns : List UInt8),
    (patchArr a off ns).toList = patchBytes a.toList off ns
  | a, off, [] => by cases h : a.toList <;> simp [patchArr, patchBytes, h]
  | a, off, n :: ns => by
    rw [patchArr, patchArr_toList, patchBytes_cons, Array.toList_setIfInBounds]

/-- `applyRelocs` on an array. -/
def applyRelocsArr (σ : String → Option UInt64) (base : UInt64) (sec : Nat) :
    List Reloc → Array UInt8 → Option (Array UInt8)
  | [], bs => some bs
  | r :: rs, bs =>
    if r.sec = sec then
      match σ r.sym with
      | none => none
      | some S =>
        match r.kind.patch S (base + UInt64.ofNat r.offset) r.addend
            (bs.extract r.offset (r.offset + r.kind.width)).toList with
        | none => none
        | some v => applyRelocsArr σ base sec rs (patchArr bs r.offset v)
    else applyRelocsArr σ base sec rs bs

theorem applyRelocsArr_toList (σ : String → Option UInt64) (base : UInt64) (sec : Nat) :
    ∀ (rs : List Reloc) (a : Array UInt8),
      (applyRelocsArr σ base sec rs a).map Array.toList = applyRelocs σ base sec rs a.toList
  | [], _ => rfl
  | r :: rs, a => by
    simp only [applyRelocsArr, applyRelocs]
    split
    · cases σ r.sym with
      | none => rfl
      | some S =>
        dsimp only
        rw [Array.toList_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left]
        cases r.kind.patch S (base + UInt64.ofNat r.offset) r.addend
            ((a.toList.drop r.offset).take r.kind.width) with
        | none => rfl
        | some v => dsimp only; rw [applyRelocsArr_toList σ base sec rs, patchArr_toList]
    · exact applyRelocsArr_toList σ base sec rs a

/-- `applyRelocs` computed through an array, which is what the compiled code runs. -/
def applyRelocsFast (σ : String → Option UInt64) (base : UInt64) (sec : Nat) (rs : List Reloc)
    (bs : List UInt8) : Option (List UInt8) :=
  (applyRelocsArr σ base sec rs bs.toArray).map Array.toList

@[csimp] theorem applyRelocs_eq_fast : @applyRelocs = @applyRelocsFast := by
  funext σ base sec rs bs
  simp only [applyRelocsFast, applyRelocsArr_toList]

/-- The bytes of a placed section, which are its relocated bytes followed by the zero fill. -/
def content (L : Layout) (objs : List Obj) (it : Item) (a : Nat) : Option (List UInt8) :=
  (applyRelocs (resolve L objs it.obj) (UInt64.ofNat a) it.idx it.relocs it.sec.bytes).map
    (· ++ List.replicate it.sec.bssSize 0)

/-- The bytes of a group placed from `cur`, which are the alignment padding and the contents. -/
def emit (cont : Item → Nat → Option (List UInt8)) : Nat → List Item → Option (List UInt8)
  | _, [] => some []
  | cur, it :: its =>
    let a := alignUp cur it.sec.align
    match cont it a, emit cont (a + it.sec.size) its with
    | some X, some B => some (List.replicate (a - cur) 0 ++ X ++ B)
    | _, _ => none

/-- A group's bytes as its segment holds them, with the group starting at `base`. With
`cfg.fullPages` they are padded with zeros to the end of the last page. -/
def fill (cfg : Config) (base : Nat) (bs : List UInt8) : List UInt8 :=
  if cfg.fullPages then
    bs ++ List.replicate (alignUp (base + bs.length) (2 ^ cfg.pageBits) - (base + bs.length)) 0
  else bs

/-- `bs` without its trailing zeros. -/
def dropZeros : List UInt8 → List UInt8
  | [] => []
  | b :: bs => match dropZeros bs with
    | [] => if b = 0 then [] else [b]
    | r => b :: r

/-- A segment holding `bs` in memory. With `trim`, its trailing zeros are left out of the file,
while `memSize` keeps the full length and the loader fills the rest with zeros. The linker trims
the read-write segment, so zero-initialised data such as the data region takes no file bytes. -/
def mkSeg (base : Nat) (bs : List UInt8) (perm : Perm) (trim := false) : Segment :=
  ⟨UInt64.ofNat base, if trim then dropZeros bs else bs, bs.length, perm⟩

/-- The number of stack pages. -/
def stackPages (cfg : Config) : Nat := (cfg.stackSize + 2 ^ cfg.pageBits - 1) / 2 ^ cfg.pageBits

/-- The lowest stack address, at or below which the image must end. -/
def limit (cfg : Config) : Nat :=
  (cfg.stackTop.toNat / 2 ^ cfg.pageBits - stackPages cfg) * 2 ^ cfg.pageBits

/-- Fails with `msg` unless `b` holds. -/
def req (b : Bool) (msg : String) : Except String Unit := if b then .ok () else .error msg

/-- Every relocation of object `j` is well formed, which means that it names a real section, its
field lies inside the section's bytes, and its symbol is resolved. -/
def relocsOk (L : Layout) (objs : List Obj) (j : Nat) (o : Obj) : Bool :=
  o.relocs.all fun r =>
    match o.sections[r.sec]? with
    | none => false
    | some s => r.offset + r.kind.width ≤ s.bytes.length && (resolve L objs j r.sym).isSome

/-- `relocsOk` against precomputed section lengths, which is what the compiled code runs. -/
def relocsOkFast (L : Layout) (objs : List Obj) (j : Nat) (o : Obj) : Bool :=
  let lens := (o.sections.map fun s => s.bytes.length).toArray
  o.relocs.all fun r =>
    match lens[r.sec]? with
    | none => false
    | some n => r.offset + r.kind.width ≤ n && (resolve L objs j r.sym).isSome

@[csimp] theorem relocsOk_eq_fast : @relocsOk = @relocsOkFast := by
  funext L objs j o
  simp only [relocsOk, relocsOkFast, List.getElem?_toArray, List.getElem?_map]
  congr; funext r
  cases o.sections[r.sec]? <;> rfl

/-- `relocsOk` for every object, numbered from `j`. -/
def allRelocsOk (L : Layout) (objs : List Obj) : Nat → List Obj → Bool
  | _, [] => true
  | j, o :: os => relocsOk L objs j o && allRelocsOk L objs (j + 1) os

/-- All global symbol names of the objects. -/
def globalNames (objs : List Obj) : List String :=
  objs.flatMap fun o => (o.symbols.filter (·.global)).map (·.name)

/-- The linker. -/
def link (cfg : Config) (objs : List Obj) : Except String Image := do
  let P := 2 ^ cfg.pageBits
  req (objs.all fun o => decide (o.symbols.map (·.name)).Nodup) "link: duplicate symbol"
  req (decide (globalNames objs).Nodup) "link: duplicate global symbol"
  req (objs.all fun o => o.symbols.all (·.sec < o.sections.length))
    "link: symbol in a missing section"
  let L := layout cfg objs
  req (allRelocsOk L objs 0 objs) "link: unresolved symbol or malformed relocation"
  req (cfg.base % P == 0) "link: base address not page-aligned"
  req (0 < cfg.stackSize && cfg.stackTop.toNat % P == 0 &&
      stackPages cfg ≤ cfg.stackTop.toNat / P) "link: bad stack"
  req (L.rwEnd ≤ limit cfg) "link: image does not fit below the stack"
  let cont := content L objs
  match emit cont L.textBase (groupItems .text objs),
      emit cont L.roBase (groupItems .rodata objs),
      emit cont L.rwBase (groupItems .rw objs) with
  | some T, some R, some W =>
    match globalAddr L objs cfg.entry with
    | none => .error "link: undefined entry symbol"
    | some e =>
      pure { segments := [mkSeg L.textBase (fill cfg L.textBase T) .rx,
                mkSeg L.roBase (fill cfg L.roBase R) .r_,
                mkSeg L.rwBase (fill cfg L.rwBase W) .rw true].filter
                  (fun sg => 0 < sg.memSize)
             entry := e
             stackSize := cfg.stackSize }
  | _, _, _ => .error "link: relocation out of range"

/-- The linker settings for x64 Linux, with 4 KiB pages, the stack top of `X64.linux`, and text at
`0x400000`. -/
def Config.x64Linux (entry : String) (stackSize : Nat) : Config :=
  { pageBits := 12, stackTop := 0x7ffffffff000, base := 0x400000, entry, stackSize }

/-- The linker settings for AArch64 Linux, with 64 KiB layout pages and whole-page segments, the
stack top `Abi.a64LinuxStackTop`, which lies below 2^39, and text at `0x400000`. -/
def Config.a64Linux (entry : String) (stackSize : Nat) : Config :=
  { pageBits := 16, stackTop := Abi.a64LinuxStackTop, base := 0x400000, entry, stackSize,
    fullPages := true }

end Millipede.Link
