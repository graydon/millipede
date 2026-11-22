import Millipede.Object.LinkProof
import Millipede.Object.Elf.Laws
import Millipede.Top.Sound
import Tests.Select

/-!
# Tests for the linker

This suite links two small hand-written objects and checks the exact image: segment addresses,
padding, patched relocation fields, zero fill and the entry point. It checks that each object's
local symbols are resolved before the globals, that every refusal of the linker gives its
message, and that the linker's validity and W^X laws hold of the concrete link.

End to end, Core programs are lowered, compiled by the x64 backend, linked and run in the x64
model from the image's initial state. Their traces equal the source's, and the ELF writer
accepts their images. The data region is a zero-filled read-write segment below the stack, and
a reactor's root bytes sit at `mp_mem`, which a check at an offset of one byte shows to fail.
The same objects and a program are also linked for arm64, with 64 KiB pages.
-/

namespace Millipede.Tests.Link

open Millipede Millipede.Link Millipede.Sel

/-- Linker settings for the small tests, with x64 Linux pages and stack and text at `0x400000`. -/
def cfg (entry : String := "main") : Config := Config.x64Linux entry 4096

/-- The first object, whose `main` calls `f` by a pc32 relocation with addend -4. It has its own
local `k` in `.rodata`, and an absolute relocation in `.data` to the global `buf`. -/
def o1 : Obj :=
  ⟨[⟨".text", .text, 16, [0xe8, 0, 0, 0, 0, 0xc3], 0⟩,
    ⟨".rodata", .rodata, 8, [1, 2, 3], 0⟩,
    ⟨".data", .data, 8, [0, 0, 0, 0, 0, 0, 0, 0], 0⟩],
   [⟨"main", 0, 0, true⟩, ⟨"k", 1, 0, false⟩],
   [⟨0, 1, .pc32, "f", -4⟩, ⟨2, 0, .abs64, "buf", 0⟩]⟩

/-- The second object, with `f` at offset 1 of its text, its own local `k` and a global bss
buffer `buf`. -/
def o2 : Obj :=
  ⟨[⟨".text", .text, 16, [0x90, 0xc3], 0⟩, ⟨".bss", .bss, 8, [], 16⟩,
    ⟨".rodata", .rodata, 4, [9], 0⟩],
   [⟨"f", 0, 1, true⟩, ⟨"buf", 1, 0, true⟩, ⟨"k", 2, 0, false⟩],
   []⟩

/-- The expected image. The text holds o1's 6 bytes, padding to 16 and o2's 2 bytes, so `f` is
at 0x400011 and the call's field is `0x400011 - 0x400005 = 12`. The read-only data at the next
page holds o1's `k`, padding to 4 and o2's `k`. The read-write segment at the page after holds
o1's `.data`, patched with the address 0x402008 of `buf`, and then o2's 16 bss bytes, which take
no bytes in the file because the linker leaves the segment's trailing zeros to the loader. -/
def expected : Image :=
  ⟨[⟨0x400000, [0xe8, 12, 0, 0, 0, 0xc3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x90, 0xc3], 18, Perm.rx⟩,
    ⟨0x401000, [1, 2, 3, 0, 9], 5, Perm.r_⟩,
    ⟨0x402000, [0x08, 0x20, 0x40], 24, Perm.rw⟩],
   0x400000, 4096⟩

example : (link (cfg) [o1, o2]).toOption = some expected := by decide +kernel

/-- Each object sees its own local `k`, and a global is seen from every object. -/
example : resolve (layout (cfg) [o1, o2]) [o1, o2] 0 "k" = some 0x401000 := by decide +kernel
example : resolve (layout (cfg) [o1, o2]) [o1, o2] 1 "k" = some 0x401004 := by decide +kernel
example : resolve (layout (cfg) [o1, o2]) [o1, o2] 0 "f" = some 0x400011 := by decide +kernel
example : resolve (layout (cfg) [o1, o2]) [o1, o2] 1 "main" = some 0x400000 := by decide +kernel
-- A symbol that no object defines is not resolved.
example : resolve (layout (cfg) [o1, o2]) [o1, o2] 1 "zz" = none := by decide +kernel

/-- The entry may be another global symbol, and the order of the objects changes the layout. -/
example : ((link (cfg "f") [o2, o1]).toOption.map (·.entry)) = some 0x400001 := by decide +kernel

/-- The image is valid for x64 Linux, so its initial memory has no page both writable and
executable. -/
example : expected.valid X64.linux = true := by decide +kernel

theorem link12 : link (cfg) [o1, o2] = .ok expected := by
  have h : (link (cfg) [o1, o2]).toOption = some expected := by decide +kernel
  revert h; cases link (cfg) [o1, o2] <;> simp [Except.toOption]

example : (expected.init X64.linux).mem.WxorX := link_wxorx X64.linux link12 rfl rfl

/-! ## Refusals -/

/-- The error message of a refused link, or the empty string if it is accepted. -/
def err (c : Config) (objs : List Obj) : String :=
  match link c objs with
  | .ok _ => ""
  | .error e => e

/-- A second global `f`. -/
def dupF : Obj := ⟨[⟨".text", .text, 1, [0xc3], 0⟩], [⟨"f", 0, 0, true⟩], []⟩
example : err (cfg) [o1, o2, dupF] = "link: duplicate global symbol" := by decide +kernel
-- Two locals of the same name in different objects are allowed, but two symbols of one name in
-- one object are not.
example : err (cfg) [⟨[⟨".text", .text, 1, [0xc3], 0⟩], [⟨"main", 0, 0, true⟩, ⟨"main", 0, 0, false⟩], []⟩]
    = "link: duplicate symbol" := by decide +kernel
/-- Without `o2`, the symbols `f` and `buf` are unresolved. -/
example : err (cfg) [o1] = "link: unresolved symbol or malformed relocation" := by decide +kernel
/-- A relocation field running past its section. -/
example : err (cfg) [⟨[⟨".text", .text, 1, [0xe8, 0, 0, 0], 0⟩], [⟨"main", 0, 0, true⟩],
    [⟨0, 1, .pc32, "main", -4⟩]⟩] = "link: unresolved symbol or malformed relocation" := by
  decide +kernel
/-- A relocation in a section that does not exist. -/
example : err (cfg) [⟨[⟨".text", .text, 1, [0xe8, 0, 0, 0, 0], 0⟩], [⟨"main", 0, 0, true⟩],
    [⟨3, 1, .pc32, "main", -4⟩]⟩] = "link: unresolved symbol or malformed relocation" := by
  decide +kernel
/-- A symbol in a section that does not exist. -/
example : err (cfg) [⟨[⟨".text", .text, 1, [0xc3], 0⟩], [⟨"main", 5, 0, true⟩], []⟩]
    = "link: symbol in a missing section" := by decide +kernel
/-- A pc32 value out of reach, from the addend 2^40. -/
example : err (cfg) [⟨[⟨".text", .text, 1, [0xe8, 0, 0, 0, 0], 0⟩], [⟨"main", 0, 0, true⟩],
    [⟨0, 1, .pc32, "main", 1099511627776⟩]⟩] = "link: relocation out of range" := by
  decide +kernel
/-- A missing entry symbol is refused, and a local symbol does not count as the entry. -/
example : err (cfg "nope") [o1, o2] = "link: undefined entry symbol" := by decide +kernel
example : err (cfg "k") [o1, o2] = "link: undefined entry symbol" := by decide +kernel
/-- A base address that is not page-aligned. -/
example : err { cfg with base := 0x400010 } [o1, o2] = "link: base address not page-aligned" := by
  decide +kernel
/-- An empty stack, or a stack too large for its top address. -/
example : err { cfg with stackSize := 0 } [o1, o2] = "link: bad stack" := by decide +kernel
example : err { cfg with stackTop := 0x10000, stackSize := 0x20000 } [o1, o2] = "link: bad stack" :=
  by decide +kernel
/-- The image would run into the stack. -/
example : err { cfg with stackTop := 0x402000 } [o1, o2] =
    "link: image does not fit below the stack" := by decide +kernel

/-! ## End to end on x64 -/

open Millipede.Flat Millipede.Lin Millipede.X64 Millipede.Tests.Core Millipede.Tests.Lower
  Millipede.Tests.Lin Millipede.Tests.Select

/-- The image of a Core program, lowered and then compiled by the x64 backend, which linearizes,
allocates, selects, checks the budget, assembles and links. -/
def memImage (p : Program) : Option Image := do
  let fp ← (lower p).toOption
  (Compile.backendOf x64Backend fp p.memBytes).toOption

/-- The events of a program's image run for `fuel` machine steps. -/
def memEvents (ω : Oracle) (p : Program) (fuel : Nat) : Option (List Event) := do
  let img ← memImage p
  let s ← runImage ω img fuel
  pure s.1.world.events

#guard memEvents ωc hello 2000 == some (hello.events ωc 5)
#guard memEvents ω0 hello 2000 == some (helloEvents ω0)
#guard memEvents ωc counter 30000 == some (counter.events ωc 10)
#guard memEvents ωc resProg 60000 == some (resProg.events ωc 10)
#guard memEvents ωc callProg 60000 == some (callProg.events ωc 10)

/-- Whether the ELF writer, which checks that the image is valid, accepts a program's image. -/
def elfOk (p : Program) : Bool :=
  match memImage p with
  | some img => (Elf.write Elf.Config.x64Linux 12 linux.stackTop img).toOption.isSome
  | none => false

#guard elfOk hello
#guard elfOk counter
#guard elfOk callProg

/-! ## The data region -/

/-- The address of `mp_mem` in a program's image. -/
def memBase (p : Program) : Option UInt64 := do
  let fp ← (lower p).toOption
  let P := Lin.linearize fp p.memBytes
  let A ← (select 0 0 P).toOption
  let obj ← (assemble A).toOption
  resolve (layout (Compile.linkConfig P) [obj]) [obj] 0 X64.memSym

/-- The `n` machine bytes at `mp_mem + off` after `fuel` machine steps. -/
def memBytesAt (ω : Oracle) (p : Program) (fuel off n : Nat) : Option (List UInt8) := do
  let img ← memImage p
  let D ← memBase p
  let s ← runImage ω img fuel
  pure (bytesFrom s.1.mem (D + UInt64.ofNat off) n)

#guard (memImage ptCount).isSome
-- The data region is a read-write segment below the stack that holds `memBytes` zero bytes at
-- `mp_mem`, after the text and read-only data, which are `r-x` and `r--`.
#guard (memImage ptCount).map (fun img => img.segments.map (·.perm)) ==
  some [Perm.rx, Perm.r_, Perm.rw]
#guard (memImage ptCount).map (fun img => img.valid linux) == some true
#guard (do let img ← memImage ptCount; let D ← memBase ptCount
           pure (bytesFrom (img.init linux).mem D ptCount.memBytes)) ==
  some (List.replicate ptCount.memBytes 0)
-- The machine trace is the source trace.
#guard memEvents ωc ptCount 20000 == some (ptCount.events ωc 10)
#guard memEvents ω0 ptCount 20000 == some (ptCount.events ω0 10)
-- A short run sees a prefix of the source trace.
#guard (memEvents ωc ptCount 600).map (·.isPrefixOf (ptCount.events ωc 10)) == some true
-- The root's bytes at `mp_mem` are the source root's, after the run.
#guard memBytesAt ωc ptCount 20000 0 16 == some (Data.encodeBytes (ptCount.run ωc 3).1)
-- One byte off, the bytes differ.
#guard memBytesAt ωc ptCount 20000 1 16 != some (Data.encodeBytes (ptCount.run ωc 3).1)
-- The memory image passes the ELF writer.
#guard (memImage ptCount).map (fun img =>
  (Elf.write Elf.Config.x64Linux 12 linux.stackTop img).toOption.isSome) == some true

end Millipede.Tests.Link

namespace Millipede.Tests.Link
open Millipede.Flat Millipede.Lin Millipede.X64 Millipede.Tests.Core Millipede.Tests.Lower
  Millipede.Tests.Lin

/-! ### The budget for memory programs -/

/-- A cost model with lower weights than `X64.κ`. -/
def κ1 : CostModel :=
  { X64.κ with word := 2, mem := 2, place := 1, ctor := 2, atom := 2, ite := 2, let_ := 1 }

-- `X64.κ` pays for the code `lower` emits, such as word copies charged `κ.word` per word, and the
-- budget check refuses the lower weights.
#guard ptCountLin.map (fun P => budgetOk 0 0 X64.κ P) == some true
#guard ptCountLin.map (fun P => budgetOk 0 0 κ1 P) == some false

/-- A cost model with every weight higher than those of `X64.κ` also covers the code, because the check is monotone in the
weights. -/
def κMem : CostModel :=
  { atom := 64, let_ := 16, ite := 64, prim := 40, div := 48, loop := 40, iter := 16, call := 64,
    ctor := 64, match_ := 24, ext := 24, word := 120, place := 32, mem := 64, ref := 64 }

#guard ptCountLin.map (fun P => budgetOk 0 0 κMem P) == some true

/-! ### `compile` needs certified building blocks

The hand-written lenses of `Pt` in `ptCount` carry no certificate of their law, so `compile`
refuses the program, although the backend that `compile` runs after its checks accepts it. -/

#guard !(compile ptCount x64Linux).toBool
#guard !Compile.checks ptCount

end Millipede.Tests.Link

namespace Millipede.Tests.Link
open Millipede Millipede.Link Millipede.Sel Millipede.Flat Millipede.Lin Millipede.Tests.Core
  Millipede.Tests.Lower Millipede.Tests.Lin Millipede.Tests.Select

/-! ## arm64 Linux

Linked for arm64, every segment of the small objects starts on a 64 KiB boundary and is padded
to whole 64 KiB pages. The image is valid for arm64 Linux and the arm64 ELF writer accepts it.
A Core program compiled by the arm64 backend has three segments `r-x`, `r--` and `rw-`, with the
data region zeroed at `mp_mem`. -/

/-- The arm64 linker settings for the small objects. -/
def cfgA (entry : String := "main") : Config := Config.a64Linux entry 4096

#guard (link (cfgA) [o1, o2]).toOption.map (fun img => img.segments.map (·.vaddr)) ==
  some [0x400000, 0x410000, 0x420000]
#guard (link (cfgA) [o1, o2]).toOption.map (fun img => img.segments.map (·.memSize)) ==
  some [65536, 65536, 65536]
-- The relocations are patched as on x64 at the 64 KiB layout, where `buf` is at 0x420008. The
-- trailing zeros of the read-write segment are not in its bytes, and its `memSize` keeps the page.
#guard (link (cfgA) [o1, o2]).toOption.map (fun img => (img.segments.getD 2 default).bytes) ==
  some [0x08, 0x00, 0x42]
#guard (link (cfgA) [o1, o2]).toOption.map (fun img =>
  (List.range 8).map fun i => img.byteAt (0x420000 + UInt64.ofNat i)) ==
  some [0x08, 0x00, 0x42, 0, 0, 0, 0, 0]
#guard (link (cfgA) [o1, o2]).toOption.map (·.valid A64.linux) == some true
#guard (link (cfgA) [o1, o2]).toOption.map (fun img =>
  (Elf.write Elf.Config.a64Linux 16 A64.linux.stackTop img).toOption.isSome) == some true
-- The x64 settings give 4 KiB pages, which the arm64 writer refuses.
#guard (link (cfg) [o1, o2]).toOption.map (fun img =>
  (Elf.write Elf.Config.a64Linux 16 A64.linux.stackTop img).toOption.isSome) == some false
-- Refusals do not depend on the target.
#guard err (cfgA) [o1] == "link: unresolved symbol or malformed relocation"
#guard err { cfgA with base := 0x401000 } [o1, o2] == "link: base address not page-aligned"

/-- The arm64 backend's image of a Core program. -/
def memImageA (p : Program) : Option Image := do
  let fp ← (lower p).toOption
  (Compile.backendOf a64Backend fp p.memBytes).toOption

#guard (memImageA ptCount).map (fun img => img.segments.map (·.perm)) ==
  some [Perm.rx, Perm.r_, Perm.rw]
#guard (memImageA ptCount).map (fun img => img.valid A64.linux) == some true
#guard (memImageA ptCount).map (fun img =>
  (Elf.write Elf.Config.a64Linux 16 A64.linux.stackTop img).toOption.isSome) == some true
#guard (do
    let fp ← (lower ptCount).toOption
    let P := Lin.linearize fp ptCount.memBytes
    let A ← (RegAlloc.A64Reg.select 0 0 P).toOption
    let obj ← (Asm.assemble A64.asm A).toOption
    let D ← resolve (layout (Compile.linkConfigA64 P) [obj]) [obj] 0 Sel.memSym
    let img ← memImageA ptCount
    pure (bytesFrom (img.init A64.linux).mem D ptCount.memBytes)) ==
  some (List.replicate ptCount.memBytes 0)

end Millipede.Tests.Link
