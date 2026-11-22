import Tests.Differential.IoTest
import Millipede.Target.A64.SelectProof
import Millipede.Target.SelInit

/-!
# The arm64 loader model against the kernel

A theorem proves that the model's initial state `img.init A64.linux` satisfies `A64.Init`. This
test checks the model's start against what the Linux kernel gives a real process, on the
properties that `A64.Init` uses. `differential loader-a64 <dir> [seed]` compiles `ioProg`, a
reactor with a data region, for `arm64Linux` through the pipeline's passes, checks that the image
is the one `compile` gives, writes `<dir>/loader.elf` and prints the model's facts as one
`key value` per line:
* `pc` is the entry pc of the initial state;
* `sp16` is the initial `sp` modulo 16, and `xzero` is `1` if `x0 … x30` are all zero;
* `sptop` is `1` if `sp` is the top of the stack region;
* `frame` is the number of words of `main`'s frame, and `framezero` is `1` if that many words
  below `sp` are zero in the model;
* `mem` and `memsize` are the address and size of the data region `mp_mem`, `memrw` is `1` if the
  model has it readable, writable and zero, and `textrx` is `1` if the page at `pc` is `r-x`.

`scripts/loader-a64.sh` starts the ELF natively under gdb, stopped before the first instruction,
and compares the kernel's pc, `sp` modulo 16, `x0 … x30`, the frame's words below `sp`, the bytes
of `mp_mem` and the mappings' permissions with these facts. A `seed` perturbs the model by
lowering `sp` by 8 bytes, moving the entry pc by 4 or setting `x0 = 1`, and the script must
notice.
-/

namespace Millipede.Tests.Differential

open Millipede

/-- The arm64 Linux ABI with a seeded error in its process entry state. -/
def seededLinux : String → Abi A64.isa
  | "sp" => { A64.linux with entryRegs := fun e sp => A64.linux.entryRegs e (sp - 8) }
  | "pc" => { A64.linux with entryRegs := fun e sp => A64.linux.entryRegs (e + 4) sp }
  | "x0" => { A64.linux with entryRegs := fun e sp => (A64.linux.entryRegs e sp).set 0 1 }
  | _ => A64.linux

def b01 (b : Bool) : String := if b then "1" else "0"

/-- The command `differential loader-a64 <dir> [seed]`. -/
def loaderA64 (dir : String) (seed : String) : IO UInt32 := do
  let p := ioProg
  let r : Except String _ := do
    let fp ← Flat.lower p
    let P := (a64Backend).prep (Lin.linearize fp p.memBytes)
    let A ← RegAlloc.A64Reg.selectFb (Compile.a64K {}) (Compile.a64C {}) P
    let obj ← Asm.assemble A64.asm A
    let kc := RegAlloc.A64Reg.kcUsed (Compile.a64K {}) (Compile.a64C {}) P
    let img ← Link.link (Compile.linkConfigA64W kc.1 kc.2 P) [obj]
    pure (P, obj, img)
  match r, compile p arm64Linux with
  | .error e, _ | _, .error e => IO.eprintln s!"loader-a64: {e}"; return 1
  | .ok (P, obj, img), .ok b =>
    match arm64Linux.fmt.write img with
    | .error e => IO.eprintln s!"loader-a64: {e}"; return 1
    | .ok bs =>
      if bs.toArray != b.data then
        IO.eprintln "loader-a64: the image differs from compile's"; return 1
      let path := s!"{dir}/loader.elf"
      IO.FS.createDirAll dir
      IO.FS.writeBinFile path b
      IO.setAccessRights path
        { user := { read := true, write := true, execution := true },
          group := { read := true, execution := true },
          other := { read := true, execution := true } }
      let abi := seededLinux seed
      let s := img.init abi
      let cfg := Compile.linkConfigA64 P
      let lo := Link.limit cfg
      let N := Sel.stackWords cfg
      let σ := Link.resolve (Link.layout cfg [obj]) [obj] 0
      let F := A64.fw ((P.funs[P.main]?).map Lin.Fn.frame |>.getD 0)
      let sp := s.regs.x 31
      IO.println s!"pc {s.regs.pc.toNat}"
      IO.println s!"sp16 {sp.toNat % 16}"
      IO.println s!"xzero {b01 ((List.range 31).all fun k => s.regs.x (BitVec.ofNat 5 k) == 0)}"
      IO.println s!"sptop {b01 (sp == Sel.wa lo N)}"
      IO.println s!"frame {F}"
      IO.println s!"framezero {b01 ((List.range F).all fun k =>
        decodeLE (Sel.bytesFrom s.mem (sp - UInt64.ofNat (8 * (k + 1))) 8) == 0)}"
      match σ Sel.memSym with
      | none => IO.eprintln "loader-a64: no mp_mem"; return 1
      | some D =>
        IO.println s!"mem {D.toNat}"
        IO.println s!"memsize {P.mem}"
        IO.println s!"memrw {b01 ((List.range P.mem).all fun i =>
          let a := D + UInt64.ofNat i
          s.mem.readable a && s.mem.writable a && s.mem.bytes a == 0)}"
        let pg := s.mem.permAt s.regs.pc
        IO.println s!"textrx {b01 (pg.r && !pg.w && pg.x)}"
        return 0

end Millipede.Tests.Differential
