import Millipede.Top.Sound

/-!
# The assumption ledger

`ledger` renders the trust table for one compiled image. It names the program and its externs,
the target and its models, the theorem that covers the bytes and the open claims it depends on,
the quantities it bounds, which are the stack bytes and the instructions per reactor step, and
what is trusted and what is checked. `mpc` writes the ledger next to the bytes.

The trust table is described in doc/design/trust.md.
-/

namespace Millipede

/-- The extern symbols that a term calls, with repetitions. -/
def Exp.externs : {Γ : List Ty} → {t : Ty} → Exp Γ t → List String
  | _, _, .atom _ => []
  | _, _, .let_ e₁ e₂ => e₁.externs ++ e₂.externs
  | _, _, .ite _ e₁ e₂ => e₁.externs ++ e₂.externs
  | _, _, .prim _ _ => []
  | _, _, .call _ body _ => body.externs
  | _, _, .ok _ => []
  | _, _, .err _ => []
  | _, _, .match_ _ eE eO => eE.externs ++ eO.externs
  | _, _, .ext sig _ => [sig.sym]
  | _, _, .extMut sig _ k => sig.sym :: k.externs
  | _, _, .mk _ _ => []
  | _, _, .read _ => []
  | _, _, .assign _ _ k => k.externs
  | _, _, .case _ _ eP eQ => eP.externs ++ eQ.externs
  | _, _, .put _ _ _ k => k.externs
  | _, _, .take (dflt := _) _ _ k => k.externs
  | _, _, .borrowShr _ body k => body.externs ++ k.externs
  | _, _, .borrowMut _ body k => body.externs ++ k.externs
  | _, _, .callRef _ _ body _ k => body.externs ++ k.externs
  | _, _, .guard _ => []
  | _, _, .loop _ _ _ c body k => c.externs ++ body.externs ++ k.externs

/-- Removes repetitions, keeping the first occurrence. -/
def dedup (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The open claims that the theorem covering the bytes of `p` depends on. There are none, because
`compile_sound` covers every image `compile` produces without hypotheses. -/
def openClaims (_p : Program) : List (String × String) := []

/-- What the ledger says about a target. It names the theorem that covers the target's images and
whether that theorem has hypotheses, the target's models, the frame and cost models, the
stack-pointer register, and the trust statements of the target, each of which names its evidence.
`Tests/Ledger.lean` checks that every script and test file named exists. -/
structure LedgerTarget where
  thm : String
  proved : Bool
  isa : String
  abi : String
  elf : String
  phi : FrameModel
  phiName : String
  kappa : CostModel
  kappaName : String
  sp : String
  abiText : List String
  /-- the ISA model and its evidence -/
  isaText : List String
  /-- how the images are run, and whether a model run is compared with the source -/
  runText : List String
  /-- the loader model's page, stack top and user-space top -/
  loaderText : List String
  /-- the modules in which `bv_decide` is used, which are those `#audit` allows it in -/
  trustedEnc : String

/-- The ledger's view of `t`, which is that of `x64Linux` unless `t` is `arm64Linux`. -/
def LedgerTarget.of (t : Target) : LedgerTarget :=
  if t.name == arm64Linux.name then
    { thm := "Millipede.compile_sound_arm64", proved := true, isa := "Millipede.A64.isa",
      abi := "Millipede.A64.linux", elf := "Millipede.Elf.a64Linux", phi := A64.φ,
      phiName := "A64.phi", kappa := A64.κ, kappaName := "A64.kappa", sp := "sp",
      abiText := [
        "- ABI model Millipede.A64.linux: svc #0 with the number in x8: exit = 93 (x0), write = 64 (x0, x1, x2),",
        "  read = 63 (x0, x1, x2; the kernel writes the bytes the oracle supplies to [x1, x1 + x2));",
        "  result in x0; all registers 0 at entry except sp. Evidence: scripts/loader-a64.sh compares the",
        "  model's initial state with the kernel's (gdb, natively)."],
      isaText := [
        "- ISA model (Millipede/Target/A64/*): an AArch64 subset, one 32-bit word per instruction. Evidence:",
        "  llvm-mc and objdump cross-check of the encodings (scripts/a64-encode-check.sh), native co-simulation",
        "  of random instruction sequences against the model (scripts/a64-cosim.sh), the ELF layer against",
        "  readelf, eu-elflint and ld.lld (scripts/a64-elf-check.sh), and native runs of the differential",
        "  suite (scripts/differential-a64.sh)."],
      runText := [
        "  Evidence: MP_TARGET=arm64-linux scripts/mpc-check.sh runs the images natively (the host is aarch64);",
        "  Tests/Top.lean compares the model run with the source."],
      loaderText := [
        "  - the model maps memory in pages of 65536 bytes (2^abi.pageBits, the layout's alignment); kernels",
        "    use 4, 16 or 64 KiB pages, and every segment is padded in the file to whole 64 KiB, so each",
        "    of them maps every byte of the model's pages;",
        "  - the stack is the PT_GNU_STACK p_memsz bytes (rounded up to 64 KiB, at most 4 MiB) directly below",
        "    0x7fffff0000; address randomisation is not modelled (Linux grows the stack on demand up to RLIMIT_STACK);",
        "  - segments start at or above mmap_min_addr = 0x10000 and end below the user-space top 2^39 - 2^16;"],
      trustedEnc := "the AArch64 encode/decode lemmas of Millipede/Target/A64/Word.lean and Decode.lean" }
  else
    { thm := "Millipede.compile_sound", proved := true, isa := "Millipede.X64.isa",
      abi := "Millipede.X64.linux", elf := "Millipede.Elf.x64Linux", phi := X64.φ,
      phiName := "X64.phi", kappa := X64.κ, kappaName := "X64.kappa", sp := "rsp",
      abiText := [
        "- ABI model Millipede.X64.linux: exit = syscall 60 (rdi), write = syscall 1 (rdi, rsi, rdx),",
        "  read = syscall 0 (rdi, rsi, rdx; the kernel writes the bytes the oracle supplies to [rsi, rsi + rdx));",
        "  result in rax; all registers 0 at entry except rsp."],
      isaText := [
        "- ISA model (Millipede/Target/X64/*): x64 subset, canonical encodings only. Evidence: objdump cross-check",
        "  (scripts/x64-encode-check.sh) and co-simulation with qemu (scripts/cosim.sh)."],
      runText := [
        "  Evidence: scripts/mpc-check.sh runs the images under qemu; Tests/Top.lean compares the model run with the source."],
      loaderText := [
        "  - the OS page size is 4096 (2^abi.pageBits);",
        "  - the stack is the PT_GNU_STACK p_memsz bytes (rounded up to pages, at most 4 MiB) directly below",
        "    0x7ffffffff000; address randomisation is not modelled (Linux grows the stack on demand up to RLIMIT_STACK);",
        "  - segments start at or above mmap_min_addr = 0x10000 and end below the user-space top 2^47 - 2^12;"],
      trustedEnc := "the AArch64 encode/decode lemmas of Millipede/Target/A64/Word.lean and Decode.lean, none of which this theorem depends on" }

/-- The backend passes that the ledger names for `t` under options `o`, which are the allocation
with its kind of locations and the selector, as the backend runs them. -/
def backendText (t : Target) (o : Compile.Options) : String :=
  if t.name == arm64Linux.name then
    let k := Compile.a64K o
    let c := Compile.a64C o
    let cregs := ["x4", "x5", "x6", "x7", "x10", "x11", "x12", "x13", "x14", "x8", "x3", "x2", "x1", "x0"]
    let cs := if c = 0 then "" else s!" and {c} caller-saved register locations ({" ".intercalate (cregs.take c)}, not live across an instruction that destroys them)"
    let alloc := if !o.regalloc then "no register allocation (frame slots as linearized), "
      else if k + c = 0 then "validated register allocation with 0 register locations (frame slots only; RegAlloc.check, a refused proposal is not used), "
      else s!"validated register allocation with {k} register locations x19..x{18 + k}{cs}, the rest frame slots (RegAlloc.check, a refused proposal is not used), "
    let sel := if c = 0 then s!"select (A64Reg.select {k}; slot locations if it refuses)"
      else s!"select (A64Reg.select {k} {c}; if it refuses, allocation again with {k} and no caller-saved register locations, then A64Reg.select {k} {c}, A64Reg.select {k} 0 or slot locations)"
    alloc ++ sel
  else
    let k := Compile.x64K o
    let c := Compile.x64C o
    let regs := ["rbx", "rbp", "r12", "r13", "r14", "r15"].take k
    let cs := if c = 0 then "" else s!" and {c} caller-saved register locations ({" ".intercalate (["r8", "r9", "r10", "rdi", "rsi", "rdx"].take c)}, not live across an instruction that destroys them)"
    let alloc := if !o.regalloc then "no register allocation (frame slots as linearized), "
      else if k + c = 0 then "validated register allocation with 0 register locations (frame slots only; RegAlloc.check, a refused proposal is not used), "
      else s!"validated register allocation with {k} register locations {" ".intercalate regs}{cs}, the rest frame slots (RegAlloc.check, a refused proposal is not used), "
    let sel := if c = 0 then s!"select (X64.select {k}; slot locations if it refuses)"
      else s!"select (X64.select {k} {c}; if it refuses, allocation again with {k} and no caller-saved register locations, then X64.select {k} {c}, X64.select {k} 0 or slot locations)"
    alloc ++ sel

/-- The ledger for program `p`, the instance `name` described by `desc`, compiled for `t` to
`size` bytes. `safeThm` names the proof of `p.Safe` that the driver checked, `o` gives the
compiler's options, and `opt` the Core passes that ran. -/
def ledger (name desc : String) (p : Program) (size : Nat) (safeThm : String := "")
    (t : Target := x64Linux) (o : Compile.Options := {}) (opt : String := "none") : String :=
  let L := LedgerTarget.of t
  let dflt := o.regalloc && o.regs == ({} : Compile.Options).regs && o.opt == Opt.Config.all
  let L := if dflt then L else { L with thm := "Millipede.compileWith_sound" }
  let comp := if dflt then "compile"
    else s!"(compileWith \{ regalloc := {o.regalloc}, regs := {o.regs}, opt := {o.opt.on} })"
  let ext := dedup (p.init.externs ++ p.step.externs)
  let κ := L.kappa
  let ω0 : Oracle := ⟨fun _ _ => ⟨0, []⟩⟩
  let costLines : List String := [
    s!"  - instructions: reactor step 0 (init) <= {p.stepCost 0 ω0 κ}, every later step <= {p.stepCost 1 ω0 κ}",
    s!"    (for the oracle answering 0; the bound p.stepCost k omega {L.kappaName} is per oracle)",
    s!"    (cost model {L.kappaName}: atom {κ.atom}, let {κ.let_}, ite {κ.ite}, prim {κ.prim}, div {κ.div}, loop {κ.loop}, iter {κ.iter}, call {κ.call}, ctor {κ.ctor}, match {κ.match_}, ext {κ.ext}, word {κ.word}, place {κ.place}, mem {κ.mem})",
    s!"  (compile checked the instruction budget of the selected code against {L.kappaName}.)"]
  let thm : List String := [
      "pipeline  : values in byte memory, root in static storage mp_mem: lower, linearize,",
      s!"            {backendText t o},",
      "            budget check, assemble, link, ELF write;",
      s!"            static data region {p.memBytes} bytes",
      "",
      "== What is proved about these bytes ==",
      (if L.proved then s!"{L.thm} (no hypotheses): the full statement CompileSound.Statement {comp}"
       else s!"NOT PROVED for this target: {L.thm} would have the statement CompileSound.Statement {comp}"),
      s!"  {t.name} (Millipede/Top/Statement.lean). Lawfulness holds by construction: every lens, constructor",
      "  and split of the program carries a certificate that it agrees with the byte layout, which compile",
      "  checked (Exp.certified; Millipede.compile_lawful). With the program's safety, the bytes load, and",
      "  for every oracle the machine never gets stuck, its event trace equals the source trace p.events,",
      s!"  {L.sp} stays within p.stackBytes {L.phiName} = {p.stackBytes L.phi} bytes below its start, and:"] ++
      costLines ++ [
      "  compile also checked (decidably): the lowered fragment (Exp.memOk; references are pointers,",
      "  justified by the borrow checker Program.wf, which implies the block rule), the certificates of",
      "  the building blocks (Exp.certified); the Lin stack bound <= p.stackBytes is a theorem",
      "  (Lin.linearize_stackBytes_le)."]
  let lines : List String := [
    "Millipede assumption ledger (doc/design/trust.md)",
    "",
    s!"program   : {name} -- {desc}",
    s!"externs   : {if ext.isEmpty then "none" else ", ".intercalate ext}",
    s!"target    : {t.name} (ISA model {L.isa}, ABI model {L.abi}, static ELF64 {L.elf})",
    s!"image     : {size} bytes",
    s!"optimised : {opt} (Core passes; the theorem covers every configuration)",
    s!"safety    : {if safeThm.isEmpty then "NOT CHECKED" else safeThm ++ " : p.Safe (proved; the premise of compile_sound)"}"] ++
    thm ++ [
    "",
    "== Open claims (doc/open-claims.md) =="] ++
    (if (openClaims p).isEmpty then ["none"] else (openClaims p).map (fun (n, d) => s!"- {n}: {d}")) ++ [
    "",
    "== Trusted ==",
    s!"- Lean kernel. bv_decide is used only in {L.trustedEnc}; #audit refuses it in any other module and",
    "  scripts/audit.sh lists the lemmas the theorem depends on.",
    "- Lean's compiler and runtime, to execute `compile` (these bytes come from running it natively)."] ++
    L.runText ++ L.isaText ++ L.abiText ++ [
    "- Loader / process-entry model (Millipede/Object/Elf/Load.lean):"] ++ L.loaderText ++ [
    "    a segment's bytes beyond its file size are zero (.bss);",
    "  - argv/envp/auxv and the vDSO are not modelled (the program never reads them).",
    "- Extern bindings: the oracle answers `write` and `read` with an arbitrary result word and `read` with",
    "  arbitrary bytes (any oracle is allowed, so every OS answer, every input, is covered); `exit` ends the trace.",
    "- The statement: CompileSound.Statement (Millipede/Top/Statement.lean). Review.",
    "",
    "== Not trusted (proved) ==",
    "mp def elaboration (each function re-checked by the kernel), lower (the open claims above, if any),",
    "linearize, the register-allocation checker (the allocator itself is untrusted: a proposal the checker",
    "refuses is not used), select, assemble, link, the ELF writer, the arena library (Millipede/Lib)."]
  "\n".intercalate lines ++ "\n"

end Millipede
