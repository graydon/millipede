# Status

This document records the state of `main`, with one table per subsystem. It is written from
the code, and where another document disagrees with the code, the code is right.

Each feature is in one of the following states. A proved feature has a theorem that the kernel
checks, with no `sorry` and no axiom beyond those `#audit` allows. A trusted feature is a model
that tests compare with the real thing. A tested feature has tests and no theorem. A construct
that is refused by `compile` is rejected with a message, so the correctness theorem never has to
cover it. A feature that is not built is planned.

There are no unproved statements: scripts/audit.sh finds no `.Statement` that is neither proved
nor listed in [open-claims.md](open-claims.md). Figures such as code size, instruction counts and
proof burden are in [measurements.md](measurements.md).

## The theorem

| feature | state | evidence |
|---|---|---|
| `CompileSound.Statement compile x64Linux` | proved, no hypotheses | `Millipede.compile_sound` (Millipede/Top/Sound.lean) |
| `CompileSound.Statement compile arm64Linux` | proved, no hypotheses | `Millipede.compile_sound_arm64` (Millipede/Top/SoundA64.lean) |
| the statement for every setting of the options | proved | `compileWith_sound` (Millipede/Top/SoundA64.lean) |
| one composition for every backend | proved | `compile_sound_of_backend` (Millipede/Top/Sound.lean) |
| `compile` refuses what the checker rejects | proved | `compile_wf` (Millipede/Top/Sound.lean) |
| every accepted building block is lawful | proved | `compile_lawful` (Millipede/Top/Sound.lean) |
| per-program corollaries, given `compile p t = .ok b` | proved; acceptance by compiled evaluation | `Examples.revProg_sound` (Millipede/Top/Examples.lean), `reqsPool_sound`, `reqsBump_sound` (Millipede/Top/Requests.lean) |
| what `hello` and `revchunks` do, for every oracle, carried to the bytes | proved, given `compile p t = .ok b` | `hello_events`, `revProg_events` (from the contracts `helloInit.spec`, `revStep.spec`, both proved automatically), `revProg_rounds`, `hello_behaviour`, `revProg_behaviour` (Millipede/Top/Behaviour.lean); Tests/Witness.lean |
| what the key-value server `kvsrv` does, for every oracle, carried to the bytes | proved, given `compile kvsrv t = .ok b`: its trace is that of an abstract key-value store | `kvsrv_events` (from the contracts `srvStep.spec`, `fill.spec`, Tests/FormatKVSrv.lean, through `kvsrv.events_reach`), `kvsrv_behaviour`, `kvsrv_answers` (Tests/KVRefine.lean) |
| `compile` accepts `exit42`, `hello` on both targets, with the default options | proved by kernel evaluation; theorems without hypothesis | `hello_runs`, `exit42_runs` (Millipede/Top/Accept.lean) |
| `compile` accepts `revchunks` with the default options | open: `CompileAccepts.Statement`; `#guard` | Millipede/Top/Accept.lean; Tests/Witness.lean |
| the whole pipeline agrees with the source on the model | tested | Tests/Top.lean (`agrees`, `eventsInBudget`) |
| instruction and stack bounds against runs under qemu, both targets | tested; step bounds 1.7 to 8.6 times the largest step of the registered programs (11 to 17 for `upper` and `kvsrv`), the image's stack request 1.0 to 1.5 times the stack used | scripts/bound-check.sh (`--selftest`), scripts/step-measure.py; doc/measurements.md |
| the machine's stack within the size the image asks for, which is at most `p.stackBytes` | proved, no hypotheses, both targets | `compile_stack_tight`, `compile_stack_tight_arm64` (Millipede/Top/StackTight.lean) |
| the driver compiles only programs with a proof of `p.Safe` | built | `Entry` (Millipede/Top/Driver.lean), `#mp_compile` (Millipede/Meta/Emit.lean); Tests/Driver.lean |

## Surface language and elaborator

| feature | state | evidence |
|---|---|---|
| `mp def`: Core term, normal form `f`, `f.exp_denote` | proved per definition (kernel) | Millipede/Meta/Elab.lean; Tests/MpDef.lean, Tests/MpDef2.lean |
| bodies in Lean's `do` notation, `mp program` | proved per definition | Millipede/Meta/Syntax.lean, Millipede/Meta/Program.lean; Tests/DoNotation.lean |
| linearity and borrow check with source positions | tested; the kernel re-checks `f.wf` by `decide` | Millipede/Meta/ANF.lean; Tests/MpDef2.lean |
| `deriving Data` (structs, enums, certified lenses, constructors, splits) | proved per type | Millipede/Meta/Derive.lean; Tests/Derive.lean, Tests/Layout.lean, scripts/layout-check.sh |
| loops, `let mut`, assignment, borrows, slices, pairs of places | proved per definition | Tests/LoopRef.lean, Tests/Slice.lean, Tests/PairRef.lean, Tests/Bytes.lean |
| statements in `do` notation: `for i in lo...hi`/`lo...=hi`, `break`, `continue`, `return`, place assignment | proved per definition; tested on both targets (differential, seeded translation bugs) | Tests/DoNotation.lean, Tests/Differential/DoFuncs.lean |
| `mp extern` (`write`, `read`, `exit`) | proved per definition | Tests/MpDef.lean, Tests/ByteBuf.lean |
| sealed structs (private constructor: unforgeable keys) | tested | Tests/Brands.lean |
| `#mp_cost` | tested | Tests/MpDef.lean |
| `#mp_report` | tested; lists the stack per target | Millipede/Meta/Report.lean; Tests/Modules.lean |
| `#mp_analyse` | tested | Millipede/Meta/Analyse.lean; Tests/Tutorial.lean (`closerOf`, `digit`) |
| `#mp_asm`, `#mp_bytes` | not built | — |
| `inline` definitions with block parameters | not built | doc/open-claims.md "Not built" |

## Core semantics and checker

| feature | state | evidence |
|---|---|---|
| terms, value semantics `Exp.denote` | definitions | Millipede/Core/Exp.lean, Millipede/Core/Denote.lean |
| instrumented semantics within the static cost | proved | `Exp.exec_sound` (Millipede/Core/Cost.lean) |
| stack and footprint used within the static bounds, in Core | proved, not used by `compile_sound`, whose stack clause comes from `Lin.lower_linearize_stackBytes_le` | `Exp.stackUse_le`, `Exp.footUse_le` (Millipede/Core/Stack.lean) |
| borrow checker guarantees (`Exp.Frozen`) | proved | `Exp.frozen_of_wf` (Millipede/Core/WfSound.lean) |
| checked forms are safe without proof | proved | `Exp.readChk_safe` (Millipede/Core/Checked.lean) |
| total terms are safe | proved | `Exp.safe_of_total` (Millipede/Core/Safe.lean) |
| certified lens/constructor/split laws for derived shapes | proved | Millipede/Core/Lawful.lean |
| C layout of structs and sums | tested against gcc | scripts/layout-check.sh (with `--selftest`), Tests/Layout.lean |

## Obligations, contracts, analyser

| feature | state | evidence |
|---|---|---|
| `requires`/`ensures`: `f.spec` (`@[spec]`), `f.post` | proved per definition | Millipede/Meta/Contracts.lean; Tests/Contracts.lean |
| `mp program … invariant I`: `p.inv`, `p.safe` | proved per program, from `Program.safe_of_inv` | Millipede/Meta/Spec.lean; Tests/ProgramInv.lean, Tests/Reactor.lean |
| `mp_safe`, `mp_loop_inv`, `mp_loop_lift` | tested | Tests/LoopRef.lean, Tests/Slice.lean |
| `mp_auto` | tested, with negatives | Tests/Reactor.lean (`rPushBad`, `rStepBad` not proved); how often it suffices: measurements.md |
| `vcgen` on every normal form, no workaround | tested | `expandTupCarriers` (Millipede/Meta/Elab.lean); doc/upstream/vcgen-carrier.lean |
| `+ - *` wrapping, `+! -! *!` obligated, `+? -? *?` checked | proved per definition | Millipede/Meta/Overflow.lean; Tests/Overflow.lean, Tests/Differential/OverflowFuncs.lean |
| verified analyser (intervals, loop growth bounds) | proved | `Exp.an_sound`, `Exp.safe_of_safeBy` (Millipede/Analysis/Sound.lean) |
| partial certification (relaxed term, computed with the analysis by `Exp.anR`) | proved | `Exp.relax_denote`, `Exp.safe_of_relax` (Millipede/Analysis/Sound.lean) |
| analyser certifies programs and refuses wrong ones | tested | Tests/Analysis.lean, Tests/Overflow.lean |
| `Exp.LoopsOk`, the analyser's hypothesis | proved per definition (`rfl`), not decided | doc/open-claims.md "Automation limits" |
| `f.safe` and `f.spec` in one `vcgen` run | not built (two proofs) | doc/open-claims.md "Not built" |
| `ensures` about events (`history`, `events`, `exited`); `p.reach`, `p.events_reach` from the contracts of `init` and `step` | proved per definition; also for a `step` with a `requires`; the automatic attempt finds a loop's invariant only for a contract `events = t` with `t` naming the loop's bound | `Spec.eventSpecH`, `Spec.runE_of_triple` (Millipede/Meta/Spec.lean), `Program.reach_of_contracts`, `Program.reach_of_contracts_req` (Millipede/Meta/Reach.lean); Tests/EnsuresEvents.lean; `revStep.spec`, `helloInit.spec` (Millipede/Top/Examples.lean), `srvStep.spec` (Tests/FormatKVSrv.lean) |
| analyser inputs: callee `ensures`, fields of reference parameters, relational facts | not built | doc/open-claims.md "Automation limits" |
| listing of indices and slice bounds computed with a wrapping `+ - *` | tested (`#mp_report`); loop bounds, conversions, a gate check not built | `Millipede.Wraps` (Millipede/Meta/Report.lean); Tests/Overflow.lean |

## Modules, interfaces, brands, units

| feature | state | evidence |
|---|---|---|
| generic definitions under `variable` binders (types, sizes, hypotheses, implementations): Core term, `wf`, `safe`, contract, program safety, each one theorem | proved | Millipede/Meta/Elab.lean; Tests/Generic.lean; Millipede/Lib/Pool.lean, Bump.lean |
| `deriving Data` for parameterised structures and enums | proved (layout laws once) | Millipede/Meta/Derive.lean; Tests/Generic.lean `GBump`, `Opt`, `Tri` |
| interfaces (`mp interface`, generated hygienically), implementations (`mp implementation`, an operation's contract its `mp def`'s), clients proved once, instances by application | proved | Millipede/Meta/Iface.lean; Tests/Modules.lean, Tests/Tutorial.lean (`Counter`); Millipede/Lib/Alloc.lean; Millipede/Top/Requests.lean, Tally.lean |
| a generic callee's variables at a call: from the expected type, the arguments, instances, hypotheses, the one context variable of its type; else named in the error | tested | Millipede/Meta/Elab.lean `inferGen`; Tests/Generic.lean (`Ctx.twice`, `outside`), Tests/Ring.lean (`rInit`) |
| one client over two allocators, both compiled | proved | `reqsPool_sound`, `reqsBump_sound`; scripts/mpc-check.sh (`reqspool`, `reqsbump`) |
| key brands (the key type); use after free rejected | tested | Tests/Brands.lean |
| held-key accounting proved once (`Alloc.Holds`, `Alloc.KeyStack`) | proved | Millipede/Lib/Alloc.lean, Millipede/Lib/Bump.lean |
| per-value brands, ghost set of outstanding keys | not built | doc/open-claims.md "Not built" |
| analyser, numeric figures and `Program.wf` of code over an implementation variable | closed instances only; decided per instance | doc/open-claims.md "Modules and brands" |
| interface relations between operations; `footprint` syntax | not built | doc/open-claims.md "Not built" |
| `mp dimension`, `mp unit`, `Q u` erased to `U64` | proved (`inBase` lemmas); tested | Millipede/Core/Quantity.lean, Millipede/Meta/Units.lean; Tests/Units.lean, Tests/Differential/UnitFuncs.lean |
| a size computation in mixed units, all obligations by the analyser | proved | Tests/Units.lean ("The exit example of phase 3") |
| `exactTo`, `cmp` across scales, quantity fields of derived structs | not built | doc/open-claims.md "Not built" |

## Compiler stages

| stage | state | evidence |
|---|---|---|
| `lower`: Core → Flat, values in byte memory, references as pointers | proved on everything accepted | `Flat.lowerM_sound` (Millipede/Compile/LowerSound.lean); Tests/Lower.lean |
| hand-back of `&mut` slices | proved | `Exp.hb_sound`, `Exp.hbx_exact` (Millipede/Compile/HandBack.lean) |
| small never-borrowed values kept in frame slots | proved (same theorem) | `Ty.slotTy` (Millipede/Compile/Lower.lean); Tests/Differential/SlotFuncs.lean |
| constructs outside `Exp.memOk` | refused by compile (message from `Exp.memWhy`) | doc/open-claims.md "Still refused by `compile`"; refusal step of scripts/differential.sh |
| values kept in memory that could be in slots | sound, not optimised | doc/open-claims.md "Not built" (values that stay in memory) |
| bounds of lowered accesses | proved | `Lin.lowerInBounds` (Millipede/Compile/LinearizeLower.lean) |
| `linearize`: Flat → Lin | proved | `Lin.linearize_sim`, `Lin.lower_linearize_sound` (Millipede/Compile/LinearizeProof.lean, LinearizeLower.lean); Tests/Lin.lean |
| Lin stack within Core's bound; frame discipline | proved | `Lin.lower_linearize_stackBytes_le`, `Lin.lower_linearize_wf` (Millipede/Compile/LowerStack.lean) |
| `select`: Lin → Asm, one proof for both instruction sets | proved | `Sel.select_lower_sound` (Millipede/Target/SelSim.lean), from the simulation that the definition `Sel.selectSim` builds; `X64.select_lower_sound` (Millipede/Target/X64/Pipeline.lean); Tests/Select.lean, Tests/SelectLoops.lean, Tests/A64Select.lean |
| instructions per reactor step | proved, given the per-program budget check | `Sel.select_lower_cost`; `X64.budgetOk` (Millipede/Target/X64/Budget.lean), `A64Reg.budgetOk` |
| `assemble` | proved | `Asm.assemble_text`, `Asm.assemble_decode` (Millipede/Compile/AssembleLaws.lean), `X64.asmLaws` (Millipede/Compile/AssembleProof.lean) |
| `link` | proved | `Asm.link_assemble`, `X64.init_of_link` (Millipede/Object/LinkProof.lean, Millipede/Target/X64/Pipeline.lean); Tests/Link.lean |
| ELF writer and loader model | proved (writer); loader trusted | `Elf.load_write`, `Elf.x64Linux_laws` (Millipede/Object/Elf/Laws.lean); Tests/Elf.lean, scripts/elf-check.sh |
| PE32+ writer and loader model for x64 Windows, used by no target | proved (writer); loader trusted; never run on Windows | `Pe.load_write`, `Pe.loadWith_write`, `Pe.iatSlots`, `Pe.win64_laws` (Millipede/Object/Pe/Laws.lean); Tests/Pe.lean, scripts/pe-check.sh |
| Core passes `inline`, `fold`, `dce`, `strength` | proved (meaning and safety kept); cost and stack bounds checked per program; every program of the suites compiles with every pass | `Opt.Pass.apply_sim`, `Opt.Config.optimize_sim`, `Exp.subst_denote` (Millipede/Opt/); Tests/Opt.lean, scripts/opt-compare.sh; gains in measurements.md |
| register allocation, Lin → Lin | proved; on by default on both targets, off with `mpc --no-regalloc` | the lock-step refinement that the definitions `RegAlloc.lockOfCheck` and `RegAlloc.allocOrId_lock` build (Millipede/RegAlloc/Sound.lean); Tests/RegAlloc.lean (seeded allocator bugs); both differential suites with allocation on and off |
| register locations: 6 preserved by default, `x19 …` on arm64, `rbx rbp r12 … r15` on x64, saved through the callee's frame, and caller-saved ones for values live across no instruction that destroys them, 14 on arm64 (`x4…x7, x10…x14`, `x8` and `x0…x3`; an extern call destroys `x8`, `x0…x2`) and 6 on x64 (`r8 r9 r10 rdi rsi rdx`; an extern call destroys `rdi rsi rdx`, a division `rdx`, a remainder `rdi rsi rdx`), with arguments, `ret`'s operands, call results and the arguments of a buffer `write`/`read` each by a parallel move (`Sel.PMove.seq_run`, `Sel.Ops.ExtLaws.run_seq`, `A64Reg.run_retR`, `X64.run_retW`), so an operand or result may sit in any argument or result register, the allocator trying that register first and the clobber check `Live.clobOk`, with no frame word (`Sel.frameW`; allocated frames checked in words, `RegAlloc.frameOk`; the linked stack bound is `P.stackBytes (φ.words k c)` ≤ `P.stackBytes φ`, `Lock.stackBytes`); a call saves only the registers live after it and writes only the callee locations live at its entry; a move of a location to itself has no code; arm64 `add`/`sub` immediates and zero stores from `xzr` | proved | the self-simulation that the definition `RegAlloc.Live.flex` builds, `Sel.StepOkAt`; `A64Reg.cases`, `A64Reg.entry_ok`, `a64Backend_laws`; `X64.cases`, `X64.sim_entry`, `X64.pkg_laws` (Millipede/Target/X64/SelectCall.lean), `x64Backend_laws`; register-selector mutants in both differential self-tests (`xreg-slot-move`, `xreg-last-arg`, `areg-slot-move`, `areg-last-arg`, `areg-imm`, `areg-zero-store`, `xreg-clobber`, `xreg-div-clobber`, `xreg-sys-clobber`, `xreg-res-clobber`, `areg-clobber`, `areg-sys-clobber`, `areg-res-clobber`, `xreg-pmove`, `areg-pmove` among them); swapped `ret` and permuted `write` in Tests/RegAlloc.lean; Tests/A64Frames.lean, Tests/X64Frames.lean; Tests/Select.lean |
| data-region addressing (`Options.memBase`, on by default; `mpc --no-membase` gives the old code byte for byte): x64 loads and stores `lea r11, [rip + mp_mem]; mov d, [r11 + a + off]` (a SIB operand), stores an immediate by `mov qword/byte [m], imm` and uses 32-bit immediates in `add sub and or xor cmp` (`X64.stImm`, `X64.binImm`); arm64 keeps the address in `x29` (set at every entry) and loads and stores `[x29, a]` or `add x16, a, #off; [x29, x16]` | proved | `Sel.Ops.MemLaws`, `Sel.Ops.sim_load`/`sim_store` (Millipede/Target/SelOps.lean), `X64.selOps_memLaws`, `X64.run_memX_disp` (Millipede/Target/X64/SelectProof.lean); `Sel.Conv.regOk`, `Sel.StraightC`, `Sel.runIs_regOk` (Millipede/Target/SelFrame.lean), `A64Reg.selOps_memLaws`, `A64.run_entryB`, `A64Reg.retR_k29` (Millipede/RegAlloc/A64RegProof.lean, A64RegCall.lean, Millipede/Target/A64/SelectProof.lean); `X64.parse_encode` (SIB, `C7 /0`, `C6 /0` without `bv_decide`), `X64.run_stImm`, `X64.binImm_correct`, `X64.run_okIn`; mutants `xmem-disp`, `xmem-base`, `xmem-index`, `xstore-imm`, `xcmp-imm`, `xcmp-signed` in the x64 differential self-test and `amem-disp`, `amem-base-call`, `amem-no-base` in the arm64 one; co-simulation of `[r+r+d]` and the immediate stores with seeded bugs 9 (SIB scale 2) and 10 (byte immediate); Tests/Select.lean |
| identity operations as moves (`Options.idOps`, on by default; `mpc --no-idops` gives the old code byte for byte): before allocation, `bin op x a w` with `w` a right identity of `op` (`add sub bor bxor shl shr` by 0, `mul udiv` by 1) becomes `mov x a`, so `bor x, x, 0` and `mul i, i, 1` select to no code on both targets | proved | `RegAlloc.step_idOps`, `RegAlloc.stackBytes_idOps`, `RegAlloc.Lock.pre` (Millipede/RegAlloc/IdOps.lean), `Compile.prep_lock`; mutant `xidop-trunc` in the x64 differential self-test |
| analyser-driven constant propagation and check elimination (blocked: `Exp.LoopsOk` not decidable), CSE; backend optimisations | not built | doc/open-claims.md (Core optimisation); [roadmap.md](roadmap.md) |
| Mach-O writer and loader model for arm64 macOS; no target uses it | proved (writer); loader trusted; good files ran on a Mac once, by hand | `MachO.load_write`, `MachO.a64Macos_laws`, `MachO.load_wxorx` (Millipede/Object/MachO/Laws.lean); Tests/MachO.lean, scripts/macho-check.sh |
| ELF64 relocatable objects (x86-64, AArch64) and reader model | proved (round trip, linking the read-back objects); system linker trusted, tested only | `ElfRel.read_write`, `ElfRel.link_norm`, `ElfRel.link_read_write` (Millipede/Object/ElfRel/Laws.lean); Tests/ElfRel.lean, scripts/elfrel-check.sh |
| `Compile.objects`: a program's relocatable object, the one its executable is linked from | proved; no driver option | `Compile.objLink_compileRun`, `Compile.objOf_link` (Millipede/Object/ElfRel/Objects.lean); Tests/ElfRelEmit.lean |
| calls between compiled code and C; macOS and Windows targets | not built; a C `_start` can call a program's entry | [roadmap.md](roadmap.md) |

## Targets

| feature | state | evidence |
|---|---|---|
| x64 ISA model (subset), decoder accepts only canonical encodings | trusted; laws proved | `X64.decode_encode` (Millipede/Target/X64/Laws.lean) |
| encoder agrees with GNU objdump | tested | scripts/x64-encode-check.sh, Tests/X64.lean |
| model agrees with qemu-x86_64 on random sequences | tested, with seeded bugs | scripts/cosim.sh (`--selftest`), Tests/CoSim/Main.lean |
| arm64 ISA model (subset, no indirect branch but `ret`), canonical decoding | trusted; laws proved | `A64.decode_encode` (Millipede/Target/A64/Decode.lean); scripts/a64-encode-check.sh, scripts/a64-cosim.sh |
| Linux system calls `read`, `write`, `exit` (`X64.linux`, `A64.linux`) | trusted | the ledger text (Millipede/Top/Ledger.lean); scripts/mpc-check.sh, scripts/loader-a64.sh |
| cost models `X64.κ`, `A64.κ`: per target, each weight a count of the construct's selected code (doc/design/resources.md) | checked per program; no test program refused in any register-allocation setting or pass configuration | `X64.budgetOk`, `A64Reg.budgetOk`; scripts/kappa.lean (`KAPPA=…`) |
| arm64 Linux target | built; run natively and on the model | `arm64Linux`, `a64Backend` (Millipede/Top/Compile.lean), `A64.init_of_link`; Tests/Top.lean, Tests/A64Reach.lean; `lake exe mpc --target arm64-linux` |
| other ABIs | not built | [roadmap.md](roadmap.md) |

## Libraries

| feature | state | evidence |
|---|---|---|
| pool arena `Pool T n W` (`Pool8`, `Pool100`) | proved (contracts) | Millipede/Lib/Pool.lean; Tests/Lib.lean |
| bump arena `Bump T n` (`Bump8`, `Buf16`) | proved (contracts) | Millipede/Lib/Bump.lean; Tests/Modules.lean |
| byte buffer `ByteBuf cap` | proved (contracts, once for every capacity) | Millipede/Lib/ByteBuf.lean; Tests/ByteBuf.lean |
| slice helpers `Slice.fill`, `copy`, `reverse` on `&mut [T; n]` | proved (contracts, once for every `T` and `n`) | Millipede/Lib/Slice.lean; Tests/Slice.lean |
| standard units | definitions | Millipede/Lib/Units.lean |
| format descriptions `Fmt`: parser, writer, validator, static bound | proved for every description: round trip, length bound, soundness, canonical parse and injectivity, validator equals parser | `Fmt.parse_write` … `Fmt.valid_iff` (Millipede/Format/Theorems.lean); Tests/Format.lean |
| format leaves in Millipede: integers, byte strings (fixed and length-prefixed), constants, ignored bytes, repetitions; parsers, writers and validators | proved (contracts against the model, once for every slice bound) | Millipede/Format/Code.lean, Leaves.lean, Seq.lean |
| `mp format`: parser, writer and validator generated from a structure and a description | proved by the command for each format (`T.parseAt.spec`, `T.writeAt.spec`, `T.validAt.spec` and `safe`); a failed proof stops the command and leaves nothing; the step from the text to the description and `T.toVal` is trusted | Millipede/Meta/FormatGen.lean; Tests/FormatKV.lean, Tests/FormatGen.lean; Tests/FormatGenFail.lean (rejections, two seeded generator bugs) |
| key-value request and response | generated by `mp format` (contracts against `reqFmt` and `respFmt`), used by `kvsrv` and its refinement theorem | `KReq.parseAt.spec`, `KResp.writeAt.spec` (Tests/FormatKV.lean) |
| batch echo program over a generated format with every form | proved safe; run on both targets against an independent reference | `batchEcho.safe` (Tests/FormatGenProg.lean); scripts/format-check.sh |
| key-value server `kvsrv` | proved: safe; `handle` answers a request as `kvStep` does; run on both targets against an independent reference | `kvsrv.safe`, `handle.spec` (Tests/FormatKVSrv.lean); scripts/format-check.sh (`--selftest`) |
| the server refines an abstract key-value store | proved for every oracle and carried to the bytes: the trace is the reads, a `write` of each response of the abstract store (a map of at most 4 keys) to the requests decoded by `Fmt.parse reqFmt`, then `exit 0`, or `exit 1` at the first malformed request; the four slots refine the map; a get after a put answers the value put; one server, one machine, one-sided | `kvsrv_events`, `kvServe_refines`, `kvsrv_answers`, `kvsrv_put_get` (Tests/KVRefine.lean); the machine in Tests/KVSpec.lean; scripts/format-check.sh compares `kvTrace` with the Python reference |
| code derived from a description; validators, field readers and the leaves for repetitions, fixed byte strings and constants in Millipede | planned | doc/open-claims.md |
| registered programs (`mpc --list`) | run under qemu and natively on arm64; `Safe` proved for every entry (the registry cannot hold one without it) | `Examples.registry` (Millipede/Top/Examples.lean); scripts/mpc-check.sh (`--selftest`) |

## Tests and mutants

| suite | what it checks | teeth |
|---|---|---|
| scripts/differential.sh | compiled functions vs independent references, under qemu; every case read at run time, and a guard that the dividing functions' images divide | `--selftest`: seeded mutants (Tests/Differential/Mutants.lean); the guard rejects an image without a division |
| scripts/differential-srcseed.sh | a bug seeded in the compiler source | slow; not in the gate |
| scripts/cosim.sh | ISA model vs qemu, every addressing form of the selector, a new seed each run | `--selftest`: seeded encoder bugs and model bugs (carry after `sub`, shift count mask, `div` remainder) |
| scripts/bound-check.sh | proved instruction and stack bounds vs runs under qemu, both targets | `--selftest`: instruction bounds divided by 16 and stack bounds by 2 must both fail |
| scripts/mpc-check.sh | every `mpc` instance under qemu, ledger written | `--selftest` |
| scripts/layout-check.sh | layouts vs gcc | `--selftest` |
| scripts/elf-check.sh, scripts/x64-encode-check.sh | ELF files, encoder | corrupted files (elf-check); no `--selftest` |
| scripts/differential-a64.sh | the differential suite compiled for arm64, run natively; cost regression | `--selftest`: arm64 selection mutants (`a64Mutants`); a mutant whose generation fails is an error |
| scripts/a64-cosim.sh | arm64 ISA model vs this CPU (native harness), with `read`, `write` and `exit` on pipes in a child process; a new seed each run | `--selftest`: seeded model and encoder bugs, a wrong system-call result |
| scripts/a64-encode-check.sh | arm64 encoder vs llvm-mc and objdump | `--selftest`: seeded encoder bugs |
| scripts/a64-elf-check.sh | arm64 assemble/link/ELF (Tests/A64Obj.lean) vs readelf, eu-elflint, ld.lld, GNU ld; runs natively | seeded corruptions and fixup bugs (an `adrp` one page off, a branch unscaled, …) |
| scripts/macho-check.sh | Mach-O files and SHA-256 vs sha256sum, llvm-readobj, llvm-otool, llvm-objdump, an independent Python checker and ld64.lld | `--selftest`: a wrong SHA-256 constant, re-signed corruptions, a wrong signature identifier, a wrong hash of the last partial page |
| scripts/elfrel-check.sh | ELF relocatable objects vs `<elf.h>`, readelf, llvm-readobj, an independent Python reader and GNU as's section flags; three programs linked by GNU ld and ld.lld and run on both machines; links with C | `--selftest`: seven bugs seeded into the written files; Tests/ElfRel.lean: 29 corrupted files |
| scripts/loader-a64.sh | the arm64 loader model's initial state vs the kernel's (gdb) | `--selftest`: a seeded model error |
| scripts/pe-check.sh | PE32+ files vs llvm-readobj and lld-link's files, disassembly, runs under wine (box64) | `--selftest`: eight bugs seeded into a file; Tests/Pe.lean: 36 corrupted files |
| `MP_TARGET=arm64-linux scripts/mpc-check.sh` | every `mpc` instance natively on arm64 | `--selftest` |
| Tests/Top.lean | compiled images run on each target's machine model: trace, instructions ≤ κ, stack ≤ φ | a zero cost model fails on both targets |
| Tests/Ledger.lean | each target's ledger names evidence that exists, and `#audit`'s `bv_decide` modules | three guards fail on an earlier arm64 ledger that named no co-simulation |
| `#guard_msgs` negatives in Tests/*.lean | refusals and failed proofs | each suite's own negatives |

## Tooling

| tool | state | evidence |
|---|---|---|
| `#audit`, `#audit_ledger` | tested, with seeded axioms | Millipede/Meta/Audit.lean; Tests/Audit.lean |
| scripts/audit.sh (`.Statement` ledger) | in the gate | scripts/check.sh |
| `mpc` driver and assumption ledger | tested | Mpc.lean, Millipede/Top/Ledger.lean; scripts/mpc-check.sh |
| proof-burden classifier | shared by `#mp_report` and the script | Millipede/Meta/Burden.lean; scripts/proof-burden.sh |
| measurements | scripts | scripts/measure.sh, scripts/kappa.lean |
| `scripts/leanq` | tool | scripts/leanq.py |
| CI configuration | not built | no `.github/` in the repository |

## Capabilities and typestate

| feature | state | evidence |
|---|---|---|
| `Exp.syms` covers every event a run appends, under every oracle | proved | `Exp.denote_syms` (Millipede/Core/Effects.lean) |
| `NoCalls` of a term and of a program from `syms` | proved | `Exp.noCalls_of_syms`, `Program.noCalls_of` (Millipede/Core/Effects.lean) |
| a program's `NoCalls` holds of the machine trace of its compiled code | proved | `Program.NoCalls.machine`, `.x64`, `.arm64` (Millipede/Top/NoCalls.lean) |
| tokens `Cap c`: zero size, linear, sealed; `Cap.drop` | proved per type (layout laws) | Millipede/Lib/Cap.lean; Tests/Tokens.lean (forging, duplication, loss) |
| `mp capability`, extern token parameters, the authority check of `mp def` with `f.noCalls` | proved per definition; the check is elaborator code | Millipede/Meta/Cap.lean, Millipede/Meta/Elab.lean; Tests/Tokens.lean |
| `mp program` grants through `init`'s token parameters, with `p.noCalls` for the classes not granted | proved per program | Tests/Log.lean (`logProg.noCalls`), Tests/Tokens.lean (`readOnly.noCalls`) |
| typestate on a handle: wrong state, use after close, double close, leak rejected | tested | Tests/Log.lean (`Log s`), Tests/Tokens.lean |
| a program with tokens and a handle, compiled for both targets | tested (traces by `#guard`; run by hand) | Tests/Log.lean (`logProg`) |
| classes finer than a symbol, attenuation, typestate transitions to a sum of states | not built | doc/open-claims.md "Not built", Surface and tooling |

## Discrepancies

Differences of substance between the design and the code are listed in
[design/deviations.md](design/deviations.md). One discrepancy found by the documentation audit is
still open: the module documentation of Millipede/Meta/Syntax.lean.