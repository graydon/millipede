# Decisions

The log of decisions about Millipede's design and the way it is built: the owner's decisions and
stated preferences, and the choices written into the signed-off plan. Read top to bottom. Each
entry: context, decision, consequence, date and where it was taken, and who took it ("owner
decision", or the plan's or orchestrator's choice; "uncertain" where the record does not say).
Numbers 1–14 are those of the old plan's section 16; new entries are
appended with the next number. Where the code differs from a decision, see
[deviations.md](deviations.md).

Part of the design ([index](README.md)).

### 1. Sequential only

- **Context.** Concurrency multiplies proof effort and attack surface (races, time of check/use).
- **Decision.** Sequential only; no threads (doc/design/goals.md).
- **Consequence.** Participants are modules, the outside world or other processes ([protocols.md](protocols.md)).
- **Date, where.** 2026-11-15; old-plan sections 1, 16.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 2. Modules in Lean

- **Context.** A module system in the object language would duplicate Lean's records and need its own metatheory.
- **Decision.** Modules entirely in Lean, with monomorphisation and no run-time dispatch (doc/design/modules.md).
- **Consequence.** Every instance has its own code; no separately compiled generic code. As built: definitions under `variable` binders, instances by application (decision 29).
- **Date, where.** 2026-11-15; old-plan sections 5, 16.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 3. One storage primitive

- **Context.** Arenas need run-time occupancy; one primitive keeps the refinement proof small.
- **Decision.** Typed arenas over one `Slots` primitive; no untyped region yet (doc/design/arenas.md, Slots).
- **Consequence.** `Pool` and `Bump` are Millipede code over `Slots` ([arenas.md](arenas.md), Slots).
- **Date, where.** 2026-11-15; old-plan sections 4.3, 16.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 4. Typestate on owned values

- **Context.** A `&mut H s` that changes `s` needs more than linearity.
- **Decision.** Typestate changes only on owned values (doc/design/protocols.md).
- **Consequence.** Planned with phase 5.
- **Date, where.** 2026-11-15; old-plan sections 7, 16.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 5. Position-independent code; optimisation late

- **Context.** Load-time relocation enlarges the loader models; optimisation multiplies proofs.
- **Decision.** Position-independent code only; no optimisation until phase 4b, then a fixed short list (doc/design/compiler.md, The shape of the generated code).
- **Consequence.** Scalar promotion was brought forward as phase 2f (decision 20).
- **Date, where.** 2026-11-15; old-plan sections 10.3, 16.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 6. ABI subset

- **Context.** The whole C ABI is large and platform-specific.
- **Decision.** ABI subset: 8 integer-class parameters, one result, no callbacks (doc/design/world.md).
- **Consequence.** Planned with phase 5.
- **Date, where.** 2026-11-15; old-plan sections 6, 16.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 7. Only our linker is verified

- **Context.** Relocatable objects for C programs go through a system linker.
- **Decision.** Relocatable objects trust the system linker; only our own `link` is verified (doc/design/targets.md, Object formats and loaders).
- **Consequence.** Planned with phase 5.
- **Date, where.** 2026-11-15; old-plan sections 11.3, 16.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 8. `bv_decide` only for encodings

- **Context.** `bv_decide` adds `Lean.ofReduceBool` to the trusted base.
- **Decision.** `bv_decide` allowed for encoding lemmas only (doc/design/trust.md).
- **Consequence.** Also a hard rule in CLAUDE.md; `#audit` validates the axioms it introduces.
- **Date, where.** 2026-11-15; old-plan sections 12, 16; CLAUDE.md.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 9. Weakest world model by default

- **Context.** A model stronger than reality makes theorems false about the real system.
- **Decision.** World models default to the weakest assumption; anything stronger is a ledger entry (doc/design/world.md).
- **Consequence.** Planned with phase 5.
- **Date, where.** 2026-11-15; old-plan sections 6, 16.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 10. Units: dimension tags with scales

- **Context.** Systems code mixes magnitudes of one dimension far more often than it multiplies dimensions.
- **Decision.** Units are dimension tags with scales, erased by the elaborator (Core sees `U64`); no dimension algebra and no unit polymorphism at first (doc/design/units.md).
- **Consequence.** Built in phase 3c as `mp dimension`/`mp unit` ([units.md](units.md)); see decision 17.
- **Date, where.** 2026-11-16 (plan revised after design review); old-plan sections 8.1, 16.
- **Who.** Owner decision (relayed by the orchestrator, 2026-11-18).

### 11. Protocols across steps by refinement

- **Context.** A typed token cannot comfortably span reactor steps (the root's type is fixed).
- **Decision.** Protocols that span reactor steps are stated as refinement of a machine, not as typestate; typestate is for handle lifecycles (doc/design/protocols.md).
- **Consequence.** Planned with phase 6.
- **Date, where.** 2026-11-16; old-plan sections 7, 16.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 12. Global types only where we own every role

- **Context.** Against an uncontrolled peer only one side can be guaranteed.
- **Decision.** Global types assume we own every role (privilege separation); against an uncontrolled peer only one-sided conformance is claimed (doc/design/protocols.md, Global types).
- **Consequence.** Planned with phase 7.
- **Date, where.** 2026-11-16; old-plan sections 7.3, 16.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 13. Derived parsers

- **Context.** Hand-written parsers are where parser differentials come from.
- **Decision.** Parsers of untrusted input are derived from format descriptions; hand-written ones are the exception and are listed by `#audit` (doc/design/security.md, Format descriptions).
- **Consequence.** Planned with phase 6.
- **Date, where.** 2026-11-16; old-plan sections 8.3, 16.
- **Who.** In the plan's list of "decisions taken here that the human may want to reverse": written by the orchestrator in the plan, which the owner signed off; whether the owner chose it or only accepted it is not recorded.

### 14. No wrapping arithmetic on sizes

- **Context.** Wrapping is defined but on a size, index or budget it is usually a bug.
- **Decision.** Arithmetic on sizes, indices and budgets uses checked or `!` forms; wrapping there is audited (doc/design/obligations.md).
- **Consequence.** The library uses `+!`; `#mp_report` lists wrapping indices (deviation 7). Cited in code as "doc/design/decisions.md (decision 14)".
- **Date, where.** 2026-11-16; old-plan sections 4.4, 16.
- **Who.** Owner decision (relayed by the orchestrator, 2026-11-18).

### 15. References are machine pointers

- **Context.** Copy-in/copy-out would make the compiled code's cost differ from what the source suggests and hide aliasing questions instead of proving them away.
- **Decision.** References (`&`, `&mut`, slices, pair borrows) are real machine pointers; never copy-in/copy-out. The value semantics treats a `&mut` borrow as a lens; the refinement theorem justifies the pointer.
- **Consequence.** Phase 2b lowered borrows and reference arguments as pointers (`lowerM_sound`); the differential suite's aliasing harnesses catch seeded copy-instead-of-pointer bugs.
- **Date, where.** 2026-11-16 (phase 2b); old-plan sections 4.2, 10.2.
- **Who.** Owner decision (relayed by the orchestrator, 2026-11-18).

### 16. The three forms of `+ - *`

- **Context.** Overflow should be visible at the operator. The phase 3b branch had the meaning reversed; the merge restored this one.
- **Decision.** Plain `+ - *` wrap; `+? -? *?` are checked (return `Result`); `+! -! *!` are obligated (the result fits; compiles to the plain instruction). The same for scale conversions (`.to`, `.to?`, `.to!`).
- **Consequence.** [obligations.md](obligations.md), [units.md](units.md); Millipede/Meta/Overflow.lean.
- **Date, where.** 2026-11-16; restored at the phase 3 merge (2026-11-17).
- **Who.** Owner decision (relayed by the orchestrator, 2026-11-18).

### 17. Units are declared

- **Context.** Units should be the program's own vocabulary, not a fixed list.
- **Decision.** Units are declared dimensions with scales: `mp dimension D`, `mp unit u : D := k`; the standard ones are a library (Millipede/Lib/Units.lean).
- **Consequence.** [units.md](units.md).
- **Date, where.** 2026-11-16 (phase 3c built it 2026-11-17); old-plan section 8.1.
- **Who.** Owner decision (relayed by the orchestrator, 2026-11-18).

### 18. Proof burden: a signal, not a gate

- **Context.** The plan set a target (user-written proof text within about twice the program). Measured programs vary.
- **Decision.** The target is a signal of where library lemmas, automation or types need work. Larger multiples are acceptable; around 50:1 would be overwhelming and is the point at which to stop and fix the library.
- **Consequence.** Reviews measure it ([../measurements.md](../measurements.md)); no gate fails on it.
- **Date, where.** 2026-11-16 (target); 2026-11-18 (signal, not gate); old-plan section 4.4.
- **Who.** Owner decision (relayed by the orchestrator, 2026-11-18).

### 19. Our own internal calling convention

- **Context.** The platform ABIs differ and are complex; proving every internal call against them buys nothing.
- **Decision.** Internal calls use one simple convention of our own; the platform ABI appears only in extern and export wrappers.
- **Consequence.** [compiler.md](compiler.md), The shape of the generated code; arm64 (phase 4) reuses the internal convention.
- **Date, where.** 2026-11-15; old-plan section 10.3.
- **Who.** Owner decision (relayed by the orchestrator, 2026-11-18).

### 20. Never-borrowed small values in frame slots, decided in `lower`

- **Context.** After phase 2e every value lived in byte memory; register allocation has nothing to allocate without promotion, and every later construct meets the location kinds. In Flat, addresses are untyped arithmetic, so a later mem2reg pass would re-prove the lowering's invariant.
- **Decision.** A never-borrowed value of at most four words whose shape has no array or `Slots` is kept as its byte representation in consecutive frame slots, decided at Core from what the borrow checker computes (phase 2f, brought forward from phase 4b). `Data.repr` stays the only encoding.
- **Consequence.** Built in stages; what stays in memory is listed in doc/open-claims.md. [compiler.md](compiler.md).
- **Date, where.** 2026-11-17; old-plan sections 10.3, 15 phase 2f.
- **Who.** Owner decision (relayed by the orchestrator, 2026-11-18).

### 21. One pipeline

- **Context.** Two lowerings, two loops and two encodings after phases 1–2d doubled the proofs.
- **Decision.** Phase 2e: one lowering through memory, one loop, one encoding; the slower code this gives simple programs is accepted (decision 20 recovers it).
- **Consequence.** `Millipede.compile_sound` is the one headline theorem.
- **Date, where.** 2026-11-16; old-plan section 15 phase 2e.
- **Who.** Orchestrator's plan; that the owner chose it is not recorded (uncertain).

### 22. Terms are built by the elaborator, not reified

- **Context.** Elaborated Lean terms are messy (instances, `OfNat`, `Decidable` proofs).
- **Decision.** Not chosen: extracting the term from plain Lean (reification). `mp def` builds the term and proves `⟦f.exp⟧ = f`.
- **Consequence.** [embedding.md](embedding.md), From syntax to term.
- **Date, where.** 2026-11-15; old-plan section 2.3.
- **Who.** Plan author's choice from the predecessor experiment `cmd` (uncertain whether the owner chose it).

### 23. Honest open claims

- **Context.** A weakened or vacuous theorem misleads more than an open one.
- **Decision.** Never weaken a theorem to get it through. A claim that cannot be proved is stated as `def X.Statement : Prop`, listed in doc/open-claims.md and checked by `scripts/audit.sh`.
- **Consequence.** CLAUDE.md "Hard rules".
- **Date, where.** 2026-11-15; CLAUDE.md; doc/open-claims.md.
- **Who.** Owner decision (relayed by the orchestrator, 2026-11-18).

### 24. Mop up

- **Context.** Agents add new paths next to old ones; reading and re-proving redundant Lean wastes their time.
- **Decision.** When a stage makes earlier code, proofs, tests or docs redundant, it deletes or merges them before its gate; keeping an old path needs a reason in doc/open-claims.md. Each review checks for leftovers.
- **Consequence.** CLAUDE.md "Hard rules"; [../roadmap.md](../roadmap.md) "Standing rules".
- **Date, where.** 2026-11-16; old-plan section 15.
- **Who.** Owner decision (stated 2026-11-16).

### 25. Cycle time and size are standing work

- **Context.** "Otherwise the whole effort will collapse under its own weight."
- **Decision.** Push on build/test cycle time and on code size and redundancy regularly: profile builds and tests, keep a cheap quick-test tier, run a size/redundancy pass between phases.
- **Consequence.** `scripts/quick.sh`; [../roadmap.md](../roadmap.md) "Standing rules".
- **Date, where.** 2026-11-17; the owner to the orchestrator.
- **Who.** Owner decision (stated 2026-11-17).

### 26. Documentation is moved, not deleted

- **Context.** The documents had grown and overlapped; the owner wants them reorganised by theme and audience without losing what might be worth finding later.
- **Decision.** Text leaving a live document goes to version control; nothing is deleted. History stays out of agents' default reading. During a phase, agents write status only to their own phase file.
- **Consequence.** deleted docs are in git to be retrieved when of interest to avoid repetition.
- **Date, where.** 2026-11-18; the owner to the orchestrator.
- **Who.** Owner decision (stated 2026-11-18).

### 27. Core and Std only

- **Context.** Mathlib is large and slow to build; the project needs little of it.
- **Decision.** No Mathlib; core and Std only (the plan allowed Batteries; none is used). Revisit if proofs need it.
- **Consequence.** CLAUDE.md, "Toolchain".
- **Date, where.** 2026-11-15; old-plan section 1 non-goals; CLAUDE.md.
- **Who.** Plan author's choice (uncertain whether the owner chose it).

### 28. `mp def` bodies in Lean's `do` notation

- **Context.** The statement forms of `mp def` were Millipede's own: `for i < N, acc := init while c do body`, `for i < N while c do body`, `mut p := v`. Newcomers could not read them: "I can't just glance at it and know what it's doing … there's so much novelty we're hitting normal users with that a hard-to-read loop form seems like needless pain."
- **Decision.** Bodies are written in the spelling of Lean's `do` notation, with Millipede's meaning: one loop form `for i in lo...hi do` / `for i in lo...=hi do` (Lean's range notation; bounds given by the user; the body assigns the outer `let mut` variables it needs, no accumulator shorthand, no `while` clause), `break` and `continue` (innermost loop), early `return` anywhere, `let`, `let mut`, reassignment `x := e` and place assignment `p.x := e`, `a[i] := e`, `if`/`else if`/`else`, `match`. Unbounded `while`/`repeat`, `try`/`catch`, `←` and `for` over anything but a range are refused, each with a message. The old spellings were migrated everywhere and removed, not kept as aliases. The owner's caveat: "if it goes sideways while you're working on it, back off and do it by hand. don't go down a bottomless rabbit hole trying to reuse lean's parser if it won't work well."
- **Route taken.** Lean's own `do` parser (the spike parsed `p.x := 5` and `r.f.g := e` as reassignments of a dotted name, `a[i] := v`, `a[i].f := e`, `s[i]! := v` as reassignments to a pattern, `&mut`, `+!` and `requires`/`ensures` without conflict); Millipede's elaborator walks the `doElem` nodes (Meta/Elab.lean, `elabSeq`, `elabFor`; the node kinds are listed there) and Lean's `do` elaborator is never called. Core, the compiler and their proofs are unchanged: `if c then break` leading a body is Core's loop condition, other jumps are carried flags and the rest of a block is placed on the paths that reach it, so migrated programs compile to byte-identical images.
- **Consequence.** [language.md](language.md) "Statements"; [../reference/surface.md](../reference/surface.md) (statement forms, loop invariants by hand); [../guide/tutorial.md](../guide/tutorial.md); Tests/DoNotation.lean, Tests/Differential/DoFuncs.lean.
- **Date, where.** 2026-11-18; branch `do-notation`.
- **Who.** Owner decision (2026-11-18, relayed by the orchestrator).
### 29. Modules are checked Lean terms, not templates

- **Context.** Modules were syntax templates (`mp module M (params) where … mp end`, re-elaborated per `mp instance I := M args`): a module over a type or size was checked and proved only per instance. The owner: the module system "doesn't actually use checked Lean terms and types for modularity", to be fixed "before it becomes a big thing".
- **Decision.** Generic code is ordinary Lean under `variable` binders: every declaration `mp def` generates is one Lean term over the variables, proved once; `deriving Data` covers parameterised structures and enums; interfaces are Lean structures of Core functions, normal forms and contracts (`mp interface`); implementations are values (`mp implementation`); instances are applications. The template mechanism (`mp module`, `mp end`, `mp instance`, `@[mp_interface]`) is removed.
- **Route taken.** The feasibility spike on branch `generic-spike`, redone on the `do` surface. Core, `compile` and `compile_sound` are unchanged: they see closed programs. The registry programs compile to the same bytes as before.
- **Consequence.** [modules.md](modules.md); deviation 5 in [deviations.md](deviations.md) resolved; Millipede/Meta/Iface.lean, Millipede/Lib/Alloc.lean, Pool.lean, Bump.lean, Millipede/Top/Requests.lean, Tally.lean; Tests/Generic.lean, Tests/Modules.lean.
- **Date, where.** 2026-11-18; branch `generic`.
- **Who.** Owner decision (relayed by the orchestrator).

### 30. Liveness-aware registers: a register's role may change within a function

- **Context.** After phase 4b stage B2 every machine register had one role for the whole program (location register, scratch, return, system-call or division register), every location register was callee-saved, and each call saved all `min k G` of the callee's low locations whatever was live (saves and restores 5.6% of x64 harness instructions). The owner: normal register allocators "allow incoming and outgoing registers to get reused during the body of a function for other purposes"; registers "change the variable they're holding at different points throughout a function. this is why there are live range calculations". (The allocator already shared a location among non-overlapping live ranges; what was missing was role flexibility.)
- **Decision.** Liveness-aware caller-saved registers on both targets, in five steps: (S1) the allocator emits a live set per program point and the checker validates it, the per-position relation speaking only of live locations; (S2) the selection relation requires agreement only on live locations; (S3) a call saves only the location registers live after it; (S4) calls, system calls, division, shifts and result delivery each destroy a stated set of registers per ISA (in the convention record), the checker rejects a live location in a destroyed register, and return, argument, system-call and division registers become locations for values not live across those points; (S5) measure, choose the register lists and `k` per target. Scratch registers selection needs at every instruction stay reserved. One allocator and one checker proof for both ISAs; no moves inserted, no live-range splitting (deferred). The fallbacks stay: a refused check gives the unallocated program, a refusing selector the slot form; `compile` never fails because of allocation.
- **Route taken.** S1–S3 built and proved: the live sets are validated by `RegAlloc.check` itself, run on the program against itself with identity maps (`RegAlloc.Live.of`), whose soundness (`lockOfCheck`) is the self-simulation up to dead locations (`Live.flex`); `Sel.pkg` relates the machine to a state so related; the call block saves `Live.callKeep`. S4 was prototyped and measured: it gains at most 0.2% static and 0.4% executed instructions on either target, so it is not built.
- **Consequence.** [compiler.md](compiler.md), the backend paragraph; Millipede/RegAlloc/Live.lean, Target/SelCases.lean (`StepOkAt`), Target/SelFrame.lean (`savedFrame`); doc/measurements.md. At this decision every location register stayed callee-saved through its frame word, because caller-saved location registers measured below 0.5%; reversed below.
- **Reversal of S4 (2026-11-19).** S4 is to be built and proved after all. The owner: "we're going to have much, much larger programs in the future and generally functions will be much more likely to face register pressure; so I don't think the measurements you're making on toy examples at this scale are really relevant to whether we need the extra registers inside a function." Requirements: a class per location register and clobber sets per event in `Sel.Conv`; the Lin-level check that no location live after an instruction sits in a register it destroys, sound through `Live`/`Flex`; `Sel.Frames` not constraining a suspended activation's caller-saved locations; parallel moves in call and return sequences; both ISAs with `compile_sound`/`compile_sound_arm64` unchanged; the number of caller-saved registers an option; no frame word for a location that is never saved; preserved registers tried first unless a value is not live across a call; synthetic high-pressure functions in the measurements.
- **Consequence of the reversal (2026-11-19).** Built and proved on both targets and on by default: 3 caller-saved locations on x64 (`r8 r9 r10`) and 10 on arm64 (`x4…x7, x10…x14`, `x8`), destroyed by a call and, for `x8`, by an extern call, which loads its system-call number there (`X64.cls`, `A64Reg.cls`); arguments for a callee's caller-saved locations by a parallel move (Target/CallArgs.lean, `Sel.PMove.seq`); with them a function returns at most 5 words on x64 and 4 on arm64; the allocator tries preserved registers first (measured better on the high-pressure functions, doc/measurements.md). Argument registers are locations already, because the internal convention passes arguments in the callee's locations. Not locations: the scratch registers every block needs (x64 `rax rcx`, arm64 `x15…x17`, `x9` the move temporary), the system-call and division registers (x64 `rdx rsi rdi` and `r11`, which `syscall` destroys and qemu does not, so the differential suite could not test it; arm64 `x0…x2`), the result registers (x64 `rax rcx rdx rsi rdi`, arm64 `x0…x3`), `x18`, `x29`, `x30` and the stack pointers. Freeing the system-call, division and result registers needs clobber sets in `Sel.Ops.ExtLaws` and a parallel move for results; a caller-saved location has no frame word (`Sel.frameW`: slot `x` is word `x - c`), and the linked stack bound is `P.stackBytes (φ.words k c)`, no larger than before S4 on every measured program (doc/measurements.md).
- **Registers with a fixed role at some instructions (2026-11-19).** A register that a system call, a result delivery or a division uses is an ordinary caller-saved location elsewhere, and the instruction's clobber set says where it is destroyed. The registers now:

  | | locations | reserved, and why |
  |---|---|---|
  | arm64 | preserved `x19…x28` (`k ≤ 10`, default 6); caller-saved `x4…x7`, `x10…x14`, `x8`, `x0`, `x1`, `x2`, `x3` (`c ≤ 14`, default 14) | `x9`, the parallel-move temporary and the remainder's scratch; `x15…x17`, the far-frame base, operands, the callee frame's address and the temporaries of the `ret`, result and system-call moves; `x18`, the platform register; `x29`, `x30`, `sp` |
  | x64 | preserved `rbx rbp r12…r15` (`k ≤ 6`, default 6); caller-saved `r8 r9 r10 rdi rsi rdx` (`c ≤ 6`, default 6) | `rax rcx`, the scratch of every block (operands, shift count, division, addresses); `r11`, which `syscall` destroys on hardware and qemu does not, so the differential suite could not show a wrongly live value there, and the temporary of the `ret` and result moves; `rsp` |

  An allocated frame is compared with the source frame in words (`RegAlloc.frameOk`, `Sel.frameW`), so caller-saved locations cost no frame; all 14 are the arm64 default and all 6 the x64 default (2026-11-19, doc/measurements.md). The clobber sets: a call destroys every caller-saved location; an extern call `rdi rsi rdx` (x64) and `x8`, `x0…x2` (arm64); a division `rdx` and a remainder `rdi rsi rdx` (x64). Where an operand or result must not sit in one of these registers (an extern call's operands in `rdi rsi rdx` / `x0…x2`, `ret`'s operands and a call's results in `rdi rsi rdx` / `x0…x3`), the allocator avoids it and the selector checks it (`noFix`, `noArg`, `noRes`).
- **Operands and results in the argument and result registers (2026-11-20).** The code that loads the result registers at `ret`, the caller's moves of the results into their locations and the argument set-up of a `write` or `read` of a buffer are each one parallel move (`Sel.PMove.seq` over places that are registers or operands, `Sel.Place`; `Sel.Ops.memTail`, arm64 `A64Reg.retLd`, `retR`), so on arm64 nothing is forbidden any more: an operand may sit in any argument or result register, a result stays in the register it arrives in, and the allocator tries the register of a value's next use or definition first (the `resReg` and `argReg` fields of `Alloc.Classes`), keeping the allocation without these hints when its frame would be longer. The order of `x0…x3` among the caller-saved locations is ascending so that consecutive result locations can be consecutive result registers. A move after a call is counted as at most `n + n/2` instructions for `n` results (`resFuel`), so the cases' counts are bounds (`Sel.StepOkAt`). x64 has the same (2026-11-20): `X64.retLd` and `retW` through `r11`, `noFix`, `noFixLoc` and the allocator's `dkill` removed, returned words 2…4 and system-call arguments as hints. Nothing the registers' fixed roles imply is forbidden any more on either target; a value is only kept out of a register an instruction destroys while it is live across it.
- **Date, where.** 2026-11-18 (decided), 2026-11-19 (S1–S3; S4 reversed to "built"); branch `regalloc`.
- **Who.** Owner decision (relayed by the orchestrator).

## The list as signed off 

**Decisions taken here that the human may want to reverse**

1. Sequential only; no threads (doc/design/goals.md).
2. Modules entirely in Lean, with monomorphisation and no run-time dispatch (doc/design/modules.md).
3. Typed arenas over one `Slots` primitive; no untyped region yet (doc/design/arenas.md, Slots).
4. Typestate changes only on owned values (doc/design/protocols.md).
5. Position-independent code only; no optimisation until phase 4b, then a fixed short list
   (doc/design/compiler.md, The shape of the generated code).
6. ABI subset: 8 integer-class parameters, one result, no callbacks (doc/design/world.md).
7. Relocatable objects trust the system linker; only our own `link` is verified (doc/design/targets.md, Object formats and loaders).
8. `bv_decide` allowed for encoding lemmas only (doc/design/trust.md).
9. World models default to the weakest assumption; anything stronger is a ledger entry (doc/design/world.md).
10. Units are dimension tags with scales, erased by the elaborator (Core sees `U64`); no dimension
    algebra and no unit polymorphism at first
    (doc/design/units.md).
11. Protocols that span reactor steps are stated as refinement of a machine, not as typestate;
    typestate is for handle lifecycles (doc/design/protocols.md).
12. Global types assume we own every role (privilege separation); against an uncontrolled peer only
    one-sided conformance is claimed (doc/design/protocols.md, Global types).
13. Parsers of untrusted input are derived from format descriptions; hand-written ones are the
    exception and are listed by `#audit` (doc/design/security.md, Format descriptions).
14. Arithmetic on sizes, indices and budgets uses checked or `!` forms; wrapping there is audited
    (doc/design/obligations.md).
