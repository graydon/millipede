# Millipede — working rules

Read the documents relevant to your task before writing code:

| for | read |
|---|---|
| the design, by topic (goals, language, obligations, modules, units, compiler, targets, trust) | `doc/design/` (index: `doc/design/README.md`) |
| decisions you must not silently reverse | `doc/design/decisions.md` |
| what is built, proved, tested | `doc/status.md` |
| surface syntax, options, tactics, generated names | `doc/reference/surface.md` |
| open items, refusals, unproved statements | `doc/open-claims.md` |
| what is next | `doc/roadmap.md` |
| old `MILLIPEDE.md §N` citations (history, commit messages) | `doc/history/section-map.md` |
| past phases, dead ends | `doc/history/`: only when changing or revisiting a past decision |

During a phase, write status only to your stream's file `doc/phases/<phase>-<stream>.md`; do not
edit README.md, `doc/design/`, `doc/status.md`, doc/open-claims.md (except a `.Statement` line) or
`doc/measurements.md` unless your task is the phase close.
Toolchain: Lean 4.35.0 (pinned in `lean-toolchain`). No Mathlib; core + Std only.

## Gate
- `scripts/check.sh` = build + tests + audit. It must stay green.
- While working, build only your own modules: `lake build Millipede.Foo.Bar` (fast, and other
  agents may be building concurrently in this same tree), and iterate with `scripts/quick.sh`
  (the library and a cheap subset of the tests; it prints what it skipped). Run the full gate
  `scripts/check.sh` only when asked or at the end of a task.
- Test files that only need `f.exp` and the normal form may `set_option mp.autoSafe false`
  (`mp def` then makes no automatic attempt at the obligations); a function whose `f.safe` is
  cited keeps the attempt (`set_option mp.autoSafe true in`).
- Inspect proof states with `scripts/leanq` or the lean-lsp MCP tools where they are available
  (`scripts/leanq`: Lean's language server from the shell; lines 1-based;
  nothing is written to disk; the file's imports must be built):
  - `scripts/leanq goal FILE LINE [LINE…]` — goal before and after the tactic on each line.
  - `scripts/leanq try FILE LINE 'tac1' 'tac2' …` — replace that line by each tactic in turn (in
    memory) and show the goal left and any error. A tactic worked if it shows `no goals` (or a
    changed goal) and no error line. Use this to compare `grind`, `simp`, `omega`, `simp?`,
    `exact?` before writing a manual chain.
  - `scripts/leanq diag FILE [START END]` — messages without a `lake build`.
  - `scripts/leanq hover FILE LINE COL`.
  Prefer it to inserting `trace_state` and rebuilding. Still finish with `lake build <module>`.

## Hard rules
- No `sorry`, no `axiom`, no `native_decide` outside `scratch/`. `bv_decide` only for
  encode/decode lemmas.
- Never weaken or make vacuous a theorem to get it through (no `True` conclusions, no false
  hypotheses, no restating a definition as its own proof). If you cannot prove a claim, state it
  as `def Foo.Statement : Prop := …` (no proof), register it in `doc/open-claims.md` (one line: name,
  file, what blocks it) and move on. An honest open claim is fine; a fake theorem is not.
- Mop up: when your work makes existing code, proofs, tests or comments redundant (an old
  pipeline next to its replacement, a construct that is now a special case of another, a second
  encoding, duplicated lemmas, stale docs), delete or merge them in the same task, keeping every
  headline theorem proved. "Existing theorems must stay proved" means their content must survive,
  not that superseded definitions must be kept. If you cannot remove something redundant, say so
  in your report and record why in `doc/open-claims.md`. Before writing a lemma, search for an
  existing one (`grep`, `scripts/leanq`); do not add a parallel copy.
- Stay inside the files/directories you were assigned. Do not edit other subsystems' files; if
  you need a change upstream, put a local lemma in your own directory and report the request.
- Add new modules to `Millipede.lean` / `Tests.lean` import lists (append a line; keep others).
- Do not `git commit` unless your task says so. Never `git add -A` from a parallel task.
- Docs: move text you replace to `doc/history/`, do not delete it; a status line names its
  evidence (a theorem, a test file or a script).

## Writing
Docs and comments (design files, module and declaration docs, messages, reports) are read by
someone who knows Lean but not this project. Write them like doc/design/language.md and memory.md:
- Say what a thing is and what it does, in the present tense. Define a term once, in a plain
  sentence where it first matters, and then repeat the noun. Use nothing before it is defined.
- Join a definition to its reason or consequence in one sentence ("which", "so", "because",
  "when"). Sentences average about 18 words and vary; a run of one-fact sentences reads as a list.
- A paragraph is one to four sentences on one thing. Tell behaviour in the order it happens.
  Introduce an example with one flat sentence and take it from a test, so it is known to compile.
- Leave out history (the phase that built it, what it replaced, who decided it) and detail the
  reader does not need to use the thing (Core constructors, lemma and file names). History goes
  to `doc/history/`, plan against build to `doc/design/deviations.md`, unbuilt work to
  `doc/open-claims.md`, each with at most one closing pointer.
- No parenthetical asides, inline cross-references, slogans, triads, "X, not Y", colon-led
  openers, bold lead-ins, rhetorical questions or closing summaries. Headings are noun phrases.
  A list is for things that are a list, introduced by a sentence.
- State only what the code and tests confirm today.

Four faults from this repository, rewritten:
- History. Before: "the array is borrowed (`&mut`) around the statement, not copied into the
  join's tuple and back (before: three more copies of the array, `2562 * κ.word` outside the
  branches)." After: "A statement `if` that writes one cell of an array borrows the array, so
  the array is not copied when the branches join."
- Asides and references. Before: "A loop body may assign the enclosing block's mutable variables
  (`let mut` variables, `&mut` references and slices, the root's fields): in Core the loop
  *carries* them (`Exp.loop`, its frame of loop-carried state): …" After: "A loop body may
  assign variables bound outside the loop, and after the loop each of them holds the last value
  assigned to it."
- Staccato. Before: "Every value has a type. The type fixes how the value is laid out in memory.
  It also says whether the value may be copied." After: "Every value has a type, which fixes how
  the value is laid out in memory and whether it may be copied."
- Slogan. Before: "**Liveness is linearity, not a ghost key set.** `Pool`'s keys are linear and
  sealed (…): `alloc` mints one, `free` consumes one, and `Exp.wf` (…) rejects …" After: "A key
  is linear and only `alloc` can create one, so each key is freed at most once, and the checker
  rejects a use of a key after `free`."

Prose is read cold by a second agent, who reports false claims, forward references and these
faults, before it lands.

## Lean style (the binding version; background in `doc/history/embedding-2026-11-19.md`, "Rules for writing the Lean")
1. Recurse structurally over plain inductive types; well-founded recursion does not unfold in
   the kernel and `decide` gets stuck.
2. No functions that compute types where `simp` must see through them (`Env` is an inductive).
3. Declarations added by an elaborator need `enableRealizationsForConst`. `autoImplicit` is off.
4. Kernel reduction (`rfl`, `decide`) vs compiled evaluation (`#eval`): proofs use the first.
5. Only `Millipede/Meta/` imports `Lean`. The library uses plain imports, not the module system
   (`module`/`meta import`); do not convert files without a task that asks for it.
6. Your training data lags the toolchain. Check every API name against the installed source
   (`~/.elan/toolchains/*/src/lean`) or `#check`. Deprecation warnings are work items.
7. Tests need teeth: each test suite must be shown to catch a seeded bug.
8. Proof style: short proofs driven by automation and shared lemmas, not long scripts.
   - Induction or case analysis over a recursive definition that ends in arithmetic: first try
     `induction x <;> intro …` then `all_goals grind [f, g, …]`, listing the definitions to
     unfold. Write manual cases only for what remains (loops; for a `match` on a dependent
     scrutinee use `cases h : scrutinee <;> simp only [...] <;> grind`).
   - Pass definitions to `grind [...]` per call; do not tag recursive definitions `@[grind]`
     globally. After adding `grind`, check `lake env lean --profile`: if one call takes over 1 s
     (UInt64 / `sext32` address arithmetic is the known bad case) keep the explicit rewrite.
   - Compare candidates with `scripts/leanq try` before writing a chain of `have`/`rw`.
   - When a block of three or more lines repeats (resolving an instruction sequence, running
     straight-line code, a branch arm, "state unchanged so not halted"), write the general lemma
     before the second copy. In simulation proofs this is where the savings are.
   - Side conditions over instruction lists (`∀ i ∈ is, i.branches = false`) are discharged by
     `simp` with `@[simp]` per-instruction lemmas, not by `rcases … with rfl | rfl | …`.
   - Do not `cases`/`subst` an equation with a large concrete term on one side: prove an
     inversion lemma (`f x = .ok y → P ∧ y = g x`) and `rw` with it.
   - State lemmas and hypotheses in simp normal form (`l[i]?.getD d`, not `l.getD i d`), or they
     will not fire after `simp`. Known trap: simp lemmas about `Asm.resolveAt arch` do not fire
     in SelectProof; use `rw` or a list-level lemma there.
   - A bundle of more than ~6 hypotheses is a `structure` with named fields (plus an `iff` with
     the curried form while call sites migrate). No twenty-name `intro`.
   - Tag `Std.WP` specifications of library functions `@[spec]`.
   - A proof over ~60 lines is a sign a lemma is missing: factor it.
   Models use `List`/`Nat`/`BitVec`; `ByteArray` code is proved equal to the model.
9. Program proofs use `Std.WP` + `vcgen` (`import Std.Tactic.Do`, `open Std.WP`,
   `set_option experimental.vcgen true`); `Std.Do`/`mvcgen` are deprecated.
10. State what a `mp def` does as its contract (`requires P ensures Q`: `f.spec` `@[spec]`,
   `f.post`; `mp prove f.spec` when not automatic), not as a hand-stated triple or a lemma about
   `(f x).run`; cite a callee's contract, do not unfold it. A reactor's root invariant is
   `mp program … invariant I`, not a hand-written induction over `Program.run`.

## Environment
- Host is aarch64 Linux. `~/tools/bin/qemu-x86_64` runs x64 Linux ELF binaries;
  `~/tools/bin/x64-objdump` disassembles x64 (`-D -b binary -mi386:x86-64 file`). `readelf`,
  `objdump` (arm64), `gcc` (arm64) are installed. `~/tools/bin/uv` / `uvx` run Python tools. No root.
- Also installed: `gdb`, `gdb-multiarch` (x64 under `qemu-x86_64 -g <port>`), `strace` (x64: `qemu-x86_64
  -strace`), `/usr/bin/time -v` (peak memory), `bc`, `rg`, `hyperfine`. Packages: ask the owner (host side).
