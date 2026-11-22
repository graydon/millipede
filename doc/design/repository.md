# Repository

Millipede is one Lean 4 package, built with Lake, which uses Lean's core library and Std and no
other dependency. The toolchain is pinned in `lean-toolchain`. This document maps the directories
and says how to build and test the project. The rules for those who change it are in CLAUDE.md.

## Directories

The library is under `Millipede/`, one directory per part:

| directory | contents |
|---|---|
| `Millipede/Core/` | types, layouts, terms, the value and instrumented semantics, the borrow checker, obligations, cost, stack and footprint, quantities |
| `Millipede/Analysis/` | the verified interval analyser and its soundness |
| `Millipede/Meta/` | the elaborators: `mp def`, `deriving Data`, contracts, `mp program`, interfaces, units, the proof tactics, `#audit` and the `#mp_` commands |
| `Millipede/Lib/` | code written in Millipede with its proofs: pool and bump arenas, the allocator interface, byte buffers, bitmaps, slice helpers, units |
| `Millipede/Opt/` | the Core optimisation passes |
| `Millipede/Compile/` | the simulation framework, the Flat, Lin and Asm representations, `lower`, `linearize` and `assemble`, and their proofs |
| `Millipede/RegAlloc/` | the register allocator, its checker and the checker's proof, and the arm64 selector with register locations |
| `Millipede/Target/` | ISA and ABI models, targets, the selection proof shared by both instruction sets, the budget check; `X64/` and `A64/` for each instruction set |
| `Millipede/Object/` | relocatable objects, images, the linker, and the writers and loader models of each format: `Elf/`, `Pe/`, and `MachO/` with SHA-256, and the writer and reader model of ELF relocatable objects in `ElfRel/` |
| `Millipede/Extern/` | extern events and oracles |
| `Millipede/Top/` | `compile`, the correctness theorem and its proof, the registered example programs, the assumption ledger |

Only `Millipede/Meta/` imports Lean's own library, because only the elaborators need it.

The rest of the repository is laid out as follows.

| path | contents |
|---|---|
| `Mpc.lean` | the compiler driver `mpc` |
| `Tests/` | test modules, the differential harnesses in `Tests/Differential/`, and the co-simulation generators |
| `scripts/` | the gate, the script-level tests, measurement and inspection tools |
| `doc/` | the design, the reference, the guides, status, roadmap, measurements and history |
| `scratch/` | experiments, ignored by git |

## Building and testing

`lake build` builds the library, and `lake build Millipede.Foo.Bar` builds one module and what it
imports. The gate is `scripts/check.sh`, which builds the library and the tests, runs the
script-level tests, and runs the audit. It must pass before a change is merged. A quicker loop
while working is `scripts/quick.sh`, which builds the library and a cheap subset of the tests and
prints what it skipped. There is no continuous-integration configuration, so the gate is run by
hand.

The script-level tests are listed in `scripts/run-tests.sh`. They include the differential
suites for both targets, the co-simulations of the instruction-set models, the encoder, ELF
and Mach-O cross-checks, the system-linker runs of relocatable objects, and the end-to-end runs of the compiler driver. scripts/audit.sh checks that no
proof uses `sorry` or an unexpected axiom, prints the axioms of the headline theorems, and checks
that every unproved claim is listed in [../open-claims.md](../open-claims.md).

`scripts/leanq` queries Lean's language server from the shell. It shows the goal before and after
a tactic, tries alternative tactics at a line without editing the file, and prints a file's
messages without a full build.

## Compiling a program

The driver compiles a registered program to an ELF file and writes the assumption ledger next to
it. These commands list the programs and compile one for each target.

```
lake exe mpc --list
lake exe mpc revchunks -o revchunks
lake exe mpc --target arm64-linux revchunks -o revchunks-arm64
```

The target is x64 Linux unless `--target` or the environment variable `MP_TARGET` names
`arm64-linux`. The option `--no-regalloc` turns register allocation off, and `--no-opt` turns the
Core passes off. A program that is not registered is compiled from Lean with
`#mp_compile p "out"`, which requires a proof of the program's safety.
