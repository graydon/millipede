# Design

The agreed design of Millipede, its goals, architecture and the owner's decisions, split by
topic from the old plan. Where the code differs from the design in substance, the
design file keeps the signed-off text and says so, and [deviations.md](deviations.md) lists it.

| file | topic | old plan section |
|---|---|---|
| [goals.md](goals.md) | what the project is: an experiment, its three hypotheses and how far each got, what it does not claim, non-goals | 1 |
| [embedding.md](embedding.md) | deep embedding, terms, `mp def`'s normal form, proofs | 2 |
| [language.md](language.md) | types, expressions, statements, loops, functions, errors, programs | 4.1, 4.3–4.5 |
| [memory.md](memory.md) | places, linear values, references, borrowing, slices | 4.2 |
| [arenas.md](arenas.md) | `Slots`, pool and bump arenas, keys, byte buffers | 4.3 |
| [obligations.md](obligations.md) | obligations, overflow, contracts, automation, analyser, loop and root invariants | 4.4 |
| [modules.md](modules.md) | generic definitions, instances, interfaces, implementations, clients | 5 |
| [units.md](units.md) | dimensions, units, quantities, conversions | 8, 8.1 |
| [resources.md](resources.md) | cost, stack, footprint, reports | 9 |
| [compiler.md](compiler.md) | architecture, IRs, passes, proof method, optimisation | 3, 10 |
| [targets.md](targets.md) | ISA, ABI, object-format and loader models | 11 |
| [trust.md](trust.md) | the top-level theorem, trusted base, evidence | 12, 13 |
| [limits.md](limits.md) | the edges of the theorem: the programs it covers, the slack of its bounds, the reach of the tests | — |
| [world.md](world.md) | externs, oracle, world model | 6 |
| [protocols.md](protocols.md) | typestate, reactor refinement, global types | 7 |
| [security.md](security.md) | information flow, format descriptions | 8.2, 8.3 |
| [repository.md](repository.md) | repository layout and workflow | 14 |
| [decisions.md](decisions.md) | the decision log | 16 (decisions) |
| [deviations.md](deviations.md) | where the code differs from the signed-off design (for the owner) | — |
| [prior-art.md](prior-art.md) | prior art | 17 |

Elsewhere: what is next in [../roadmap.md](../roadmap.md); what is built in
[../status.md](../status.md); the surface syntax in [../reference/surface.md](../reference/surface.md).
