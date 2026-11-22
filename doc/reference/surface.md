# Surface reference

This reference describes every form in which a Millipede program and its proofs are written: the
commands, the statements and expressions of a function's body, the tactics and attributes of
proofs, the options, the names the commands generate, and the messages they print. The forms are
available in a Lean file that imports `Millipede.Meta.MpDef`. The meaning of the language is
described in the design documents [language.md](../design/language.md),
[memory.md](../design/memory.md) and [arenas.md](../design/arenas.md), and its terms are defined
in the [glossary](glossary.md).

The reference is divided into the following parts. Each part begins with a table of its forms,
and then gives each form a short section that says what it is, what it does and what rules it
follows, with an example taken from a test.

| part | contents |
|---|---|
| [definitions.md](definitions.md) | functions, parameters, contracts, externs, capabilities, handles, data types, programs, units, generic code, interfaces |
| [statements.md](statements.md) | the statements of a block, and loops |
| [expressions.md](expressions.md) | types, places, references, slices, arithmetic, quantities, calls |
| [proofs.md](proofs.md) | the automatic attempts, `mp prove`, tactics, attributes and their options |
| [tools.md](tools.md) | the commands that report, compile and audit, and the driver `mpc` |
| [names.md](names.md) | the declarations that the commands generate |
| [library.md](library.md) | arenas, byte buffers and slice functions |
| [messages.md](messages.md) | the messages a programmer is likely to meet |

## Index

The following table lists every command, tactic and attribute, with the part that describes it.

| form | part |
|---|---|
| `mp def`, `requires`, `ensures` | [definitions.md](definitions.md) |
| `mp extern`, `noreturn` | [definitions.md](definitions.md) |
| `mp capability`, `for` | [definitions.md](definitions.md) |
| `mp program`, `invariant` | [definitions.md](definitions.md) |
| `deriving Data` | [definitions.md](definitions.md) |
| `mp format`, `uint`, `lbytes`, `bytes`, `const`, `skip`, `union`, `array` | [definitions.md](definitions.md) |
| `mp dimension`, `mp unit` | [definitions.md](definitions.md) |
| `mp interface`, `op`, `mp implementation` | [definitions.md](definitions.md) |
| `let`, `let mut`, `:=`, `if`, `match`, `for`, `break`, `continue`, `return` | [statements.md](statements.md) |
| `&`, `&mut`, `a[lo..hi]`, `[T; n]`, `+!`, `-!`, `*!`, `+?`, `-?`, `*?` | [expressions.md](expressions.md) |
| `mp prove` | [proofs.md](proofs.md) |
| `mp_auto`, `mp_safe`, `mp_inst_posts`, `mp_vcgen_post` | [proofs.md](proofs.md) |
| `mp_safe_setup`, `mp_loop_split`, `mp_loop_inv`, `mp_loop_lift`, `mp_check_terms` | [proofs.md](proofs.md) |
| `fmt_close`, `fmt_safe`, `fmt_parsed`, `fmt_written`, `fmt_checked`, `fmt_full`, `fmt_pre`, `fmt_norm`, `fmt_split`, `fmt_mp`, `fmt_le`, `fmt_junk` | [proofs.md](proofs.md) |
| `@[mp_auto]`, `@[mp_auto_fwd]`, `@[spec]` | [proofs.md](proofs.md) |
| `#mp_cost`, `#mp_analyse`, `#mp_report` | [tools.md](tools.md) |
| `#mp_compile`, `mp_entry%`, `mpc` | [tools.md](tools.md) |
| `#audit`, `#audit_ledger` | [tools.md](tools.md) |

## Options

An option is set for one definition with `set_option … in`, or for the rest of a file.

| option | default | part |
|---|---|---|
| `mp.autoSafe`, `mp.autoSafe.maxHeartbeats`, `mp.autoSafe.kernelHeartbeats` | `true`, `200000`, `10000` | [proofs.md](proofs.md) |
| `mp.autoSpec`, `mp.unfoldPreds` | `true` | [proofs.md](proofs.md) |
| `mp.analyser`, `mp.analyser.trace` | `true`, `false` | [proofs.md](proofs.md) |
| `mp.normalForm` | `true` | [proofs.md](proofs.md) |
| `mp.selftest.doMutant` | `""` | [proofs.md](proofs.md) |
| `mp.selftest.badProof` | `""` | [proofs.md](proofs.md) |
| `mp.format.seedBug` | `0` | [proofs.md](proofs.md) |
| `mp.opt.inline`, `mp.opt.fold`, `mp.opt.dce`, `mp.opt.strength` | `true` | [tools.md](tools.md) |
| `mp.regalloc` | `true` | [tools.md](tools.md) |

## Library

The library's arenas, byte buffers and slice functions, with their contracts, are described in
[library.md](library.md). A program that keeps keys of an arena from one step to the next states
in its invariant which keys it holds, usually with `A.KeyStack s keys n`, which says that the
first `n` cells of the `Slots` value `keys` hold keys that the arena `s` holds. Without it, the
precondition of `alloc!` cannot be proved, and the messages of the automatic attempts point here.
