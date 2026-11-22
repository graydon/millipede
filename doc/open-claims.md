# Open claims

This file lists what is stated but not proved, what the compiler refuses, what is not built, what
the automation cannot do, and the redundancy kept on purpose. 

## Open statements

An open statement is a `def X.Statement : Prop` with no proof, listed on a line of the form
`- \`X.Statement\` — file — what blocks it`. `scripts/audit.sh` accepts such a definition only when
a theorem proves it or when it is listed here.

- `CompileAccepts.Statement` — Millipede/Top/Accept.lean — that the default `compile` accepts
  `revchunks`: the kernel does not finish the budget potential `Sel.potential` (20 minutes).
  Checked by `#guard` in Tests/Witness.lean.

## Still refused by `compile` (open)

`compile` refuses each of the following with an error that names it, so `compile_sound` is not
affected.

- A reference to a pair of elements is refused when it is used other than through its fields.
- A `&mut` borrow body or reference callee is refused when it does not hand back its references
  in place, which only Core terms written by hand can do.
- A `&mut` argument through a `Slots` cell is refused when the cell is not reached by certified
  fields and is written back after another `&mut` argument on the same root.
- A slice view is refused when it is used whole other than by passing it on.
- A place with a selector under a slice or a pair is refused, which only hand-written Core has.
- An extern call that writes is refused unless its output buffer is exactly one mutable slice.
- On arm64, a frame of 2,096,640 slots or more, data more than 4 GiB from the code, and a
  constant `write` buffer of 2^32 bytes or more are refused. On x64 the frame limit is 2^24 slots.

Some refusals are not gaps but the design or a resource limit. They are terms the borrow checker
rejects, building blocks without a certificate, forms outside the language, the limits of the
64-bit targets and of the cost model, externs other than `write`, `read` and `exit`, and brands
for each arena value.

## Not built

Each of the following is described in the design or a plan and does not exist in the code.

Surface and tooling:
- The kernel's check of a function's normal-form equation grows about as the cube of its number of
  statements, and the statement-size limit does not bound it, so a function of a dozen jumping
  statements can take minutes and several gigabytes.
- The commands `#mp_asm` and `#mp_bytes` do not exist.
- The `Usage` record of the design is not built: `Exp.exec` returns a value, a world and steps; frame depth is the static `Exp.stack`.
- There is no configuration for continuous integration, and `scripts/check.sh` is run by hand.
- The code uses plain imports, not Lean's `module` system, which CLAUDE.md allows.
- `inline` definitions with block parameters are not built, because no client needed one.
- Machines have no Lean type or general refinement theorem; `kvsrv` alone is proved (Tests/KVRefine.lean).
- Contracts about events: `p.reach` is not derived for an effectful `init` whose contract is not about events; a root invariant of a program whose `step` has a contract about events is proved from the step's body (`kvsrv.inv_step`), since the contract says nothing of a run after `exit`.
- Formats have no length-prefixed nested message, no reader of one field in place, no constants or ignored runs over eight bytes, and no step bound in terms of the description; `mp format`'s step from the text to the description and `T.toVal` is trusted, and a program over generated code has no trace theorem. 
- Images pad their headers and each text and read-only segment to a page in the file, 64 KiB on
  arm64 and 4 KiB on x64: the loader model needs page-aligned file offsets and segment addresses,
  and a layout with segments inside pages, as `ld`'s, needs a model whose mapped pages hold the
  file's neighbouring bytes. 
- Loads and stores compute the data region's address for every access (five or six instructions
  each); seven tenths of the code are such accesses. 
- Only constructors of 64 bytes or more with one large argument in memory, or a fill with a
  literal whose element divides 8 bytes, are written by loops; a literal atom, a second large
  argument and other copies are one store per word, and the root's zeros are stored by `init`
  rather than taken from the zero-filled data region. 
- In `do` blocks, `return` inside a loop needs a result type that is not linear and has a
  default, two or more large variables written in a joined statement are copied, and Lean's
  `for … invariant`, `while`, `repeat`, `try` and `←` are refused.
  
- Capability classes are sets of extern symbols and tokens cannot be split, generic definitions
  get no `f.noCalls`, and no handle has a transition to a sum of states.

Core optimisation:
- Analyser-driven constant propagation and check elimination: the analyser needs `e.LoopsOk`, which `compile` cannot decide.
- Common-subexpression elimination is not built, because no opportunity was measured.
- Inlining does not apply to callees that write or borrow a parameter, nor to `callRef`.
- `r11` holds no location, because qemu does not destroy it at `syscall`, so the differential suite could not test it. 

Modules and brands:
- The analyser and the stack, cost and footprint figures exist only for closed definitions.
  
- `compile` decides `Program.wf` of code over an implementation variable per instance. Same link.
- An implementation variable that unification does not find must be named at the call, as in
  `f (A := impl) …`. Same link.
- `mp prove` of a generic program's invariant goals is not supported, so its invariant comes from
  the contracts of `init` and `step`. Same link.
- Interfaces state no relations of cost or size between operations, and there is no syntax for
  the footprint of each arena. Same link.
- `#mp_report` lists a generic client's interface operations, not the functions behind them.
- Keys are branded by the type of their arena, not by the arena value, so two arenas of one type
  share a key type. 

Contracts and quantities:
- `f.safe` and `f.spec` are two proofs, where obligations.md asks for one `vcgen` run.
  
- `exactTo` and `cmp` across scales are not built.
  
- A derived structure cannot have a field of type `Q u`. Same link.
- The casts `KiB n` and `q.val` are not listed by `#mp_report`, a unit cannot have a scale given
  by a size parameter, and the only carrier is `U64`. Same link.
- The listing of wrapping operators covers indices and slice bounds only, not loop bounds,
  conversions of quantities, or flows through fields and arguments, and `scripts/audit.sh` does
  not check it. 

Values that stay in memory, which is sound and costs only code size:

- A field smaller than a word, which shares a word with other fields, keeps its variable in memory.
- A `case` with a renumbered rest keeps its value in memory, which only hand-written splits use.
- Only scalar parameters of one word are passed as words. Parameters of several words, and those
  beyond the first `FR - REXT`, are copied into the callee's region.
- The accumulator of a loop body with carried variables goes through memory.
- A loop body's value goes to slots after the loop variables' and is moved one word at a time.
- The binders of borrow continuations and of a reference call's result stay in memory.

## Automation limits

Each of the following is provable but not proved automatically.


- Under a contract about events, the automatic attempt finds a loop's invariant only when the
  contract is `events = t` with `t` naming the loop's bound (Tests/EnsuresEvents.lean, `putEach`),
  and `mp_auto` reports a wrong invariant as the goal `False` rather than at the invariant.
  `mp_auto` on obligations passes the `post` of a callee's contract about events to `grind`,
  which rejects it, so it fails on such a caller (`mp_safe` and the automatic attempt leave it
  out). Both are in Millipede/Meta/Auto.lean.

- The analyser does not read bounds on fields of reference parameters or a callee's `ensures`,
  only `requires` on word parameters. 
- The analyser does not handle `Slots` cells, `put` and `take`, or a callee's `requires`.
- The analyser widens bytes twice, loses growth through an inner loop, and relates by one comparison.
- Automatic loop invariants are only the postcondition and then `True` for a contract, and
  `requires`, `ensures` and both for obligations. Other invariants are written by hand, and
  loops are matched to invariants by position.
- `Exp.LoopsOk`, a hypothesis of the analyser, is proved for each definition by `rfl`, not decided.
- With `mp.autoSafe false` the analyser does not run.
- `inBase_def` does not fire on a variable of type `Q u`, so specifications state it as `UInt64`.
- In a proof by hand, the goals of `vcgen` have anonymous hypotheses, which the messages of the
  automatic attempts name. 
- No simp lemma covers `&&` or `||` with a call on the right, a case that was not reproduced.
  Same link.
- A contract's predicates are unfolded only when they are defined in the current file or tagged
  `@[mp_auto]`.
- `Bump`'s proofs pass the `BumpInv` lemmas to `mp_auto` by hand, to keep them out of other calls.
- When `p.safe` was not generated, `example : p.Safe := p.safe` fails with Lean's own message
  "Invalid field `safe`", and only the info of `mp program` above it names what is missing.
- There is no `#mp_explain` of a goal, and an `mp def` cannot take a string, so a function that
  chooses among messages chooses at each extern call.
- The automatic attempt at a function's obligations can find a proof that unfolds a loop over a
  large array, which the kernel does not check within `mp.autoSafe.kernelHeartbeats`; the
  obligations are then left for `mp prove` (Tests/Overflow.lean, `fillOff`). The attempt's own
  cost grows with the variables in scope, and a long function can exceed
  `mp.autoSafe.maxHeartbeats`, which the message names (Tests/AutoHints.lean). The normal form
  is checked at a cost independent of the loop bounds (Tests/LoopBounds.lean).
  

## Redundancy kept

The following duplication is kept on purpose. 

- `Flat.LoopG` in LowerLoop.lean is generic although it has one instance, because the generic
  statements are shorter.
- Each ISA proves for itself its operations' laws, jumps, the entry sequence and the call and
  return sequences with register locations, in Millipede/Target/X64/, Millipede/Target/A64/ and
  Millipede/RegAlloc/, and everything else of selection is shared in Millipede/Target/.
- `IfaceOp.declare` in `Meta/Iface.lean` defines an interface operation's `req` from the
  structure's `_req` field, beside the one `mp def` defines from its `requires` clause.
- `scripts/differential.sh` and `scripts/differential-a64.sh` share only `scripts/difflib.sh`.
