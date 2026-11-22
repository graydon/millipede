import Millipede.Meta.Elab
import Millipede.Meta.Contracts
import Millipede.Meta.Program
import Millipede.Meta.Prove
import Millipede.Meta.Auto
import Millipede.Meta.Iface

/-!
# `mp def`

Importing this module provides `mp def`, `mp extern`, `mp program`, `mp prove`, `mp interface`,
`mp implementation`, `#mp_cost` and `deriving Data`. It is made of the following modules.
- `Millipede.Meta.Sem` gives the `Id` and `StateM World` views of the denotation with their rewrite
  lemmas, the constructors that `mp def` uses, and the lemmas about loop obligations. It does not
  import `Lean`.
- `Millipede.Meta.Basic` holds the surface types `STy` and the registry of declared functions,
  externs and derived data types.
- `Millipede.Meta.Derive` is the `deriving Data` handler, which generates instances, lenses,
  constructors, the exhaustive split chain and simp lemmas, for closed and parameterised types.
- `Millipede.Meta.Syntax` declares `&` and `&mut`, slices and the commands. Statements are Lean's
  `do` notation, translated by `Millipede.Meta.Elab`.
- `Millipede.Meta.ANF` is the named A-normal form with the source-level checkers of linearity
  and borrowing.
- `Millipede.Meta.Units` holds `mp dimension`, `mp unit` and the typing rules of quantities
  `Q u`, which are erased to `UInt64`.
- `Millipede.Meta.Elab` is the elaborator, with the declarations it generates and `mp_safe`.
- `Millipede.Meta.Contracts` handles `mp def … ensures`, which gives `f.spec` and `f.post`, and
  `mp prove f.spec`.
- `Millipede.Meta.Program` derives the safety and root invariant of an `mp program`, with the
  library side in `Millipede.Meta.Spec`.
- `Millipede.Meta.Iface` handles `mp interface`, a structure of Core functions, normal forms and
  contracts, and `mp implementation`.
- `Millipede.Meta.Auto` provides `mp_auto`, the usual proof of a contract or of obligations.
- `Millipede.Meta.Prove` provides `mp prove`, which dispatches on the target and records the
  theorems proved for `#mp_report`.

Every command works under Lean `variable` binders. A definition that uses a variable is generic,
and every declaration it generates is a Lean term over the variables it takes. The modules use
plain `import`s, since the elaborator is ordinary meta-level code and the kernel checks the
declarations it adds. The embedding is described in doc/design/embedding.md.
-/
