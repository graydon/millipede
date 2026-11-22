# Prior art

Millipede borrows most of its ideas from earlier work. The list below names that work by topic.
It was written from background knowledge and has not been checked against the sources, so a
detail should be verified before anything relies on it.

Millipede's compiler theorem has the shape of the theorems of CompCert and CakeML, a simulation
from the source down to a model of the machine, but it covers a much smaller language and two
targets. Those projects compile real software and have years of use, review and published work
behind them, while Millipede was built in days and has compiled only small test programs.

- Verified compilation to machine code: CompCert, with its simulations, the validated register
  allocation of Rideau and Leroy, CompCertELF and Stack-Aware CompCert; CakeML, which compiles to
  bytes with ISA models and an FFI oracle carrying a file-system model, and is the closest
  precedent for Millipede's world model; Bedrock2, which compiles to RISC-V with I/O as traces;
  and Jasmin, which preserves constant time. Cost-preserving compilation: CerCo, and the verified
  stack bounds of Carbonneaux et al. (PLDI 2014).
- ISA and format models that could give a second opinion on Millipede's: Sail and its Lean
  backend; LNSym, a model of Armv8 in Lean 4; the ACL2 x86 model; "The missing link" by Kell,
  Mulligan and Sewell, on ELF linking; and the binary verification of seL4.
- World models: FSCQ and Perennial for crashes; Verdi and IronFleet for network faults; Jones's
  rely/guarantee; Dolev–Yao; Capsicum and WASI for capability-style interfaces to the operating
  system.
- Value semantics, linearity and references: Cogent and its refinement through restraint; Hylo;
  the second-class values of Osvald et al. (OOPSLA 2016); Wadler's `let!`; Austral; Aeneas;
  Cyclone and Tofte–Talpin regions; Oxide; RustBelt. Staged modules: Terra and Zig's `comptime`.
- Typestate and sessions: Strom and Yemini; Plaid; Brady's "State machines all the way down";
  Honda, Yoshida and Carbone (POPL 2008); Montesi; Pirouette; Kalas.
- Information flow: Denning; Volpano, Smith and Irvine; Jif; Sabelfeld and Myers; ct-verif.
  Relational proofs: Benton's relational Hoare logic, and the product programs of Barthe, Crespo
  and Kunz.
- Format descriptions: EverParse by Ramananandro et al.; PADS; Nail; the LangSec programme.
- Refinement of state machines: IronFleet; seL4; the refinement mappings of Abadi and Lamport;
  the interface automata of de Alfaro and Henzinger. Mechanised multiparty session types: Zooid,
  by Castro-Perez et al.
- Verified static analysis: Verasco by Jourdan et al., and Astrée for the abstract domains.
- Units: Kennedy, and F#. Resources: AARA by Hoffmann; time credits by Atkey and by Charguéraud
  and Pottier; Haslbeck and Lammich; Dependent ML.
- Lean: a search on 2026-11-07 found no library for linear or quantitative types. Related work
  is Iris-Lean, the tick monad `TimeM` of CSLib, and Huisinga's thesis on uniqueness types in
  Lean's intermediate representation.
