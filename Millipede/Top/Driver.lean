import Millipede.Top.Ledger

/-!
# The driver's entries

`compile_sound` takes `p.Safe` as a premise, so the image of a program whose obligations are not
proved carries no guarantee. The driver therefore compiles only an `Entry`, which cannot be built
without that proof, and the ledger it writes names the theorem. `lake exe mpc` compiles the entries
of `Examples.registry`, and `#mp_compile p "out"` builds the entry of any program whose `p.safe` is
proved and writes the same files. Both refuse a program without `p.safe` and name what is
missing.
-/

namespace Millipede

/-- A program that the driver may compile, with the proof of `prog.Safe` that `compile_sound`
needs as its premise. -/
structure Entry where
  /-- the name of the image, used by `mpc NAME` and the ledger -/
  name : String
  /-- one line for the ledger -/
  desc : String
  prog : Program
  /-- every obligation of every step holds, for every oracle -/
  safe : prog.Safe
  /-- the name of the theorem that `safe` cites, which the ledger shows -/
  safeThm : String

/-- A program whose `init` is safe and whose `step` is safe from every root and world is `Safe`.
This serves programs without an invariant, such as `Examples.sum`. -/
theorem Program.safe_of_parts (p : Program) (hi : ∀ ω, p.init.safe ω .nil World.init)
    (hs : ∀ ω r w, p.step.safe ω (.cons r .nil) w) : p.Safe :=
  fun ω => ⟨hi ω, fun _ => hs ω _ _⟩

/-- The optimisation switches of a driver run, read from the environment variable `MP_OPT`, which
is `all`, `none`, `name,…` or `-name,…`. When it is absent every pass is on, and an unknown pass
name is an error. -/
def Opt.Config.fromEnv : IO Opt.Config := do
  match ← IO.getEnv "MP_OPT" with
  | .none => return Opt.Config.all
  | .some s => match Opt.Config.parse s with
    | .ok o => return o
    | .error e => throw (IO.userError e)

/-- Compiles the entry for `t` with options `o`, which by default run every Core pass and register
allocation. It writes the executable ELF file to `out` and the assumption ledger for `t` to
`out.ledger.txt`, naming `e.safeThm`, the passes that ran, and whether `compileRun` fell back to a
shorter prefix of them. It returns the image's size, or `compile`'s error. -/
def Entry.emit (e : Entry) (out : String) (t : Target := x64Linux) (o : Compile.Options := {}) :
    IO (Except String Nat) := do
  match compileRun o e.prog t with
  | .error err => return .error err
  | .ok (b, c) =>
    let opt := if c.on == o.opt.on || o.opt.passes.isEmpty then c.describe
      else s!"{c.describe}: FALLBACK (the program optimised by {o.opt.describe} was refused)"
    IO.FS.writeBinFile out b
    IO.setAccessRights out
      { user := { read := true, write := true, execution := true },
        group := { read := true, execution := true },
        other := { read := true, execution := true } }
    IO.FS.writeFile (out ++ ".ledger.txt") (ledger e.name e.desc e.prog b.size e.safeThm t o opt)
    return .ok b.size

end Millipede
