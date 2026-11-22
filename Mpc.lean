import Millipede

/-!
# `mpc`, the Millipede compiler driver

`lake exe mpc [--no-regalloc] [--no-membase] [--no-idops] [--target T] [--no-opt | --no-opt-<pass> …] <instance> -o <file>`
compiles a program registered in `Examples.registry` for the target `T` with `compile`. It writes
the ELF file, made executable, and the assumption ledger `<file>.ledger.txt` next to it. The
target is `x64-linux` by default or `arm64-linux`, the environment variable `MP_TARGET` gives the
default, and any other name is refused. Every instance carries the proof of its safety, the
premise of `compile_sound`, and the ledger names it. A program outside the registry is compiled
with `#mp_compile p "out"`. `lake exe mpc --list` lists the instances.

The Core passes are on unless `MP_OPT` or the flags say otherwise. `--no-opt` switches every pass
off and `--no-opt-<pass>` one pass, and `--no-regalloc` turns the validated register allocation
off. `--no-membase` and `--no-idops` turn off two backend improvements (`Compile.Options`).
`compileWith_sound` covers every setting.
-/

open Millipede

/-- The help text. -/
def usage : String :=
  "usage: mpc [--no-regalloc] [--no-membase] [--no-idops] [--target T] [--no-opt | --no-opt-<pass> ...] <instance> -o <file>\n       mpc --list\n" ++
    "passes: " ++ ", ".intercalate Opt.names ++ "\n" ++
    "targets: " ++ ", ".intercalate (targets.map (·.name)) ++
    " (default x64-linux, or the environment variable MP_TARGET; any other name is refused)\n" ++
    "instances: " ++ ", ".intercalate (Examples.registry.map (·.name))

/-- Compile instance `name` to `out` and write the ledger next to it. -/
def build (target : Option String) (name out : String) (o : Compile.Options := {}) :
    IO UInt32 := do
  let env ← IO.getEnv "MP_TARGET"
  match Target.ofOption (target <|> env) with
  | .error err => IO.eprintln s!"mpc: {err}\n{usage}"; return 2
  | .ok t =>
  match Examples.registry.find? (·.name == name) with
  | none =>
    IO.eprintln s!"mpc: unknown instance '{name}'\n{usage}"
    return 2
  | some e =>
    match ← e.emit out t o with
    | .error err =>
      IO.eprintln s!"mpc: {err}"
      return 1
    | .ok size =>
      IO.println s!"mpc: wrote {out} ({size} bytes, {t.name}) and {out}.ledger.txt (safety: {e.safeThm})"
      return 0

/-- Apply the optimisation flags `--no-opt` and `--no-opt-<pass>` to `o`, and return the other
arguments. -/
def optFlags (o : Opt.Config) : List String → Except String (Opt.Config × List String)
  | [] => .ok (o, [])
  | a :: as =>
    if a == "--no-opt" then optFlags Opt.Config.none as
    else if a.startsWith "--no-opt-" then
      let n := (a.drop 9).toString
      if Opt.names.contains n then optFlags (o.off n) as
      else .error s!"unknown optimisation pass '{n}' (known: {", ".intercalate Opt.names})"
    else (optFlags o as).map fun (o', r) => (o', a :: r)

def main (args0 : List String) : IO UInt32 := do
  let (opt, args) ← match optFlags (← Opt.Config.fromEnv) args0 with
    | .ok r => pure r
    | .error e => IO.eprintln s!"mpc: {e}"; return 2
  -- `--no-regalloc`, anywhere among the arguments, compiles with register allocation off, and
  -- `--no-membase` with every data access computing its full address (`Options.memBase`),
  -- `--no-idops` with the identity operations selected as operations (`Options.idOps`).
  let o : Compile.Options := { regalloc := !args.contains "--no-regalloc",
                               memBase := !args.contains "--no-membase",
                               idOps := !args.contains "--no-idops", opt }
  let build := fun t n out => build t n out o
  match args.filter (fun a => a != "--no-regalloc" && a != "--no-membase" && a != "--no-idops") with
  | ["--list"] =>
    for e in Examples.registry do
      IO.println s!"{e.name}\t{e.desc}"
    return 0
  | [name, "-o", out] => build none name out
  | ["-o", out, name] => build none name out
  | ["--target", t, name, "-o", out] => build (some t) name out
  | ["--target", t, "-o", out, name] => build (some t) name out
  | _ =>
    IO.eprintln usage
    return 2
