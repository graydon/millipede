import Millipede.Top.Examples

/-!
# arm64 data addresses beyond 1 MiB

A data address is formed by `adrp` and `add :lo12:`, which reach ±4 GiB. The program here writes a
constant buffer of `n` bytes `a`, then `OK\n`, and exits with 0. Its data item lies after the
code, so the distance from the `write` to the buffer's end grows with `n`. A buffer just under
1 MiB and one of 2.5 MiB must both compile, and on an aarch64 host run natively and print exactly
their bytes. `scripts/a64-elf-check.sh` seeds an `adrp` one page off and requires it to be caught.
-/

namespace Millipede.Tests.A64Reach

open Millipede Millipede.Examples

def bigInit (n : Nat) : Exp [] Ty.unit :=
  (Exp.ext sysWrite (EArgs.word (Atom.lit 1)
      (EArgs.bufIn (Buf.const (List.replicate n 97)) EArgs.nil))).let_
  ((Exp.ext sysWrite (EArgs.word (Atom.lit 1)
      (EArgs.bufIn (Buf.const [79, 75, 10]) EArgs.nil))).let_
  ((Exp.ext sysExit (EArgs.word (Atom.lit 0) EArgs.nil)).let_ (Exp.atom (Atom.lit ()))))

def big (n : Nat) : Program := ⟨Ty.unit, bigInit n, keepUnit.exp⟩

/-- Compile `big n` for arm64, and on an aarch64 host run it and compare its output. -/
def check (n : Nat) : IO Bool := do
  match compile (big n) arm64Linux with
  | .error e => IO.eprintln s!"{n}: refused: {e}"; return false
  | .ok b =>
    let f := s!".lake/test-a64reach-{n}"
    IO.FS.writeBinFile f b
    IO.setAccessRights f { user := { read := true, write := true, execution := true } }
    unless (System.Platform.target.splitOn "aarch64").length > 1 do return true
    let out ← IO.Process.output { cmd := f }
    let want := String.ofList (List.replicate n 'a') ++ "OK\n"
    return out.exitCode == 0 && out.stdout == want

/-- info: [true, true] -/
#guard_msgs in
#eval [1048000, 2621440].mapM check

end Millipede.Tests.A64Reach
