import Tests.KVRefine

/-! # The key-value specification on the inputs of scripts/format-check.sh

`lake env lean --run scripts/kvspec.lean DIR IN…` evaluates the specification `kvTrace` of
Tests/KVSpec.lean on each input file `DIR/IN`, under an oracle that delivers the file in reads of
at most 7 bytes and accepts every write whole. It writes the bytes of the trace's writes, in
order, to `DIR/IN.spec` and the exit status to `DIR/IN.speccode`, which scripts/format-check.sh
compares with its Python reference. -/

open Millipede Millipede.Tests.KV

/-- The bytes of the writes of a trace and its exit status. -/
def outputs (tr : List Event) : List UInt8 × Nat :=
  ((tr.filter (·.sym == "write")).flatMap fun e => e.bytesIn.headD [],
    match tr.getLast? with
    | some e => if e.sym == "exit" then (e.args.headD 0).toNat else 99
    | none => 99)

def main (args : List String) : IO Unit := do
  match args with
  | dir :: ins =>
    for i in ins do
      let data ← IO.FS.readBinFile s!"{dir}/{i}"
      let (out, code) := outputs (kvTrace (feed data.toList 7))
      IO.FS.writeBinFile s!"{dir}/{i}.spec" ⟨out.toArray⟩
      IO.FS.writeFile s!"{dir}/{i}.speccode" s!"{code}\n"
  | [] => throw (IO.userError "usage: kvspec DIR IN…")
