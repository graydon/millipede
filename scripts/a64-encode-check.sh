#!/usr/bin/env bash
# Cross-checks the arm64 encoder against two independent tools.
#  1. Lean prints, for every instruction of `sample` in Tests/A64.lean (each form of the subset
#     with 60 pseudo-random operand sets, plus edge cases), the word `encode` emits, the text
#     `llvm-mc` should assemble to that word (pc-relative operands as `#offset`), and the text GNU
#     objdump should print for it (`-M no-aliases`, so the canonical instruction and never an alias).
#  2. `llvm-mc -show-encoding` assembles the first texts; every word must equal ours.
#  3. Our words, as one little-endian blob at 0x10000, are disassembled by objdump; every line
#     must read as the second text, with comments dropped and `addr <sym>` read as `0xaddr`.
# Exit status 0 means both tools agree with every line.
#   scripts/a64-encode-check.sh                       normal run
#   A64_LISTING=file scripts/a64-encode-check.sh      check a saved listing instead
#   scripts/a64-encode-check.sh --selftest            require each seeded encoder bug to be caught
set -euo pipefail
cd "$(dirname "$0")/.."
LLVM_MC="${LLVM_MC:-llvm-mc}"
OBJDUMP="${OBJDUMP:-aarch64-linux-gnu-objdump}"

work=$(mktemp -d)
src=$(mktemp -d)
trap 'rm -rf "$work" "$src"' EXIT

# check <listing>: exit 0 iff both oracles agree with every line.
check() {
  local listing="$1"
  cut -f2 "$listing" > "$work/in.s"
  "$LLVM_MC" -triple=aarch64 -show-encoding "$work/in.s" > "$work/mc.txt" 2> "$work/mc.err" || true
  python3 -I - "$listing" "$work/blob.bin" <<'PY'
import sys
with open(sys.argv[2], "wb") as f:
    for l in open(sys.argv[1]):
        if l.strip():
            f.write(int(l.split("\t")[0], 16).to_bytes(4, "little"))
PY
  "$OBJDUMP" -D -b binary -m aarch64 -M no-aliases --adjust-vma=0x10000 "$work/blob.bin" \
    > "$work/objdump.txt"
  python3 -I - "$listing" "$work/mc.txt" "$work/mc.err" "$work/objdump.txt" <<'PY'
import re, sys
expected = [l.rstrip("\n").split("\t") for l in open(sys.argv[1]) if l.strip()]
norm = lambda s: re.sub(r"\s+", " ", s.strip())
# llvm-mc: one "encoding: [0x.., 0x.., 0x.., 0x..]" per assembled instruction, in order.
mc = [int("".join(reversed(re.findall(r"0x([0-9a-f]{2})", m))), 16)
      for m in re.findall(r"encoding: \[([^\]]*)\]", open(sys.argv[2]).read())]
mcerr = open(sys.argv[3]).read().strip()
od = []
for l in open(sys.argv[4]):
    m = re.match(r"^\s*([0-9a-f]+):\t([0-9a-f]{8})\s+\t?(.*)$", l.rstrip("\n"))
    if m:
        t = re.sub(r"//.*$", "", m.group(3))
        t = re.sub(r"\b([0-9a-f]+) <[^>]*>", r"0x\1", t)
        od.append((int(m.group(1), 16), int(m.group(2), 16), norm(t)))
bad = 0
def report(msg):
    global bad
    bad += 1
    if bad <= 20: print("a64-encode-check: " + msg)
if mcerr:
    report("llvm-mc errors:\n" + "\n".join(mcerr.splitlines()[:12]))
if len(mc) != len(expected):
    report(f"llvm-mc assembled {len(mc)} instructions, {len(expected)} expected")
if len(od) != len(expected):
    report(f"objdump disassembled {len(od)} instructions, {len(expected)} expected")
for k, (w, asm, dis) in enumerate(expected):
    w = int(w, 16)
    if k < len(mc) and mc[k] != w:
        report(f"#{k} llvm-mc: '{asm}' assembles to {mc[k]:08x}, our word {w:08x}")
    if k < len(od):
        a, ow, t = od[k]
        if a != 0x10000 + 4 * k or ow != w or t != norm(dis):
            report(f"#{k} objdump: our word {w:08x} reads as '{t}', model text '{norm(dis)}'")
if bad:
    print(f"a64-encode-check: FAILED ({bad} mismatches of {len(expected)})"); sys.exit(1)
print(f"a64-encode-check: OK ({len(expected)} instructions agree with llvm-mc and objdump)")
PY
}

emit() {  # emit <bug>: the listing with seeded encoder bug <bug> (0: none)
  cat > "$src/A64Emit.lean" <<LEAN
import Tests.A64
def main : IO Unit := Millipede.A64.Tests.printListing $1
LEAN
  lake env lean --run "$src/A64Emit.lean"
}

if [ -n "${A64_LISTING:-}" ]; then
  check "$A64_LISTING"
  exit
fi
lake build Tests.A64 >/dev/null
if [ "${1:-}" = "--selftest" ]; then
  ok=0
  for bug in 1 2 3 4 5 6; do
    emit "$bug" > "$work/bug$bug.tsv"
    if check "$work/bug$bug.tsv" > "$work/bug$bug.log" 2>&1; then
      echo "a64-encode-check selftest: seeded bug $bug NOT caught"; ok=1
    else
      echo "a64-encode-check selftest: caught seeded bug $bug ($(grep -c '^a64-encode-check: #' "$work/bug$bug.log" || true)+ mismatches)"
    fi
  done
  exit "$ok"
fi
emit 0 > "$work/listing.tsv"
check "$work/listing.tsv"
