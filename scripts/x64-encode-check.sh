#!/usr/bin/env bash
# Cross-checks the x64 encoder against an independent disassembler.
#  1. Lean prints, for several hundred instructions of the modelled subset (`sample` in
#     Tests/X64.lean), the bytes `encode` emits and the Intel-syntax text of the instruction as
#     the model understands it (`text`: operands, immediates, branch targets, rip-relative targets).
#  2. The bytes are concatenated into one blob and disassembled with GNU objdump.
#  3. Every objdump line must start at the expected offset, have the expected bytes and read as
#     the expected text, with whitespace normalised. Any mismatch fails the check.
# Exit status 0 means no mismatch.
# Usage: scripts/x64-encode-check.sh            normal run
#        X64_LISTING=file scripts/x64-encode-check.sh   check a saved listing instead
set -euo pipefail
cd "$(dirname "$0")/.."
OBJDUMP="${OBJDUMP:-$HOME/tools/bin/x64-objdump}"

work=$(mktemp -d)
src=$(mktemp -d)
trap 'rm -rf "$work" "$src"' EXIT

if [ -n "${X64_LISTING:-}" ]; then
  cp "$X64_LISTING" "$work/listing.tsv"
else
  lake build Tests.X64 >/dev/null
  cat > "$src/X64Emit.lean" <<'LEAN'
import Tests.X64
def main : IO Unit := Millipede.X64.Tests.printListing
LEAN
  lake env lean --run "$src/X64Emit.lean" > "$work/listing.tsv"
fi

python3 -I - "$work/listing.tsv" "$work/blob.bin" <<'PY'
import sys
lines = [l.rstrip("\n").split("\t") for l in open(sys.argv[1]) if l.strip()]
with open(sys.argv[2], "wb") as f:
    for hexb, _ in lines:
        f.write(bytes(int(b, 16) for b in hexb.split()))
PY

"$OBJDUMP" -D -b binary -mi386:x86-64 -M intel "$work/blob.bin" > "$work/objdump.txt"

python3 -I - "$work/listing.tsv" "$work/objdump.txt" <<'PY'
import re, sys
expected = [l.rstrip("\n").split("\t") for l in open(sys.argv[1]) if l.strip()]
norm = lambda s: re.sub(r"\s+", " ", s.strip())
# objdump lines look like "  addr:\tbytes\ttext"; a long instruction continues on "  addr:\tbytes" lines.
insts = []
for l in open(sys.argv[2]):
    m = re.match(r"^\s*([0-9a-f]+):\t([0-9a-f ]+?)\s*(?:\t(.*))?$", l.rstrip("\n"))
    if not m:
        continue
    addr, byts, text = int(m.group(1), 16), m.group(2).split(), m.group(3)
    if text is None:
        if insts:
            insts[-1][1].extend(byts)
        continue
    insts.append([addr, byts, norm(text)])
bad = 0
off = 0
for i, (hexb, want) in enumerate(expected):
    wb = hexb.split()
    if i >= len(insts):
        print(f"x64-encode-check: FAIL: objdump stopped before #{i} ({want})"); bad += 1; break
    addr, got_b, got = insts[i]
    if addr != off or got_b != wb or got != norm(want):
        bad += 1
        if bad <= 20:
            print(f"x64-encode-check: MISMATCH #{i} at {off:#x}: bytes {' '.join(wb)}")
            print(f"    model:   {norm(want)}")
            print(f"    objdump: {got} @ {addr:#x} [{' '.join(got_b)}]")
    off += len(wb)
if len(insts) != len(expected):
    print(f"x64-encode-check: FAIL: {len(insts)} instructions disassembled, {len(expected)} expected")
    bad += 1
if bad:
    print(f"x64-encode-check: FAILED ({bad} mismatches of {len(expected)})"); sys.exit(1)
print(f"x64-encode-check: OK ({len(expected)} instructions, {off} bytes agree with objdump)")
PY
