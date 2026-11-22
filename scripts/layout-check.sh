#!/usr/bin/env bash
# Checks that the data layout follows the C layout for naturally aligned fields. The script
# compiles scripts/layout-check.c (sizeof, _Alignof and offsetof of a dozen structs and sums) with
# gcc and compares its output with Lean's layout of the same types, which Tests/Layout.lean
# `report` produces and scripts/layout-dump.lean prints. Exit status 0 means the outputs are
# identical.
#
# With `--selftest`, each seeded bug must make the comparison fail: on the C side the structs
# declared `__attribute__((packed))` (-DPACKED), on the Lean side a layout without tail padding
# (`notail`) and one without field alignment (`noalign`).
set -euo pipefail
cd "$(dirname "$0")/.."
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
lake build Tests.Layout >/dev/null
gcc -std=gnu11 -O0 -o "$tmp/c" scripts/layout-check.c
gcc -std=gnu11 -O0 -DPACKED -o "$tmp/c-packed" scripts/layout-check.c
"$tmp/c" > "$tmp/c.txt"
lake env lean --run scripts/layout-dump.lean > "$tmp/lean.txt"

if [ "${1:-}" = "--selftest" ]; then
  "$tmp/c-packed" > "$tmp/c-packed.txt"
  lake env lean --run scripts/layout-dump.lean notail > "$tmp/notail.txt"
  lake env lean --run scripts/layout-dump.lean noalign > "$tmp/noalign.txt"
  ok=1
  for pair in "c-packed.txt lean.txt" "c.txt notail.txt" "c.txt noalign.txt"; do
    set -- $pair
    if diff -q "$tmp/$1" "$tmp/$2" >/dev/null; then
      echo "layout-check selftest: seeded bug ($1 vs $2) NOT detected"; ok=0
    fi
  done
  [ "$ok" = 1 ] || exit 1
  echo "layout-check selftest: 3/3 seeded bugs detected"
  exit 0
fi

if ! diff -u "$tmp/c.txt" "$tmp/lean.txt"; then
  echo "layout-check: Lean layout differs from gcc"; exit 1
fi
echo "layout-check: $(wc -l < "$tmp/c.txt") types agree with gcc"
