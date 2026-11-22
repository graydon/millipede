#!/usr/bin/env bash
# Seeds a bug into the source of the compiler and requires the memory differential suite to fail.
# The script copies the tree to a scratch directory, seeds the bug there, rebuilds the
# differential executable and the modules it imports in the copy, and runs the suite. It takes
# about five minutes, so run-tests.sh does not include it. Exit status 0 means the seeded bug was
# caught.
#
# The default bug re-introduces one the suite found: `Split.mode` (Millipede/Compile/Lower.lean)
# renumbers the rest of a `case` on an enum although the split chain of `deriving Data` keeps the
# original tags, so a `match` on an enum with three or more variants takes the wrong arm.
#
#   scripts/differential-srcseed.sh                          the default bug (functions mEnum mop)
#   scripts/differential-srcseed.sh FILE 'PERL-S-EXPR' fn…   run `perl -0pi -e EXPR FILE` in the
#                                                            copy, then the functions fn…
#
# A bug in a definition that the proofs unfold makes the copy fail to build, because the proofs
# are checked there too and `lake build` then stops this script with an error. The enum `case`
# lemma (LowerCase.lean) is proved, so the default copy may refuse to build before it reaches
# the differential suite.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/tools/bin:$PATH"
QEMU="${QEMU:-$HOME/tools/bin/qemu-x86_64}"
if [ $# -ge 3 ]; then file="$1"; expr="$2"; shift 2; fns="$*"
else
  file=Millipede/Compile/Lower.lean
  expr="s/      else if vs'\\.length = vs\\.length then \\.whole\\n//"
  fns="mEnum mop"
fi
copy="$(mktemp -d)"
trap 'rm -rf "$copy"' EXIT
tar --exclude=./scratch --exclude=./.git -cf - . | tar -xf - -C "$copy"
cd "$copy"
before="$(md5sum "$file")"
perl -0pi -e "$expr" "$file"
[ "$before" != "$(md5sum "$file")" ] || { echo "srcseed: the seeded bug did not change $file"; exit 1; }
lake build differential >/dev/null
bad=0
for f in $fns; do
  mkdir -p out
  .lake/build/bin/differential gen out "$f" || { echo "srcseed: $f: compile failed (seed caught by the compiler)"; continue; }
  want="$(head -c "$(awk '{print $2}' out/$f.cases)" < /dev/zero | tr '\0' '.')"
  got="$(timeout 20 "$QEMU" out/$f.0.elf < out/$f.0.in || true)"
  if [ "$got" = "$want" ]; then echo "srcseed: $f passes with the seeded bug (NOT caught)"; bad=1
  else echo "srcseed: caught the seeded bug in $f"; fi
done
exit "$bad"
