#!/usr/bin/env bash
# Build the Lean library and check every paper's Lean entry file against its axioms.expected.
#
#   scripts/check_papers.sh            # lake build, then every papers/*/lean/*.lean
#   scripts/check_papers.sh P1 P3      # lake build, then only the papers whose directory starts with P1, P3
#   SKIP_BUILD=1 scripts/check_papers.sh P1   # reuse an existing build
#
# For each paper directory papers/<dir>/, every lean/<file>.lean is run with `lake env lean` from
# lean/ (several files: in file-name order, outputs concatenated). The check passes iff each run
# exits 0 without an error message, and the lines `... depends on axioms: [...]` of the output equal
# those of papers/<dir>/axioms.expected, in order. Other output lines (e.g. #check) are not compared.
# Exit status: 0 iff the build succeeds, it reports no `sorry`, and every paper passes.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
cd "$ROOT/lean" || exit 2
fail=0

if [ "${SKIP_BUILD:-0}" != "1" ]; then
  echo "== lake build"
  log="$(mktemp)"
  if ! lake build >"$log" 2>&1; then
    tail -40 "$log"; echo "FAIL: lake build"; exit 1
  fi
  tail -1 "$log"
  if grep -q "declaration uses 'sorry'" "$log"; then
    grep "declaration uses 'sorry'" "$log"; echo "FAIL: sorry in the library"; fail=1
  fi
  rm -f "$log"
fi

shopt -s nullglob
dirs=()
if [ "$#" -eq 0 ]; then
  for d in "$ROOT"/papers/*/; do dirs+=("$d"); done
else
  for p in "$@"; do for d in "$ROOT"/papers/"$p"*/; do dirs+=("$d"); done; done
fi

for d in "${dirs[@]}"; do
  d="${d%/}"; name="$(basename "$d")"
  files=("$d"/lean/*.lean)
  [ "${#files[@]}" -eq 0 ] && continue
  if [ ! -f "$d/axioms.expected" ]; then echo "FAIL: $name has no axioms.expected"; fail=1; continue; fi
  out="$(mktemp)"; rc=0
  for f in "${files[@]}"; do lake env lean "$f" >>"$out" 2>&1 || rc=1; done
  if [ "$rc" -ne 0 ] || grep -qE '(^|: )error' "$out"; then
    grep -E '(^|: )error' "$out" | head -20; echo "FAIL: $name: Lean reported errors"; fail=1
  elif diff -u <(grep 'depends on axioms' "$d/axioms.expected") <(grep 'depends on axioms' "$out"); then
    echo "OK:   $name ($(grep -c 'depends on axioms' "$out") axiom lines, ${#files[@]} file(s))"
  else
    echo "FAIL: $name: axiom lines differ from axioms.expected"; fail=1
  fi
  rm -f "$out"
done

[ "$fail" -eq 0 ] && echo "All checks passed." || echo "Some checks FAILED."
exit "$fail"
