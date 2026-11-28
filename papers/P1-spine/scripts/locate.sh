#!/usr/bin/env bash
# Print file:line of the declaration of every Lean name that lean/P1.lean checks.
# Usage: scripts/locate.sh   (from papers/P1-spine; reads ../../lean/GallaiLean)
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$HERE/../../lean/GallaiLean"
names=$(awk '/^#cited$/{f=1;next} /^\/-!/{f=0} f' "$HERE/lean/P1.lean" | tr ' ' '\n' | grep '^Gallai\.' | sed 's/^Gallai\.//')
miss=0
for n in $names; do
  short="${n##*.}"
  hit=$(grep -nE "^(@\[[^]]*\] *)?(private |protected |noncomputable )*(theorem|lemma|def|abbrev|structure|inductive|class) +(Gallai\.)?($n|$short)([ :({\[]|$)" "$SRC"/*.lean | head -1)
  if [ -n "$hit" ]; then echo "$n  ${hit#$SRC/}" | cut -d: -f1,2; else echo "$n  (not found by pattern)"; miss=$((miss+1)); fi
done
echo "# $(echo "$names" | wc -w) names, $miss not located by the pattern" >&2
