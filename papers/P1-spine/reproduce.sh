#!/usr/bin/env bash
# Reproduce the P1 artifact end to end.
#   ./reproduce.sh --quick   check lean/P1.lean against axioms.expected (needs a built library),
#                            check the name map, rebuild paper.pdf, verify SHA256SUMS. A few seconds
#                            plus about a minute for LaTeX.
#   ./reproduce.sh           the same, preceded by a full `lake build` of the library
#                            (about 5 minutes on 4 cores once the Mathlib cache is downloaded).
# Requirements: elan (Lean toolchain from lean/lean-toolchain), python3, pdflatex with lmodern.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
quick=0; [ "${1:-}" = "--quick" ] && quick=1

echo "== 1. Lean: library build and entry file"
if [ "$quick" -eq 1 ]; then
  SKIP_BUILD=1 "$ROOT/scripts/check_papers.sh" P1
else
  (cd "$ROOT/lean" && lake exe cache get >/dev/null)
  "$ROOT/scripts/check_papers.sh" P1
fi

echo "== 2. Every Lean name cited in paper.tex is checked by P1.lean"
python3 -I "$HERE/scripts/check_names.py"

echo "== 3. Paper"
if command -v pdflatex >/dev/null; then
  tmp="$(mktemp -d)"; cp "$HERE/paper.tex" "$tmp/"
  (cd "$tmp" && for i in 1 2 3; do pdflatex -interaction=nonstopmode -halt-on-error paper.tex >/dev/null; done)
  if grep -E "LaTeX Warning|undefined" "$tmp/paper.log"; then echo "FAIL: LaTeX warnings"; exit 1; fi
  echo "paper.pdf: $(pdfinfo "$tmp/paper.pdf" 2>/dev/null | awk '/Pages/{print $2}') pages, no LaTeX warnings"
  rm -rf "$tmp"
else
  echo "pdflatex not found; skipped"
fi

echo "== 4. Checksums"
(cd "$HERE" && sha256sum -c --quiet SHA256SUMS && echo "SHA256SUMS: OK")
echo "== P1 reproduced."
