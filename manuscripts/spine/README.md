# The Gallai reduction spine

`spine.tex` (`spine.pdf`, 27 pages) is a standalone proof that Gallai's path decomposition
conjecture is equivalent to two deletion tests on 3-connected graphs (marked-reduction
Theorem 114). It follows the Lean proof `Gallai.gallai_iff_spineTests'` in `lean/GallaiLean/`.

* Build the paper: `pdflatex spine.tex` (run twice).
* Check the formal side, from `lean/`:
  * `lake exe cache get && lake build`
  * `lake env lean ../manuscripts/spine/SpineAxioms.lean`: `#print axioms` for the main
    theorems. Expected output: only `propext`, `Classical.choice`, `Quot.sound`.
  * `lake env lean ../manuscripts/spine/SpineCheck.lean`: `#check` of every Lean name the paper cites.
* Audit: `research/audit/A15-spine-paper.md`.
