# overview: the programme paper

`overview.tex` (compile with `pdflatex` three times; `overview.pdf` is committed). A standalone survey
and reduction paper: the spine, the five reversible lifts, cones, the constrained-Lovász layer, the
dense T(6)-i frontier, a dependency diagram (TikZ) and a table of headline theorems with Lean names,
axiom records and audits.

New here (paper only, not in Lean): the converse of the all-odd (T1) lift (Prop 3.11), independent
proofs and checks of the (T2) forest and floor converses (Props 3.15, 3.17; these are also test2
Props 4.6 and 5.2, in Lean for matchings), and the all-odd lift with the root as a child of the forest
(Theorem 3.10(b)), which settles the three order-9 roots where every forest base fails (Example 3.12).

Audit: `research/audit/A38-overview.md` (2 ERROR, 5 OVERCLAIM, 1 GAP, 19 MINOR; all addressed, see the
response section there).

## Scripts (`scripts/`, Python 3 + networkx)

| script | checks | log |
|---|---|---|
| `converses.py [seed] [samples8]` | the three converses, exhaustively, on every connected graph of the atlas with ≤ 7 vertices and ≤ 13 edges, plus random order-8 graphs; executes and verifies every lift | `converses_run.txt` (`python3 converses.py 1 40`) |
| `k26_alloddlift.py` | all-odd lift on the cone over K_{2,6}: no base with r a root (all 32 forests, 128 rootings); a base with r a child | `k26_alloddlift.txt` |
| `k26_variant_witness.py` | the explicit witness of Example 3.12, lifted and re-checked | `k26_variant_witness.txt` |
| `hsaad_alloddlift.py` | both variants at every root of `HsaAD~}` | `hsaad_alloddlift.txt` |
