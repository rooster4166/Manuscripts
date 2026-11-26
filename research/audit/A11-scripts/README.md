# A11 scripts

Independent checks for audit A11 (`manuscripts/bs-prescribed`). They share no code with
`manuscripts/bs-prescribed/scripts/`. Run from this directory with `nice -n 19 python3 <script>`.
`selftest_exact.py` also needs `/home/user/Manuscripts/tools` (pathnum.py) and OR-Tools.

| script | checks | output |
|---|---|---|
| `cert_check.py` | A: the 11 bowtie certificates, transcribed from the .tex, transported to all 93 labelled cases, with printed counts and final pairs. B: Lemmas 10–12 on every graph on five labelled vertices; Prop 13 on the 38 rims. C: own exhaustive certificate search (bowtie on T, T+u, T+u+v; 41 cores × 31 contact sets; 38 rims on T) | `partAB.txt`, `partC.txt` |
| `mutation_check.py` | dropping any hypothesis of Lemmas 10–12 breaks the certificate; A = T supplies | `mutation.txt` |
| `exact.py` | own DFS solver for exact end vectors and "floor with an end at y" | library |
| `selftest_exact.py` | `exact.py` against `tools/pathnum.py` on random graphs of order 5–7 | `selftest_exact.txt` |
| `random_replay.py` | end-to-end replay on 120 bowtie and 120 six-core random hosts, every certificate node realised; global blank count = local | `random_replay.txt` |
| `counterexamples.py` | first-draft G_t; order-5 example; L and D of Prop 9; exact census at N = 5, 7 | `counterexamples.txt` |
| `family_tt.py` | Prop 8 (G_{t,t'}); the six N = 7, e = 5 failures | `family_tt.txt` |
| `bowtie_no_uv.py` | Remark 15(iii): bowtie hosts with no pair (u, v) | `bowtie_no_uv.txt` |
