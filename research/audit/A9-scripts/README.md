# A9 scripts

Independent checks for audit A9 (d6-frontier; endpoint-structure Sections 5-6).
Run from this directory with `nice -n 15 python3 <script>`. The CP-SAT checks need
`/home/user/Manuscripts/tools` (pathnum.py, pathnum2.py) and OR-Tools.

| script | checks | output |
|---|---|---|
| `adversarial.py` | symbolic model: special vertices only, free adjacencies taken present (worst case), every grouped donor branched | library |
| `check_tables.py` | every step table of d6-frontier Thms 4.1(i)-(iii), 4.3, 4.4 (m = 1..4), 5.2 (both forms), 6.1(a),(b) (d = 4..10), plus sharpness | `check_tables.out` |
| `worst.py` | per-step supply and worst-case blank count | `worst.out` |
| `terminal_more.py` | Thms 3.1/3.2 brute force with up to 4 full vertices | `terminal_more.out` |
| `limit1.py` | Sec. 8 limitation (1): \|N(y) & T\| = 3 | `limit1.out` |
| `es_examples.py` | endpoint-structure examples (two triangles, K_{2,4}+e, P3+(K5-e), 2(K5-e)) | stdout |
| `es_exhaust.py` | all graphs <= 7 vertices, no isolated vertex, all orders: Rem. 32, Thm 37/Cor 39, Prop 46 (L),(S),(C) | stdout (no violations) |
| `k3r.py` | K3+r configuration in connected graphs (Thm 45 / Rem. 49) | stdout |
| `census.py` | two-even census, orders 4, 6, 8, obstruction classes | `census.out` |
