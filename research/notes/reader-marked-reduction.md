# Reader notes: marked-reduction.pdf

"Cut vertices and cycle intersections in Gallai's path decomposition problem" (192 pp., Nov 24). Not independently verified.

The paper has 180 numbered results. Internal cross-references are consistent. It does **not** prove Gallai.

## Reduction chain

The chain is computer-free, every step is two-directional, and the equivalences are class-level.

1. **Thm 1.** Gallai ⇔ (A) ∧ (B):
   - (A) the marked bound on every 2-connected graph and every nonempty S;
   - (B) if J is 2-connected, |J| = 2k+1 and p(J) = k+1, then every odd x has ≥ 3 ends in some (k+1)-partition.

   The conjunction is essential: all-even markings alone do not give (B).
2. **Thm 7.** Restrict to 2-connected B with no "parts + interpart paths" decomposition. In particular B has no matching cut.
3. **Thm 57.** The ceiling on connected graphs with no matching cut, plus bridge-doubles of even 2-connected graphs.
4. **Thm 59.** Over C = {2-connected, no matching cut}, Gallai ⇔ both of:
   - F2(B,x) ≤ k when |B| = 2k and d(x) is even;
   - F3(B,x) ≤ k+1 when |B| = 2k+1 and d(x) is odd.

   Tests through core order m+1 cover all graphs with blocks of order ≤ m.
5. **Thm 113 (separator theorem).** At a least failure, every component of B − {x,y} avoiding the root contains an even vertex.
6. **Thm 114.** Gallai ⇔ two tests on 3-connected J with a specified z, where J − z may be assumed to have no matching cut:
   1. If z is the only even vertex, then for each r ∈ N(z), J − z has ≤ (|J|−1)/2 paths with ≥ 2 ends at r.
   2. If z and r are the only even vertices and are adjacent, then J − z has ≤ |J|/2 paths with ≥ 3 ends at r.

Further results:

- **Thm 145.** In the even test, restrict to d_B(r) = 2 or r having ≥ 3 even neighbours.
- **Thm 162.** Gallai ⇔ for every connected H on 2k vertices and every edge xy: p(H^{xy}) ≤ k+1 ⇒ p(H) ≤ k. Here H^{xy} adds two adjacent cubic vertices joined to x and y.
- **Cors 163–164.** The edge xy may be taken on an (induced) cycle of even vertices.

## Status by deletion degree d = d_J(z)

d = 2 cannot occur; d = 4 passes via Fan–Hou–Zhou. At any d, a failure needs K = J[N(z) − r] to contain two triangles meeting in exactly one vertex, or a block of maximum degree ≥ 4.

**Three-end (odd) test**

| d | Status |
|---|---|
| 6 | Proved (Thm 123). |
| 8 | Proved (Thm 128), computer-assisted via Thm 124 (1,044 classes, 10,906 graphs). |
| 10 | Proved when r has 1–2 or ≥ 5 contacts in T, or with a hub (Thms 153, 156). **Open for 0, 3 or 4 contacts.** |
| 12, 14, 16 | Proved only with a hub (Thm 153, Cors 158, 161). |

**Two-end (even) test**

- **d = 6: OPEN, heavily restricted.** What is known:
  - Root degree 2 or 4 passes.
  - δ(B) ≥ 5, and even vertices have degree ≥ 6 (Cor 138).
  - B[T] ∈ {K1, K2, K3} cores.
  - What remains is Thm 144: roots with d(r) ≥ 8 and ≥ 3 T-neighbours. Equivalently, the floor bound for every connected odd-order W with a leaf and exactly five even vertices.
- **d = 8:** proved only for d_B(r) = 2 (Thm 130).
- **d ≥ 10:** open.

At a least failure, the odd root has degree ≥ 9 (≥ 11 if the even test holds).

## Unconditional results

- **Thm 2.** The marked bound holds if every cycle has ≤ 3 vertices of block-degree ≥ 6.
- **§5–8.** The marked bound holds if cycle–path pairs share ≤ 7 vertices, or ≤ 8 with no subdivision of L. This includes graphs with no three disjoint cycles. Per-cycle counting conditions are in §8.
- **Block transfer.** Treewidth ≤ 4 (Lu–Yi); K5-minor-free (Zhang–Liu–Hong).
- **Thm 4.** K_{2k+1} − H with |E(H)| ≤ k+1.
- **Dense.** Thms 12–13 and 78 (Hamilton-decomposable, regular d ≥ ⌊n/2⌋, lower-regular).
- **Endpoint results.** Thms 47–50 (k−1 universal vertices); Thm 74 (K_{2k} − D with Δ(D) ≤ 2).
- **Subcubic.** Thms 118–120.
- **Eulerian.** Thm 166 and Cors 168–172.
- **Cycles through a vertex.** Thm 38 (≤ 7 cycles); Thm 175 (8 cycles give 9 paths, sharp by K17); Cor 176 (m + ⌊√m⌋ − 1).
- **Conditional.** Thms 17 and 34 assume the odd floor; Thms 69 and 72 assume the even test.

## Minimal-counterexample structure

- **Marked bound.** No bridge or cut vertex with large sides. Residual-cycle partners share ≥ 8 vertices with the cycle (Thm 3).
- **Ordinary counterexample (Thm 55).** Every nonsingleton matching bond bisects. Shores have treewidth ≥ 5 and ≥ 5 even nonports.
- **Least failure of the pair.** No proper 3-edge cut; degree-3 vertices are independent; bonds have size ≥ 5 if 3-connected.
- **Eulerian.** Degrees ≥ 16/18/20 (Cor 178, Thm 180).

## Computation

Summarised on pp. 187–190, but **no supplement or URL is given in the PDF**.

The Lean files and the C++/Python programs are named only. Load-bearing certificates:

- §6–7 contact orders: 1,320 path templates and 202 cycle templates.
- 485 thin-pair classes (Thms 2, 3).
- Thm 124: seven-site certificate (feeds Thms 128, 130).
- The d = 6 tables: Thm 135 (9,330), Thm 137 (235), Lemma 133 (103).
- Lemma 71: 106,400 cases.
- Thm 159: 216,329 pairs (feeds Thm 175).
- Thm 170: 6,131 certificates.

## Flags

- **Shaik [25]**, an unrefereed Hexagon preprint dated Oct 16, 2026, is load-bearing for Cor 106 and Thm 144, and for the "two universal vertices" remark.
- **Wording.** "Three or more parts" in the intro, but Thm 7 allows ≥ 2.
- **Extraction.** The "book" K2 ∨ K3 is probably K2 ∨ K̄3 (overline lost).
- The §6 count table is garbled in extraction.
- Every abstract claim maps to a theorem.

## Literature

**Load-bearing:**

- Lovász (mixed decomposition).
- Fan (addible-edge Lemmas 3.3–3.6).
- Fan–Hou–Zhou.
- Pyber.
- Botler–Sambinelli.
- Shaik.
- Xie [28].
- Chu–Fan–Zhou.
- Zhang–Liu–Hong (Lemmas 2.5–2.6).
- Chu–Fan–Liu.
- Javadi–Miralaei.
- Bahmanian–Rodger.
- Csaba et al. and Pfenninger.
- Glock–Kühn–Osthus.
