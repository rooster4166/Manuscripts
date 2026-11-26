# Reader notes: Nov 26 papers, cycle absorption, degree-50 case

These are a reader's notes on `03-november-26-papers/*` and the related cycle-absorption parts of the big manuscripts. They have not been verified independently.

## Main theorems

### cycle-and-contact.pdf (17 pp.)

**Theorem 1.** Take 12 edge-disjoint cycles, each containing all of U except possibly one fixed vertex w. Their union has p = 13 exactly, and any x on all twelve cycles can get exactly two ends.

- Rainbow-path growth is done by hand up to 9 sites. Sizes 10 and 11 are done by computer: the eleven-site exceptional-end search closes in 9,706 states.
- The twelve-contact catalogue has 1,509 canonical exceptions among 9,985,920 orders.

**Theorem 2 (conditional, "under the stated reduction hypotheses").** This is the consecutive-visit degree-50 case.

- At q = 25 a failure has 3 ≤ l ≤ 6, J ≥ 20 total omissions, and n ≤ 37.
- At q = 26 a failure has n ≤ 50, with n = 52 excluded by a Javadi–Miralaei planted-mark construction on K51.

**§3–7 (focal pair).** The focal pair is the cycle 012345670 with the path 03476125, links 12, 34, 67 doubled. A third path meeting the cycle at 1–11 sites with a nonpole extreme gives a three-path return. The same holds for any number of contacts in at most two private blocks, and for one private block of size ≥ 2 with arbitrary extremes. Several of these statements are unnumbered "Theorem."

These sections are heavily computer-assisted:

- 3,621 anchor words reduced to 66 (13 orbits);
- 3,638,880 placements at 13 contacts;
- exceptional-record tables of size 1, 2, 17, 166, 1509 at h = 8–12;
- 1,510,778 Hamilton donors;
- 5,724 literal certificates, among others.

**§8.** Two examples (h = 8, 9) with private extremes need exactly 4 paths, so the nonpole hypothesis is needed locally.

**What a failure needs.** A failed degree-six instance with a genuine nonpole donor end needs at least 12 contacts and at least 3 private blocks per selection. If both extremes are distinct nonpole anchors, it needs at least 14 contacts and at least 4 blocks.

### degree-preserving-decompositions.pdf (8 pp.)

- **Thm 1.** Let r labelled spanning trees have every row-degree fixed, on n ≥ r vertices. A nonempty class has at least 2^max(0, C(r,2) − p) members when p edges are pinned. Across a bipartite cut the exponent becomes 2C(r,2) − |I ∪ P|. Tight examples exist at every r.
- **Proof method.** A determinant of stacked incidence matrices, which is Kalai's hyperconnectivity matrix.
- **Thm 3.** At equality, the class is a product of binary exchanges.
- **Thm 4 / Cor 5.** Support-preserving version for paths. Applied to twelve cycles it gives at least 2^(66−b) rearrangements, but the paper leaves open whether one of them opens the cycles at the required ends.
- **Thm 6 (mixed path/cycle partitions).** At most two sets exceed the forest density bound. If two do, they are nested with a one-vertex gap.
- **Cor 7.** One extra row suffices once |S| ≥ N(c), with N(3) = 119.
- **§5.** A determinant count of complementary Hamilton paths.

### two-vertex-separators.pdf (7 pp.)

- **Thm 1.** An exact gluing formula for p(A ∪ B) when A and B meet at {u, v}. It uses five endpoint-type counts and a disjointness matching number ρ.
- **Thm 2.** Optimal global partitions can induce arbitrarily non-optimal local partitions, so reductions must keep full local records, not just p(A).
- **Lemma 3 and Thms 5–6.** Auxiliary-edge and pole-identification reductions that use only smaller ceilings. These remove separators unless the pole degrees are very unbalanced or identification creates parallel edges.
- **Thm 7.** All attainable endpoint vectors. Private-leaf formula: p(G_x) = min_P |P| + [b_P(x) = 0].
- **Thm 9.** The private-leaf bound holds at every root when both shores are odd semi-cliques.

## The cycle-absorption program

**Strategy.**

1. Lovász's path–cycle theorem gives a mixed partition within the marked budget.
2. Take one with the fewest cycles. The residual cycles have rigid properties.
3. Absorb a cycle together with a member it meets into two paths. Parity preserves the assigned ends.
4. Goal: zero residual cycles.

**Contact sizes handled.**

| Contacts | How handled |
|---|---|
| ≤ 5 | Published: Zhang–Liu–Hong; Chu–Fan–Liu. Exceptions are only K5 − ab and K5. |
| 6–7 | Finite checks. |
| 8 | Unique blocked order 03476125 (marked-reduction §7, classify_eight.cpp, 1,320 templates). |
| 9 | Cycle–cycle criterion (1,219 classes). |
| 10–12 | Blocked orders: 17, 166, 1,509. |
| ≥ 13 | Only under block-structure hypotheses. |

**Marked-reduction Thm 3.** In a minimal counterexample, every member meeting a residual cycle shares at least 8 vertices with it.

**Marked-reduction Thm 175.** 8 cycles through x give 9 paths with two ends at x. In general m cycles give m + ⌈m/8⌉ paths, and Cor 176 gives m + max{1, ⌊√m⌋ − 1}.

**Cor 40.** A minimal family failing the m + 1 bound has at least 8 cycles, any two sharing at least 10 vertices, and a nearly spanning first cycle at order 2m + 2. Cycle-and-contact Thm 1 settles m = 12 exactly in that shape.

**Open: the "m + 1 cycles-through-a-vertex" bound for general m (9–11 and ≥ 13).**

## Consecutive-visit reduction and the degree-50 case

These are referenced only in cycle-and-contact and degree-preserving. **Their set-up is not in any manuscript in the collection.** The following are cited but absent:

- the gluing inequality;
- the complete-core linear-forest theorem;
- the seven-visit capacity exclusion;
- the short-support capacity calculation;
- the leaf-and-cut argument;
- the finite absorptions for t = 2, 4, 6, 8.

The reader's inference: 50 = 2(12 + 13).

## Code availability

**No code is in the collection.** Named but absent:

- counterexamples-expected.txt
- classify_eight.cpp
- thin-pair-certificates.tsv
- check_thin_pairs.py
- c8-pair-rows.tsv
- verify_nine.py
- referee/verify.sh
- the Lean modules

## Flags

- Cycle-and-contact Thm 2 cannot be checked from the collection.
- "Ten numerical rows" is used where only six are shown.
- "2 + 23 ends" is unexplained.
- Hilton's extension theorem is used without its hypotheses.
- The claim that the degree-six test produces a focal pair whose donor has a genuine nonpole end is asserted but not derived in marked-reduction.
- Several main results are unnumbered.
- Load-bearing external result: Javadi–Miralaei (Discrete Math. 349, 2026).
