# Experiment log

## E1. Solver self-test

Command: `tools/pathnum.py`

Exact path numbers come out correct for:

- K2–K8;
- C3–C8;
- the Petersen graph (5);
- K5−e (3);
- K3,3 (3);
- K4,4 (3).

Each returned partition was checked to cover every edge exactly once, using only simple paths.

## E2. Complementary-pair property CP

Command: `tools/complementary.py 7`

**CP(G):** there are path decompositions D1, D2 of G such that:

- every odd vertex ends exactly one path in each;
- every even vertex ends two paths in one of them and none in the other.

Counting ends gives |D1| + |D2| = n, so CP(G) implies p(G) ≤ ⌊n/2⌋. This was motivated by:

- the complementary trail partitions in root-endpoint-costs Thm 6.1;
- the complementary cone profiles in even-degrees;
- the "any 3 of 6 doubled" prescription in six-clique;
- Li's perfect path double cover.

**Result: all connected graphs with n ≤ 7 (atlas).**

| n | CP holds | CP fails |
|---|---|---|
| 2 | 1 | 0 |
| 3 | 1 | 1 |
| 4 | 6 | 0 |
| 5 | 19 | 2 |
| 6 | 112 | 0 |
| 7 | 847 | 6 |

The failures are the odd semi-cliques (K3, K5−e, K5, and four graphs K7−H with e(H) ≤ 2), plus **two non-semi-cliques**:

- K3 ∨ 4K1 (n = 7, m = 15);
- K6 plus a vertex adjacent to three of its vertices (n = 7, m = 18).

Both satisfy the floor p = 3.

**Why they fail.** An even vertex of degree 2t cannot be an end in a t-path decomposition. In both examples the smaller member of any candidate pair would have to expose an even vertex of degree 2|D|.

**Status: REFUTED as stated.** CP is strictly stronger than Bonamy–Perrett, and it fails through degree saturation in dense odd-order graphs.

The obvious relaxation, |D1| + |D2| ≤ n + 1, is just Gallai: take D1 = D2. A degree-restricted version (for example Δ ≤ n − 2) is untested.
