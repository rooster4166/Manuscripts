# Roadmap to unrestricted Gallai

This is the single source of truth for the proof architecture. Every node is a statement with a source, a status, an audit result and a formalization status. Update it after every finding.

**Status values:**

| Status | Meaning |
|---|---|
| `PROVED-EXT` | published external result |
| `CLAIMED` | proved in a collection manuscript, not yet audited |
| `AUDITED` | passed an adversarial audit (`research/audit/`) |
| `GAP` | the audit found a fixable gap |
| `ERROR` | the audit found a false step |
| `OPEN` | not proved |
| `CONJ` | conjecture with computational evidence |
| `REFUTED` | counterexample known |

**Verification values:**

| Value | Meaning |
|---|---|
| `lean` | formalized in `lean/` |
| `lean-ext` | the author's external Lean repository (not here) |
| `comp(n≤N)` | exhaustive computation in `tools/` |
| `—` | none |

## Top-level chain

```
GALLAI (every connected G: p(G) ≤ ⌈n/2⌉)
 ⇔ [N1] rooted private-leaf test R: ∀ connected H, |H| = 2k, ∀ r: p(H + leaf at r) ≤ k
 ⇔ [N2] marked bound on 2-connected graphs ∧ three-end test on tight odd 2-connected graphs   (MR Thm 1)
 ⇔ [N3] pair of tests F₂ / F₃ on 2-connected graphs without a matching cut                       (MR Thms 7, 57, 59)
 ⇔ [N4] two rooted deletion tests on 3-connected J                                               (MR Thms 113, 114)
      (i)  z the unique even vertex, d(z) = d: J − z has ≤ (|J|−1)/2 paths with ≥ 2 ends at r ∈ N(z)
      (ii) z, r the only even vertices, adjacent: J − z has ≤ |J|/2 paths with ≥ 3 ends at r
 ⇐ [T(d)] test (i) at deletion degree d, together with test (ii) at deletion degree d, for every even d ≥ 4
```

## Node table

| Node | Statement | Source | Status | Verification |
|---|---|---|---|---|
| N1 | Gallai ⇔ R (doubling identity p(double) = 2p(H^r) − 1) | REC §1, SP §1 | **AUDITED** (A3) | **lean** (`gallai_iff_rootedTest`) |
| N2 | MR Thm 1 | MR §1–2 | **AUDITED** (A1); wording gaps G1–G4 | comp (eq. (2): 210 instances) |
| N3 | MR Thms 7, 57, 59 | MR | **AUDITED** (A1); gaps G6–G9 (wording) | comp (bridge/diamond doubles: 210) |
| N4 | MR Thms 113, 114 | MR §18–19 | **AUDITED** (A2): no errors; external paraphrases (Fan, FHZ, Shaik) being verified (A7) | lean-ext; comp (n ≤ 8) |
| T(4) | both tests at d = 4 | MR p.129 (Fan–Hou–Zhou) | CLAIMED | — |
| T(6)-ii | three-end test, d = 6 | MR Thm 123 | CLAIMED | — |
| T(8)-ii | three-end test, d = 8 | MR Thm 128 (computer: Thm 124) | CLAIMED | lean-ext? |
| T(6)-i | two-end test, d = 6 (= floor for odd W with a leaf and 5 even vertices, MR Thm 144) | Nov 26 studies | **OPEN**, heavily reduced; audit A6 in progress | — |
| T(8)-i | two-end test, d = 8 | MR Thm 130 (only root degree 2) | **OPEN** | — |
| T(≥10) | both tests | partial (hubs) | **OPEN** | — |
| U | a uniform-in-d mechanism closing T(d) for every d | this project: FD / EMC (`research/connections.md` B, C) | **CONJ** | comp(n ≤ 6) |

## Side chains that also reach Gallai

| Node | Statement | Source | Status |
|---|---|---|---|
| S1 | Bonamy–Perrett floor for 2-connected odd graphs, plus N2's marked bound, implies Gallai | MR Thm 1 + semi-clique Thm 4 | CLAIMED |
| S2 | first failure: either a 2-connected odd floor witness, or failing hosts are 6-edge-connected with δ ≥ 6 | SP Thm 10.16, Cor 13.5 | **AUDITED** (A3) modulo JM; citation gaps G1 and G2 in §12 |
| S3 | odd semi-cliques: p = k + 1 exactly | OSB Thm 4 (Javadi–Miralaei) | **AUDITED modulo JM** (A4). **JM's proof has a substantive gap (Thm 8, Claim 12)**; JM verified computationally for k ≤ 7; repair in progress |
| S4 | dense: exact at δ ≥ (1/2+ε)n, large n | SP Thm 14.1 | CLAIMED |
| S5 | blocks with Δ ≤ 7 satisfy the floor | block-degree Thm 3 | **AUDITED + all enumerations independently replayed** (A5). Cited ≤ 5-contact lemmas re-proved exhaustively. JM needed only for k ≤ 3, which Liu–Chen covers. |

## External dependencies

| Result | Used by | Status |
|---|---|---|
| Lovász mixed theorem | everything | classical |
| **Javadi–Miralaei (Wu's conjecture)** | OSB Thm 4 / Thm 11; SP Thm 10.16 equality case; block-degree Thm 2 | **published (DM 349, 2026); proof gap in Thm 8 / Claim 12 (A4)**. Liu–Chen covers k ≤ 5, linear forests, and support ≤ k+1. Repair agent running. |
| Fan addible-edge lemmas | six-even program; MR | Lemma 3.4 (single edge) **matches** (A7, via quotations); the grouped Lemma 3.3 has no accessible source. Lean formalization in progress. |
| Fan–Hou–Zhou | T(4); MR p.129 | **matches** (A7): no triangle pair, and each block has Δ ≤ 3; ceiling conclusion |
| Chu–Fan–Zhou Lemma 2.4 | MR (≈5 places), even-degrees, SP | **RISK** (A7): used with \|V(P)\| + q ≤ 7, but the verifiable version has ≤ 6. Repair agent running. |
| Shaik (Hexagon preprint, unrefereed) | MR Thm 144, Cor 106 | A7: Botler–Sambinelli replaces it at the Thm 144 r ∈ T step and in the zero-exception case of Cor 106. **The one-exception case of Cor 106 still needs Shaik**, so Thm 144 remains conditional. |

**The MR equivalence spine (N2–N4) does not depend on JM** (A1, A2).

## Current strategy

1. **Robustness first.** Audit N1–N4, S2, S3 and S5. Fix every gap in the manuscripts. Formalize the elementary nodes (N1, the parity lemmas, the W(F,S) identity) in Lean.
2. **Uniform mechanism.** Test FD and EMC further: n = 8 exhaustive and random n = 10, 12. Then try to prove the single-descent lemma, which would give T(d) for all d. This is the only route found so far that does not grow with d.
3. **Close T(6)-i** using the shape reductions as a testbed for the uniform mechanism.

## Log

- 2026-11-26: collection pushed; orientation `STATUS.md`; tools built.
- FD and EMC hold on all critical graphs with n ≤ 6.
- CP refuted at n = 7.
- Audits A1–A6 launched.
- Lean project created (`lean/`).
- Lean: N1 (`gallai_iff_rootedTest`), parity, the private-leaf formula, and the endpoint-structure Lemmas 1–4 are all formalized.
- Corrigenda document written (`manuscripts/corrigenda`).
- New manuscript draft `manuscripts/endpoint-structure`.
