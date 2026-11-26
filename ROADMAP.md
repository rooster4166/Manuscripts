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
| T(4) | both tests at d = 4 | MR p.129 (Fan–Hou–Zhou); **also endpoint-structure Cor 22 (BP_3 from Lovász + Fan only, via the floor form of MR Thm 114)** | CLAIMED | **lean** (`rooted_four`, `rooted_le_four`; Lovász as hypothesis) |
| T(6)-ii | three-end test, d = 6 | MR Thm 123 | CLAIMED | — |
| T(8)-ii | three-end test, d = 8 | MR Thm 128 (computer: Thm 124) | CLAIMED | lean-ext? |
| T(6)-i | two-end test, d = 6 (= floor for odd W with a leaf and 5 even vertices, MR Thm 144) | Nov 26 studies | **OPEN**, heavily reduced. **A6: no errors; shape-theorem banks independently re-derived; Thm 144 can be made Shaik-free (BS Thm 13 + Lemma 133).** Unreplayed inputs remain: Thm 135, Thm 137, Lemma 121, the INC trees, 6CL's 31,442 records, D10's tables | comp (n = 8 all instances) |
| T(8)-i | two-end test, d = 8 | MR Thm 130 (only root degree 2) | **OPEN** | — |
| T(≥10) | both tests | partial (hubs) | **OPEN** | — |
| U | a uniform-in-d mechanism closing T(d) for every d | this project: FD / EMC (`research/connections.md` B, C, N) | **CONJ**; proved parts: FD for \|S\| ≥ e − 1 (two descent steps, endpoint-structure Thm 19) and EMC for e = 4 (Thm 21) | comp(n ≤ 6); the proved parts are **lean** (`two_step_descent`, `endpoint_matroid_four`) |

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
| Fan addible-edge lemmas | six-even program; MR | **Both proved in Lean** (`fan_single`, `fan_grouped`; sorry-free). Lemma 3.4 also matches its published quotation (A7). |
| Fan–Hou–Zhou | T(4); MR p.129 | **matches** (A7): no triangle pair, and each block has Δ ≤ 3; ceiling conclusion |
| Chu–Fan–Zhou Lemma 2.4 | MR (≈5 places), even-degrees, SP | **RISK** (A7): used with \|V(P)\| + q ≤ 7, but the verifiable version has ≤ 6. Repair agent running. |
| Shaik (Hexagon preprint, unrefereed) | MR Thm 144, Cor 106 | A7: Botler–Sambinelli replaces it at the Thm 144 r ∈ T step and in the zero-exception case of Cor 106. **The one-exception case of Cor 106 still needs Shaik**, so Thm 144 remains conditional. |

**The MR equivalence spine (N2–N4) does not depend on JM** (A1, A2).
### Contingency if the Javadi–Miralaei repair fails

| Result | Effect |
|---|---|
| SP Thm 10.16, alternative 1 | "≥ h+1 missing edges" weakens to "≥ h, and exactly h only when the hole graph is JM-residual (h ≥ 6, not a linear forest, support ≥ h+2)" |
| OSB Thm 4 | the lower bound p ≥ k+1 is elementary; the upper bound loses only the residual family (k ≥ 6, ⌈(k+4)/2⌉ ≤ m ≤ k−1, sparse non-linear-forest H) and its m = k analogue |
| MR equivalence spine (N2–N4) | unaffected |
| block-degree Thm 3 | unaffected |



## Final assembly target (after the audits)

**Floor form of the two tests.** Using MR Thm 114 (audited) and the private-leaf trick:

- **Test (i) at degree d** is the floor bound for W = (J − z) plus one leaf at r. W has odd order and exactly d − 1 even vertices, namely N(z) − r.
- **Test (ii) at degree d** is the floor bound for (J − z) plus two leaves at r. This graph also has odd order and d − 1 even vertices.

So **Gallai ⇔ BP_t for every odd t** (restricted to the apex class), where:

> **BP_t:** connected, odd order, at least one pendant leaf, exactly t even vertices ⇒ p ≤ ⌊n/2⌋.

| t | Status | Source |
|---|---|---|
| 1 | proved | Lovász |
| 3 | proved | Fan–Hou–Zhou / Botler–Sambinelli (A7 confirms the statements); **independently endpoint-structure Cor 22 from Lovász + Fan, Lean-verified (`rooted_le_four`)** |
| 5 | **open** | test (i) at d = 6, i.e. MR Thm 144, which is conditional on Shaik; test (ii) at d = 6 is closed (MR Thm 123) |
| 7 | **open** | test (i) at d = 8; test (ii) at d = 8 is closed (MR Thm 128, computer, audit A8) |
| ≥ 9 | **open** | — |

For t = 5, Botler–Sambinelli leaves only E-subgraphs that contain a bowtie or a block with a degree-4 vertex, i.e. dense E-subgraphs on five vertices.

**What a complete proof needs:** an argument for BP_t that is uniform in t, or an induction BP_t ⇒ BP_{t+2}.

Candidate uniform mechanisms (`research/connections.md`):

- the endpoint matroid conjecture (EMC); **proved for e = 4, and its first two descent steps are proved for every e** (connections §N);
- faithful descent (FD);
- a theorem on cliques of even vertices.

## Current strategy

1. **Robustness first.** Audit N1–N4, S2, S3 and S5. Fix every gap in the manuscripts. Formalize the elementary nodes (N1, the parity lemmas, the W(F,S) identity) in Lean.
2. **Uniform mechanism.** Test FD and EMC further: n = 8 exhaustive and random n = 10, 12. Then try to prove the single-descent lemma, which would give T(d) for all d. This is the only route found so far that does not grow with d.
3. **Close T(6)-i** using the shape reductions as a testbed for the uniform mechanism.


## Work queue (next wave)

| # | Item | Purpose |
|---|---|---|
| Q1 | Shaik [25, Cor 1.2]: there is a **public Lean formalization**, github.com/shaikidris/gallai-two-exception (488 files, 79k lines, Lean v4.35.0-rc3). Its statement file `Challenge.lean` was inspected and is faithful: `ceiling_bound` is exactly Cor 1.2, with decompositions as genuine edge partitions into nonempty simple paths. A grep finds no sorry, axioms or IO. Building it here was **blocked by the session's permission policy** (third-party code). To verify: `lake exe cache get && lake build Solution`, then `#print axioms Gallai.Submission.ceiling_bound`. If clean, Cor 106 and Thm 144 become machine-verified. Fallback: prove the one-exception odd-order case directly. The gadget attempts (edge xx′; path x–y–x′) each lose one unit of budget (connections §L). | makes MR Thm 144 unconditional |
| Q2 | Close D = ∅ at d = 6: clique core B[U] = K6 with full exterior vertices (six-clique Thm 6 covers ≤ 5 core neighbours; false-twin-return covers some full cases) | the largest residual d = 6 shape |
| Q3 | EMC for structured classes: cones K1 ∨ H (arm-pairing reformulation) and thread graphs (all even vertices of degree 2). **Done for e = 4 in general (Thm 21).** Next: the third descent step for e = 6, i.e. Thm 19 with the second deleted vertex avoiding N(y) (connections §N) | provable special cases of the uniform conjecture |
| Q4 | Lean: Prop "critical ≠ forced" lower bound; the d = 4 test from Botler–Sambinelli as an explicit hypothesis | pair the manuscript propositions with formal proofs |
| Q5 | Audit SP §14 (dense exact theorem) | off the Gallai-critical path; lower priority |

## Log

- 2026-11-26: collection pushed; orientation `STATUS.md`; tools built.
- FD and EMC hold on all critical graphs with n ≤ 6.
- CP refuted at n = 7.
- Audits A1–A6 launched.
- Lean project created (`lean/`).
- Lean: N1 (`gallai_iff_rootedTest`), parity, the private-leaf formula, and the endpoint-structure Lemmas 1–4 are all formalized.
- Corrigenda document written (`manuscripts/corrigenda`).
- New manuscript draft `manuscripts/endpoint-structure`.
- 2026-11-26 (cloud session, branch `claude/emc-four-even`): **two-step faithful descent** (Thm 19) and **EMC for e = 4** (Thm 21), both from Lovász + Fan's transfers. Formalized in `lean/GallaiLean/EMCFour.lean` (no sorry). Corollary: BP_3 / T(4) without Fan–Hou–Zhou or Botler–Sambinelli. Next target: a third descent step with the second deleted vertex avoiding N(y) (connections §N).
