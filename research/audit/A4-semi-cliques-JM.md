# A4 — Referee audit: odd semi-cliques (Thm 4, Thm 11 / Cor 12, §15 equivalences, e(G) clash) and the Javadi–Miralaei dependency

Auditor: adversarial referee pass, 2026-11-26.

Sources audited:
- **[OSC]** "Odd semi-cliques and sharp path partitions near complete graphs" (J. Williams, 23 Nov 2026), `gallai/01-original-manuscripts/odd-semi-clique-boundary.pdf`, 56 pp. Page numbers below are PDF pages.
- **[SEP]** "Gallai's conjecture for the odd semi-cliques" (September note), `gallai/06-historical-context/odd-semi-cliques-september.pdf`, 9 pp.
- **[JM]** R. Javadi, M. Miralaei, "A Conjecture on Rainbow Hamiltonian Cycle Decomposition", arXiv:2403.17290v1 (26 Mar 2024). This is the only arXiv version. I downloaded it and read it in full.

Verdicts: **SOUND**; **GAP** (fixable; the fix is stated); **ERROR** (false as stated; a counterexample or concrete defect is given); **UNCLEAR** (cannot be settled from the available material).

---

## 0. Executive summary

1. **Thm 4 (= SEP Thm 1.4/2.4) is sound modulo [JM].** This covers the planted-path proof, the endpoint prescription with total budget L + 1 and its sharpness, the m = k rigidity, and the m > k, support ≤ k + 1 case. I verified the elementary steps line by line. Where the paper uses the rainbow theorem, the statement it cites is exactly JM's main theorem.
   - Dependency bookkeeping is incomplete. The statement "JM is needed only for k ≥ 6, ⌈(k+4)/2⌉ ≤ m ≤ k−1, |V(H)| ≥ k+2, H not a linear forest" covers only the m < k upper bound.
   - The m = k part needs JM for every k-edge H with k ≥ 6, |V(H)| ≥ k + 2 that is not a linear forest.
2. **Thm 11 / Cor 12: the elementary skeleton and all arithmetic are sound.**
   - I reproduced the finite donor table independently: 17,507 triples, least margin 2 at (k, g, r) = (19, 2, 26). I also brute-forced every inequality of the k ≥ 130 argument for 130 ≤ k < 1500 (9.08 M triples): 0 failures.
   - Weak point 1: the proof rests on JM's *matching-extension* theorem, and uses its *proof* rather than its statement.
   - Weak point 2: the citation "Theorem 3.8" is wrong. In arXiv v1 the result is **Theorem 8** (§3), and nothing is numbered 3.8. I could not access the published version (ScienceDirect returned 403), so I cannot tell whether that version renumbers it.
   - **The proof of JM Theorem 8 has a gap (Claim 12; §2, J2).** Thm 11 therefore inherits an **UNCLEAR** status in its general case (g ≥ 1 with h > 0). The statement agrees with every computation I ran.
3. **JM main theorem (Wu's conjecture).**
   - The statement has no restrictions: every k-edge X ⊆ K_{2k+1} is rainbow in some Hamilton decomposition.
   - Published: Discrete Math. **349(1)** (Jan 2026), Art. 114676, DOI 10.1016/j.disc.2025.114676 (Crossref).
   - Proof audit:
     - **J1** (GAP, fixable): the transfer steps in Thm 7 state an insufficient separation condition.
     - **J2** (GAP, substantive): in Claim 12 the "pairing" step is not justified when L′ contains both duplicates of an endpoint edge. Even as stated, Claim 12 (iv) does not imply the linear-forest conclusion.
   - **I verified the theorem computationally for every k-edge X up to isomorphism at n = 5, 7, 9, 11, 13, 15 (k ≤ 7)**: 2 + 5 + 11 + 26 + 68 + 177 classes, no failures. This covers the whole JM-residual range of Thm 4 at k = 6, 7.
4. **§15.** Thm 43, Cor 44, Prop 45, Thm 46, Prop 47, Thm 48 and Thm 50 are **SOUND**.
   - **Cor 44's quantifier must be "for every C" (a conjunction over C).** The hosts used have ≈ |V(X)|·N missing edges, so no single fixed C works.
   - The reader-notes paraphrase "for any fixed C > 0" claims more than the paper proves (**ERROR in notes**; **UNCLEAR wording** in the paper).
5. **e(G) clash: no proof uses the wrong meaning mathematically.** Every numerical use matches its intended meaning. Read literally, however:
   - **Cor 27 is false at odd order**: K_{2k+1} itself is a counterexample.
   - The second alternatives of Thm 20 and Cor 23, and Cor 40, are vacuous.
   - Thm 28, Thm 31 and Cors 33/34 become unproved sparse statements.
   - In Prop 26 and Thm 31, X = {v : d_G(v) > .01n} is a typo for the missing degree.
   - Inside the proofs of Thm 20 and Thm 38, e(G) also denotes |E(G)| (correctly).

---

## 1. Verdict table

| # | Item (location) | Verdict | Note |
|---|---|---|---|
| T4.1 | Lower bound p ≥ k+1 from e(G) = 2k²+L > 2k² ([OSC] p.3; [SEP] Lemma 2.5 p.4) | SOUND | |
| T4.2 | Greedy plant Q of length L, using δ(G) ≥ 2k−m ([OSC] p.3; [SEP] Lemma 2.6 p.4–5 via Dirac) | SOUND | Greedy extension needs 2k−m > j−1 for j ≤ L; it holds. |
| T4.3 | Rainbow step: X = H ∪ E(Q), \|X\| = k; open each cycle at its mark; restore Q ([OSC] p.3; [SEP] p.5) | SOUND given [JM] main theorem | [SEP] Thm 2.2 quotes JM Conj. 1 correctly (§2.1). |
| T4.4 | Endpoint formula (1): b_v = d_H(v)+2·1_{V(Q)} ([OSC] p.3) | SOUND | Uses L ≥ 1. |
| T4.5 | Cap e_v ≤ d_H(v)+2 and parity e_v ≡ d_H(v) ([OSC] p.3) | SOUND | |
| T4.6 | Prescription with Σr_v ≤ L+1: path through S with universal connectors ([OSC] p.3) | SOUND | g ≤ e(H[S]) ≤ ½Σ_S d_H; ≥ 2L+1−\|S\| ≥ L ≥ g universal vertices lie outside S. |
| T4.7 | Sharpness of the total L+1 (m-matching + L+2 universal vertices) ([OSC] p.3–4) | SOUND | Counting: 2m+2(L+2) = 2k+4 > 2k+2. |
| T4.8 | Individual cap, deleted (k−1)-star, triangle remarks ([OSC] p.4) | SOUND | |
| T4.9 | m = k: p = k, all optimal paths Hamiltonian ([OSC] p.4; [SEP] Prop 3.1 p.6) | SOUND given [JM] | **GAP (bookkeeping):** the "Earlier rainbow theorems" paragraph and [SEP] §4 discuss the residual JM-dependence only for m < k; m = k needs JM for k ≥ 6, \|V(H)\| ≥ k+2, H not a linear forest. |
| T4.10 | m > k, support s ≤ k+1 ([OSC] p.4) | SOUND | Lovász gives ≤ s−1 paths; split into k; greedy linear forests on K_s (≤ s−2 < k forbidden colours); Hilton/JM Cor 6 needs ≥ 2s−2k−1 ≤ 1 edges per class; remove the paths; lower bound from a vertex off the support. Replayed for k ≤ 5 (§4). |
| T4.11 | "Earlier rainbow theorems" and residual family ([OSC] p.4; [SEP] Thm 4.3, Lemma 4.4, Cor 4.5 pp.6–7) | SOUND | The smallest residual H, K_{1,3} ⊔ 2K_2 at n = 13, is unique (re-derived). All 8 plant orbits verified (§4). |
| T11.1 | Form of all attainable vectors with b ≥ d_H ([OSC] p.11) | SOUND | |
| T11.2 | Min path cover of G[S], clique of chosen ends in H, g ≤ L, connectors W, Q of length L+g ([OSC] p.11) | SOUND | |
| T11.3 | Special cases g = 0; L = 1; (g, L) = (1, 2); coverage of k ≤ 2 ([OSC] p.11) | SOUND | Arc bookkeeping re-derived; replayed at n ≤ 9. |
| T11.4 | (ℓ, D), e(H[S]) ≥ D, k colours (g wedges + k−g singletons) ([OSC] p.11) | SOUND | |
| T11.5 | Core bounds s ≤ 2k−L−g+1, r ≤ 2t−1, (2) 2r ≤ 3k−5, (3) ([OSC] p.11) | SOUND | Algebra re-derived. |
| T11.6 | Reduction to completing K_r into k linear forests via "JM matching extension … Theorem 3.8" ([OSC] p.12; also p.9) | **ERROR (citation)** + **GAP (hypothesis)** + **UNCLEAR (inherited)** | v1 has Theorem 8; "3.8" does not exist. Statement of Thm 8 assumes G ≇ tK_2, but its proof uses only r ≤ 2t−1 (needed for k ≥ 4); [OSC] has r ≤ 2t−1. Inherits JM gap J2. |
| T11.7 | Small core r ≤ k+1: two edges per empty colour; greedy completion ([OSC] p.12) | SOUND | Slack k(k−3)/2+t−g ≥ 0. |
| T11.8 | Larger cores: JM at order 2d+1, protected singletons, transfer observation, one- and two-forest schemes ([OSC] p.12) | SOUND | The transfer observation (orientation rule, from the Thm 9 proof p.9) is correct. Counts re-derived for u ≥ 2. |
| T11.9 | Estimates for k ≥ 130 (three ranges) ([OSC] pp.12–13) | SOUND | Brute force over 130 ≤ k < 1500 (9,075,959 triples): 0 failures. b > 0 only at (3j, 4j, 1), (3j+2, 4j+2, 2), as stated. |
| T11.10 | Finite comparison 1 ≤ k < 130 ([OSC] p.13) | SOUND | Reproduced exactly: 17,507 triples, least margin 2 at (19, 2, 26); also 0 failures for k < 400. The cited anc/ files and Lean proof are **not in the repository**. |
| T11.11 | Opening cycles: vector d_H+d_Q−2·1_W, then +Q gives d_H+2·1_S ([OSC] p.13) | SOUND | |
| C12.1 | End-pair multigraph = H + cycle on S ([OSC] p.13–14) | SOUND | At n ≤ 7 *every* Hamilton cycle C on S is realizable; this is stronger than claimed (§4). |
| C12.2 | Appending a new vertex: possible iff S meets every tree component of H inside N ([OSC] p.14) | SOUND | Hall plus rooted orientation. |
| S.1 | [SEP] Remark 2.3, Remark 2.7, §5 even-order obstruction (Δ(H) ≤ k, e ≤ v by SDR) | SOUND | |
| S.2 | [SEP] "Thm 1.4 is new exactly for n ≥ 9" | SOUND | (4·7+6)/7 < 5; (4·9+6)/7 = 6 > 5. |
| S.3 | [SEP] Data availability (n = 7, 9 labelled; 13 ≤ n ≤ 25 classes); [OSC] anc/ supplement | UNCLEAR | No artefact (URL "to be inserted"). |
| Q43 | Thm 43 p(Y_h) = p(X)+h+η_X(x) ([OSC] p.44) | SOUND | 254 instances checked. |
| Q44 | Cor 44 ([OSC] p.45) | SOUND under "∀C"; **UNCLEAR wording**; reader-notes reading is an **ERROR** | Y_h has j(2h+1)−1+C(j,2)−e(X) ≈ jN missing edges (j = \|X\|). |
| Q45 | Prop 45 (7), (8) ([OSC] p.45) | SOUND | Hub formula 3(p+η)−1 checked on 32 instances. |
| Q46 | Thm 46 ([OSC] pp.46–47) | SOUND | All six implications and the two-ends claim re-derived. |
| Q47 | Prop 47 ([OSC] p.47) (load-bearing for 48) | SOUND | Floor accounting for proxies (+2h−2 vertices, +h−1 paths) and odd branches checked. |
| Q48 | Thm 48 ([OSC] p.48) | SOUND | Amplification host 2-connected for m ≥ 2; integrality bound (N+m)/2 + 1/(2(m+1)) correct. |
| Q50 | Thm 50 ([OSC] pp.50–51) | SOUND | p_i = p(D + i leaves), bridge and diamond identities re-derived and machine-checked on small cores. |
| E.1 | Thm 20 hypothesis "e(G) ≤ Cn and δ ≥ K" ([OSC] p.25) | notation ERROR (literal: vacuous); proof OK | The proof uses e(G) = \|E(G)\| in Σa_v = s(n−1)−e(G) and the missing-edge meaning for \|X\| ≤ 200C. |
| E.2 | Cor 23 ([OSC] p.27) | notation (literal: vacuous); proof OK | |
| E.3 | Prop 26 ([OSC] p.30) | notation + typo | X = {v : d_G(v) > .01n} should use the missing degree. |
| E.4 | Cor 27 ([OSC] p.31) | **ERROR (literal statement false)**; proof OK | K_{2k+1} has 0 missing edges and L′ = ∅, and e(G) ≥ k, yet p = k+1. |
| E.5 | Thm 28 ([OSC] p.31) | notation; proof OK | Proof needs the missing-edge meaning (Thm 19, Lemma 25). |
| E.6 | Thm 31, Cor 33, Cor 34 ([OSC] pp.34–36) | notation (+ typo d_{G′}(v) in Thm 31); proofs OK | |
| E.7 | Thm 38 proof / Cor 39 / Cor 40 ([OSC] pp.39–42) | notation (Cor 40 literal: vacuous); proofs OK | Thm 38 proof: e(G) = \|E(G)\| (p.41); Cor 39: e(G) = missing (p.39). |
| JM0 | JM statement, scope, publication | verified | §2.1. |
| JM1 | JM Thm 7 transfer steps (Cases 1–2, pp.4–6) | GAP (fixable, no change in counts) | §2.3. |
| JM2 | JM Thm 8, Claim 12 (pp.8–9) | GAP (substantive; likely repairable) | §2.4. |
| JM3 | JM Thm 8 hypothesis "G ≇ tK_2" | GAP (minor) | Only r ≤ 2t−1 is used. |

---

## 2. Javadi–Miralaei: statement verification and proof audit

### 2.1 Bibliographic and publication status

- arXiv:2403.17290 has a single version, **v1, 26 Mar 2024, 36 KB**. The abstract page lists no later versions.
- Crossref record for DOI **10.1016/j.disc.2025.114676**:
  - title "A conjecture on rainbow Hamiltonian cycle decomposition", authors Javadi, Miralaei;
  - *Discrete Mathematics* **349**, issue **1**, article **114676**, issued **2026-01**;
  - record created 2025-07-23 (i.e. accepted mid-2025).
  - [OSC] ref. [14] and [SEP] ref. [13] match this.
- I could not obtain the published text (ScienceDirect 403; the Elsevier API refused). **Whether the published version renumbers Theorem 8, or changed the proof of Claim 12, is UNCLEAR.** [OSC] p.12 says explicitly "See also Theorem 3.8 and its proof in the preprint". In the preprint, theorems are numbered consecutively (Thm 2, 3, 4, 5, Cor 6, Thm 7, Thm 8, Lemmas 9–11, Claim 12, Conj 13), so "3.8" is a citation error in any case.

### 2.2 Statements (verbatim from v1)

> **Conjecture 1** [14]. Let H be a subgraph of K_{2n+1} with n edges. Then, K_{2n+1} admits a Hamiltonian cycle decomposition C such that H is rainbow in C.

> Abstract: "…The conjecture was partially settled by Liu and Chen (2023) in cases that |V(H)| ⩽ n+1, H is a linear forest, or n ⩽ 5. In this paper, we settle the conjecture completely."

> **Theorem 2** [11] (Liu–Chen). Suppose that H is a subgraph of K_{2n+1} with n edges such that either H has at most n+1 vertices, or H is a linear forest, or n ⩽ 5. Then, there is a Hamiltonian cycle decomposition C of K_{2n+1} such that H is rainbow in C.

> **Corollary 6** [8] (Hilton). Let 1 ⩽ r ⩽ 2n be an integer. An edge decomposition C = (C1,…,Cn) of K_r can be extended to a Hamiltonian cycle decomposition C′ = (C′1,…,C′n) of K_{2n+1} where C_i ⊆ C′_i, for each i ∈ [n], if and only if 1. for each i ∈ [n], the induced subgraph of K_r on C_i is a linear forest, and 2. for each i ∈ [n], |C_i| ⩾ 2r − 2n − 1.

> **Theorem 7.** Let H be a minimal counterexample to Conjecture 1 with n edges. Also let H′ be the subgraph of H containing all its connected components which are not isomorphic to K2 and suppose that H′ has r vertices and t edges. Then, the complete graph K_r admits an edge decomposition (P1,…,Pn) such that (1) each P_i induces a linear forest in K_r; (2) H′ is rainbow in (P1,…,Pt); (3) |P_i| ⩾ 2r−2n−1 for i ∈ [t]; (4) |P_i| ⩾ 2r−2n for i ∈ [t+1,n].

> **Theorem 8.** Let G be a graph with t edges and r vertices, where G ≇ tK2 and also let n ⩾ t be an integer. Suppose that K_r admits an edge decomposition P = (P1,…,Pn) such that for each i ∈ [n], P_i induces a linear forest in K_r, G is rainbow in P1,…,Pt and for each i ∈ [t], |P_i| ⩾ 2r − 2n − 1 and for each i ∈ [t+1,n], |P_i| ⩾ 2r − 2n. Then, P can be extended to a Hamiltonian cycle decomposition of K_{2n+1} in which the graph G ∪ (n − t)K2 is rainbow.

> "Combining Theorems 7 and 8 settles Conjecture 1 … So, Conjecture 1 is settled."

**What this means for the audited papers** (JM's n is the audited papers' k):
- **Main theorem.** There is no restriction on k or on the structure of X. With |X| = k exactly, "rainbow" means exactly one X-edge per cycle. [SEP] Thm 2.2 and [OSC] p.3 use it in exactly this form. ✔
- **Matching extension (Theorem 8).** The hypotheses are: a k-colour decomposition of K_r into linear forests; a rainbow "representative" graph G on the first t colours; sizes ≥ 2r−2k−1 (seeded colours) and ≥ 2r−2k (the others); and G ≇ tK_2. The conclusion places an (n−t)-edge matching *on the exterior vertices* in the remaining colours. Two points about how [OSC] uses it:
  - [OSC] needs the matching to be a *prescribed* matching. Relabelling the exterior vertices (a symmetry fixing K_r) gives this. ✔ (Here r + 2h ≤ 2k − 1.)
  - [OSC] applies it with a representative graph that may have isolated vertices on V(K_r). Read literally, Theorem 8 allows this (G has "r vertices", and an isolated vertex makes G ≇ tK_2). The **proof**, however, needs k_JM := 2n − 2s − r + 1 ≥ 4 for all s ≤ n − t − 1, i.e. **r ≤ 2t − 1** (p.9: "since k ⩾ 4 as r ⩽ 2t − 1"). With isolated vertices allowed, "G ≇ tK_2" does not imply this, and for r ≥ 2t + 2 the conclusion cannot even fit. [OSC] has r ≤ 2t − 1 (Thm 11 p.11, Thm 9 p.9), so the use is legitimate, but it goes through the proof, as [OSC] itself says. **GAP (minor, JM3):** the hypothesis should read "r ≤ 2t−1".
  - Seeds that are wedges (two edges in one colour) are harmless: Theorem 8 keeps P_i ⊆ C′_i, and only one representative per seed is needed. ✔
- **Hilton's theorem.** [OSC]'s use (≥ 2s−2k−1 edges per class, s ≤ 2k) matches Cor 6 exactly. ✔

### 2.3 JM1 — Theorem 7, transfer steps (pp.4–6): GAP, fixable

- **Case 1.** "let e1 and e2 be two edges in P_j incident with a and b, respectively (if exist) such that in G[P_j∖{e1,e2}], a and b are in different connected components." Separation alone does not keep the receiver {ab} ∪ (moved edges) linear. If a is internal to a P_j-path and is already separated from b, the stated rule allows e1 to be absent, and then a can receive degree 3.
- **Case 2.** "P′_ℓ … all edges incident with I_i along with at most one edge incident with each vertex in J_i such that if z, w are two endpoints of a path in G[P_i] then z and w are in different connected components of G[P_ℓ∖P′_ℓ]." This does **not** prevent cycles through *two* receiver paths.
  - Example: P_i ⊇ {z1w1, z2w2} as two separate paths, and P_ℓ ⊇ {w1x, xz2, w2y, yz1}.
  - The stated condition holds with P′_ℓ = ∅, yet moving these edges creates the cycle z1 w1 x z2 w2 y z1.
- **Fix (counts unchanged).** Orient every path of P_ℓ (respectively P_j). Delete all its edges at internal vertices of the receiver, and its out-edge at each end of the receiver. Each surviving component then meets the receiver in at most one vertex, a receiver end that is its sink, so the union stays a linear forest. At most 2|I_i| + |J_i| = 2|P_i| edges are deleted, which is the bound JM use.
- This is exactly the "transfer observation" [OSC] proves on p.9, so [OSC]'s own transfers are sound.

### 2.4 JM2 — Theorem 8, Claim 12 (pp.8–9): GAP (substantive)

**Setting.** G̃ is the colour/vertex bipartite multigraph:
- one edge c_i u_j if u_j is an end of a path of Q_i;
- two parallel edges if u_j is isolated in Q_i;
- none if u_j is internal.

Ĝ doubles every edge. A balanced k-colouring L_1,…,L_k of Ĝ is taken, four classes L_1,…,L_4 are selected (via the vertex u′), and L′ = L′_1 ∪ L′_3 ⊆ L̂_1 ∪ … ∪ L̂_4 is formed. Then:

> "we apply Lemma 10 for the graph F = Ĝ[L′] and the following pairing: if there are two parallel edges e1, e2 joining ci to uj, then e1 and e2 form an i-pair. If ci is adjacent to uj and uj′, where uj and uj′ are the endpoints of one path in Qi, then ciuj and ciuj′ form an i-pair. … Therefore, there is a balanced two-coloring for F, called E1, E2, such that if ci is adjacent to some vertices uj1 and uj2 in Ei … then uj1 and uj2 are not the endpoints of a path in Qi."

Then E1 is split *by an arbitrary balanced 2-colouring* (Lemma 9) into E11, E12, which give G1 and G2.

**Problems.**

(a) **Pairing conflict.** Let u_j and u_{j′} be the two ends of a path A of Q_i.
- The two Ĝ-duplicates of c_i u_j lie in two different classes of the balanced k-colouring. If both classes are among L_1,…,L_4, nothing in the construction stops both duplicates from surviving into L′.
- F then has two parallel edges c_i u_j. A balanced 2-colouring of F must split them: E1 and E2 each get one.
- So whichever of E1, E2 receives an edge c_i u_{j′} contains **both ends of A**. The two pairing rules cannot both be honoured: the parallel copies are already paired with each other. Lemma 10 itself allows at most one parallel copy to be paired outside its class, and balance still forces the same outcome.
- E1 is then fixed by a degree requirement at c_{s+t+2}, so it cannot be chosen to avoid this. The asserted property of E1 is therefore not established.
- Similarly, an isolated u_j can contribute up to four duplicates to L′. E1 may then hold two of them, so the clause "G1 ∪ G2 has no parallel edges" in (v) is not guaranteed either. At c_{s+t+1} that would create the triangle u′ u_j u″.

(b) **(iv) as stated is not sufficient.** (iv) is a per-G_ℓ condition. Suppose that, at c_i, G1 joins u′ to the ends z_A, z_B of two different paths A, B, and G2 joins u″ to their other ends w_A, w_B. Then (iv) holds for each G_ℓ, yet Q_i acquires the cycle u′ z_A … w_A u″ w_B … z_B u′. The linear-forest conclusion ("because of Conditions (ii), (iv) and (v) of Claim 12, each Q_i induces a linear forest") needs the *joint* condition: no two ends of a common Q_i-path among the G1 ∪ G2-neighbours of c_i. The pairing step was meant to supply exactly that, and by (a) it does not.

(c) Problems (a) and (b) together can force a genuine failure: if E1 at c_i contains both ends of two different paths, *every* split into G1/G2 creates a cycle. Nothing in L′'s construction excludes this.

**Assessment.**
- This is a gap in the written proof, not a counterexample. Every computation agrees with the theorem (§4: all k-edge X for k ≤ 7).
- Plausible repairs: add the two new vertices *sequentially*, with Hilton's undoubled one-vertex step and the edge u′u″ handled in colour s+t+1; or use an amalgamation/detachment argument with an auxiliary colour carrying the matching, in the style [OSC] itself uses for Lemma 15 (pp.15–17). Neither repair is a one-liner.
- **Recommendation:** until an expert confirms a repair, treat JM's main theorem as "published, computationally confirmed for k ≤ 7, proof with a gap in Claim 12". Every result of [OSC] that depends on it should carry that dependency explicitly: Thm 4 (residual family, k ≥ 6), Thm 4 at m = k, Thm 11 / Cor 12 / Cor 13, Thms 3, 9 and 16.

### 2.5 Other JM steps checked (SOUND)

- Thm 7:
  - r ≤ (3t−1)/2.
  - The extension to Ĥ with v(Ĥ) ≤ e(Ĥ) = n when r ≤ n: fill inside V(H′) first, then add pendant edges.
  - s = ⌈r/2⌉ ≤ t < n.
  - Case 1 claim |P_{n−s}| ≥ 4r−4n−1: f_n(n+1) = 3n−11 and f_n((4n−1)/3) = 1.
  - Case 2 claim: f_{n,t}(4n/3) = 2n−2t−δ+2ε, g_n((8n+3)/9) = 4n/9−2δ−4/3, g_n(n−1) = n(3−δ)+10δ−32, all re-derived.
  - The donor index ranges [1, t−s], [t−s+1, 2t−2s], [2t−2s+1, n+t−2s], [n+t−2s+1, 2n−2s] are disjoint.
  - Every donor retains ≥ 2r−2n−1.
- Thm 8, counting:
  - deg_G̃(u_j) = k, deg_G̃(c_i) = 4s+2r−2|Q_i|.
  - ⌊(4k−4x)/k⌋ ≥ 4−x and ⌊(4k−4x+4)/k⌋ ≥ 5−x for k ≥ 4.
  - The existence of a class L_1 with exactly one u′-edge (deg u′ ≤ 2k−2).
  - Lemma 11's applicability (either deg_B(x_0) < 3, or deg_A = deg_B = 3 odd with η = 4 and all deg_B(y) = 2).
  - The degree bookkeeping giving (2) at s+1, and the final application of Cor 6 (r′ = 2n−2t+r ≤ 2n).

---

## 3. Detailed notes on the audited papers

### 3.1 Thm 4 ([OSC] p.3–4; [SEP] Thm 2.4, Lemmas 2.5–2.6, Prop 3.1, §4)

- **Endpoint prescription.**
  - g counts consecutive pairs in S joined by H-edges, all distinct, so g ≤ e(H[S]) ≤ ½Σ_S d_H.
  - Since r_v ≥ d_H(v)+1 on S, |S| + g ≤ Σ_S r_v ≤ L+1.
  - Connectors: universal vertices outside S number ≥ 2L+1−|S ∩ U| ≥ L ≥ g.
  - The final greedy extension to L edges is fine.
- **m > k case.**
  - Lovász: q paths + c cycles with q+c ≤ ⌊s/2⌋, and q+2c ≤ s−1 except when c = s/2 and s is even.
  - Two of the s/2 cycles meet, since disjoint cycles would need ≥ 3s/2 > s vertices. Removing one edge from each at a shared vertex w gives a path a–w–b (a ≠ b by edge-disjointness).
  - Greedy colouring: a forbidden colour uses ≥ 2 of the ≤ 2(s−2) coloured incidences at x, y, so ≤ s−2 < k colours are forbidden.
  - Hilton condition per class: 2s−2k−1 ≤ 1 ≤ |class|.
  - Removing the assigned subpath from a Hamilton cycle on 2k+1 > s vertices leaves the complementary arc.
  - Lower bound: a vertex off the support has degree 2k.
- **Residual family.** For m = k the same counting as in [SEP] Lemma 4.4 shows that the cases not covered by Liu–Chen are exactly k ≥ 6, |V(H)| ≥ k+2, H not a linear forest (then m = k ≥ (k+4)/2 automatically). The paper never says this. The reader-note line "JM is needed only for k ≥ 6, ⌈(k+4)/2⌉ ≤ m ≤ k−1 …" is correct only for the m < k upper bound.

### 3.2 Thm 11 / Cor 12 ([OSC] pp.11–14)

All steps are checked in table rows T11.1–T11.11. Additional remarks:
- **First appearance of each branch.** The *general* (wedge) branch first occurs at n = 11 (g = 1 with L = 3, or g = 2 with L = 2 and H = K_3 on S). The *larger-core* branch (r ≥ k+2) needs (3k−5)/2 ≥ k+2, i.e. **k ≥ 9 (n ≥ 19)**. So no small-n computation tests the donor machinery; its correctness rests on the arithmetic I re-derived and reproduced (T11.9, T11.10).
- **Dependence on JM Theorem 8.** It is genuine and goes beyond the main theorem. Every general case with h > 0 (an exterior matching of isolated-edge marks) uses JM Theorem 8's *proof*. Only the special cases (g = 0, L = 1, (g, L) = (1, 2)) and h = 0 (Hilton) avoid it.
- **Reader-note overstatement.** "Computer- and Lean-checked for k < 130" refers only to the donor-count table, not to the theorem. The anc/ Python files and anc/lean/DonorTable.lean are not in the repository; I reproduced the table independently (§4).

### 3.3 §15 ([OSC] pp.43–51)

- **Thm 43.** Removing the bridge splits at most one path. Equality needs both pieces nonempty, both sides optimal, and x an end. ✔
- **Cor 44.**
  - Y_h has j(2h+1) − 1 + C(j,2) − e(X) = Θ_X(N) missing edges, about jN. To reach a given X one needs C ≳ |V(X)|.
  - What is proved is therefore: *Gallai ⇔ for every C > 0 there is N_0(C) such that every connected graph of even order N ≥ N_0 with ≤ CN missing edges satisfies p ≤ N/2.*
  - The paper's sentence before Cor 44 ("…for every fixed C, it would give …") supports this reading.
  - The single-C reading in the reader notes ("for any fixed C > 0"; "the linear-deletion dense regime is as hard as Gallai itself") is **not established**.
  - The even-|X| step (three copies plus a degree-3 hub, ≥ 3p(X)−1 paths, odd order 6k+1) is ✔.
- **Prop 45.** (7): the paths internal to B_i number ≥ p(B_i)−1+η. (8): leaf-only rows cover ≤ 2 leaves at one base. ✔ Applying it with a one-vertex core (the hub, X⁺ = K_{1,3}, p = 2) is legitimate.
- **Thm 46.** 3 ⇒ 1 and the rooted inequality: hub host, integrality (3k+1 resp. 3k+2; floor 3k resp. 3k+2). 1 ⇒ 2: one leaf gives p(X)+η ≤ ⌈(n−1)/2⌉. 2 ⇒ 1: trimming. The two-ends statement: two leaves, k+1 = p(X) forces every row to survive. 1 ⇒ 3: even–even sides via rooted ends at z; odd–odd sides via the tight/non-tight case split; joins are simple since A ∩ B = {z}. ✔
- **Prop 47.** Even branch: partition with ≤ h paths ending at z, obtained by trimming the induction with one leaf. Odd branch: ≤ h paths, or h+1 paths with two ends at z. Proxies cost +h−1 paths per +2h−2 vertices; odd branches cost +h per +2h vertices. Leafless roots: even D, or odd D via the two-odd-sides argument. ✔
- **Thm 48.**
  - The reduction to single leaves on subsets plus double leaves at one vertex (pairs of leaves cost one path and raise the floor by one) is ✔.
  - Amplification: m+1 copies on K_{m+1}. H − v stays connected because each site carries exactly one joining edge and K_{m+1} minus an edge is connected for m ≥ 2. (m+1)p(D_S) ≤ p(H) + C(m+1,2), and integrality gives the floor. ✔
  - Blocks of order 2 with leaves are trees, for which p = o/2 ≤ ⌊n/2⌋. ✔
- **Thm 50.**
  - p_i(D, x) = p(D + i leaves) when d_D(x) ≥ 2: one split restores the ends, using parity when one end remains.
  - Bridge identity ✔. Diamond identity: the diamond with two ends at each terminal needs exactly 3 paths, e.g. xaby, xb, ya.
  - Cut analysis: j ≤ min(b, e) and extra splits ≤ 2 − j, so ≤ 4 extra paths in total. ✔
  - Sufficiency: Lovász for all-odd even cores; a degree-2 vertex added to odd cores; the even-root/odd-order case uses the two-site amplification, which needs only the ordinary bound on 2-connected graphs. ✔

### 3.4 e(G) notation ([OSC] §§12–14)

There is no global definition. Uses found:

| Location | Meaning used | Literal-reading consequence |
|---|---|---|
| Thm 1 proof p.24: "e(G) ≥ k(n−1)−(n−2)" | \|E(G)\| | — |
| Thm 20 statement p.25: "e(G) ≤ Cn and δ(G) ≥ K" | missing | vacuous: avg deg ≤ 2C < K ≤ δ |
| Thm 20 proof p.25: "Σ a_v = s(n−1) − e(G) ≥ 0 gives s ≥ n/2 − Cn/(n−1)" | \|E(G)\| (identity) combined with missing ≤ Cn | correct, but the symbol switches meaning within one proof |
| Cor 23 p.27 | missing | vacuous |
| Prop 26 p.30: "e(G) ≤ Cn"; "X = {v : d_G(v) > .01n}" | missing; d_G should be the missing degree | as typed, L ⊆ X is false |
| Cor 27 p.31: "at most Cn missing edges … also at odd order n = 2k+1 when e(G) ≥ k" | missing | **false**: K_{2k+1} (L′ = ∅, e(G) = k(2k+1) ≥ k) has p = k+1 |
| Thm 28 p.31: "e(G) ≤ Cn … whenever e(G) ≥ k" | missing (both) | different, unproved sparse statement |
| Thm 31 p.34; proof "e(G′) ≤ (C+1)n", "X = {v : d_{G′}(v) > .01n}" | missing; d_{G′} typo | — |
| Cor 33 p.35 ("e(G) < 3n − 4827"), Cor 34 p.36 | missing | — |
| Thm 38 proof p.41: "t(n−1) − e(G) ≤ n²/6000 + n" | \|E(G)\| | correct |
| Cor 39 proof p.39: ".045np ≤ 2e(G) ≤ n²/3000" | missing | — |
| Cor 40 p.42: "e(G) ≤ n²/6000, L = ∅" | missing | vacuous |
| Prop 41 / Thm 42 p.43; Thm 43 p.44 ("−e(X)") | \|E(G)\| | — |

**Conclusion.** No proof uses the wrong meaning mathematically. **Fix:** write ē(G) := C(n,2) − e(G) (or e(Ḡ)) wherever "missing" is meant, in Thms 20, 28, 31, Cors 23, 27, 33, 34, 40 and Prop 26. Keep e(G) = |E(G)| in the proofs of Thms 1, 20, 38, 42 and 43. Correct d_G(v), d_{G′}(v) > .01n to the missing degree in Prop 26 and Thm 31.

---

## 4. Computations

All code is in `research/audit/A4-scripts/` (copied from the scratchpad). It uses `tools/pathnum.py` (CP-SAT exact cover over all simple paths) and a CP-SAT `AddCircuit` model for Hamilton decompositions with prescribed colour classes (`circ.py`). Every reported partition and decomposition is re-verified edge by edge.

| Check | Scope | Result |
|---|---|---|
| Thm 4: p(K_n − H) = k+1, m < k | n = 5, 7: all H up to iso (2 + 4 classes) | all = k+1 |
| Thm 4: every plant Q of length L completes by k Hamilton paths | n = 5, 7: **every labelled Q** for every H (30 + 9; 420 + 95 + 19 + 19) | all succeed |
| Thm 11: exact vector d_H + 2·1_S with k+1 paths | n = 5, 7: **every labelled S** (10 + 10; 35 + 35 + 21 + 21) | all succeed |
| Cor 12: end-pair multigraph = H + C | n = 5, 7: every S and **every** Hamilton cycle C on S | all succeed (stronger than claimed) |
| Thm 11 construction replay (special cases), certificate-checked | n = 9: all 43 (H, S) iso types (35 g = 0, 7 L = 1, 1 (g, L) = (1, 2)) | all OK |
| Thm 11 construction replay, g ≥ 1, certificate-checked | n = 11: 25 (H, S) types (21 L = 1, 3 (g, L) = (1, 2), 1 general wedge case H = K_3 = S); n = 13: 82 types (66 L = 1, 12 (1, 2), 4 general: 2 with g = 1, 2 with g = 2) | **all OK**; the general branch first exists at n = 11 |
| Wu / JM main theorem, all k-edge X up to iso | n = 5, 7, 9 (path-cycle exact cover); n = 11, 13, 15 (circuit model): 2, 5, 11, 26, 68, 177 classes | **all rainbow-decomposable** |
| Thm 4 residual case H = K_{1,3} ⊔ 2K_2, n = 13 | all 8 plant orbits under Aut(H) | all give 7-path partitions |
| Thm 4, m = k: p = k, all paths Hamiltonian | n = 5, 7 all H; n = 9, 11, 13, 15 via Wu above | ✔ (see §4.1) |
| Thm 4, m > k, support ≤ k+1 | k = 2, 3, 4, 5: 1, 4, 20, 123 classes (H ⊆ K_{k+1}, m > k) | all give k-path partitions (path number by pathnum for k ≤ 3; replayed Hilton construction for k ≤ 5) |
| Sharpness of the total L+1 (matching + L+2 universal vertices) | k = 2, 3, all m < k | L+1 prescriptions feasible in every case. L+2 prescriptions: solver-proved INFEASIBLE for k = 2. For k = 3 the solver returned UNKNOWN within 120 s; infeasibility follows from the parity count. |
| Thm 11 finite donor table | 1 ≤ k < 130 | **17,507 triples, least margin 2 at (19, 2, 26)**: exactly as claimed; 0 failures also for k < 400 |
| Thm 11 estimates k ≥ 130 | every inequality, 130 ≤ k < 1500 (9,075,959 triples) | 0 failures |
| Thm 43 | all connected X with 2–5 vertices, every root, h = 1, 2 (254 instances) | identity holds |
| Prop 45 hub formula 3(p+η)−1 | connected X with ≤ 4 vertices, every root (32) | holds |
| Thm 50: p_i = p(D + i leaves); bridge/diamond identities | 2-connected cores with ≤ 6 vertices (one root per degree / neighbour-degree class) | see §4.1 |

### 4.1 Consequences and limits

- **m = k for n ≤ 15.** Wu's statement at order n gives p(K_n − H) ≤ k for every k-edge H, and counting gives ≥ k.
- **Thm 4 for m < k at n ≤ 15.** For any plant Q, the k-edge set H ∪ E(Q) is covered by the Wu check, so the m < k upper bound holds at n ≤ 15 *independently of the JM proof*. This includes the whole JM-residual family at k = 6, 7.
- **Endpoint claims at n ≤ 13.** These follow from the certificate-checked Thm 11 replays (all (H, S) types at n ≤ 9; all g ≥ 1 types at n = 11, 13; the g = 0 case is Thm 4 with Q a Hamilton path of G[S]).
- **Limit.** These computations cannot test the larger-core donor branch of Thm 11 (it needs n ≥ 19), nor JM's Claim 12 as such. The CP-SAT circuit model finds the decompositions directly and does not run JM's construction.
- **Logs.** All logs are in `research/audit/A4-scripts/*.log`.

---

## 5. Required fixes

1. **[OSC] p.9 and p.12: citation.**
   - Replace "[14, Theorem 3.8 and its proof]" and "See also Theorem 3.8 … in the preprint" with "arXiv:2403.17290v1, Theorem 8 (§3) and its proof". Confirm the label in the published version, Discrete Math. 349(1) (2026) 114676.
   - State explicitly that the proof of Theorem 8 needs only: a decomposition of K_r into n linear forests with sizes ≥ 2r−2n−1 (seeded colours) and ≥ 2r−2n (others); a rainbow representative set in the seeded colours; and r ≤ 2t−1. The representatives may leave isolated vertices.
2. **JM dependency flag.** Add a remark that the proof of JM Theorem 8 (Claim 12) has the gap described in §2.4, together with the computational confirmation for k ≤ 7. Better still, supply an independent proof of the extension step actually used, e.g. by the auxiliary-colour detachment of [OSC] Lemma 15.
3. **[OSC] p.4, "Earlier rainbow theorems", and [SEP] §4.** Add the m = k residual family (k ≥ 6, |V(H)| ≥ k+2, H not a linear forest). Note that Thm 11 / Cor 12 / Cor 13 and Thms 3, 9, 16 use JM Theorem 8's proof, not only the main theorem.
4. **[OSC] Cor 44, p.45.** Reword as: "Gallai's conjecture is equivalent to the assertion that for every C > 0 there is N_0(C) such that every connected graph of even order N ≥ N_0(C) with at most CN missing edges has p ≤ N/2." The hosts need C ≳ |V(X)|.
5. **e(G) notation (§3.4).**
   - Introduce ē(G) = C(n,2) − e(G) and use it in Thms 20, 28, 31, Cors 23, 27, 33, 34, 40 and Prop 26.
   - In particular Cor 27 must read "…at odd order n = 2k+1 when ē(G) ≥ k". As printed, it is false for K_{2k+1}.
   - Fix X = {v : n−1−d_G(v) > .01n} in Prop 26 (p.30) and Thm 31 (p.34).
6. **Reproducibility.** The anc/rainbow and anc/lean supplements, and the [SEP] package, are missing from the collection. The donor table is now independently reproduced (`A4-scripts/donor.py`), but the claimed Lean proof is unverifiable here.

## 6. Corrections to `notes/reader-semi-clique-even-degrees.md`

1. "JM is needed only for k ≥ 6, ⌈(k+4)/2⌉ ≤ m ≤ k−1 …". This is true only for the m < k upper bound of Thm 4.
   - The m = k part needs JM for k ≥ 6, |V(H)| ≥ k+2, H not a linear forest.
   - Thm 11 / Cor 12 need JM Theorem 8's *proof* in the general case.
2. "Thm 11 / Cor 12 … Computer- and Lean-checked for k < 130". Only the donor-count inequality table is checked, not the theorem. The Lean artefact is not in the repository; the table is reproduced in `A4-scripts/donor.py`.
3. "A Cor 44 … for any fixed C > 0". This is wrong: the result needs all C (§3.3).
4. Flag 2 (Theorem 3.8 vs 8) is **confirmed**. Add: JM Claim 12 has a proof gap (§2.4), and the published-version numbering could not be checked.
5. Flag 1 (e(G)) is **refined**. No proof is wrong, but Cor 27 is literally false, three statements are literally vacuous, and there are two d_G typos (§3.4).
6. "The reader found no logical errors in the proofs traced (Thms 4, 16, 42–52 …)". For Thms 4, 43–50 I concur, except for the Cor 44 quantifier and the JM-inherited status.
