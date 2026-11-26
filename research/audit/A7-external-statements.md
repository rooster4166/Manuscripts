# A7 — Exact statements of external results cited in paraphrase

Date: 2026-11-26. Scope: the eight items in the A7 brief. Manuscript text is grepped from the extracted raw text (`scratchpad/raw/*.txt`). Line numbers below refer to those files.

**Sources and access.**
- Downloaded and read in full: arXiv 1911.04546 (Botler–Sambinelli), arXiv 2611.21673v1 (Zhang–Liu–Hong, K5-minor-free), EJC 31(4) P4.49 (Pfenninger), arXiv 1401.4159v2 (Csaba–Kühn–Lo–Osthus–Treglown), Filomat 37:17 (2023) 5829–5834 (Xie), arXiv 2510.12806 (Chu–Wang, *Path decompositions of Eulerian graphs*), arXiv 1609.06257 (Bonamy–Perrett), arXiv 1803.06768 (Botler–Jiménez–Sambinelli), and Shaik's two Zenodo PDFs (records 23141299 v1.1 and 22754815 v0.8).
- Abstract only: Fan–Hou–Zhou, from the journal's own pages (jorsc.shu.edu.cn, EN and CN); Lu–Yi, from the ECNU research portal; Chu–Fan–Liu, from Semantic Scholar.
- Not accessible: ScienceDirect (all Elsevier full texts: Fan 2005, Chu–Fan–Liu, Chu–Fan–Zhou, Lu–Yi, Zhang–Liu–Hong 2024) returned HTTP 403. Springer returned a bot challenge. The JORSC PDF link returned HTML. Where a primary text was blocked I used verbatim restatements in refereed citing papers and say so each time.
- Local copies: `/tmp/claude-0/-home-user-Manuscripts/a40c9215-4484-5bc3-a3e1-2bba3a808810/scratchpad/dl/`.

Verdict scale: **MATCHES** / **STRONGER-THAN-NEEDED** / **WEAKER-THAN-NEEDED (gap)** / **NOT FOUND**. "NOT FOUND" means I could not obtain the primary statement or any reliable verbatim restatement.

---

## Summary table

| # | Result as cited | Verdict | Basis |
|---|---|---|---|
| 1a | Fan [JCTB 2005] Lemma 3.4 (single edge "addible towards x") | **MATCHES** | Verbatim restatements: Botler–Sambinelli Lemma 6 + Definition 1, which they say "precisely matches" Fan's Def. 3.2; Botler–Jiménez–Sambinelli Lemma 3; Shaik input 4 |
| 1b | Fan Lemma 3.6 (half-star, ⌈s/2⌉, prescribed edge) | **MATCHES** | Botler–Sambinelli Lemma 7; Xie Lemma 2.3 (both labelled "Lemma 3.6 of Fan") |
| 1c | Fan Lemma 3.3 (grouped donors, sum of donor ends > zero-end neighbours) | **NOT FOUND** (primary blocked) | No accessible source quotes Lemma 3.3. The paraphrase is consistent with 3.4 and A2 tested it empirically, but there is no verbatim check |
| 1d | Fan Lemma 3.5 | **NOT FOUND** | Never quoted in accessible sources; cited only inside the range "Lemmas 3.3–3.6" |
| 1e | Fan main theorem: each block of E-subgraph triangle-free with Δ ≤ 3 ⇒ p ≤ ⌊n/2⌋ | **MATCHES** | Botler–Sambinelli Thm 2(c); Bonamy–Perrett Thm 1.2 (both state ⌊n/2⌋) |
| 2a | FHZ main theorem: no triangle pair, each block of G_e has Δ ≤ 3 ⇒ Gallai (⌈n/2⌉) | **MATCHES** (ceiling only) | Journal abstract, verbatim |
| 2b | FHZ "at most one E-vertex of degree > 3" | **MATCHES** as FHZ *Theorem 5*, which is a different statement in the same paper (ceiling with D(x) ≥ 2) | Xie Thm 1.3 = "Theorem 5, [4]"; Shaik input 2 |
| 3a | Botler–Sambinelli Thm 13 (Δ(EV) ≤ 3 ⇒ Gallai or SET) | **MATCHES** (every use checked) | arXiv v1, verbatim |
| 3b | BS main theorem (family 𝒢), Conjecture 4 | **MATCHES** (one background sentence understates Thm 15; harmless) | arXiv v1 + JGT abstract |
| 4 | Shaik Thm 1.1 / Cor 1.2 | Statements **MATCHE** the preprint. **Unrefereed.** BS replaces it at the Thm 144 "r ∈ T" step only. Cor 106 (one-exception case) and the "two universal vertices" remark stay **conditional** | Zenodo PDF v1.1 |
| 5a | Chu–Fan–Liu main theorem (Δ = 6, degree-6 vertices independent ⇒ ⌊n/2⌋ unless K3, K5, K5⁻) | **MATCHES** | Abstract |
| 5b | Chu–Fan–Liu "two cycles, ≤ 5 common vertices, exceptions K5 and subdivided K5" | **NOT FOUND**, attribution doubtful | The only Chu–Fan–Liu lemma quoted by a coauthor (Chu–Wang, Lemma 2.1 citing [CFL, Lemma 2.1]) is a *path–cycle* lemma |
| 5c | Chu–Fan–Zhou Lemma 2.4 (short path + cycles) | **NOT FOUND**. Paraphrases conflict (≤ 6 vs ≤ 7). The sum = 7 uses are a potential **gap** | Chu–Wang Lemma 2.2 verifies only the ≤ 6 form |
| 5d | Chu–Fan–Zhou Lemmas 2.1, 2.5; Theorems 1.3, 1.4, 1.7 | **NOT FOUND** (primary blocked) | Bibliographic data only |
| 6a | "Lemmas 2.5–2.6" path–cycle (≤ 5, exception K5 − ab with pendant paths) | **MATCHES**, but these are lemmas of Zhang–Liu–Hong **DM 347 (2024) 114057**, not of arXiv 2611.21673 | Restated in arXiv 2611.21673 §2.2; manuscripts cite the right paper |
| 6b | Zhang–Liu–Hong arXiv 2611.21673 Thm 1.1 and Lemma 2.2 | **MATCHES**. Unrefereed (v1, 14 Nov 2026) | arXiv v1 |
| 7 | Lu–Yi: tw ≤ 4 ⇒ floor except K3, K5 − e, K5 | **MATCHES** (bound symbol not rendered in public abstract; the exception list forces ⌊n/2⌋) | ECNU portal abstract |
| 8a | Pfenninger [EJC 31(4) P4.49] Thms 3, 4; Lemmas 5, 6, 8 | **MATCHES** (minor quantifier caveat at Lemma 6) | EJC PDF |
| 8b | CKLOT memoir Thm 1.3.5 | **MATCHES** | arXiv 1401.4159v2 |

No item was found to be WEAKER-THAN-NEEDED on the evidence I could obtain. The one live risk is 5c (see §5).

---

## 1. G. Fan, "Path decompositions and Gallai's conjecture", JCTB 93 (2005) 117–125

**Primary access.** ScienceDirect returned 403 to both curl and WebFetch, and the Elsevier text API needs a key. Each statement below is taken from refereed papers that quote Fan's lemmas by number.

### 1a. Lemma 3.4 (single-edge addition)

Botler–Sambinelli (arXiv 1911.04546, §2) write: "The next two lemmas are results of Fan [9, Lemmas 3.4 and 3.6]."

> **Lemma 6.** Let G be a graph and uv ∈ E(G). Suppose that D′ is a path decomposition of G′ = G \ uv. If D′(v) > |{w ∈ N_{G′}(u) : D′(w) = 0}|, then uv is addible towards u with respect to D′.

Here "addible towards u" is their Definition 1, which they say "precisely matches the definition of addible at given by Fan [9, Definition 3.2]":

> (i) |D| = |D′|; (ii) D(u) = D′(u) + |A| and D(x_i) = D′(x_i) − 1, for 1 ≤ i ≤ k; (iii) D(v) = D′(v) for each v ∈ V(G) \ {u, x_1, …, x_k}.

Botler–Jiménez–Sambinelli (arXiv 1803.06768, Lemma 3, "a result of Fan [6, Lemma 3.4]") give the same hypothesis, with N_{G′}(u). Shaik (input 4) gives it too, with the transfer "+1 at u, −1 at v, and zero elsewhere".

**Manuscript usage.** "If b(y) > #(zero-end neighbours of x), then the missing edge xy can be added towards x." Examples: marked-reduction 412, 819, 6684, 7768, 8102; separating-pairs 1937, 2065, 2415; root-endpoint-costs 1725, 2459; odd-semi-clique-boundary 2757. The receiver is x, the donor is y, and the count is over x's current neighbours, i.e. N_{G′}(x). The "other counts unchanged" clause is Definition 1(iii).

**Verdict: MATCHES.** This settles A2-F4 for Lemma 3.4.

### 1b. Lemma 3.6 (half-star)

> **BS Lemma 7.** Let u be a vertex in a graph G and let G′ = G \ {ux_1, …, ux_h}, where x_i ∈ N_G(u). Suppose that D′ is a path decomposition of G′ with D′(v) ≥ 1 for every v ∈ N_G(u). Then, for any x ∈ {x_1, …, x_h}, there is A ⊆ {ux_1, …, ux_h} such that ux ∈ A and |A| ≥ ⌈h/2⌉; and A is addible towards u with respect to D′.

Xie (Filomat 2023) states the same as "Lemma 2.3 (Lemma 3.6, [3])". The hypothesis is again over N_G(w), the neighbours in the full graph, missing leaves included.

**Usage.** Marked-reduction 820–822: "with s > 0 missing spokes at v, if every neighbor of v in the final graph has an end, then at least ⌈s/2⌉ spokes can be added toward v simultaneously, including any one specified missing spoke."

**Verdict: MATCHES.**

### 1c. Lemma 3.3 (grouped / several donors)

**Usage.**
- Marked-reduction 6685: "For a choice of several donors at one recipient, his Lemma 3.3 gives an admissible donor when their total count exceeds the number of such neighbors."
- Marked-reduction 7424: "Fan's multiple-edge addition lemma [14, Lemma 3.3], on the current graph with just the offered edges adjoined, restores at least one of them…"
- Also marked-reduction 892, 910, 6712, 6763, 8596; even-degrees 1468; four-exterior-neighbors 1228, 2011; root-endpoint-costs 3663 ("Lemmas 3.3–3.4").

**Evidence.** None of BS, BJS, Xie, Bonamy–Perrett, Shaik or Chu–Wang quotes Lemma 3.3, and the primary is blocked. The paraphrase is the natural generalisation of 3.4: with a single donor it reduces exactly to 3.4. Fan's numbering (3.3 general, 3.4 the special case) makes it plausible, and A2 §6 C1 found no counterexample on random graphs.

**Verdict: NOT FOUND.** The exact hypothesis is unconfirmed, in particular whether the zero-end count runs over N_{G′}(u) for G′ = current graph, as the manuscripts assume.

**Impact.** All grouped-donor steps of marked-reduction (book/contact certificates; Thm 113/114 neighbourhoods; Thms 144–145 via 8596) and the certificate banks of four-exterior-neighbors rely on it.

**Recommendation.** Quote it from the JCTB PDF (Elsevier open archive) or add a half-page proof. Fan's argument for 3.4 charges each failed attempt to a distinct zero-end neighbour, so it should extend.

### 1d. Lemma 3.5

Cited only inside "[14, Definitions 3.1–3.2 and Lemmas 3.3–3.6]" (marked-reduction 825). No individual use was found. **NOT FOUND, not load-bearing.** Also unverified: "Fan's endpoint counts refer to nontrivial paths in Definition 3.1."

### 1e. Main theorem

> **BS Theorem 2(c)** (Lovász; Pyber; Fan 2005). Let G be a connected graph on n vertices. … (c) If each block of EV(G) is triangle-free and has maximum degree at most 3, then pn(G) ≤ ⌊n/2⌋.

> **Bonamy–Perrett Theorem 1.2 [Fan].** If G is a graph on n vertices such that each block of G_E is a triangle free graph of maximum degree at most 3, then G can be decomposed into ⌊n/2⌋ paths.

**Usage.** Historical-context 37 and block-degree reader notes cite it as "Fan [10] when each of its blocks is triangle-free with maximum degree at most three" (floor). **Verdict: MATCHES.**

---

## 2. Fan, Hou, Zhou, "Gallai's Conjecture on Path Decompositions", J. Oper. Res. Soc. China 11(3) (2023) 439–449, doi:10.1007/s40305-022-00435-3

**Primary access.** I read the abstract verbatim on the journal's own pages: jorsc.shu.edu.cn/EN/abstract/article/2194-668X/19867 and /CN/Y2023/V11/I3/439. The full text was not reachable: the PDF link returned HTML and Springer returned a bot challenge.

**Main theorem (abstract, verbatim).**
> Gallai's conjecture asserts that every connected graph on n vertices can be decomposed into at most (n+1)/2 paths. The E-subgraph of a graph G, denoted by G_e, is the subgraph induced by the vertices of even degree in G. A triangle pair is a graph consisting of two triangles with exactly one vertex in common. In this paper, it is proved that Gallai's conjecture is true for graphs G in which G_e contains no triangle pair and each block of G_e has maximum degree at most 3.

**Second statement in the same paper (Theorem 5).** This is quoted by Xie (refereed) and by Shaik.
> **Xie, Theorem 1.3 (Theorem 5, [4]).** Let G be a connected graph on n vertices and F be the E-subgraph of G. If there is a vertex x ∈ V(F) such that d_F(v) ≤ 3 for every vertex v ∈ V(F)\{x}, then G has a path-decomposition D such that |D| ≤ (n+1)/2 and D(x) ≥ 2.

Xie also quotes FHZ Lemma 5 (Xie Lemma 2.4), an outward multi-edge transfer.

**Resolving the two paraphrases.**
- (b) "no triangle pair, and each block of G_e has max degree ≤ 3" is the **main theorem** (abstract).
- (a) "at most one E-vertex of degree > 3" is FHZ **Theorem 5**. It has the stronger conclusion D(x) ≥ 2, and Shaik notes that x must have positive degree.
- Both are statements of the paper, so neither paraphrase is false. Xie's abstract sentence ("If the E-subgraph of G has at most one vertex with degree greater than 3, Fan, Hou and Zhou verified…") describes Theorem 5.
- **Both conclusions are the ceiling ⌈n/2⌉ = ⌊(n+1)/2⌋, not the floor.**

**The block reading (A2-F3).** The abstract says "each block of G_e has maximum degree at most 3". The degree bound is taken inside each block, not over G_e as a whole. So the Section 2.1 doubling step of marked-reduction (lines 344–356) is covered: a joining bridge between two even supports is a K2 block and creates no triangle.

**Manuscript usage.**
- Marked-reduction 344–361 (Section 2.1 criterion): the hypothesis is quoted exactly as in (b). It is applied to the even-order doubled host, where ceiling = floor, and to G with A = ∅ as the ordinary ceiling, with the odd tight case handled separately. MATCHES.
- Marked-reduction 6638–6645 (Thm 114 neighbourhood paragraph): "both rooted assertions follow whenever K contains no two triangles meeting in exactly one vertex and each block of K has maximum degree at most three." Contrapositive: a failure needs K to contain a bowtie or a block with Δ ≥ 4. MATCHES. The test hosts have even order, so the ceiling suffices.
- Marked-reduction 4314, 7824 (Thm 136, t = 1), 8180, and odd-semi-clique-boundary 2718: all are ceiling applications on even-order connected hosts. MATCHES. In 7824 and 8180 only four vertices are even, so BS Theorem 13 would also do.
- Marked-reduction 7321–7563 and 7702 use the "marked consequence" from Section 2.1, which inherits the above.

**Verdict.** (b): **MATCHES**. Precision of "maximum degree ≤ 3" (per block) is confirmed, so A2-F3 is resolved in the manuscript's favour. (a): **MATCHES** as Theorem 5 (secondary quotation only). The manuscripts never need a floor from FHZ.

---

## 3. F. Botler, M. Sambinelli, "Towards Gallai's path decomposition conjecture", J. Graph Theory 97 (2021) 161–184 (arXiv:1911.04546v1, the only arXiv version)

The JGT abstract (via Semantic Scholar) is identical in substance to arXiv v1, relabelling (i), (ii) as (a), (b). Xie and Shaik both cite the JGT version as "Theorem 13" and "Corollary 14", so the numbering is the same in print.

**Main theorem.**
> Let 𝒢 denote the family of graphs for which (i) each block has maximum degree at most 3; and (ii) each component either has maximum degree at most 3 or has at most one block that contains triangles.
> **Theorem 3.** If G is a connected graph on n vertices such that EV(G) is a subgraph of a graph in 𝒢, then pn(G) ≤ ⌈n/2⌉.
> **Theorem 5 (= Theorem 15).** If G is a connected graph such that EV(G) is a subgraph of a graph in 𝒢, then G is a Gallai graph or G ∈ 𝒮.

**Theorem 13.**
> If G is a connected simple graph on n vertices such that ∆(EV(G)) ≤ 3, then either G is a Gallai graph or G is a SET graph.

SET graph: "EV(G) is a triangle and every odd vertex of G has at least two even neighbors". SET graphs have odd order. Corollary 14 gives the ceiling for Δ(EV) ≤ 3.

**Conjecture 4.**
> If G is a connected simple graph on n vertices, then either pn(G) ≤ ⌊n/2⌋, or pn(G) = ⌈n/2⌉ and G is an odd semi-clique.

Odd semi-cliques are graphs with |E(G)| > ⌊n/2⌋(n − 1). For n = 2k + 1 this is K_{2k+1} minus at most k − 1 edges, the manuscripts' definition.

**Usage checked.**
- **six-even-root-shapes 68.** "If B[T] is subcubic, BS Theorem 13 gives the floor in W; the exception would require exactly three even sites." |T| = 5, so W is connected and not SET. MATCHES.
- **marked-reduction 7484.** "floor bound when the even sites induce a subcubic graph, except possibly when they induce a triangle and each odd vertex has at least two neighbors on it." Applied componentwise with SET excluded. MATCHES.
- **marked-reduction 7658.** Componentwise; the component with ≥ 5 even sites is not SET. MATCHES.
- **marked-reduction 7832.** Exactly the SET case is left. MATCHES.
- **marked-reduction 8163.** A leaf has no even neighbour, so the graph is not SET. MATCHES.
- **four-exterior-neighbors 1080–1084, 1206.** The SET definition is quoted exactly. MATCHES.
- **odd-semi-clique-boundary 49 and historical-context 80.** Conjecture 4 is quoted exactly. MATCHES.
- **historical-context 37–38.** "Botler and Sambinelli allowing one block to contain triangles" understates Theorem 15 (per component, and closed under subgraphs). This is background only and harmless. Suggest "whose E-subgraph is a subgraph of a graph in 𝒢".

**Verdict: MATCHES.** Theorem 13 is used only in forms it supports.

---

## 4. I. A. Shaik, "Gallai's conjecture with two exceptional even vertices"

**Records.**
- Zenodo v1.0.0 (doi 10.5281/zenodo.23134427) and v1.1.0 (record 23141299), both dated 4 Oct 2026.
- SSRN abstract_id 7559778.
- Listed on the author's site as "Read on Hexagon · v1 2026-10-16", matching the manuscripts' "hexagon:2610.00286v1, 16 October 2026".
- Lean formalization at github.com/shaikidris/gallai-two-exception, registered as PALOMAR-2026-10-04-000006.

**Exact statements (v1.1 PDF).**
> **Theorem 1.1 (prescribed endpoint).** Let G be a connected finite simple graph, and let h, x be distinct even vertices with d_G(h) > 0. Suppose d_F(v) ≤ 3 for v ∈ V(F) \ {h, x}. Then G has a path decomposition D satisfying |D| ≤ k(G) = ⌈|V(G)|/2⌉, D(h) ≥ 2.
> **Corollary 1.2.** Let G be a connected finite simple graph. If at most two vertices of EV(G) have degree greater than three in that subgraph, then p(G) ≤ k(G).

Proposition 3.1 and Corollary 3.2 give one partition with D(h), D(x) ≥ 2 within ⌊n/2⌋ + 1 paths, which equals Gallai's bound at odd order. The proof uses BS Thm 13 / Cor 14, FHZ Thm 5, Xie Thm 1.4, and Fan Lemmas 3.4 and 3.6.

**Companion paper: "Gallai's Path Decomposition Conjecture for Graphs with Small Bowtie Boundaries".** Zenodo 22754815, draft v0.8, 11 Sept 2026; SSRN 7453518. It proves the ceiling with D(y) ≥ 2 when the E-subgraph has a *whole-bowtie component* with at most four external neighbours and every other even vertex except y has E-degree ≤ 3. It is computer-assisted. It states: "The unrestricted even-order two-nonadjacent-exception problem remains open." Three weeks later, the October paper claims that open problem. The bowtie paper is not cited by the manuscripts.

**Refereed?** No.
- Zenodo, SSRN and Hexagon are preprint venues. Press reports describe Hexagon as a new (Aug 2026) archive for LLM-assisted mathematics.
- The author is an independent researcher. The README says: "OpenAI Codex and Claude assisted the mathematical development … Registry verification and automated editorial review do not constitute a literature-priority finding or human peer review."
- The Lean formalization is claimed but not something I could check (GitHub API access was denied for this session; the README was read raw).
- Treat as unrefereed.

**Manuscript usage.**
- **(U1) marked-reduction 395 and odd-semi-clique-boundary 2778: Thm 1.1.** "Allows x, y to be nonadjacent. The partition may depend on the chosen vertex." MATCHES.
- **(U2) marked-reduction 6196, 6201: Cor 106.** The doubled host has E-subgraph two copies of the original, so a single high vertex becomes two; Cor 1.2 gives the ceiling. MATCHES the statement.
- **(U3) marked-reduction 6643: Thm 114 paragraph.** "Shaik's ordinary bound [25, Cor 1.2] also applies if K has at most one vertex of degree > 3, since doubling gives at most two. At d_J(z) = 6 a failure therefore requires two universal vertices." MATCHES the statement.
- **(U4) marked-reduction 8237: Thm 144, case r ∈ T.** "The connected B has four even sites and r is odd. Shaik's ordinary bound gives k paths." MATCHES the statement.
- **(U5) six-even-root-shapes 72–77 and two-exterior-contacts 50–54.** Doubling arguments, flagged there as optional. MATCHES.

**Can Botler–Sambinelli replace it?**
- **(U4) Yes.** B has exactly four even vertices, so Δ(EV(B)) ≤ 3 trivially. B is connected of even order 2k. A SET graph has exactly three even vertices and odd order, so B is not SET. BS Thm 13 gives p(B) ≤ k, and r is odd, so an end at r exists to take ℓ. Replace "[25, Corollary 1.2]" by "[7, Theorem 13]" at line 8237. This confirms the conjecture in connections.md.
- **(U2) Only partly.**
  - Zero high-degree vertices: BS Thm 13 applies to L directly. L has a leaf whose support is odd, so a leaf is an odd vertex with fewer than two even neighbours and L is not SET. That gives p(L) ≤ ⌊|L|/2⌋ without doubling.
  - One high-degree vertex: if |V(L)| is even, FHZ Thm 5 on L gives the ceiling = floor directly. If |V(L)| is odd, the doubling produces two nonadjacent exceptions in different components of the E-subgraph. Neither BS (blocks must have Δ ≤ 3), nor FHZ (one exception), nor Xie (adjacent exceptions) covers that. **Cor 106 stays conditional on Shaik in the one-exception, odd-order case.**
- **Thm 144 as a whole.** Its next sentence ("By Corollary 106 with mark r, at least two vertices of K have degree four in K") also inherits Cor 106. So it stays conditional on [25] unless Cor 106 is restricted or reproved.
- **(U3) No.** The two universal vertices conclusion needs two exceptions in the doubled host, so keep it marked conditional (A2-F2). FHZ alone gives one universal vertex.

**Verdict.**
- Statement fidelity: **MATCHES**.
- Status: **unrefereed, AI-assisted preprint**. Its own September companion called the key case open.
- BS replaces the r ∈ T step of Theorem 144 and the zero-exception case of Cor 106. Cor 106 (one-exception, odd-order case), the remainder of Thm 144, and the Thm 114 "two universal vertices" remark remain conditional.

---

## 5. Chu–Fan–Liu (DM 344 (2021) 112212) and Chu–Fan–Zhou (DM 349(2) (2026) 114725)

**Primary access.** ScienceDirect returned 403. Neither paper has an arXiv version (arXiv API search). I found partial evidence in Chu–Wang, arXiv 2510.12806 ("Path decompositions of Eulerian graphs", Discrete Math. 2025). Y. Chu is a coauthor of both cited papers, and Chu–Wang quote Chu–Fan–Liu verbatim.

### 5a. Chu–Fan–Liu main theorem (abstract)
> In this paper, we prove that a connected graph with maximum degree 6, in which the vertices of degree 6 form an independent set, can be decomposed into ⌊n/2⌋ paths, unless it is K3, K5 and K5⁻.

Usage (reader notes; block-degree introduction): "Δ ≤ 6 with independent degree-6 vertices, floor". **MATCHES.**

### 5b. The "two cycles with ≤ 5 common vertices" lemma
Chu–Wang quote:
> **Lemma 2.1 (Lemma 2.1 in [7] = Chu–Fan–Liu).** Let G be a connected graph consisting of edge-disjoint path P and cycle C. If |V(P) ∩ V(C)| ≤ 5, then G can be decomposed into two paths, unless G is isomorphic to the exceptional graph.

The figure shows |V(C)| = 5 and |V(P) ∩ V(C)| = 5, with P's tails dashed: K5 − e with pendant paths.

So the Chu–Fan–Liu lemma that can be confirmed is the **path–cycle** lemma, the same content the manuscripts attribute to Zhang–Liu–Hong (§6a).

**Usage.**
- block-degree 153–154: "For two cycles the five-intersection statement is due to Chu, Fan and Liu [8]" (exceptions K5 and K5 with one edge subdivided).
- marked-reduction 1005–1007: "the two-cycle result of Chu, Fan and Liu [9]".

**Verdict: NOT FOUND.** No source confirms that Chu–Fan–Liu contain a two-cycle five-intersection lemma. The one of their lemmas quoted by a coauthor is path–cycle, so the attribution may be wrong. Zhang–Liu–Hong's restatement covers two cycles only up to **four** common vertices.

**Impact: low.** A5 proved the five-vertex two-cycle statement by exhaustive enumeration (A5-F1, F2; the subdivided path must have length ≥ 2). Fix: cite the internal finite lemma instead of [8]/[9], or quote [CFL] after obtaining it.

### 5c. Chu–Fan–Zhou Lemma 2.4 ("short path and cycles")
The manuscripts give **two different hypotheses**:
- separating-pairs 3934–3936: route ≤ 4 vertices, meets each cycle, "the sum of its order and the number of cycles is at most six".
- marked-reduction 2181, 4749, 9752: "|V(P)| ≤ 4 and |V(P)| + q ≤ 7". Even-degrees 156–157 likewise uses |V(P)| + (m − 1) = m + 1 ≤ 7.

The only verifiable published statement is:
> **Chu–Wang Lemma 2.2.** Let 𝒞 be a set of edge-disjoint cycles and P be a path such that E(P) ∩ E(𝒞) = ∅ and V(P) ∩ V(C) ≠ ∅ for every cycle C ∈ 𝒞. If |V(P)| + |𝒞| ≤ 6 and |V(P)| ≤ 4, then E(P) ∪ E(𝒞) can be decomposed into |𝒞| + 1 paths.

Chu–Wang add: "the condition |V(P)| ≤ 4 is necessary because of the exceptional graph". They prove the 6-cycles-through-a-vertex case (|V(P)| = 1, sum 7) separately as their Lemma 2.3, with a page of case analysis. That suggests the ≤ 7 form was not available to them in Oct 2025, though it does not prove that Chu–Fan–Zhou state only ≤ 6.

**Uses at sum = 7**, outside Chu–Wang 2.2:
- marked-reduction 2755: a 4-vertex planted path plus 3 cycles.
- marked-reduction 2789: a spoke plus q ≤ 5 cycles.
- marked-reduction 2181, 4749, 9752: the general "≤ 7" form.
- even-degrees 157: m = 6, a spoke plus 5 cycles.

**Verdict: NOT FOUND, with a potential WEAKER-THAN-NEEDED gap.** If Chu–Fan–Zhou Lemma 2.4 is the ≤ 6 statement, the sum = 7 applications are unsupported. Separating-pairs needs only ≤ 6, which Chu–Wang Lemma 2.2 covers; A3-G2 also offers the internal Lemma 13.6. Fix: obtain the Chu–Fan–Zhou PDF, or prove the sum = 7 cases internally. They are finite configurations near the common vertex, suitable for the A5-style segment-model enumeration.

### 5d. Chu–Fan–Zhou Lemmas 2.1, 2.5 and Theorems 1.3, 1.4, 1.7
Paraphrases in the manuscripts:
- **Lemma 2.1 (star lemma)**, even-degrees 177–180 and marked-reduction 3479, 7490: delete s edges at u; if a p-path partition has an end at every neighbour of u, H has a mixed partition into p members with at most ⌊s/2⌋ cycles, all through u. This is consistent with Fan Lemma 3.6 iterated.
- **Lemma 2.5**, marked-reduction 3185: j ≤ 7 cycles through a vertex give j + 1 paths. Chu–Wang Lemma 2.3 confirms only j ≤ 6. Marked-reduction proves its own Theorem 38 for j ≤ 7 with two ends, so this citation is not load-bearing.
- **Theorem 1.3**: E-subgraph a clique K_r, r ≤ 15 ⇒ p ≤ ⌊n/2⌋ + 1. Comparison only: ordered-even-clique 37, six-clique-prescribed-ends 27, historical-context 39.
- **Theorem 1.4** ("star criterion"): odd-semi-clique-boundary 107.
- **Theorem 1.7**: p ≤ (4n + 6)/7 for odd semi-cliques. Comparison only: odd-semi-clique-boundary 106, historical-context 113.

**Verdict: NOT FOUND** (bibliographic data confirmed by DBLP/Semantic Scholar: Y. Chu, G. Fan, C. Zhou, DM 349(2) (2026) 114725). Theorems 1.3, 1.4 and 1.7 are cited only for comparison. Lemma 2.1 is load-bearing in marked-reduction (Thm 113 area, 7490) and even-degrees. Its paraphrase follows from Fan 3.4/3.6 and is low risk, but it should be quoted.

---

## 6. Zhang, Liu, Hong

### 6a. "Lemmas 2.5–2.6" (path–cycle with ≤ 5 common vertices)
**Attribution check.** In arXiv 2611.21673v1, Lemma 2.5 says "a smallest counterexample with a vertex of degree ≤ 2 has all others of degree ≥ 5", and Lemma 2.6 is a K5-minor-free edge-addition lemma. Neither is the path–cycle lemma. The path–cycle lemmas are Lemmas 2.5–2.6 of **Zhang–Liu–Hong, "Gallai's conjecture for 3-degenerated graphs", DM 347 (2024) 114057**. arXiv 2611.21673 restates them (§2.2, citing its ref. [3]):

> We use two results of Zhang, Liu, and Hong [3, Lemmas 2.5–2.6]. Let a path and a cycle be edge-disjoint and meet in at least one and at most five vertices. Their union has a decomposition into two paths, with one exception: K5 − e with a possibly empty pendant path at each end of the missing edge. Also, two edge-disjoint cycles whose intersection has between one and four vertices can be decomposed into two paths.

The manuscripts cite the right paper: block-degree [17] and marked-reduction [23] are DM 347 (2024) 114057.

**Usage.**
- block-degree 150–153: "For a path and a cycle the only possible exception is K5 − ab with an optional pendant path at each of a, b."
- marked-reduction 1005–1007, 7963–7965.

Both match the restatement and Chu–Fan–Liu Lemma 2.1 (§5b). **MATCHES**, via same-author restatement; the 2024 primary was blocked. A5-F1 reached the same conclusion.

### 6b. arXiv 2611.21673v1 main theorem (14 Nov 2026, unrefereed)
> **Theorem 1.1.** Let G be a connected K5-minor-free graph. If G is not isomorphic to K3 or K5 − e, then pn(G) ≤ ⌊|V(G)|/2⌋.

Corollary 7.1 gives the ceiling for all of them and the floor exactly outside {K3, K5 − e}.

**Usage.**
- marked-reduction 433: "A connected K5-minor-free graph has the floor bound with the exceptions K3 and K5 − e". MATCHES.
- marked-reduction 49–51: "[24, Lemma 2.2]" is the cut-vertex lemma, with the explicit two-path lists at z for K3, K5 − e. MATCHES.
- odd-semi-clique-boundary 2464: "split-and-join argument … [23, Lemma 2.2]". MATCHES.
- block-degree 2035. MATCHES.
- The 3-degenerate main theorem (cited as [16, Thm 1.3] / [22, Thm 1.3]: floor for connected 3-degenerate graphs except K3, K5 − e) agrees with arXiv 2611.21673's description ("The same exceptions occur … for connected 3-degenerate graphs [3]"). The theorem number is unverified.

**Verdict: MATCHES.** Note that 2611.21673 is a 12-day-old unrefereed preprint.

---

## 7. C. Lu, N. Yi, "The problem of path decomposition for graphs with treewidth at most 4", DM 347(6) (2024) 113957

**Abstract** (ECNU research portal, pure.ecnu.edu.cn):
> In this paper, we show that if G is a graph with treewidth at most 4, then G can be decomposed into at most [Formula presented] paths or G is isomorphic to K3, to K5−e, or to K5.

The portal renders it as "K 5 − (K 5 −e)". The bound symbol is not rendered in any accessible copy. The exception list fixes it as ⌊n/2⌋: all three graphs meet ⌈n/2⌉, and they are exactly the odd semi-cliques of treewidth ≤ 4. Connectivity is implicit in context.

**Usage.**
- marked-reduction 4285: "floor bound on connected graphs of treewidth at most four apart from…"
- even-degrees 999: "the floor bound in that class apart from K3, K5 − e, K5".
- block-degree 65.

**Verdict: MATCHES** (the bound is inferred, not read). Leaf augmentation preserving treewidth ≤ 4 (marked-reduction 4287) is elementary.

---

## 8. Pfenninger and Csaba–Kühn–Lo–Osthus–Treglown

**Which Pfenninger paper.** separating-pairs [9] (and dense-exact-counts [9], marked-reduction [22], odd-semi-clique-boundary [19]) is V. Pfenninger, "A note on Hamilton decompositions of even-regular multigraphs", Electron. J. Combin. 31(4) (2024) #P4.49, doi 10.37236/12637, arXiv 2312.09873. It is not a bipartite-tournament paper.

**Exact statements** (EJC PDF; the "≪" symbols were dropped by text extraction and are restored here):
> **Theorem 3.** Let 1/n ≪ ν ≪ τ ≪ 1/r, α ≤ 1. Let D be an n-vertex multidigraph with multiplicity at most r such that (a) D is s-regular for some s ≥ αn; (b) the underlying simple digraph of D is a robust (ν, τ)-outexpander. Then D has a Hamilton decomposition.
> **Theorem 4.** Same hierarchy. Let G be an n-vertex multigraph with multiplicity at most r such that (a) G is s-regular for some s ∈ 2ℕ with s ≥ αn; (b) the underlying simple graph of G is a robust (ν, τ)-expander. Then G has a Hamilton decomposition.
> **Lemma 5** ([Kühn–Osthus JCTB 2014, Lemma 3.1]). 1/n ≪ η ≪ ν, τ, α < 1. If G is a robust (ν, τ)-expander on n vertices with δ(G) ≥ αn, then one can orient G so that D is a robust (ν/4, τ)-outexpander and d^±_D(x) = (1 ± η) d_G(x)/2.
> **Lemma 6** ([KO, Lemma 3.4]). 1/n ≪ ν′ ≪ ξ ≪ ν ≤ τ ≪ α < 1. Let D be a robust (ν, τ)-outexpander on n vertices with δ⁰(D) ≥ αn. Then D contains a ξn-factor which is still a robust (ν′, τ)-outexpander.
> **Lemma 8** ([KO, Lemma 3.8]). 1/n ≪ ν ≪ τ ≪ ε < 1. A graph G on n vertices with δ(G) ≥ (1/2 + ε)n is a robust (ν, τ)-expander.

**Usage.**
- **Theorem 4** (separating-pairs 7264–7266; dense-exact-counts 385). The augmented multigraph is D-regular with D even and linear, multiplicity ≤ r, and robust expansion after halving parameters. "Choose τ first according to that theorem, then ν." This is consistent with ν ≪ τ ≪ 1/r, α. **MATCHES.**
- **Theorem 3** (7744–7746). D/2-regular in both directions, multiplicity ≤ r, underlying simple digraph a robust outexpander (supplied by the retained robust factor F of Lemma 14.11). **MATCHES.**
- **Lemma 8** (7723). A Dirac graph with fixed margin; choose τ ≪ min(ε, 1/r, α). **MATCHES.**
- **Lemmas 5, 6** (7706–7710). "Take a robust directed t0-factor with t0/N sufficiently small in terms of c." Lemma 6 also requires ξ = t0/N ≪ ν, the robustness of the oriented digraph, and τ ≪ α; the latter is stated ("take τ sufficiently small in terms of a"). The two smallness requirements are compatible. **MATCHES**, with a wording fix: "t0/N sufficiently small in terms of c and of the robust parameter".

**CKLOT memoir Theorem 1.3.5** (arXiv 1401.4159v2; Mem. AMS 244 (2016) no. 1154):
> There are ε_ex > 0 and n0 ∈ ℕ such that the following holds. Let n ≥ n0 and suppose that D ≥ (1/2 − ε_ex)n is even. Suppose that G is a D-regular graph on n vertices which is ε_ex-bipartite. Then G has a Hamilton decomposition.

Here "G is ε-bipartite if there exists A ⊆ V(G) with |A| = ⌊n/2⌋ such that e(A), e(V(G) \ A) ≤ εn²."

**Usage.**
- separating-pairs 8547–8550 paraphrase: "partition into two sets of sizes strictly between N/2 − 1 and N/2 + 1 and each set spans at most εN² edges". This is equivalent to |A| = ⌊N/2⌋ after swapping sides when N is odd.
- 8798 applies it to a simple D-regular balanced bipartite graph on 2m + 2 sites, with D = 2m − 2P even and D = m − o(m) ≥ (1/2 − ε_ex)(2m + 2). Both parts span no edges.
- 8954 uses the same application.

**MATCHES.**

---

## Actions

1. **Theorem 144 (marked-reduction 8237).** Replace [25, Cor 1.2] by [7, Theorem 13]: four even sites, connected, even order, not SET.
2. **Corollary 106.** Split it. The zero-exception case follows from BS Thm 13 (L has a leaf, so it is not SET). The one-exception case at even |L| follows from FHZ Thm 5. Keep the one-exception odd-order case, and everything downstream that uses it (Thm 144's "two vertices of degree four in K"; the Thm 114 "two universal vertices" remark), labelled conditional on [25].
3. **Chu–Fan–Zhou Lemma 2.4.** Obtain the primary and check whether the hypothesis is |V(P)| + q ≤ 7 or ≤ 6. If it is ≤ 6, reprove the sum = 7 configurations (marked-reduction 2181, 2755, 2789, 4749, 9752; even-degrees 157) or cite Chu–Wang Lemma 2.2/2.3 where they suffice. Make the separating-pairs and marked-reduction paraphrases agree.
4. **Chu–Fan–Liu.** Re-attribute the two-cycle five-intersection lemma (block-degree 153–154, marked-reduction 1006) to the internal finite lemma (A5). The only confirmed Chu–Fan–Liu lemma is path–cycle.
5. **Fan Lemma 3.3.** Quote it verbatim from the JCTB PDF (Elsevier open archive), or add a short proof of the grouped version. Lemmas 3.4 and 3.6 are confirmed.
6. **FHZ.** No change needed. The hypothesis is per block and the conclusion is the ceiling. Optionally cite Theorem 5 by number where "one exceptional vertex" is meant.
