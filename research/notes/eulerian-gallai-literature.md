# Gallai's conjecture for Eulerian graphs: verified literature survey (focus: rooted / prescribed-end statements)

**Date:** 2026-11-27.

**How this was produced.** A Claude Code agent session. arXiv e-print sources (TeX) and PDFs were downloaded and read directly from arxiv.org. Metadata came from the arXiv API, Crossref and the Semantic Scholar API. One journal abstract page (JORSC) and one open-access journal PDF (Filomat) were also fetched. Every statement quoted below was copied from a source I opened. When a statement is quoted from a *restatement* in another paper, the section says which paper. LaTeX macros are expanded lightly: `\pn` is written as `pn`, `\floor{x}` as `⌊x⌋`, `\ceil{x}` as `⌈x⌉`. Nothing here is stated from memory.

**Access levels.**

| Level | Sources |
|---|---|
| Full text (arXiv TeX source and/or PDF read) | Chu–Wang 2510.12806 (entire paper); Bonamy–Perrett 1609.06257v1 (entire paper); Botler–Jiménez 1510.02526 (intro, Sec. 2 set-up, key lemmas); Botler–Jiménez–Sambinelli 1803.06768 (Secs. 1–3, main theorem); Botler–Sambinelli 1911.04546 (Secs. 1–2, main theorems, absorbing lemmas, conclusion); Botler–Sambinelli–Coelho–Lee 1706.04334 (Secs. 1–2, main theorems of Secs. 3–4, conclusion); Blanché–Bonamy–Bonichon 2110.08870v2 (main file, start of Sec. 3; the reduction-rule chapters were only skimmed); Zhang–Liu–Hong 2611.21673 (Sec. 1, Sec. 2 lemmas, final proof, corollary); Anto–Basavaraju 2211.07159v3 (Sec. 1, main theorem); Kindermann–Schlipf–Schulz 1706.04130 (Sec. 2 types and Theorem 1); Jiménez–Wakabayashi 1402.3741v3 (Sec. 1, main results); M. Xie, Filomat 37:17 (2023) (open-access PDF: abstract, Secs. 1–2, start of the proof) |
| Abstract only | Chu–Fan–Liu, Discrete Math. 344 (2021) 112212 (abstract via the Semantic Scholar API); Fan–Hou–Zhou, J. Oper. Res. Soc. China 11 (2023) 439–449 (abstract from the journal page jorsc.shu.edu.cn) |
| Not accessible; restatements used | Fan, JCTB 93 (2005): ScienceDirect returned HTTP 403, including on the Elsevier open-archive PDF link `.../pii/S0095895604000875/pdf`. Pyber, JCTB 66 (1996): HTTP 403 on `.../pii/S009589569690012X/pdf`. Favaron–Kouider (1988): no online text. Lovász (1968): book chapter. Harding–McGuinness, JGT 75 (2014): closed access. Dean–Kouider, Discrete Math. 213 (2000): ScienceDirect. Zhang–Liu–Hong, Discrete Math. 347 (2024) 114057 (3-degenerate graphs): not on arXiv. Chu–Fan–Zhou, Discrete Math. 345 (2022) 112866: not on arXiv. Geng–Fang–Li (2015): not located. Liu–Zhang–Hong, K_{3,3}-minor-free: cited only as "Unpublished manuscript, June 2026" |

**Notation.** p(G) or pn(G) is the path number. 𝒟(v) is the number of paths of 𝒟 that end at v. 𝒟(v) ≡ d(v) (mod 2), as observed in BJS, BS and Chu–Wang. A **Gallai graph** is a graph with pn(G) ≤ ⌊n/2⌋. BSCL take n to be the number of non-isolated vertices. BJS, BS and ZLH 2026 take n = |V(G)|.

---

## 0. A derived observation used in every "relevance to RE" paragraph (not from the literature)

This short argument was worked out for this note. It is not quoted from any paper, although ZLH 2026 uses the same leaf device inside the proof of its Lemma 2.2 (§12a below).

**Leaf lemma.** Let B be a connected graph with every degree even, |V(B)| = n even, and r ∈ V(B). Let B^r = B + rℓ, where ℓ is a new vertex. Then:

> B has a path decomposition into at most n/2 paths in which r is an end of at least two paths **if and only if** p(B^r) ≤ n/2 = ⌊|V(B^r)|/2⌋.

*Proof.* (⇒) Take such a decomposition. Extend one path that ends at r by the edge rℓ. The result is still a path, because ℓ is new.

(⇐) Let 𝒟 be a decomposition of B^r with |𝒟| ≤ n/2. Exactly one path P ∈ 𝒟 contains rℓ, and ℓ is an end of P.
- If P = ℓr, then 𝒟 − P decomposes B into at most n/2 − 1 paths. If no path ends at r, then r is an inner vertex of some path Q, since d_B(r) ≥ 2. Split Q at r. This gives at most n/2 paths, and two of them end at r.
- Otherwise P − ℓ is a path of B ending at r, and the decomposition still has at most n/2 paths. Then 𝒟'(r) ≥ 1, and 𝒟'(r) ≡ d_B(r) ≡ 0 (mod 2), so 𝒟'(r) ≥ 2. ∎

**Consequences.**
1. Suppose a theorem says "every connected graph in 𝒞 is a Gallai graph, except for listed graphs of minimum degree ≥ 2". If 𝒞 is closed under adding a pendant edge, the theorem implies RE for every 2-connected Eulerian B ∈ 𝒞 of even order and **every** root r. The usual exceptions K3, K5−e and K5 have minimum degree ≥ 2, while B^r has a leaf.
2. A theorem with only the **ceiling** bound ⌈n'/2⌉ gives nothing through this route, because |V(B^r)| = n+1 is odd and ⌈(n+1)/2⌉ = n/2 + 1.
3. An odd semi-clique on 2k+1 vertices has minimum degree ≥ 2k − (k−1) = k+1 ≥ 2, so B^r is never an odd semi-clique. Hence a positive answer to Bonamy–Perrett's Question 1.1 (§3) implies RE in full. So do BSCL's Conjecture 3 (§7) and BS's Conjecture 4 (§6), which state the same thing.

---

## 1. Y. Chu, Y. Wang, "Path decompositions of Eulerian graphs"

- **Citation:** Yanan Chu, Yan Wang. arXiv:2510.12806 (v1, 4 Oct 2025). Published as *Discrete Math.* **349** (2026), Article 114830, DOI 10.1016/j.disc.2025.114830; Crossref lists issue date Feb. 2026, and Semantic Scholar/DBLP list the year as 2025.
- **Access:** full text (complete TeX source read).

**Main theorems (verbatim):**
> **Theorem 1.3.** Let $G$ be an Eulerian graph on $n \ge 4$ vertices. If the distance between any two triangles in $G$ is at least $3$, then $p(G)\leq \frac{3n}{5}$.

> A *triangle removal set* of a graph $G$ is a set of vertices $R=\{v_1,\ldots,v_k\}$ such that $G-R$ is triangle-free and $R$ has the following properties: for any distinct $i, j\in [k]$, (i) $d_G(v_i)\geq 4$; (ii) all the vertices in $V(G)\backslash R$ have even degree in $G$; and (iii) ($N_G(v_i)\cup \{v_i\})\cap (N_G(v_j)\cup \{v_j\})=\emptyset$.
>
> **Theorem 1.4.** Let $G$ be a graph on $n$ vertices with no component isomorphic to a triangle. If $G$ has a triangle removal set, then $p(G)\leq \frac{3n}{5}$.

**Lemmas (verbatim).** None of them prescribes path ends at given vertices. The paper defines 𝒫(v), "the number of paths in 𝒫 with v as an end vertex", but no statement uses it as a hypothesis or conclusion.
> **Lemma 2.1** (Lemma 2.1 in [CFL]). Let $G$ be a connected graph consisting of edge-disjoint path $P$ and cycle $C$. If $|V(P)\cap V(C)|\leq 5$, then $G$ can be decomposed into two paths, unless $G$ is isomorphic to the exceptional graph (see Figure 1).

> **Lemma 2.2.** Let $\mathcal{C}$ be a set of edge-disjoint cycles and $P$ be a path such that $E(P)\cap E(C)=\emptyset$ and $V(P)\cap V(C)\neq \emptyset$ for every cycle $C\in \mathcal{C}$. If $|V(P)|+ |\mathcal{C}|\leq 6$ and $|V(P)|\leq 4$, then $E(P)\cup E(\mathcal{C})$ can be decomposed into $|\mathcal{C}|+1$ paths.

> **Lemma 2.3.** Let $\mathcal{C}$ be a set of edge-disjoint cycles such that all elements in $\mathcal{C}$ contain a common vertex. If $|\mathcal{C}|\leq 6$, then $E(\mathcal{C})$ can be decomposed into $|\mathcal{C}|+1$ paths.

> **Lemma 2.4.** Let $G$ be a connected graph consisting of $q$ edge-disjoint cycles such that all cycles contain a common vertex. (1) If $q\equiv 0 \pmod 6$, then $G$ can be decomposed into $\frac{7q}{6}$ paths; (2) If $q\equiv \delta \pmod 6$ for $\delta=1,2,3,4,5$, then $G$ can be decomposed into $\frac{7q}{6}+1-\frac{\delta}{6}$ paths.

> **Theorem 2.5** (Theorem 3.1 in [CFZ]). If $G$ is a triangle-free graph, then $p(G)\leq \frac{\alpha(G)}{2}+\lfloor \frac{3\beta(G)}{5}\rfloor$. *(α = number of odd vertices, β = number of non-isolated even vertices; [CFZ] = Chu, Fan, Zhou, Discrete Math. 345 (2022) 112866.)*

**The paper's own survey of the Eulerian case (verbatim, Sec. 1):**
> "Favaron and Kouider [FK] verified Conjecture 1.1 for all Eulerian graphs with maximum degree at most $4$. For $2k$-regular graphs ($k\geq 3$), Botler and Jiménez [BJ] showed that if $G$ has girth at least $2k-2$ and a pair of disjoint perfect matchings, then $p(G)\leq \frac{n}{2}$."

Here Conjecture 1.1 is "If $G$ is a connected graph on n vertices, then $p(G)\leq \frac{n+1}{2}$." The same section also surveys Pyber, Fan, Botler–Sambinelli, Harding–McGuinness (girth g ≥ 4 gives (g+1)n/(2g)) and Chu–Fan–Zhou (triangle-free graphs give 3n/5).

**Proof method (as read).** The proof deletes the triangle removal set R, decomposes G − R with Theorem 2.5, re-attaches each v_i to the paths that end at its neighbours, and splits the cycles this creates with Lemma 2.4.

**Relevance to RE: no.** The bound 3n/5 exceeds n/2, and nothing in the paper is rooted. The paper does not prove Gallai's bound for any new Eulerian class.

---

## 2. O. Favaron, M. Kouider, "Path partitions and cycle partitions of Eulerian graphs of maximum degree 4"

- **Citation:** *Studia Sci. Math. Hungar.* **23** (1988) 237–244. This bibliographic data appears identically in Chu–Wang, Bonamy–Perrett and Xie.
- **Access:** not accessible. Restatements only:
  - Chu–Wang: "Favaron and Kouider verified Conjecture 1.1 for all Eulerian graphs with maximum degree at most $4$."
  - Bonamy–Perrett: "In 1988, Favaron and Koudier [eulerian] proved that the conjecture holds for graphs where the degree of every vertex is either $2$ or $4$."
  - Botler–Jiménez: "it is known that the conjecture holds on 4-regular graphs [FKfav]."
  - BJS: "Favaron and Kouider [FavaronKouider88] verified Conjecture 1 for Eulerian graphs with maximum degree at most \(4\)". Here Conjecture 1 is pn ≤ ⌊(n+1)/2⌋.
  - BBB: "graphs in which each vertex has degree $2$ or $4$ [favaron]".
  - Jiménez–Wakabayashi: "the broadest subclass of Eulerian graphs, excluding the complete graphs on an odd number of vertices, for which the conjecture is known to be true is the one composed of graphs of maximum degree 4 (see [FKfav])."
  - Xie: "verified by Favaron and Kouider [5] for Eulerian graphs with degrees 2 and 4".
- **Bound:** every restatement says "Gallai's conjecture", i.e. ⌈n/2⌉. None says whether FK proved ⌊n/2⌋. The ⌊n/2⌋ version for connected Eulerian graphs with Δ ≤ 4 (except K3 and K5) follows from BSCL Theorem 4.1, which I read (§7).
- **Relevance to RE: unknown.** No restatement mentions any end condition.

---

## 3. M. Bonamy, T. Perrett, "Gallai's path decomposition conjecture for graphs of small maximum degree"

- **Citation:** arXiv:1609.06257 (v1 only, 20 Sep 2016). *Discrete Math.* **342** (2019) 1293–1299, DOI 10.1016/j.disc.2019.01.005.
- **Access:** full text of arXiv v1. The journal version was not seen.

**Main theorem (verbatim):**
> **Theorem 1.3.** Let $G$ be a connected graph on $n$ vertices. If $\Delta(G) \leq 5$, then $G$ admits a path decomposition into $\lceil \frac{n}{2} \rceil$ paths.

> **Question 1.1.** Does every connected graph $G$ that is not an odd semi-clique admit a path decomposition into $\lfloor \frac{|V(G)|}{2} \rfloor$ paths? *("odd semi-clique": obtained from a clique on 2k+1 vertices by deleting at most k−1 edges.)*

**Is there a stronger induction hypothesis? No, not in arXiv v1.** The proof takes a vertex-minimal counterexample to "has a *good* decomposition", where good means at most ⌈|V(G)|/2⌉ paths (Section 2). Lemma 3.1 shows that the configurations C1–C5 are reducible. Lemma 3.2 then says:
> **Lemma 3.2.** Let $G$ be a connected graph such that $G \not\in \{K_3, K_5\}$. If $\Delta(G) \leq 5$ and $G$ does not contain configurations $C_1, \dots, C_5$, then the graph $G_E$ is a forest.

Pyber's theorem finishes the proof. End conditions appear only implicitly inside claim proofs; for example, "since $u$ has odd degree in $G_1$, there is a path $P_u \in \mathcal{D}_1$ ending at $u$" (cut-edge claim). No lemma prescribes ends.

**Restatements in this paper (verbatim):**
- Pyber: "If $G$ is a graph on $n$ vertices such that $G_E$ is a forest, then $G$ can be decomposed into $\lfloor n/2 \rfloor$ paths."
- Fan: "If $G$ is a graph on $n$ vertices such that each block of $G_E$ is a triangle free graph of maximum degree at most $3$, then $G$ can be decomposed into $\lfloor n/2 \rfloor$ paths."
- Lovász: "every graph on $n$ vertices has a decomposition $\mathcal{D}$ consisting of paths and cycles, and such that $|\mathcal{D}|=\lfloor n/2 \rfloor$."

**Relevance to RE: no.** The theorem gives p(B) ≤ n/2 for Eulerian B of even order with Δ ≤ 4, but nothing rooted. The ceiling bound is useless for B^r (§0, consequence 2). Question 1.1, if answered positively, implies RE in full (§0, consequence 3).

---

## 4. F. Botler, A. Jiménez, "On path decompositions of 2k-regular graphs"

- **Citation:** arXiv:1510.02526 (v1, Oct 2015). *Discrete Math.* **340** (2017) 1405–1411; the bibliographic data is as cited in Chu–Wang and Xie, and I did not retrieve the DOI. Extended abstract: *Electron. Notes Discrete Math.* **50** (2015) 163–168, DOI 10.1016/j.endm.2015.07.028.
- **Access:** full text of arXiv v1 (Secs. 1–3 statements, Lemma 2.6).

**Main statements (verbatim; 𝒢_k = 2k-regular graphs of girth ≥ 2k−2 with a pair of disjoint perfect matchings, k ≥ 3):**
> **Theorem 1.** Every $G\in \mathcal{G}_k$ on $n$ vertices has a decomposition into $n/2$ paths.

> **Theorem 2.** For every $G\in \mathcal{G}_k$ there exists a decomposition $\mathcal{D}$ into paths of lengths in $\{2k-1,2k,2k+1\}$. Further, in $\mathcal{D}$, the number of paths of length $2k-1$ is equal to the number of paths of length $2k+1$.

**End-type condition (verbatim).** The condition concerns lengths of the paths ending at each vertex, not which vertices are ends:
> **Definition 2.1.** … We say that $\mathcal{D}$ is *$k$-balanced* (or simply *balanced*) at $v$ if the number of paths of $\mathcal{D}$ of length at most $2k$ with end vertex $v$ is at least the number of paths of $\mathcal{D}$ of length at least $2k+1$ with end vertex $v$. Further, we say that $\mathcal{D}$ is a *$k$-balanced decomposition* of $G$ if it is $k$-balanced at every vertex of $G$ and the number of paths of length $2k-1$ is equal to the number of paths of length $2k+1$.

**Proof start (verbatim, Sec. 2.2).** "Since each vertex of $G'$ is the end vertex of exactly one path in $\mathcal{P}$, it follows that the edge set of $G$ admits a partition $\mathcal{W}$ into $(M,\mathcal{P})$-alternating closed trails." Here G' = G − M is decomposed into paths of length 2k−1 by Botler et al.

**Relevance to RE: no.** The class consists of even-order Eulerian graphs, so it lies inside RE's domain when 2-connected. But no statement says which vertices are ends: the decomposition has n ends in total, each vertex has an even number of them, and r is not controlled. B^r is not regular, so the leaf lemma does not apply.

---

## 5. F. Botler, A. Jiménez, M. Sambinelli, "Gallai's path decomposition conjecture for triangle-free planar graphs"

- **Citation:** arXiv:1803.06768 (v1, Mar 2018). *Discrete Math.* **342** (2019) 1403–1414, DOI 10.1016/j.disc.2019.01.020.
- **Access:** full text of arXiv v1 (Secs. 1–3, main theorem).

**Main theorem (verbatim):**
> **Theorem 6.** Every triangle-free planar graph is a Gallai graph. *(Gallai graph: pn(G) ≤ ⌊n/2⌋; no connectivity assumption appears in the statement.)*

**End-condition lemma.** This is Fan's addible lemma, restated **verbatim** as "a result of Fan [Lemma 3.4]":
> **Lemma 3.** Let $u$ be a vertex of a graph $G$ and $G' = G - uv$, where $v \in N_G(u)$. Let $\mathcal{D}'$ be a path decomposition of $G'$. If $\mathcal{D}'(v) > |\{w\in N_{G'}(u)\colon \mathcal{D}'(w) = 0\}|$, then there is a path decomposition $\mathcal{D}$ of $G$ such that $|\mathcal{D}| = |\mathcal{D}'|$.

**Related definitions (verbatim, Definition 1).** A feasible reducing scheme (H, 𝒜, ℒ) requires, among other things: "(iii) $\mathcal{A}$ is a set of vertex-disjoint paths such that each $P \in\mathcal{A}$ has an end vertex $v$ with odd degree in $G_\mathcal{H}$ …". This is an end condition used for concatenation, not a rooted conclusion.

**Relevance to RE: yes, on 2-connected Eulerian triangle-free planar graphs of even order, every root.** B^r is triangle-free and planar, so Theorem 6 gives p(B^r) ≤ n/2, and §0 applies. BBB (§9) subsumes this.

---

## 6. F. Botler, M. Sambinelli, "Towards Gallai's path decomposition conjecture"

- **Citation:** arXiv:1911.04546 (v1, Nov 2019). *J. Graph Theory* **97** (2021) 161–184, DOI 10.1002/jgt.22647.
- **Access:** full text of arXiv v1.

**Main theorems (verbatim).** 𝒢 is "the family of graphs for which (i) each block has maximum degree at most 3; and (ii) each component either has maximum degree at most 3 or has at most one block that contains triangles".
> **Theorem 5.** If $G$ is a connected graph such that $EV(G)$ is a subgraph of a graph in $\mathcal{G}$, then $G$ is a Gallai graph or $G\in\mathcal{S}$.

> **Theorem 13.** If $G$ is a connected simple graph on $n$ vertices such that $\Delta(EV(G))\leq 3$, then either $G$ is a Gallai graph or $G$ is a SET graph.

> SET graph: "$EV(G)$ is a triangle and every odd vertex of $G$ has at least two even neighbors."

**Seminal results as restated here (verbatim, Theorem 2).** This is the best available restatement of Lovász, Pyber and Fan:
> **Theorem 2** (Lovász, 1968; Pyber, 1996; Fan, 2005). Let $G$ be a connected graph on $n$ vertices. (a) If $EV(G)$ contains at most one vertex, then $pn(G)\leq\lfloor n/2\rfloor$; (b) If $EV(G)$ is a forest, then $pn(G)\leq\lfloor n/2\rfloor$; (c) If each block of $EV(G)$ is triangle-free and has maximum degree at most $3$, then $pn(G)\leq\lfloor n/2\rfloor$.

> **Conjecture 4.** If $G$ is a connected simple graph on $n$ vertices, then either $pn(G) \leq \lfloor n/2\rfloor$, or $pn(G) = \lceil n / 2\rceil$ and $G$ is an odd semi-clique.

**End-condition / rooted lemmas (verbatim).**
> **Definition 1.** Let $u$ be a vertex in a graph $G$ and let $B$ be a set of edges incident to $u$. Let $G' = G \setminus B$, let $\mathcal{D}'$ be a path decomposition of $G'$, and let $A = \{ux_i \colon 1 \leq i \leq k\}$ be a subset of $B$. We say that $A$ is *addible towards $u$* (resp. *addible outwards $u$*) *with respect to $\mathcal{D}'$* if $G' + A$ admits a path decomposition $\mathcal{D}$ such that (i) $|\mathcal{D}|=|\mathcal{D}'|$; (ii) $\mathcal{D}(u) = \mathcal{D}'(u) + |A|$ and $\mathcal{D}(x_i) = \mathcal{D}'(x_i) -1$, for $1\leq i\leq k$ (resp. $\mathcal{D}(u) = \mathcal{D}'(u) - |A|$ and $\mathcal{D}(x_i) = \mathcal{D}'(x_i) +1$, for $1\leq i\leq k$); (iii) $\mathcal{D}(v) = \mathcal{D}'(v)$ for each $v \in V(G)\setminus \{u,x_1,\ldots,x_k\}$.
>
> "the present definition of *addible towards* precisely matches the definition of *addible at* given by Fan [Fan05]" ([Fan05, Definition 3.2]).

> **Lemma 6** ([Fan05, Lemma 3.4]). Let $G$ be a graph and $uv \in E(G)$. Suppose that $\mathcal{D}'$ is a path decomposition of $G' = G \setminus {uv}$. If $\mathcal{D}'(v) > |\{w\in N_{G'}(u) \colon \mathcal{D}'(w) = 0\}|$, then $uv$ is addible towards $u$ with respect to $\mathcal{D}'$.

> **Lemma 7** ([Fan05, Lemma 3.6]). Let $u$ be a vertex in a graph $G$ and let $G' = G\setminus\{ux_1,\ldots,ux_h\}$, where $x_i\in N_G(u)$. Suppose that $\mathcal{D}'$ is a path decomposition of $G'$ with $\mathcal{D}'(v)\geq 1$ for every $v\in N_G(u)$. Then, for any $x\in\{x_1,\ldots,x_h\}$, there is $A\subseteq\{ux_1,\ldots,ux_h\}$ such that $ux\in A$ and $|A|\geq\lceil \frac{h}{2}\rceil$; and $A$ is addible towards $u$ with respect to $\mathcal{D}'$.

> **Lemma 10** (rooted). Let $K$ be an ESET graph on $n$ vertices. If $u$ is a connection vertex of $K$, then $K$ admits a path decomposition $\mathcal{D}$ of $K$ such that $\mathcal{D}(u) \geq 2$ and $|\mathcal{D}|\leq \lceil n/2\rceil$. *(For an ESET graph of type (i), i.e. a SET graph, every vertex is a connection vertex.)*

> **Lemma 11.** Let $G$ be a graph that can be decomposed into an ESET graph $K$ on $n$ vertices with a connection vertex $u\in V(K)$, and a path $P$ such that $V(P)\cap V(K)=\{u\}$. Then $pn(G)\leq \lceil n/2\rceil$.

**Relevance to RE.**
- **Direct: trivial.** For Eulerian B, EV(B) = B, and in a 2-connected B the condition forces Δ(B) ≤ 3, so B is a cycle.
- **Via §0: yes, on a rooted structural class.** EV(B^r) = B − r. If B − r is a subgraph of a graph in 𝒢 (Theorem 5), or Δ(B − r) ≤ 3 (Theorem 13), then B^r is a Gallai graph or lies in 𝒮. It is not a SET graph, because its odd vertex ℓ has no even neighbour. So RE holds at that r.
- **Lemma 10 is a genuine rooted lemma** (𝒟(u) ≥ 2, ⌈n/2⌉ paths), but only for SET/ESET graphs, which are not Eulerian (they have odd vertices).

---

## 7. F. Botler, M. Sambinelli, R. S. Coelho, O. Lee, treewidth ≤ 3

- **Citation:** arXiv:1706.04334 (v1, Jun 2017), titled "On Gallai's and Hajós' Conjectures for graphs with treewidth at most 3". Journal version: "Gallai's path decomposition conjecture for graphs with treewidth at most 3", *J. Graph Theory* **93** (2020) 328–349, DOI 10.1002/jgt.22489. I did not check whether the journal version keeps the Δ ≤ 4 and girth-6 sections.
- **Access:** full text of arXiv v1 (statements and Sec. 2).

**Main theorems (verbatim, arXiv numbering):**
> **Theorem 3.2.** Let $G$ be a connected partial $3$-tree with $n$ vertices. Then $pn(G) \leq \lfloor n / 2\rfloor$ or $G$ is isomorphic to $K_3$ or to $K_5^-$.

> **Corollary 3.3.** Let $G$ be a connected graph with $n$ vertices and with no subdivision of $K_4$. Then $pn(G)\leq\lfloor n/2 \rfloor$ or $G$ is isomorphic to $K_3$.

> **Theorem 4.1.** Let $G$ be a connected graph with $n$ vertices. If $G$ has maximum degree $4$, then $pn(G)\leq \lfloor n/2\rfloor$ or $G$ is isomorphic to $K_3$, $K_5$ or to $K_5^-$. *(The section title reads "maximum degree at most 4".)*

> **Theorem 2.2.** Every connected planar graph with girth at least $6$ is a Gallai graph.

> **Conjecture 3.** Let $G$ be a connected graph with $n$ vertices. If $|E(G)| \leq (n-1)\lfloor{n}/{2} \rfloor$, then $pn(G) \leq \lfloor {n}/{2} \rfloor$. Otherwise, $pn(G) = \lceil {n}/{2} \rceil$.

**Restatements (verbatim):** Lovász: "a graph with $n$ vertices can be decomposed into at most $\lfloor n/2\rfloor$ paths and cycles." Pyber: "If $G$ is a graph with $n$ vertices in which every cycle contains a vertex of odd degree, then $pn(G)\leq\lfloor n/2\rfloor$."

**End-type lemma (verbatim).** This is the only lemma with a structural conclusion on one of the paths:
> **Lemma 2.3.** Let $G$ be a connected graph that admits a decomposition into a path $P$ and a cycle $C$. (i) if $P$ contains at most one chord of $C$, then $G$ admits a decomposition into two paths $P_1$ and $P_2$ such that $P_1$ contains exactly one edge of $C$; and (ii) if $C$ has length at most $5$ and $P$ contains at most three chords of $C$, then $pn(G) = 2$.

**Relevance to RE.**
- **Theorem 3.2: yes.** Adding a leaf keeps treewidth ≤ 3, so RE holds on all 2-connected Eulerian partial 3-trees of even order, for every root.
- **Theorem 2.2: yes.** Adding a leaf keeps planarity and girth, so RE holds on planar Eulerian graphs of girth ≥ 6.
- **Theorem 4.1: partial.** On Eulerian graphs with Δ ≤ 4 it gives RE for roots of degree 2, because B^r then still has Δ ≤ 4. It gives nothing for roots of degree 4, because B^r then has Δ = 5 (see §12 for a possible fix).

---

## 8. G. Fan, "Path decompositions and Gallai's conjecture"

- **Citation:** *J. Combin. Theory Ser. B* **93** (2005) 117–125, DOI 10.1016/j.jctb.2004.09.008.
- **Access:** not accessible. ScienceDirect returned HTTP 403 on the article page and on the open-archive PDF link that Semantic Scholar lists. Restatements:
  - The main theorem, as restated verbatim in BS (Theorem 2(c), §6): connected G whose E-subgraph has triangle-free blocks of maximum degree ≤ 3 has pn ≤ ⌊n/2⌋. Bonamy–Perrett restate it with the same ⌊n/2⌋ bound (§3). Jiménez–Wakabayashi restate it as "Corollary of the Main Theorem of Fan": "… then $G$ satisfies Gallai's conjecture."
  - The addible machinery is restated verbatim in BS (Definition 1 ≙ Fan's Definition 3.2; Lemmas 6, 7 ≙ Fan's Lemmas 3.4, 3.6), in BJS (Lemma 3 ≙ Lemma 3.4), and in Xie (Definition 2.2, "addible at w", and Lemma 2.3 ≙ Lemma 3.6, wording: "… there is an edge set $B$ … such that $wx\in B$, $|B|\geq\lceil s/2\rceil$, and $B$ is addible at $w$ with respect to $\mathcal{D}$").
- **Relevance to RE.** Fan's addible lemmas are the standard end-transfer tools: re-adding edges at u raises 𝒟(u) without increasing |𝒟|. They are the natural engine for a rooted induction.
  - Direct application to Eulerian B is trivial: the blocks are cycles.
  - **Via §0 (restatement-based): yes on a rooted class.** If every block of B − r is triangle-free with maximum degree ≤ 3, then p(B^r) ≤ ⌊(n+1)/2⌋ and RE holds at r.

## 9. A. Blanché, M. Bonamy, N. Bonichon, "Gallai's path decomposition in planar graphs"

- **Citation:** arXiv:2110.08870 (v1 Oct 2021, v2 21 Jun 2022). Extended abstract: "Gallai's Path Decomposition for Planar Graphs", in *Extended Abstracts EuroComb 2021*, Trends in Mathematics 14, pp. 758–764, DOI 10.1007/978-3-030-83823-2_121 (Crossref metadata only). I found no full journal version.
- **Access:** full text of arXiv v2 (main file; Sec. 3 introduction and some lemmas).

**Main theorems (verbatim):**
> **Theorem 1.1.** Every connected planar graph on $n$ vertices can be decomposed into $\lceil \frac{n}{2} \rceil$ paths.

> **Theorem 1.2.** Every connected planar graph on $n$ vertices, except $K_3$ and $K_5^-$, can be decomposed into $\lfloor \frac{n}{2} \rfloor$ paths.

**Method (verbatim).** "The general method consists in fixing a shortest path $P$ between the two special vertices. … In $G$, the edges of $P$ are then colored with the extra color. This has the advantage of having an end of this extra color on each of the two special vertices". The paper also uses the Chu–Fan–Liu path+cycle lemma, restated as:
> "Let $C$ be a cycle and $P$ a path, such that $C$ and $P$ are edge-disjoint. If $1\leq \vert V(C)\cap V(P)\vert \leq 5$, then $E(C)\cup E(P)$ can be decomposed into $2$ paths, unless $C\cup P$ is the exceptional graph."

There is no rooted lemma: the end conditions are internal to the reduction rules.

**Relevance to RE: yes, on all 2-connected planar Eulerian graphs of even order, every root.** B^r is connected and planar, and it is neither K3 nor K5^- (it has a leaf). Theorem 1.2 gives p(B^r) ≤ n/2, and §0 applies.

---

## 10. L. Pyber, "Covering the edges of a connected graph by paths"

- **Citation:** *J. Combin. Theory Ser. B* **66** (1996) 152–159, DOI 10.1006/jctb.1996.0012.
- **Access:** not accessible (HTTP 403). Restatements (verbatim):
  - BS Theorem 2(b): connected, EV(G) a forest ⇒ pn(G) ≤ ⌊n/2⌋.
  - BSCL Theorem 1.2: "every cycle contains a vertex of odd degree" ⇒ pn(G) ≤ ⌊n/2⌋.
  - Bonamy–Perrett: G_E a forest ⇒ ⌊n/2⌋ paths.
- **Relevance to RE: via §0, yes on a rooted class.** If B − r is a forest, i.e. every cycle of B passes through r, then RE holds at r. Directly the theorem is vacuous for Eulerian graphs.

## 11. L. Lovász, "On covering of graphs"

- **Citation:** in P. Erdős, G. Katona (eds.), *Theory of Graphs*, Academic Press, New York / Akadémiai Kiadó, Budapest, 1968, 231–236.
- **Access:** not accessible. Restatements (verbatim):
  - Chu–Wang Theorem 1.2: "Let $G$ be a graph (possibly disconnected) on $n$ vertices. If $G$ contains at most one vertex of even degree, then $p(G)\leq \frac{n}{2}$."
  - BSCL: "a graph with $n$ vertices can be decomposed into at most $\lfloor n/2\rfloor$ paths and cycles."
  - Bonamy–Perrett: "|𝒟| = ⌊n/2⌋" paths and cycles.
  - Jiménez–Wakabayashi: "path-cycle decomposition of cardinality at most $\lfloor n/2\rfloor$".
- **Relevance to RE: no.** B^r has n − 1 even vertices.

---

## 12. Other papers found and read

### 12a. J. Zhang, Q. Liu, Y. Hong, "Gallai's path decomposition conjecture for K5-minor-free graphs" (new, Nov 2026)
- **Citation:** arXiv:2611.21673 (v1, 14 Nov 2026). Not yet published.
- **Access:** full text (Sec. 1, Sec. 2 lemmas, final proof).

**Main theorem (verbatim):**
> **Theorem 1.1.** Let $G$ be a connected $K_5$-minor-free graph. If $G$ is not isomorphic to $K_3$ or $K_5-e$, then $pn(G)\le\lfloor|V(G)|/2\rfloor$.

**Rooted content (verbatim, inside the proof of Lemma 2.2, cut-vertex reduction).** This is the leaf device of §0 plus rooted decompositions of the exceptions:
> "In that case, add a leaf at $z$ in each $G_i$. Each resulting graph is smaller than $G$, is $K_5$-minor-free, and is not exceptional. It has a decomposition into at most $n_i/2$ paths. Delete the leaf edge. Either a whole path is removed, or a path now ends at $z$."
>
> "Each exceptional graph has an optimal decomposition with at least two paths ending at any prescribed vertex $z$." (Explicit lists are given for $K_3$ and $K_5-e$.)

**Restatements (verbatim):** "The same exceptions occur for connected graphs of treewidth at most three [TreewidthThree] and, more generally, for connected $3$-degenerate graphs [ZhangLiuHong]." The source is J. Zhang, Q. Liu, Y. Hong, "Gallai's conjecture for 3-degenerated graphs", *Discrete Math.* **347** (2024) no. 7, 114057, DOI 10.1016/j.disc.2024.114057, which I could not access. The paper also paraphrases ZLH 2024 Lemmas 2.5–2.6 (path+cycle meeting in 1–5 vertices gives 2 paths, except "$K_5-e$ with a possibly empty pendant path at each end of the missing edge"; two cycles meeting in 1–4 vertices give 2 paths), and cites Liu–Zhang–Hong on K_{3,3}-minor-free graphs, "Unpublished manuscript, June 2026" (not verified).

**Relevance to RE: yes** on 2-connected Eulerian K5-minor-free graphs of even order, every root, since K5-minor-freeness survives adding a leaf. Through the restated 3-degenerate theorem, **yes** also for 3-degenerate graphs; this rests on a restatement, as ZLH 2024 was not read.

### 12b. N. Anto, M. Basavaraju, "Gallai's Path Decomposition for 2-degenerate Graphs"
- **Citation:** arXiv:2211.07159v3. *Discrete Math. Theor. Comput. Sci.* **25:1** (2023), DOI 10.46298/dmtcs.10313.
- **Access:** full text (main theorem and intro).

> **Theorem 1.** Let $G$ be a connected 2-degenerate graph on $n$ vertices. Then the edges of $G$ can be decomposed into at most $\lfloor \frac{n}{2} \rfloor$ paths unless $G$ is a triangle.

**Restatement of Chu–Fan–Liu (verbatim):** "[Chu2021] proved that the edges of any connected graph $G$ with maximum degree $6$ in which the vertices of degree $6$ form an independent set can be decomposed into at most $\lfloor \frac{n}{2} \rfloor$ paths, unless $G$ is $K_3$, $K_5$ or $K_5-e$."

**Relevance to RE: yes** on 2-connected Eulerian 2-degenerate graphs of even order, since adding a leaf keeps 2-degeneracy.

### 12c. Y. Chu, G. Fan, Q. Liu, "On Gallai's conjecture for graphs with maximum degree 6"
- **Citation:** *Discrete Math.* **344** (2021) 112212, DOI 10.1016/j.disc.2020.112212.
- **Access:** abstract only (Semantic Scholar):
> "we prove that a connected graph with maximum degree 6, in which the vertices of degree 6 form an independent set, can be decomposed into n 2 paths, unless it is K 3 , K 5 and K 5 − ." *(The fraction is garbled in the API text. Anto–Basavaraju restate the bound as ⌊n/2⌋.)*

**Relevance to RE: partial, and conditional.** The exception list contains K3 and K5−e, which have Δ < 6. This suggests the hypothesis is Δ ≤ 6, but that is an inference I have not verified in the full text. If it holds, B^r stays in the class whenever d_B(r) ≤ 4. That would give RE for every root of degree ≤ 4 in Eulerian graphs with Δ ≤ 6 and independent degree-6 vertices, and in particular for **every root of every even-order Eulerian graph with Δ ≤ 4**, closing the gap left by BSCL Theorem 4.1.

### 12d. G. Fan, J. Hou, C. Zhou, "Gallai's Conjecture on Path Decompositions"
- **Citation:** *J. Oper. Res. Soc. China* **11** (2023) no. 3, 439–449, DOI 10.1007/s40305-022-00435-3.
- **Access:** abstract (journal page) plus one theorem restated verbatim in Xie (12e).

Abstract (verbatim):
> "it is proved that Gallai's conjecture is true for graphs $G$ in which $G_e$ contains no triangle pair and each block of $G_e$ has maximum degree at most 3."

**Rooted theorem**, as restated verbatim by Xie as "Theorem 1.3 (Theorem 5, [4])":
> Let $G$ be a connected graph on $n$ vertices and $F$ be the E-subgraph of $G$. If there is a vertex $x \in V(F)$ such that $d_F(v) \le 3$ for every vertex $v \in V(F)\setminus\{x\}$, then $G$ has a path-decomposition $D$ such that $|D| \le \frac{n+1}{2}$ and $D(x) \ge 2$.

Also restated by Xie (Lemma 2.4 = [4, Lemma 5]): if $D(w)\ge l+k$ and each $x_i$ has at most $l$ passing neighbours, then the edges $wx_1,\dots,wx_k$ can be re-added with $D^*(w)\ge l$, $D^*(x_i)=D(x_i)+1$, and $|D^*|=|D|$.

**Relevance to RE.** This is a **rooted statement of exactly RE's shape**, with the bound (n+1)/2, which for even n is ≤ n/2. For Eulerian B, F = B, so every v ≠ x must have degree 2. For 2-connected B that forces B to be a cycle, so RE holds only on the trivial class. Through §0 the bound is too weak: B^r has odd order, so (n+2)/2 = n/2 + 1.

### 12e. M. Xie, "On Gallai's path decomposition conjecture"
- **Citation:** *Filomat* **37:17** (2023) 5829–5834, DOI 10.2298/FIL2317829X.
- **Access:** open-access PDF; abstract, Secs. 1–2 and the start of the proof read.

> **Theorem 1.4.** Let $G$ be a connected graph on $n$ vertices and $F$ be the E-subgraph of $G$. If there are two vertices $x, y \in V(F)$ and an edge $xy \in E(F)$ such that $d_F(v) \le 3$ for every vertex $v \in V(F)\setminus\{x, y\}$, then $G$ has a path-decomposition $D_1$ such that $|D_1| \le \frac{n+1}{2}$ and $D_1(x) \ge 2$, and a path-decomposition $D_2$ such that $|D_2| \le \frac{n+1}{2}$ and $D_2(y) \ge 2$.

The proof is by minimal counterexample, using FHZ Theorem 5 as the rooted base.

**Relevance to RE: yes, on a small class.** It applies to 2-connected Eulerian B with an edge xy such that every other vertex has degree 2, with RE at x and at y (|D| ≤ (n+1)/2 means ≤ n/2 for even n). The real value is methodological: **this paper and FHZ are the only sources found whose main theorem is a prescribed-end (D(x) ≥ 2) Gallai statement.**

### 12f. P. Kindermann, L. Schlipf, A. Schulz, "On Gallai's conjecture for series-parallel graphs and planar 3-trees"
- **Citation:** arXiv:1706.04130 (2017); cited by BBB as CoRR abs/1706.04130.
- **Access:** full text (Sec. 2).

> **Theorem 1.** Any series-parallel graph $G$ with $n$ vertices admits a path cover of size at most $\lceil n/2\rceil$.

**Prescribed-end induction (verbatim, Lemma 2 and its types).** G has source s and sink t; ρ is the number of "braces".
> "$I_P$: A path cover is of type $I_P$ if it contains an $s$-$t$-path and if it has size at most $n/2+\rho$. … $O$: … contains two interior-vertex-disjoint $s$-$t$-paths and … size at most $(n+1)/2+\rho$. $L$: … contains an $s$-$t$-path and a path that starts in $s$ and does not include $t$ and … size at most $n/2+\rho$."
>
> **Lemma 2.** Each series-parallel graph admits a path cover of type $I_P$ if the root of its SPQ-tree is a Q-node, a path cover of a type in $\Pi$ if the root of its SPQ-tree is a P-node, and a path cover of a type in $\Sigma$ if the root of its SPQ-tree is an S-node.

**Relevance to RE: no directly.** The bound is a ceiling, and the end conditions are at the two terminals, with slack ρ. Still, it is a clear example of a stronger inductive statement with end conditions. Series-parallel graphs have treewidth ≤ 2, so BSCL Theorem 3.2 already gives RE there.

### 12g. A. Jiménez, Y. Wakabayashi, "On path-cycle decompositions of triangle-free graphs"
- **Citation:** arXiv:1402.3741v3. *Discrete Math. Theor. Comput. Sci.* **19:3** (2017), DOI 10.23638/DMTCS-19-3-7.
- **Access:** full text (intro, results).

> **Corollary 2.** Every graph in $\mathcal{G}$ on $n$ vertices with at most $4\lceil n/2\rceil$ edges has a path decomposition into at most $\lceil n/2\rceil$ paths.

Here $\mathcal{G}$ = {connected triangle-free graphs with odd distance ≥ 3}. The paper notes it corresponds to triangle-free Eulerian graphs minus a suitable matching, possibly empty, so it contains connected triangle-free Eulerian graphs.

**Restatements (verbatim):**
- Dean–Kouider: "every graph $G$ has a path decomposition into at most $\frac{p}{2} + \lfloor \frac{2}{3} q\rfloor$ paths" (p = number of odd vertices, q = number of even non-isolated vertices).
- Harding–McGuinness: "the bound $\frac{p}{2} + \lfloor \frac{g+1}{2g} q\rfloor$, where $g\geq 4$ denotes the girth".

**Relevance to RE: no.** It gives Gallai for triangle-free Eulerian graphs with |E| ≤ 2n, but nothing rooted. B^r has odd vertices r and ℓ at distance 1, which violates odd distance ≥ 3.

### 12h. Not read (bounds above n/2, or not Eulerian-relevant)
- Dean–Kouider (2000), Harding–McGuinness (2014) and Chu–Fan–Zhou (2022): known only through the restatements above. Their bounds are 2n/3, (g+1)n/(2g) and 3n/5 for Eulerian graphs. **Relevance to RE: no.**
- arXiv papers found but not read in detail: Wang–Zhang 2210.16406 (complete graphs), Chen–Wu 2310.11189 and 2310.11704 (Cartesian products), Sahu–Padinhatteeri 2409.06298 (Levi graphs), Mehendale 1106.0642. Also listed in Crossref: "Gallai's Path Decomposition Conjecture for Graphs with Small Bowtie Boundaries" (SSRN 2026). None of their titles or abstracts mentions Eulerian graphs or prescribed ends.

---

## Summary table

"RE?" means the source, read with its exact hypotheses, implies RE: for 2-connected Eulerian B of even order n and root r, at most n/2 paths with r an end of at least 2 of them. "§0" means the implication goes through the leaf lemma of §0.

| Class of Eulerian graphs | Bound proved | Source | Access | Gives RE on the class? |
|---|---|---|---|---|
| Δ ≤ 4 (degrees 2 and 4) | ⌈n/2⌉ (as restated; exact form unseen) | Favaron–Kouider 1988 | restatements (CW, BP, BJ, BJS, BS, JW, BBB, Xie) | unknown: no end condition in any restatement |
| Δ ≤ 4, except K3 and K5 | ⌊n/2⌋ | BSCL Thm 4.1 | full (arXiv) | partial: §0 gives roots of degree 2 only (B^r has Δ = 5 when d(r) = 4) |
| Δ ≤ 5 | ⌈n/2⌉ | Bonamy–Perrett Thm 1.3 | full (arXiv v1) | no: ceiling bound, no rooted lemma or stronger induction |
| Δ ≤ 6, degree-6 vertices independent, except K3 and K5 | ⌊n/2⌋ (as restated by Anto–Basavaraju) | Chu–Fan–Liu 2021 | abstract only | partial: §0 gives roots with d(r) ≤ 4, which would cover all of Eulerian Δ ≤ 4, if the hypothesis is Δ ≤ 6 (inferred, unverified) |
| planar, except K3 | ⌊n/2⌋ | Blanché–Bonamy–Bonichon Thm 1.2 | full (arXiv v2) | **yes** (§0; B^r planar, not K3 or K5^-) |
| K5-minor-free, except K3 | ⌊n/2⌋ | Zhang–Liu–Hong 2026, Thm 1.1 | full (arXiv) | **yes** (§0; the leaf device also appears in their Lemma 2.2) |
| treewidth ≤ 3, except K3 | ⌊n/2⌋ | BSCL Thm 3.2 | full (arXiv) | **yes** (§0) |
| 3-degenerate, except K3 | ⌊n/2⌋ (restated) | Zhang–Liu–Hong 2024 (DM 347, 114057) | restatement in ZLH 2026 | yes, if the restatement is accurate (§0) |
| 2-degenerate, except K3 | ⌊n/2⌋ | Anto–Basavaraju Thm 1 | full (arXiv) | **yes** (§0) |
| triangle-free planar | ⌊n/2⌋ | BJS Thm 6 | full (arXiv) | **yes** (§0; subsumed by planar) |
| planar, girth ≥ 6 | ⌊n/2⌋ | BSCL Thm 2.2 | full (arXiv) | **yes** (§0; subsumed by planar) |
| 2k-regular, girth ≥ 2k−2, two disjoint perfect matchings, k ≥ 3 | n/2 (n even) | Botler–Jiménez Thm 1 | full (arXiv) | no: no control over which vertices are ends; B^r not regular |
| triangle-free with \|E\| ≤ 4⌈n/2⌉ | ⌈n/2⌉ | Jiménez–Wakabayashi Cor 2 | full (arXiv) | no: not rooted; B^r violates odd distance ≥ 3 |
| B − r a forest (r fixed) | ⌊n/2⌋ for B^r | Pyber 1996 | restatement (BS, BSCL, BP) | yes at that r (§0), restatement-based |
| blocks of B − r triangle-free with Δ ≤ 3 (r fixed) | ⌊n/2⌋ for B^r | Fan 2005 | restatement (BS, BP, JW) | yes at that r (§0), restatement-based |
| B − r ⊆ a graph in 𝒢 of BS, or Δ(B − r) ≤ 3 (r fixed) | ⌊n/2⌋ for B^r | Botler–Sambinelli Thms 5, 13 | full (arXiv) | yes at that r (§0; B^r is not a SET graph) |
| all vertices but x of degree 2 (for 2-connected B: cycles) | (n+1)/2 with D(x) ≥ 2 | Fan–Hou–Zhou Thm 5 | restated verbatim in Xie | yes, but the class is trivial; genuinely rooted |
| adjacent x, y; all other vertices of degree 2 | (n+1)/2 with D(x) ≥ 2, resp. D(y) ≥ 2 | Xie 2023, Thm 1.4 | full (open access) | yes at x and y; small class; genuinely rooted |
| triangles pairwise at distance ≥ 3 | 3n/5 | Chu–Wang Thm 1.3 | full (arXiv) | no: bound exceeds n/2 |
| all Eulerian (and all graphs) | 2n/3, (g+1)n/(2g), 3n/5 | Dean–Kouider; Harding–McGuinness; Chu–Fan–Zhou | restatements | no: bounds exceed n/2 |
| any graph whose leaf extensions B^r satisfy Bonamy–Perrett Q1.1 / BSCL Conj. 3 / BS Conj. 4 | ⌊n/2⌋ (conjectural) | — | — | these conjectures imply RE in full (§0, consequence 3) |
