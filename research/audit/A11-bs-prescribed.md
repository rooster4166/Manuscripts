# A11 — Referee audit: bs-prescribed (Corollary 106 without Shaik; five even vertices with one universal vertex)

Auditor: independent adversarial referee pass, 2026-11-26.

Sources audited:
- **[BSP]** `manuscripts/bs-prescribed/bs-prescribed.tex`, with its scripts in `manuscripts/bs-prescribed/scripts/`. I started from commit 7ea2368. The author revised the draft while I worked (4606a76, b8cf1c3, 871d91f: G_{t,t'} family, census numbers, Lean section). I re-audited every change. Numbers such as "Lemma 10" refer to the compiled PDF of the current draft.
- **[MR]** `gallai/01-original-manuscripts/marked-reduction.pdf`, text extracted with `pdftotext` (layout and raw). Page numbers are MR's printed page numbers.
- **[Lean]** `lean/GallaiLean/FiveEven.lean` and `FiveEvenCerts.lean` (from 8b1bbf4 and 871d91f, now merged). Statements were compared; I did not rebuild.
- Background: `research/connections.md` §L; audits A6 (F16–F21), A7 §§1, 3, 4; `manuscripts/endpoint-structure` (Lemma 15 = Fan's transfers, Corollary 22 = rooted test for four even vertices); `manuscripts/corrigenda`.

The author's `verify_certs.py` is treated as **non-independent**. Every verdict below rests on my own re-derivation and on my own scripts in `research/audit/A11-scripts/`. These share no code with `manuscripts/bs-prescribed/scripts/` (one cross-check uses `tools/pathnum.py`).

Verdicts: **SOUND**; **GAP** (fixable; the fix is stated); **ERROR** (false; a counterexample is given); **UNCLEAR** (cannot be settled from the available material).

---

## 0. Summary table

| # | Item ([BSP] / [MR] location) | Verdict | Note |
|---|---|---|---|
| **S0** | **Scope claim: "every use of Cor 106 has at most five unmarked even vertices"** | **SOUND** | Cor 106 is cited exactly three times in MR, all in the proof of Thm 144 (pp. 156–157). Its second sentence is used once (the paragraph after its proof, p. 120). No other result cites it, and no later result cites Thm 144 (§1). |
| S1 | Use 1, p. 156: "By Corollary 106 with mark r, at least two vertices of K have degree four" | SOUND | G = B = W − ℓ, S = {r}, U = T, \|U\| = 5. The leaf floor is applied to L_{r}(B) = W: odd order, a leaf at the odd support r, connected. Cor 2 → Thm 1(a), or Thm 1(b) through Lemma 14. |
| S2 | Use 2, p. 157: H = B − rw with four even vertices | SOUND | The mark is the other even neighbour w′ of r (if any), so \|U\| = 3 and BS Thm 13 applies to H + leaf. With no mark, BS Cor 14 directly (strictly speaking Cor 106 needs S ≠ ∅). In the bridge case, the components have ≤ 4 even vertices, so BS applies. |
| S3 | Use 3, p. 157: matching-cut shores | SOUND | \|U\| = 0 on C and ≤ 4 on A. Zero-exception case; A = ∅ is handled by BS Cor 14 and the two-leaf trick. |
| S4 | Second sentence of Cor 106 (p. 120), both even supports and the mixed case | SOUND | Exactly seven even sites with two even marks gives \|U\| = 5, and L = H + 2 private leaves has odd order. The general sentence (≥ 9 even sites) is used nowhere; Thms 122/124 supersede it. |
| S5 | Thm 114 remark, p. 129 (cites Shaik directly) | SOUND | Both d = 6 tests follow from floors of J − z + one or two leaves at r. These have odd order, leaves at the odd support r, and five even vertices. Cor 2 applies. Also already covered inside MR by Thm 123 + Lemma 133 (§1.3). |
| S6 | Thm 144 step "r ∈ T", p. 156 (cites Shaik directly) | SOUND | BS Thm 13 (B has four even vertices and even order). Agrees with A6 F16 and A7 U4. |
| S7 | Other inputs of Thm 144 (Thm 113, Lemma 6, Thm 123, Cor 129, Cor 138, Prop 139 and their inputs) | SOUND as to Shaik | None of them cites [25] or Cor 106 (full-text search). Their own status is unchanged: A6 F19/F21, UNCLEAR by inheritance from absent tables. |
| S8 | Remaining direct Shaik citation in MR §2.1, p. 8 (Thm 1.1: a failing single even mark needs two further high even vertices) | Not addressed by [BSP]; **unused** | No later result uses it (the next paragraph's proof does not). Now recorded in [BSP] §7, "What remains conditional". |
| S9 | Attribution: A6 F17 and the corrigenda already gave a Shaik-free route for Thm 144 (Lemma 133 for connected B, or the A6 bank) | GAP (attribution), **fixed** | Paragraph added to §4. [BSP]'s new content is a human-checkable proof plus a corrected Cor 106. |
| S10 | FHZ Thm 5 (A7: secondary quotation only) in Cor 16 | SOUND; never needed in a use | Whenever L[U] has a degree-4 vertex in an actual use, \|L\| is odd. Sentence added. |
| M1 | Lemma 3 (Lovász, exact form, componentwise) | SOUND | |
| M2 | Lemma 4 (Fan Lemmas 3.3/3.4) | SOUND | Matches Fan's primary text (A6 §2) and ES Lemma 15. "b_D(t) ≥ 1" follows from Fan's (b). |
| M3 | Definition 5, Lemma 6 (count; realisable pair) | SOUND | The pair conclusion needs the final vector to be (2,2,0,0,0) on T. The author's verifier does not check this; mine does (B2). |
| **M4** | **Localisation: "a vertex outside M is never blank"; a certificate on M is valid for every host** | **SOUND** | Held edges lie inside M ⊇ T = Ev(W), so outside vertices keep their odd W-degree. They get one end in the seed, are never donors or receivers, and keep that end. Adjacency inside M and parities on M are fully fixed by the hypotheses. Confirmed on 240 concrete hosts: the global blank count equals the local one at every move (B6). |
| M5 | The seven rims (41 labelled; 38 non-bowtie + 3 bowties) | SOUND | Enumerated. |
| M6 | Lemma 10 (two disjoint even edges) | SOUND | Recomputed: q→p is (1 > 0), as p ≁ z; q′→p′ is (1 > 0), as the blanks z, q miss p′. Code: all 3,840 (graph, labelling) pairs meeting the hypotheses, on every graph on five labelled vertices; each hypothesis is necessary (mutation test). |
| M7 | Lemma 11 (odd star) | SOUND | Steps: (1 > 0); (2 > ≤1), blank w only, since z ≁ a; (3 > ≤2), blanks ⊆ {w, t, z} minus one. Both donor branches. Code: 6,000 pairs; each hypothesis necessary. |
| M8 | Lemma 12 (universal star) | SOUND | Steps: (2 > ≤1), blank d; x→t′ (2 > ≤1); x→c (1 > 0), as c has no T-neighbour but x. Code: 1,200 pairs; each hypothesis necessary. |
| M9 | Prop 13 (the six cores) and Thm 1(a) | SOUND | Every printed assignment re-checked by hand. The code checks all 38 labelled rims. No hypothesis outside T and no connectivity is used. |
| M10 | Lemma 14 (u, v from a leaf at an odd support) | SOUND | Also Lean `exists_uv`. |
| M11 | Orbit reduction (group of order 8; 31 contact sets in 11 orbits) | SOUND | Recomputed. Transport was also verified directly on all 3 × 31 labelled cases. |
| **M12** | **Table 2, ten rows: every supply and blank count, seed, final pair** | **SOUND** | All recomputed by hand (§2.3) and by code from a hand transcription of the .tex. Every printed (supply > blanks) pair matches, and every leaf ends with u = v = 1 and T = (2,2,0,0,0) at the printed S. |
| M13 | The case A = T (six moves) | SOUND | Valid in either order of s₁, s₂. Supplies 4 then 3, blanks ≤ 2. All 6 donor branches (12 with both orders). |
| M14 | Thm 1(b) | SOUND | |
| M15 | Cor 2 | SOUND | Minor: in the even-support case r is odd in L − ℓ, so *every* partition ends at r. ES Cor 22 (or BS Thm 13) is needed only for p(L − ℓ) ≤ \|L − ℓ\|/2. |
| M16 | Cor 16 (corrected Cor 106) | SOUND; GAP (wording), **fixed** | "In each case every leaf support is odd" overstates: G may have leaves at unmarked even vertices. What is used is a private leaf at an odd support. |
| M17 | Cor 17 (Thm 144 and the Thm 114 remark without Shaik) | SOUND | |
| B1 | `verify_certs.py` (author), run with `nice` | Reproduced | `OK: 38 local certificates (46 leaves), 93 bowtie certificates (129 leaves)`. `bowtie_table.py` reproduces Table 2 exactly. |
| B2 | Independent check of the 11 certificates (`cert_check.py` A) | SOUND | 11 representatives plus transport to 93 labelled cases; every move legal; final vectors are realisable pairs. |
| **B3** | **"Valid for every host": how unknown adjacencies are handled** | **SOUND** | Inside M there are none: K is fixed, N(u) ∩ T = A, N(v) ∩ T = ∅, and uv is present. All edges from M to the outside are arbitrary and irrelevant, because outside vertices always have one end. u and v may have any exterior neighbours. If v is a leaf, holding uv isolates it; the seed and the move u→v (2 > 0) still work. Lean `soundS` formalizes exactly this (outside vertices have b₀ > 0). |
| B4 | Own exhaustive search (`cert_check.py` C) | SOUND (matches every claim) | Bowtie on T alone: no certificate (matches end of §5). T + u: 25/31, exceptions exactly ab, cd, xab, xcd, abcd, xabcd (Rem. 15(ii)). T + u + v: 31/31. All 41 one-universal cores × 31 contact sets: certified (A6 bank). All 38 non-bowtie rims on T: certified. |
| B5 | Author's verifier checks only the end sum at leaves | GAP (script), not a gap in the theorem | It does not check that the final vector is a pair. B2 checks it. Suggest adding the check to `verify_certs.py`. |
| B6 | End-to-end replay on random concrete hosts (`random_replay.py`) | SOUND | 120 bowtie hosts (orders 9–13; v a leaf in about ¼; exterior adjacent to T, u, v) and 120 six-core hosts (orders 7–11). At every node of every certificate, the predicted end vector is realised on the concrete intermediate graph (own exact solver), and global blanks = local blanks. No host skipped. |
| C1 | Lemma 7 (forcing) | SOUND | |
| C2 | Prop 8 (family G_{t,t′}) | SOUND | Exact check for (t, t′) = (1,0), (2,0), (1,1), (3,0), (2,1), (4,0), (3,1), (2,2): no floor partition ends at y, but p ≤ (N−1)/2. Note: the family has e = N − 2, so it gives one e per N. The first-draft family G_t (t = 2, 4) also checked. |
| C3 | Table 1 (census), N = 5 and N = 7 | SOUND | All "pairs" and "no floor partition" entries reproduced with my own solver, including (5 SET) and (29 SET). Game rows reproduced with the author's `odd_fan_game.py` (non-independent): 7/14/0 and 130/230/64/0. The 7ea2368 draft had "4 SET" and two undefined macros; both are corrected in the current draft. |
| C4 | The six N = 7, e = 5 failures (list after Prop 8) | SOUND | The six graphs found match the six descriptions (G_{1,1}, G_{2,0}, two pendant-triangle shapes, K_{1,1,3}, K_5). |
| C5 | "187 of 424 lost pairs, 58 of 64 with e = 5, have the partition" | SOUND | 424 − 237 and 64 − 6. |
| C6 | Prop 9: L of order 9 with p(L) = 4; gadget D of order 17 | Statement SOUND; proof GAP (wording), **fixed** | "Four is the parity bound for its four odd vertices" is false: four odd vertices force only two paths. The lower bound 4 comes from Lemma 7 (two forced triangle ends). For D: no 8-path partition ends at y, and p(D) ≤ 8. Both confirmed exactly. |
| C7 | N = 9 sample (596 pairs) and "8 held edges recover 1 of 64" | Not re-run | Supplementary, not load-bearing. |
| L1 | Lean files present, no `sorry` | SOUND (by inspection) | grep: no `sorry`/`admit`/`native_decide`/`axiom`. Kernel `decide +kernel`. Not rebuilt. |
| L2 | `five_even_local` vs Thm 1(a) | SOUND, floor only | `hnu` ⇔ rim max degree ≤ 2 and `hnb` ⇔ rim not a perfect matching; this is exactly the hypothesis. The conclusion is 2\|D\| + 1 = \|V\|; the realisable pair is not formalized (`okS` ignores leaf vectors). Text fixed. |
| L3 | `five_even_bowtie` vs Thm 1(b) | SOUND, floor only | All 93 labelled cases are checked directly, with no orbit argument. |
| L4 | `exists_uv`, `five_even_floor` | SOUND | They are Lemma 14 and the floor of Thm 1 for connected W with a leaf at an odd support (the main case of Cor 2). |
| L5 | What the Lean checks | Note | The 38 Lean local certificates are `certgen.py`'s, not literally Lemmas 10–12 in their general form. Lean proves Thm 1(a), not the three lemmas as stated. Lemmas 10–12 are covered by my exhaustive check (M6–M8). |

**Overall.** I found **no ERROR**. Every step of Theorem 1 is SOUND: the three lemmas, the eleven bowtie certificates, Lemma 14, and the localisation argument that makes the certificates valid on every host. Every computation the paper reports reproduced. The scope claim is correct.

**Is the Shaik dependency removed from every use? Yes.** Every use of Cor 106 in MR satisfies the corrected Cor 16 with \|U\| ≤ 5: the three citations in Thm 144, and the second sentence in the Prop 105 paragraph. So do the Thm 114 remark and the "r ∈ T" step, which cite Shaik directly. Theorem 144 and these uses now rest only on Lovász, Fan Lemmas 3.3–3.4, BS Thm 13 / Cor 14 and ES Cor 22.

Two things remain conditional on [25], and neither is used anywhere in MR:
- Cor 106 in its original generality: one exception, odd order, \|U\| ≥ 7.
- The §2.1 remark on p. 8.

The fixes were textual. Five gaps were fixed in the .tex (C6, M16, S9, the Lean-scope wording in L2, and the Rem. 15(iii) and §7 additions). The recompile is clean.

---

## 1. Scope: every use of Corollary 106

### 1.1 Search

I searched the line-joined raw text of MR for "Corollary 106", "Theorem 144", "[25", "Shaik", "the corollary", "leaf floor", "two universal vertices" and "three universal" (`mr_join.txt`). The results:

| MR p. | Text | What it is |
|---|---|---|
| 8 | "Shaik [25, Theorem 1.1] allows x, y to be nonadjacent … a failing single even-degree mark x … requires at least two other even vertices with at least four even neighbors each" | direct Shaik use, §2.1 remark (S8) |
| 120 | Cor 106 statement and proof ("Shaik's ordinary ceiling bound [25, Corollary 1.2]"; "If A is empty, Shaik's ordinary bound applies to G") | the corollary |
| 120 | "If H in Proposition 105 has exactly seven even sites … F has at least three universal vertices" | the only use of the second sentence (S4) |
| 129 | "Shaik's ordinary bound [25, Corollary 1.2] also applies if K has at most one vertex of degree greater than three … two universal vertices in this five-vertex K" | Thm 114 remark (S5) |
| 156 | "Shaik's ordinary bound [25, Corollary 1.2] gives k paths" | Thm 144, r ∈ T (S6) |
| 156–157 | "By Corollary 106 with mark r …" | Thm 144, use 1 (S1) |
| 157 | "so Corollary 106 gives an ordinary k-path partition" | Thm 144, use 2 (S2) |
| 157 | "Corollary 106 gives the marked bounds in these cases" | Thm 144, use 3 (S3) |
| supplement | "leaf substitutions in Theorem 144" | description of a computation only |

No other theorem, lemma or corollary of MR cites Cor 106 or Thm 144. The "two universal vertices" restrictions used later are each derived afresh:
- Thms 135, 136, 137 and 140 say "Lemma 133 and the book case leave K1, K2, K3";
- Thm 123 handles t = 2 without assuming two universal vertices.

The leaf floor bound is used outside Cor 106 only in its Fan–Hou–Zhou form of §2.1, which has no exceptional vertex (Thm 123, the book paragraph).

Other files in the repository mention Thm 144 or Cor 106 only descriptively: STATUS, ROADMAP, reader notes, A2/A6/A7, connections, and the corrigenda.

### 1.2 Each use against Corollary 16

**Use 1 (S1).** Here W is a least leafy counterexample, ℓ a leaf at r, and B = W − ℓ with |B| = 2k. We already know r ∉ T, so r is even in B and Ev(B) = T ∪ {r}. Cor 106 is applied with G = B and S = {r}. Then U = T and |U| = 5, and the proof's leaf floor is applied to L_{{r}}(B) = W. This W is connected and has odd order and a leaf at the odd support r.

If K = W[T] has no vertex of degree four, BS Thm 13 applies; a leaf rules out SET. If it has exactly one, that vertex is universal (|T| = 5). Then Thm 1 applies, through Lemma 14 in the bowtie case. Either way p(W) ≤ k, contradicting the choice of W. So this use is exactly Cor 2.

**Use 2 (S2).** Here H = B − rw with w ∈ T a neighbour of r. Ev(H) = T − w; both r and w are now odd. If r has another even neighbour w′, the mark is {w′}, so U = T − {w, w′} and |U| = 3. L = H + leaf at w′ has odd order, and BS Thm 13 applies (the leaf has one even neighbour, so L is not SET). Without w′, the claim is p(H) ≤ k, which is BS Cor 14 for H itself.

The bridge case cites only "ordinary half-order bounds". Each shore has ≤ 4 even vertices, so BS applies.

**Use 3 (S3).** The matching cut is taken in W, with ℓ on its support's shore. Unmarked vertices keep their W-degrees, so the unmarked even sites of a shore lie in T. On C none are even. On A at most four are, when a crossing edge touches T. In both cases the even subgraph is subcubic, which is BS.

If every mark on A is odd (A_even = ∅), the corollary's proof uses the ordinary ceiling (BS Cor 14) and, in the odd-order tight case, the leaf floor on G + two leaves (BS Thm 13).

**Second sentence (S4).** H is two-connected of odd order with exactly seven even sites, both supports even and marked, so |U| = 5. L = L_{{a,b}}(H) has odd order and leaves at odd supports, so Cor 2 applies.

In the mixed case, Prop 105 turns the failure into one with even supports b, t on the same H, again with |U| = 5. The general sentence (≥ 9 even sites, |U| ≥ 7) is never used. Thm 122 independently proves "at least nine even vertices".

**Thm 114 remark (S5).** Test 1: z is the only even vertex of J, so |J| is odd. L = (J − z) + leaf at r has order |J|, r is odd in L, and Ev(L) = N(z) − r.

Test 2: z and r are the only even vertices and are adjacent, so |J| is even. L = (J − z) + two leaves at r has order |J| + 1, r is odd in L, and Ev(L) = N(z) − r.

Both L are connected (J is 3-connected). Trimming a floor partition gives the test, as in MR's book paragraph (p. 130–131).

### 1.3 Earlier Shaik-free routes, and what is new

- **Thm 144 alone.** A6 F17, F20 and the corrigenda had already removed Shaik from Thm 144. Lemma 133 of MR is stated for two-connected B, but its proof uses only connectivity, and it gives use 1 directly. The A6 seven-site bank also gives it. Lemma 133, however, rests on the `boundary-even.json` table for M, P, C, which is not in the collection.
- **The Thm 114 remark.** It is covered inside MR by Thm 123 (the odd-order test at d = 6 always passes) and Lemma 133 (B = J − z is two-connected).
- **What [BSP] adds.** It supplies (i) a proof checkable by hand, replacing both tables, and (ii) a corrected statement of Cor 106 itself. When I started, [BSP] did not mention these earlier routes. A paragraph recording them is now added to [BSP] §4.

### 1.4 Remaining dependencies

The uses rest on:
- Lovász;
- Fan 3.3/3.4 (MATCHES, A6 §2);
- BS Thm 13 / Cor 14 (MATCHES, A7 §3);
- ES Cor 22, which itself uses only Lovász and Fan.

FHZ Thm 5 enters only the even-order clause of Cor 16, which no use needs (S10).

---

## 2. Theorem 1 and its lemmas

### 2.1 The localisation argument (M4)

Let M be the local set and H ⊆ E(W[M]) the held edges. Every vertex w ∉ M keeps d_W(w), which is odd, because Ev(W) = T ⊆ M. So w gets exactly one end in the Lovász seed (Lemma 3). It is never a donor or a receiver, since every held edge has both ends in M, so b(w) = 1 throughout. In particular w is never blank.

The legality of a move (r, D) therefore depends only on:
- b on M;
- which edges inside M are present, meaning not held or already restored.

Both are determined by the model:
- W[T] = K is given;
- N(u) ∩ T = A, N(v) ∩ T = ∅, and uv ∈ E;
- d_W is even on T and odd on u, v.

Nothing about edges between M and V − M, or about edges outside M, enters. Holding edges may disconnect W − H or isolate v; Lemma 3 is componentwise, and an isolated vertex is the even one, with 0 ends. So "valid for every host" is justified. Lean's `soundS` proves the same transport, with hypothesis `hb₀`: outside vertices have b₀ > 0.

### 2.2 The three lemmas

These were checked by hand and by `cert_check.py` B on every graph on five labelled even vertices and every labelling meeting the hypotheses. `mutation_check.py` shows that every hypothesis of each lemma is needed for its certificate, so the checker is not vacuous.

- **Lemma 10.** Hold pq, p′q′; the seed has only z even.
  - q→p: blanks ⊆ {z} ∩ N(p) = ∅.
  - q′→p′: blanks ⊆ {z, q} ∩ N(p′) = ∅.
  - Final: p, p′ = 2 and q, q′, z = 0.
- **Lemma 11.** Hold aw, ap, aq; a has degree d(a) − 3, which is odd; z is even, and a ≁ z.
  - w→a: (1 > 0).
  - {p,q}→a: blanks ⊆ {w} (z ≁ a), so (2 > ≤1). This returns t.
  - a→t′: (3 > ≤2), since the blanks lie in {w, t, z} and t′ misses one of them.
  - Final: a, t′ = 2 and w, t, z = 0.
- **Lemma 12.** Hold xa, xb, xc; d is the only even vertex.
  - {a,b}→x: blanks ⊆ {d}, so (2 > ≤1). This returns t.
  - x→t′: blanks ⊆ {t, d} (x itself has 2), and t′ misses one, so (2 > ≤1).
  - x→c: c has no T-neighbour but x, and xc is held, so (1 > 0).
  - Final: t′, c = 2 and x, t, d = 0.
- **Prop 13.** Check each assignment:
  - K₂+2K₁: (a,b,c,x,d), with a ≁ d, c ≁ d and c ≁ b.
  - P₃+K₁ and P₄: (b,c,a,x,d), with b ≁ d, a ≁ d and a ≁ c.
  - K₃+K₁: Lemma 11 at a with (x,b,c,d), since b ≁ d and c ≁ d.
  - C₄: Lemma 11 at a with (x,b,d,c), since b ≁ d.
  - 4K₁: Lemma 12.

  All 38 labelled rims check.

### 2.3 Table 2 (bowtie, centre x, triangles xab, xcd; u ~ v odd; A = N(u) ∩ T)

Hand recomputation (blank counts in the current graph). Each move is written as donor→receiver: (supply > blanks).

- **A = x.** Hold ab, cd, xu; the seed has u even.
  - b→a: 1 > 0, since a ≁ u.
  - d→c: 1 > 0, since the blanks u and b miss c.
  - x→u: 1 > 0, since u's present M-neighbour is only v.
  - S = ac.
- **A = a.** Hold xb, cd, au; the seed has u even.
  - b→x: 1 > 0, since x ≁ u.
  - d→c: 1 > 0.
  - a→u: 1 > 0, since u sees only v.
  - S = xc.
- **A = ac.** Hold xb, cd, au; the seed has u even.
  - b→x: 1 > 0.
  - a→u: 1 > 0, since u sees c (1) and v (1).
  - d→c: 1 > 0, since the blanks a, b miss c.
  - S = xc.
- **A = ab.** Hold xa, cd, bu, uv; the seed has v even.
  - d→c: 1 > 0.
  - x→a: 1 > 0, since a sees b, u (1 each).
  - b→u: 1 > 0, since u sees only a (2).
  - u→v: 2 > 0.
  - S = ac.
- **A = abc.** Hold xa, bu, cu; the seed has d even.
  - x→a: 1 > 0.
  - c→u: 1 > 0, since u ≁ x, d.
  - u→b: 2 > 1, the blank being x.
  - S = ab.
- **A = xac.** Hold xb, au, cu; the seed has d even.
  - u→a: 1 > 0.
  - c→u: 1 > 0, since u ≁ d.
  - x→b: 1 > 0, since b ≁ c, d, u.
  - S = ab.
- **A = xabc.** Hold xa, bu, cu; the seed has d even.
  - u→b: 1 > 0.
  - c→u: 1 > 0.
  - x→a: 1 > 0.
  - S = ab.
- **A = xa.** Hold xb, xc, xu, au; the seed has d even.
  - u→a: 1 > 0.
  - {b,c}→x: 2 > 1, the blank being d.
  - Branch [b]:
    - x→c: 2 > 1, the blank being d.
    - x→u: 1 > 0.
    - S = ac.
  - Branch [c]:
    - x→b: 2 > 0.
    - x→u: 1 > 0.
    - S = ab.
- **A = abcd.** Hold xa, bu, cu, du, uv; the seed has v even.
  - x→a: 1 > 0.
  - b→u: 1 > 0, since u ≁ x.
  - {c,d}→u: 2 > 1, the blank being b.
  - Branch [c]:
    - u→d: 3 > 2, the blanks being x and c.
    - u→v: 2 > 0.
    - S = ad.
  - Branch [d] is symmetric, with S = ac.
- **A = xab.** Hold cd, xu, au, bu, uv; the seed has v even.
  - d→c: 1 > 0.
  - x→u: 1 > 0, since u has no present M-neighbour.
  - {a,b}→u: 2 > 1, the blank being x.
  - Branch [a]:
    - u→b: 3 > 2, the blanks being x and a.
    - u→v: 2 > 0.
    - S = bc.
  - Branch [b] is symmetric, with S = ac.
- **A = T.** Hold all six edges at u; the seed has v even.
  - x→u: 1 > 0.
  - {a,b}→u: 2 > 1. This returns t₁.
  - The remaining three are offered to u: 3 > 2, the blanks being x and t₁. This returns t₂.
  - u→s₁: 4 > ≤2.
  - u→s₂: 3 > ≤2, since s₂ sees x and its one rim partner.
  - u→v: 2 > 0.

  This holds in either order of s₁, s₂.

Every printed number agrees with this recomputation and with `cert_check.py` A. That script transcribes the table from the .tex, not from the author's JSON. It then transports the table to all 3 labelled bowties × 31 contact sets by explicit automorphisms, and checks every final vector.

### 2.4 Grouped donors are adversarial

All grouped moves offer donors with b = 1 and branch on every donor. The certificates do not assume which donor Fan's lemma returns. In the A = T case, t₁ ∈ {a,b} and t₂ ∈ the other three give 6 branches, all checked (12 with both orders of s₁, s₂).

---

## 3. Computations

| Script (A11-scripts) | Checks | Output |
|---|---|---|
| `cert_check.py` | A: Table 2 + A = T, transported to 93 labelled cases. B: Lemmas 10–12 on all graphs on 5 labelled vertices, and Prop 13 on 38 rims. C: own exhaustive AND–OR search (bowtie on T; T + u; T + u + v; 41 cores × 31; 38 rims on T) | `partAB.out`, `partC.out` |
| `mutation_check.py` | each lemma hypothesis is necessary; A = T supplies 4, 3 | `mutation.out` |
| `exact.py` | own DFS solver: exact end vectors; floor with an end at y | library |
| `selftest_exact.py` | `exact.py` vs `tools/pathnum.py` (CP-SAT) on random graphs of order 5–7 | `selftest_exact.out` (308 agree, 9 CP-SAT time-outs skipped) |
| `random_replay.py` | end-to-end replay on 120 bowtie + 120 six-core random hosts; every node realised; global = local blanks | `random_replay.out` |
| `counterexamples.py` | first-draft G_t (t = 2, 4); order-5 example; L, D of Prop 9; exact census N = 5, 7 | `counterexamples.out` |
| `family_tt.py` | Prop 8 for eight (t, t′); the six N = 7, e = 5 failures | `family_tt.out` |
| `bowtie_no_uv.py` | Rem. 15(iii) without the (u, v) hypothesis: 11 connected order-7 bowtie graphs (none has a pair (u, v)), and 60 + 60 random hosts of orders 9, 11 with no pair; all satisfy the floor | `bowtie_no_uv.out` |

Author scripts re-run (non-independent): `verify_certs.py` and `bowtie_table.py` (exact match); `exact_prescribed.py` on conn5 (16 failures, 5 SET pairs at e = 3); `odd_fan_game.py` on conn5 and conn7 with kmax = 4 (7/14/0 and 130/230/64/0; 2,218 pairs tested, equal to my count).

**Census (own solver).**

| | e = 1 | e = 3 | e = 5 | e = 7 |
|---|---|---|---|---|
| N = 5, pairs | 7 | 30 | 5 | — |
| N = 5, no floor partition ending at y | 7 | 9 (5 in SET graphs) | 0 | — |
| N = 7, pairs | 130 | 1236 | 845 | 7 |
| N = 7, no floor partition ending at y | 130 | 101 (29 in SET graphs) | 6 | 0 |

`connections.md` E14 records the same N = 7 numbers.

---

## 4. Lean (statements only; not rebuilt)

Comparison with [BSP] §8:
- `okS`/`soundS` and `seed`/`floor_of_cert` are as described. `soundS` bounds the real blank count by the model count using `hb₀` (outside vertices have positive ends). This is the localisation argument of §2.1.
- `five_even_local` has these hypotheses:
  - ι injective onto the even vertices: `heven` with `hout`;
  - ι0 adjacent to the rest;
  - `hnu`: no other universal vertex, equivalent to rim max degree ≤ 2;
  - `hnb`: the rim is not a perfect matching.

  These are exactly Thm 1(a) for labelled rims. The conclusion is ∃ D, 2|D| + 1 = |V|.
- `five_even_bowtie`: ι : Fin 7 → V, `hmatch` (a perfect-matching rim), u ~ v odd, v ↛ T, u → T. This is Thm 1(b), floor only.
- `exists_uv` is Lemma 14. `five_even_floor` is the floor of Thm 1 for connected W with a leaf at an odd support.
- grep finds no `sorry`, `admit`, `native_decide` or `axiom`. The tables are checked with `decide +kernel`.

What is not formalized:
- the realisable-pair conclusion of Thm 1 (`okS` leaves are free); the text is now fixed to say "floor conclusion";
- Lemmas 10–12 as general statements (Lean checks `certgen.py`'s 38 labelled certificates instead);
- the BS case of Cor 2, Cor 16, Section 3.

---

## 5. Changes made to the .tex (recompiled twice with pdflatex, no warnings, 10 pp.)

1. **Prop 9 proof.** "Four is the parity bound for its four odd vertices" is replaced by the correct lower bound: four odd ends plus two forced even ends per triangle (Lemma 7), so at least 8 ends.
2. **§4, Thm 114 remark.** The tests "follow from" the floor bounds, by trimming as in MR §19. A new paragraph records the earlier Shaik-free routes (A6 F17, the corrigenda, Lemma 133, Thm 123) and states what is new.
3. **Remark 15(iii).** It now notes that the author's leafless random hosts usually still contain a pair (u, v), and reports the A11 test on hosts without one.
4. **Cor 16 proof.** "Every leaf support is odd" is replaced by "L has a leaf at an odd support, namely a private leaf at a mark".
5. **After Cor 17.** In the uses, FHZ Thm 5 is never needed. "What remains conditional" now names MR §2.1 p. 8 (Shaik Thm 1.1), which is unused.
6. **§8 Lean.** `five_even_local`, `five_even_bowtie` and `five_even_floor` are described as the *floor* conclusions. The realisable pair is not formalized.

## 6. Recommendations (not done; for the author)

1. Make `verify_certs.py` check that every leaf vector is 1 on u, v and (2,2,0,0,0) on T (B5).
2. Consider citing MR Lemma 133 and Thm 123 alongside Cor 2 in the final corrigendum for Thm 144, as independent confirmation. They give the same conclusion by a different (table-based) route.
3. In MR itself: replace the three Cor 106 citations in Thm 144 by Cor 2 (use 1) and BS (uses 2, 3). Replace "[25, Corollary 1.2]" at "r ∈ T" by BS Thm 13. Restate Cor 106 as Cor 16, and mark the §2.1 p. 8 remark as conditional on [25].
