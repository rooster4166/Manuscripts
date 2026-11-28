# A39c: Audit of the A39b fix-up of dense-root (commit 2660c7e)

Date: 2026-11-28. Referee stance: adversarial. Scope: `git diff be56355 2660c7e` and the resulting
files. Grades: **ERROR** (false as stated); **GAP** (an omission that changes how a result reads;
fixable); **NIT** (wording or hygiene). "l." is a line of `manuscripts/dense-root/dense-root.tex` at
2660c7e. Scripts: `research/audit/A39c-scripts/` (`runs.sh` lists every command).

## 0. Verdict

**The fix-up is correct. No ERROR.** A39b F1 is applied at the right generality, the δ = 1 proof
does go through verbatim for Q = q₁ysq₂ and q₁syq₂, every number reproduces (shipped scripts and an
independent recount), and the Lean change is comments only, with a green build. One pre-existing
GAP (Table 1 runs off the page, hiding the column the fix updated) and five NITs.

- **Mathematics (Theorem 4.1, Cor. 4.2).** Sound; details in §1.
- **Lean.** Code byte-identical modulo comments in `DenseRoot.lean` and `DenseRootB.lean`
  (comment-stripped diff empty). `lake build`: "Build completed successfully (18436 jobs)", exit 0.
  Fresh `lake env lean` of both files: exit 0 (11 and 59 warnings, no errors). No `sorry`, `admit`,
  `native_decide`, `axiom`. `#print axioms`: standard three for all seven declarations. Unused
  binders still exactly `hjU` (`connector_core`) and `hy` (`..._mid`), as the new docstrings say.
  The 28 instances `A39b-scripts/len3_instances.lean` compile (18 s), all with the standard axioms.
- **Numbers.** All reproduce (§3).

## 1. Mathematics

Theorem 4.1 (l.254–271), its proof (l.273–308), Cor. 4.2 (l.310–315) and the remark after it (l.317–318).

| Claim | Check | Grade |
|---|---|---|
| "(The other interior vertices of Q are then s, so Q has length at most 2+δ.)" (l.257–258) | d_B(r) = 2k−2 = \|B\|−2 gives V(G) = N ∪ {s}; interior vertices other than y are not in N, so each is s, and a path has at most one; length ≤ 2 (δ=0), ≤ 3 (δ=1). The forms listed at l.281, l.285 are exhaustive. | SOUND |
| Trivial members off V(Q) | V(Q) ∩ N = {q₁,q₂} or {q₁,y,q₂} as before; s ∉ N is never an attachment or trivial member. Trivial members ⊆ N ∖ {q₁,y,q₂} = N ∖ V(Q). | SOUND |
| Far ends a, b, o(q₁), o(y) ∉ V(Q) | All are in N ∖ {q₁,q₂,y}: a = o(q₁) ≠ q₂ as P(q₁) ≠ P(q₂), and ≠ y as P(y) ends at o(y) ∉ {q₁,q₂}; likewise b; when o(y) = q₂, o(q₁) ∉ {y,q₂}; o(y) ∉ {q₁,q₂} by the case. So they are off V(Q) whether or not s ∈ V(Q). | SOUND |
| λ bounds the L-paths meeting V(Q) | v ∈ N lies on (d_{G'}(v)+1)/2 L-paths, s (even in G', no end) on d_{G'}(s)/2; both = ⌈d_{G'}(v)/2⌉; union bound over V(Q), now including s. | SOUND |
| Counting | h̃_t ranges over N ∖ V(Q), unchanged between q₁yq₂ and q₁ysq₂/q₁syq₂; partners are attachments in N ∖ V(Q); every trivial member has an own path; at most δ unpaired. Both bounds on \|J_S\| as stated. | SOUND |
| Cor. 4.2 new case (l.311): parity automatic | T = {q₁,q₂} ⊆ N (s ∈ Z); y ∈ G ∖ {q₁,q₂,s} ⊆ N ∩ Z is odd in G and loses two edges; q₁,q₂ even, lose one; s is not in N. Also checked at order 9 for every q₁–q₂ path with ≤ 1 interior N-vertex (`indep_cov.py`, assertion). "y ∈ N" is automatic in J − {z,r}. | SOUND |
| Abstract (iv) (l.45–49) | Equivalent to the hypotheses of Theorem 4.1 (A39b §1). | SOUND |

**Literal run of the new case** (`literal_len3.py`: A39's checker `literal_AB.py`, patched to
length-3 connectors). Every Lovász decomposition of G′, every tie-break of the attachment plan,
every S; checks no trivial member on Q, pairs disjoint and inside N ∖ V(Q), ≤ δ unpaired, ≤ λ
L-paths meeting V(Q), both |J_S| bounds, Hall, and the reassembled decomposition from scratch.
- Order 9: all 1,706 admissible length-3 connectors (the condition holds for one at 709 roots);
  348,710 Lovász decompositions, 696,322 plans; every reassembly verified; **0 violations**.
- Random B (A39's generator, length-3 connectors only): k = 5, 1,541 connectors (condition holds at
  588), 120,170 decompositions; k = 6, 893 (139), 12,842; k = 7, 505 (41), 676 (decomposition cap
  300, node cap 4·10⁵ per instance). **0 violations.**

## 2. Findings

**F1 (GAP; pre-existing, not introduced by 2660c7e). Table 1 runs off the page; the column the
fix updated is invisible in the PDF.** l.377–398; `dense-root.pdf` p. 7.
- The table is 110 pt overfull (LaTeX log; the same 110.14 pt at be56355). Rendered, the last column
  ("multi-token's unscheduled": 1,597 / 1,597 / 404 / n.c. / 1,068 / 1,472 / (119) / 1,528 / …)
  lies beyond the page edge: the header is cut at "multi-token's unsch" and none of its numbers is
  printed (`pdftotext` does not see them either).
- So the abstract's "1,472 of multi-token's 1,597" and §5's unscheduled counts have no visible source
  in the paper.
- *Fix:* shorten the long row labels (e.g. "MR Thm. 74 / 166 hypotheses", "method, every D, Φ separate
  (`drm -A -m 0`)"), use a `p{}` first column, or `\footnotesize`.

**F2 (NIT). "No connector" contradicts §4's definition of a connector.** l.403, l.528 (§8 item 2:
"No connector. At 24 order-9 roots there is no connector"), README l.51; also Table 1 l.386 "all
connectors".
- §4 (l.249–250) calls any q₁–q₂ path of G a connector (deleting its edges makes N odd). G = J − {z,r}
  is connected (J 3-connected), so every s ∈ Z root has connectors. At the 24 roots they all meet N
  in ≥ 2 interior vertices: the least such number is 2 at 23 roots and 3 at one (`indep_cov.py`).
- The old wording ("no short connector") was accurate; the new one is not. §5 l.403–404 explains what
  is meant, but §8 and the README do not.
- It also hides what the open case is: a connector with two interior N-vertices, which meets the
  obstruction of §8 item 1 (an L-path joining two interior N-vertices of connectors).
- *Fix:* "no admissible connector (every connector has ≥ 2 interior vertices in N)"; Table 1:
  "Theorem B, all admissible connectors (lengths 1–3)".

**F3 (NIT). §5 l.365–368 overstates A39's literal run for the new theorem.** "Audit A39 ran Theorems
A and B literally at every order-9 instance … with no violation." A39's `literal_AB.py`
(`connectors()`) enumerates connectors of length 1 or 2 only; it never ran q₁ysq₂ or q₁syq₂. The new
case is covered by the Lean proof, and by the A39c run above (0 violations).
- *Fix:* add "(connectors of length ≤ 2; length 3: audit A39c)" or similar.

**F4 (NIT). Remark 4.3, l.327–331, two small inaccuracies.**
- "which takes an arbitrary one from `exists_lovasz_connector`": true for δ = 1
  (`DenseRootB.lean` l.863); the δ = 0 proof obtains it from `lovasz_ends` inline (l.615; A39b F6).
  *Fix:* "from `lovasz_ends` (through `exists_lovasz_connector` for δ = 1)".
- "every side condition by `decide`": the t-range in `hstar` is first reduced to t = 3 by `omega`.
  Harmless; "closed by `decide`/`omega`".

**F5 (NIT). Stale descriptions in files the paper points to.**
- `scripts/coverage.py` l.4: "B1 = Theorem B with connectors of length <= 2"; `scripts/look.py` l.2:
  "noQ: … no connector of length <= 2"; `scripts/thm_cov.py` l.53: "extended: Theorem B with
  Q = q1 y q2". The code is right (lengths 1–3; §3); only the comments are stale.
- `research/audit/A39b-scripts/len3_instances.lean`, cited by Remark 4.3, says the 28 roots are "among
  the 52 … no connector of length ≤ 2 (§5, §8 item 2)". That is the superseded text; it is an audit
  record, so leave it, but the Remark could say "listed by A39b against the earlier version".

Not findings (checked and correct):
- `DenseRoot.lean` "Lemma 2.1" → "Lemma 2.2": correct (Definition 2.1 shares the counter; `.aux`
  gives lem:fam = 2.2, thm:hall = 2.3).
- `DenseRootB.lean` module header, `connector_core` and `exists_decomp_of_connector_mid` docstrings
  match the code (`jU`, `[jU.isSome]` in both floors, `hπdes`, `hπQ`; `hy`, `hjU` unused).
- Remark 4.3 otherwise: hypotheses (ends in N, `hQint`, exactly one y via `hy`/`hyr`/`hy1`/`hy2`,
  `hodd`, any λ ≥ Σ⌈d_{G'}/2⌉), existential conclusion: correct.
- The committed PDF matches the .tex (`pdftotext` of a fresh compile is identical).
- Proved / computed / conjectured labels: no overclaim beyond F3. Coverage numbers are computations
  of the hypotheses (Table 1 caption and §5 say so); the 28 length-3 roots are additionally Lean
  instances.

## 3. Numbers

Shipped scripts, from `manuscripts/dense-root/scripts/`:
- `coverage.py order9 …/J9_d6.g6`: roots 1,756; s ∈ Z 1,262; A 459; B0 838; B1 1,171; A|B1 1,630;
  MR74 24; MR166 111; MR any 123; A|B1|MR 1,686.
- `cov1597.py`: 1,597 roots; A 404; B 1,068; A|B 1,472; MR 119; all 1,528.
- `look.py`: noQ 16 + 5 + 2 + 1 = 24 (23 with ≤ 2 neighbours of r of degree 7); cond 36 (four),
  17 + 29 (five), 14 + 6 (six) = 102.
- `crosscheck.py`: A 459, B 1,171, 0 mismatches (§5's "no mismatch" still holds with length 3).

Independent (`indep_cov.py`: own graph6 parser, every q₁–q₂ path of any length, the Lean hypotheses
evaluated literally, parity checked not assumed): B 1,171 (1,143 with length ≤ 2); A ∪ B 1,630
(1,602); unscheduled A ∪ B 1,472 (1,445), B 1,068 (1,041); outside 126 = 24 + 102; the 24 at
distance 3 (21) and 4 (3), 23 sparse, each with a q₁–q₂ path of δ = 2 (23) or 3 (1); 28 roots need length 3 (all at distance 3, 27 unscheduled),
and they are exactly the 28 theorems of `len3_instances.lean`. Every admissible connector has ends
T and length ≤ 2 + δ.

Against the text: abstract l.51–52 (1,630; 1,472), Table 1 l.380–389 (1,171 / 1,068; 1,630 / 1,472;
1,686 / 1,528; 838; 24 / 111 (123); (119)), §5 l.401–409 (126; 24; 21; 3; 23; 102; 36, 17+29, 14+6),
§8 l.528 (24), Remark 4.3 (28), README l.34–38, l.51: **all agree.** Grep for 1,602, 1,445, 1,041,
1,658, 1,501, 154, 52, "length ≤ 2", "distance at most two", "short connector" in the .tex, README,
scripts and both Lean files: only l.418 ("Φ of … paths of length ≤ 2", residual runs; correct), the
README's "1,143 with connectors of length ≤ 2" (correct) and the docstrings of F5. `thm_cov.py`'s
length-3 loop (l.64–68) is right: y ranges over G ∖ {q₁,q₂,s} = N ∖ {q₁,q₂}, both orientations,
δ = 1, h̃ over N ∖ V(Q), λ over V(Q) including s.

## 4. What I ran

Every command is in `A39c-scripts/runs.sh`.
- `git diff be56355 2660c7e` (Lean, README, scripts; word diff of the .tex).
- `strip_lean_comments.py`: comment-stripped old/new Lean, diff empty for both files.
- `lake build` (18,436 jobs, exit 0); `lake env lean` on `DenseRoot.lean`, `DenseRootB.lean` (exit 0);
  A39b's `axioms.lean`, `unused_hyps.lean`, `len3_instances.lean` (exit 0, 28 × standard axioms).
- Shipped `coverage.py`, `cov1597.py`, `look.py`, `crosscheck.py`.
- `indep_cov.py` (writes `new28.txt`), compared with the theorem names of `len3_instances.lean`.
- `literal_len3.py J9`, and `rand` at k = 5, 6, 7.
- `pdflatex` ×2 of the .tex in scratch; `pdftotext` diff against the committed PDF (identical);
  overfull check at 2660c7e and be56355; page 7 rendered with `pdftoppm`.

I modified no file outside this report and `A39c-scripts/`, and committed nothing.
