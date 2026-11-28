# Audit A43: Conjecture 31, the profile form PC, the block criterion and joint paths (session `claude/conj31`)

**Auditor:** independent audit agent, 2026-11-28. **Scope:** `manuscripts/conj31/conj31.tex` (and PDF),
`README.md`, `data/`, `scripts/`; `lean/GallaiLean/Conj31.lean`, `lean/GallaiLean/Conj31Up.lean` (scope
addition), and the first section of `lean/README.md`. I also read the cited parts of
`manuscripts/endpoint-structure` (EP) and `manuscripts/conj-r` (CR).
**Scripts and outputs:** `research/audit/A43-scripts/`. I edited no other file and made no commit.
Classes: ERROR = false statement; OVERCLAIM = status or claim stronger than supported; MINOR = wording,
precision or provenance.

## Verdict

| item | verdict | main finding |
|---|---|---|
| Lemma 2.2 (DB) | **OK** | Correct; Lean `degree_add_le_sum_of_realises` matches. |
| Lemma 2.4 (DBfail, parity slack) | **OK**, MINOR | Forward direction correct. The converse needs `b = 0` on `Z` (as literally stated, `Z` is any set off which `b ≥ 1`; counterexample below). Every use has `Z = Z(b)`. Lean proves a weaker forward direction (no "`b = 1` elsewhere"). |
| Lemma 2.5 (upward closure) | **OK** | Correct; `realisesProfile_up` matches (hypothesis `b(x) < d(x)`, equivalent under parity). |
| Thm 2.6 (PC with ≤ 1 zero) | **OK**, MINOR | Proof correct (Lovász `lovasz_ends`, EP leaf dictionary Lemma 5, EP Remark 32, upward closure). The Lean versions match the scope the paper states (no isolated vertex; one zero at even order); the status table omits "no isolated vertex". |
| Prop 2.7 (minimal profiles) | **OK** | (i), (ii) and the "PC iff (a) and (b)" are correct. |
| Abstract ll. 43–44: "PC reduces to the minimal profiles, that is, to … Ev∖{u,v} … for every pair" | **OVERCLAIM** | Prop 2.7 needs part (b), the (DB)-boundary configuration, where `m_Z` fails (DB) and `Ev∖{u,v}` is *not* realisable. The table and README state it correctly. |
| Prop 3.2 (PC ⇒ 31) | **OK** | Correct; `conj31_of_profileConj`, `ProfileConj`, `Conj31On` are faithful. |
| Moves CYC, EAR, SUP, TR, NEW, TRI, SPL, TW2, DOWN | **OK**, MINOR | Every realisation step and every output condition (2-connected, ≤ 2 zeros, zeros of positive even degree, `1 ≤ b ≤ d`, parity, (DB)) checks, including the EAR slack computation, the `r = 1` exclusion, the Fan counts and the Hall argument. No appended segment can close a cycle or revisit a vertex. TW2 is subsumed by SUP (it never fires); two wording slips. |
| Thm 5.11 (minimal counterexample is irreducible) | **OK** | The measure `|E| + Σb` drops under every move. |
| Thm 7.1 (gluing), both directions, `2·max ≤ M + t` | **OK**, MINOR | Correct; I re-proved that the pairing condition is exactly `M ≥ t` and `2·max ≤ M + t`. The closing sentence of the proof gives the wrong reason (the tree, not "two blocks share one vertex"). |
| Def 7.2 (BC), Cor 7.3 | **OK**, MINOR | Read literally ("block profiles as in Theorem 7.1", which are *realisable*) BC would be circular; the parity and `b_B ≤ d_B` conditions are not listed. `blockcrit.h` implements the intended reading. |
| Prop 8.1 (J), Conj 8.2 (P) | **OK**, MINOR | Proof correct. "Joined instance" is restricted to connected `F`, while CR's Conjecture J covers every instance; the proof does not use connectivity. |
| Lean (`Conj31.lean`, `Conj31Up.lean`) | **PASS**, MINOR | Both files compile with no errors; the full build is green (18,450 jobs); no `sorry`/`admit`/`axiom`/`native_decide`. `#print axioms` gives `propext, Classical.choice, Quot.sound` for all 16 theorems. Statements are faithful. Manuscript numbers in docstrings and README are off by one. |
| Computations | **PASS** | Every number I re-derived with my own code matches (table in §3): census n ≤ 8, Conjecture 31 for 2-connected n ≤ 8, PC (0, 1, 2 zeros) n ≤ 7, BC ⇔ tight n ≤ 8, Conjecture J at orders 6 and 8 including the (L)/(C)/(B) split, and irreducible instances n = 5, 6, 7 (identical lists at n = 5, 6). Order-10 samples agree: 5,709 graphs for BC; 563 for Conjecture 31; 106,985 joined J instances. |
| Witness checkers | **PASS**, MINOR | `wcheck31.py` and `jwcheck.py` check what they claim; they accept 3,470 valid witnesses from my solver and reject all 25,532 corruptions I made. The two-zero PC run (`pc_le8.txt`) records no witness check, unlike `pc_le1zero.txt`. |
| Status labels, README, Lean README, citations | **OK**, MINOR | Conjecture 31, PC, P and J are never claimed. One OVERCLAIM (above). Citations of EP use §5 for what is §6 (and EP numbers the conjecture 48). Several other wording points are MINOR. |

**Required fixes: 1** (one OVERCLAIM). **No ERROR, no gap in any proof.** 17 MINOR points (list in §5).

## 0. Versions audited

The author committed twice during the audit; I re-read every change.

| commit | content |
|---|---|
| `4f2c0a0` | start of the audit |
| `41d78f0` | `Conj31Up.lean`; Lean citations in Lemma 2.5, Thm 2.6 and the status table; README and Lean README |
| `f598e2d` | abstract sentence on J (ll. 54–56); new paragraph on the order-8 irreducible classes (ll. 457–461); `scripts/classify_irred.py`, `data/irreducible_classes.txt` |

Final files: `conj31.tex` `7d4c9669…`, `README.md` `f96137dc…`, `Conj31.lean` `17ba25f2…` (unchanged throughout),
`Conj31Up.lean` `7278933e…`, `lean/README.md` `067856f5…`. **Line numbers refer to `conj31.tex` at `f598e2d`.**

Compiled numbering (my pdflatex build, 9 pages, no undefined references, no overfull boxes; five
underfull hboxes): Def 2.1, Lemma 2.2 (DB), Def 2.3 (PC instance), Lemma 2.4 (DBfail), Lemma 2.5 (up),
Thm 2.6 (PC1), Prop 2.7 (min); Conj 3.1 (PC), Prop 3.2; Prop 4.1; Lemmas 5.1–5.9 (CYC, EAR, SUP, TR, NEW,
TRI, SPL, TW2, DOWN), Def 5.10, Thm 5.11; Thm 7.1 (glue), Def 7.2 (BC), Cor 7.3, Prop 7.4; Prop 8.1,
Conj 8.2 (P). **The committed `conj31.pdf` is from `41d78f0`.** It lacks the `f598e2d` changes (the
abstract sentence on J and the order-8 classification paragraph); rebuild it (M17).

## 1. The proofs

### 1.1 Lemma 2.2 (DB), ll. 138–144: OK
A path uses two edges at an interior visit and one at an end, and a path cannot have both ends at `x`.
So `d(x) + b(x) ≤ 2|D| = Σb`.

### 1.2 Lemma 2.4 (where (DB) fails), ll. 160–171: OK, MINOR
The slack `sl(x) = Σ_{y≠x} b(y) − d(x)` is even, because `Σb ≡ Σd ≡ 0` and `b(x) ≡ d(x)`. In (2.1) only
vertices of `Z` can contribute negatively, each at least −1, and `x ∉ N(x)`. So `sl(x) ≥ −2`, and `sl(x) < 0`
forces `sl(x) = −2`. Then `Z ⊆ N(x)` with `b = 0` on `Z`, `b = 1` on the other neighbours and no
non-neighbour. This also shows `x ∉ Z`.

- **MINOR (M1).** The "if" direction is false as literally stated, because `Z` is only a set outside which
  `b ≥ 1`. Example: `K₄` with `b ≡ 1`, any `Z` of size 2 and any `x` satisfy the right-hand side, but
  `d(x) + b(x) = 4 = Σb`, so (DB) holds. The converse needs `b = 0` on `Z`, i.e. `Z = Z(b)`. Every use
  (Conj 3.1 "Equivalently", the gloss in Def 7.2, Prop 2.7(ii)) has `Z = Z(b)`. Fix: "with `b ≥ 1` outside
  the zero set `Z`" or "`b = 0` on `Z`".
- **MINOR (M2).** l. 173: "Lean proves the forward direction". `universal_of_not_degreeBound` concludes
  `|Z| = 2 ∧ Z ⊆ N(x) ∧ ∀y≠x, x ∼ y`. That is enough for Prop 3.2, but it omits "`b(y) = 1` for
  `y ∉ Z ∪ {x}`". Say "Lean proves the forward direction without the last clause".

### 1.3 Lemma 2.5 (upward closure), ll. 175–183: OK
`d(x) = b(x) + 2·#(interior visits)`, so `b(x) < d(x)` gives a visit `AxB`, and splitting it adds two ends at
`x`. (DB) is preserved: at `x` both sides grow by 2, elsewhere only `Σb` grows. Lean `realisesProfile_up`
uses the hypothesis `b x < d x` (equivalent under parity, which realisability implies) and proves it via
`exists_interior` and `split_at_interior`.

### 1.4 Theorem 2.6 (PC with ≤ 1 zero), ll. 190–200: OK, MINOR
The exceptional vertex with `b = 0` has even degree by parity, so `Z ⊆ Ev`. `G^{Ev∖Z}` has at most one
vertex of positive even degree. `lovasz_ends` (Lovasz.lean l. 505) allows isolated vertices and gives
`ends = d mod 2`. EP Lemma 5 (leaf dictionary, EP §2) turns this into `Ev∖Z ∈ F(G)`, i.e. `m_Z` is
realisable. Its single-edge case (`s` left with no end, then split) is handled in EP's proof. At odd order
this uses EP Remark 32. Raising to `b` with Lemma 2.5 is valid because the current value stays below
`b(x) ≤ d(x)`.

Lean (scope addition):
- `realisesProfile_of_no_zero`: no isolated vertex, parity, `b ≤ d`, `b ≥ 1` everywhere. This is the
  zero-free case.
- `realisesProfile_of_one_zero`: no isolated vertex, even order, `z ∈ evenSet`, `b ≥ 1` off `z` (`b(z) ≥ 2`
  is also allowed). This is the one-zero case at even order.
- Both go through `realisesProfile_of_le` (strong induction on `Σ(b − m)`), from `realisable_evenSet'` and
  `realisable_evenSet_erase'`. These are unconditional (`lovaszStatement`).

So the Lean statements are the paper's statement restricted exactly as ll. 202–204 say.

- **MINOR (M3).** The status table (l. 111) says "Lean (one zero: even order)" and omits "no isolated vertex".
  The text after the theorem and both READMEs state it.
- **MINOR (M4).** l. 187: "By the leaf dictionary of [EP, §2], `m_Z` is realisable iff `Ev∖Z` is a realisable
  set". This equivalence is EP's *definition* of a realisable set. The leaf dictionary is what Thm 2.6 uses
  in its proof.

### 1.5 Proposition 2.7, ll. 206–228: OK
(i) holds because (DB) and realisability are both closed under `+2·1_x` (Lemma 2.5) and every profile with
zero set `Z` is `m_Z` plus even increments. (ii) is Lemma 2.4 with `b = m_Z`: the vertices with `m_Z = 1` are
the odd ones, and `x ∉ Z`. The "PC iff (a) and (b)" holds, with ≤ 1 zero covered by Thm 2.6. The remarks
after the proof cite results that exist: EP Thm 37 (second descent step), EP Cor 39 (E-twins), and Lean
`realisable_evenSet_erase_pair` and `etwin_of_not_realisable` (TwoEven.lean, even order, `LovaszStatement`
hypothesis). The section numbers are wrong (M15).

**OVERCLAIM (V1), abstract ll. 43–44.** "PC reduces to the minimal profiles, that is, to the second descent step
`Ev∖{u,v}` of [EP] for every pair." Prop 2.7 shows PC ⟺ (a) ∧ (b), where (b) is about the configuration of
(ii): there `m_Z` fails (DB) and `Ev∖{u,v}` is not realisable at all, and one must realise every *non-minimal*
profile satisfying (DB). (b) is not reduced to minimal profiles. Irreducible instances with non-minimal
profile exist: 3 of the 11 at order 6 (`EFzw`), and 93 of the 366 at order 8. "For every pair" is false
literally. The status table (l. 112, "minimal profiles and the (O1) boundary") and the README state it
correctly. Fix: "…to the minimal profiles, that is, to the second descent step `Ev∖{u,v}` for every pair
`u, v` off the (DB) boundary of Proposition 2.7(ii), together with that boundary configuration."

### 1.6 Proposition 3.2 (PC ⇒ Conjecture 31), ll. 241–248: OK
`b = d mod 2`, `Z = {u, v}`. If (DB) failed at `x`, Lemma 2.4 makes `x` adjacent to all others and `x ∉ Z`,
so `x` is odd. `n = |Od| + 2` is even, so `d(x) = n − 1` is odd: a universal odd vertex. The Lean proof does
the same through `degree_of_adj_all` and a parity count.

### 1.7 The moves, ll. 285–410: OK (all), MINOR
I re-did every realisation step and every output condition.

- **CYC.** `b = 2` off `Z`. With ≥ 2 non-zero vertices the arcs realise `b`. With one (the triangle with two
  zeros), (DB) fails at it.
- **EAR.**
  - *Realisation.* Inner segments become paths. An appended end segment has all its other vertices in the
    removed interior, so it cannot revisit a vertex of `B'`.
  - If `r ≥ 2`, the two appended segments are disjoint, so even when both are appended to the *same* path
    (one with ends `x₀, x_m`) the result `S₀⁻¹ P S_r` is a path.
  - If `r = 1`, they share the middle vertex, so they need different paths. A path never has both ends at
    one vertex, so `b'(x₀) ≥ 2` always leaves a second choice. The only failure is
    `b'(x₀) = b'(x_m) = 1`, which (since `δ_i = +1` there) means `x₀, x_m ∈ Z`; this is the case excluded.
  - *Conditions.* `b'(x_i) = 0` would need `b(x_i) = d(x_i) = 1`, impossible since `d(x_i) ≥ 3`. Zeros at
    `x_i` become `b' = 1` with `d' = d − 1` odd. `b' ≤ d'` and parity hold.
  - *(DB).* I re-derived the three requirements `sl(w) ≥ 2r − δ₀ − δ_m` and `sl(x₀) ≥ 2r − 1 − δ_m`
    (resp. `x_m`) and the lower bounds. The interior vertices with `b = 2` are non-neighbours of every
    `w ≠ x₀, x_m` (`+2` each). For `x₀`: `x₁` gives `+1` if `b(x₁) = 2`, or is counted among the ≤ 2 zeros.
    `x_m` gives `≥ 2` when `δ_m = −1` (`b = d ≥ 3`). This holds also for `m = 2`, where `x₁ = x_{m−1}`. The
    evenness of slacks closes the one-unit gap. The identities `2r − δ₀ − δ_m = 2r − 2 + 2e₀ + 2e_m` and
    `2r − 1 − δ_m = 2r − 2 + 2e_m` are right.
- **SUP.** Subdividing/suppressing preserves 2-connectivity when the result is simple (`x₀ ≁ x_m`) and
  `B` is not a cycle. Degrees, `Σb` and the zeros' degrees are unchanged. The interior vertices have no end,
  so subdividing the edge inside its path works.
- **TR.**
  - Fan's lemma (EP Lemma fan-b, `fan_single`) with `(a, b) = (y, x)` needs fewer than `b'(x) = b(x) + 1`
    end-free neighbours of `y` in `B − xy`. These are exactly `N_{B−xy}(y) ∩ Z'` (`x` is not a neighbour
    there, `y` not its own).
  - *Output.* A new zero `y` (`b(y) = 1`) has `d'(y) = d(y) − 1` even and ≥ 2. `x ∈ Z` becomes `b' = 1`.
    `b'(x) ≤ d'(x)` uses `b(x) ≤ d(x) − 2`. `Σb' = Σb`, and `d + b` drops by 2 at `y` and is unchanged
    elsewhere.
  - With `x ∈ Z` the condition is `y ≁ v`, which is `tight_of_transfer` (TwoEven.lean l. 590).
- **NEW.** New zeros `x` or `y` (`b = 1`) have positive even degree in `B − xy`. `Σ` drops by 2, `d + b` drops
  by 2 at `x, y`, and elsewhere (DB) is exactly `sl(w) ≥ 2`.
- **TRI.**
  - In `B − xy`, `u` has non-adjacent neighbours, and suppressing it gives `B − u`.
  - The end-free neighbours of `y` in `B − xy` are `u` and possibly `v` (`x` is not a neighbour in `B − xy`,
    and `y` itself does not count). So the count is `1 + [y ∼ v] ≤ b(x)` under the hypothesis, since
    `b(x) ≥ 1`.
  - *Output.* Zeros: `v` and possibly `y`, whose new degree `d(y) − 1` is even and ≥ 2. `b₁(x) ≤ d(x) − 1`.
    `Σ` and (DB) hold as stated.
- **SPL.**
  - No new zero can appear (that would need `b(y) = d(y) = 1`), so `Z(b') = Z ∖ N(x)`; the hypothesis
    `|Z(b')| ≤ 2` is automatic.
  - Appending `yx` to a path ending at `y` cannot revisit `x ∉ B − x`. Two edges appended to one path
    would close a cycle through `x`, hence the need for distinct paths.
  - Hall: every `y` with `b' = b + 1` has `b' ≥ 2`, except one zero with `b' = 1`
    (`|N(x) ∩ Z| ≤ 1`). Each path has ≤ 2 ends, so a set `S` meets at least `⌈(2|S| − 1)/2⌉ = |S|` paths.
  - Output conditions: `b' ≤ d'`, parity, `b' ≥ 1` off `Z ∖ N(x)`.
- **TW2.** `Z(b'') ⊆ {x, y}`. A zero `x` has `d'' = d − 1` even and ≥ 2. Subdividing `xy` by `u` and adding
  `xvy` gives `b`.
- **DOWN.** `b(x) − 2 ≥ 1` (no new zero) and `≤ d(x) − 2`, so Lemma 2.5 applies.

MINOR points:
- **M5.** TW2 is subsumed by SUP. Under TW2's hypotheses `u` is a degree-2 zero with non-adjacent neighbours.
  So `x u y` is a thread with interior in `Z` and `x ≁ y` (if `d(x) = 2` then `B = C₄`, which is CYC), and
  SUP applies. The data agree: TW2 fires 0 times in `irreducible.txt`. My check: 9, 52 and 778
  TW2-applicable instances at n = 5, 6, 7, all with SUP applicable (`a43_tw2.py`). So "TW2 settles `|N| = 2`
  with `x ≁ y`" (l. 469) is true but already done by SUP, which leaves one zero (then Thm 2.6 applies). And
  "for Conjecture 31 itself the only moves available are SUP, TRI and TR from a zero" (l. 426) literally
  omits TW2, which can apply to parity profiles. It is harmless because TW2 ⇒ SUP.
- **M6.** l. 292: "Each move below outputs a PC instance … with fewer edges". DOWN keeps the edges (and
  CYC has no output). Thm 5.11's proof states it correctly.

### 1.8 Theorem 5.11, ll. 415–423: OK
`|E| + Σb` decreases strictly. EAR removes `m ≥ 2` edges with `Σb' ≤ Σb`. SUP removes 1 or 2 edges. TR, NEW and
TRI remove 1, 1 and 2 edges. SPL removes `d(x)` edges with `Σb' ≤ Σb`. TW2 has net −3 edges. DOWN gives
`Σ − 2`. Each output is a PC instance with (DB) (§1.7), so it is realisable by minimality.

### 1.9 Theorem 7.1 (gluing), ll. 474–493: OK, MINOR
- *Restriction.* A path that left a block `B` at `c` and re-entered it at `c' ≠ c` would close a cycle
  through vertices outside `B`, contradicting maximality; `c' = c` is a revisit. Ends of `D_B` at `c` are
  either ends of `D` with end edge in `B` (≤ `t(c)`) or passes of `D` through `c` between `B` and another
  block (≤ `g_c`). This gives `M_c = t(c) + 2g_c` and `2b_B(c) ≤ M_c + t(c)`.
- *Gluing.* With sizes `a_B = b_B(c)` and `h = (M − t)/2` (parity holds automatically), a choice of kept ends
  with a valid cross-block pairing exists iff `Σ_B min(a_B, h) ≥ 2h`. I checked that this is equivalent to
  `M ≥ t` and `2·max a_B ≤ M + t`, in both cases `a₂ ≤ h` and `a₂ > h`.
- Paired pieces form chains whose blocks follow a non-backtracking walk in the block-cut tree: consecutive
  pieces are in different blocks, and a piece has two distinct ends. So no block, cut vertex or vertex
  repeats, and no chain closes up. A vertex shared by pieces in non-consecutive blocks would put both blocks
  at one cut vertex, which the walk would have to pass through.
- **MINOR (M7).** The proof's last sentence attributes this to "two blocks share at most one vertex". The
  operative reason is the tree. Also, for "any graph", isolated vertices need `t = 0` (or count `K₁` as a
  block); in every use `t ≤ d`.

### 1.10 Definition 7.2 (BC), Corollary 7.3, ll. 496–506: OK, MINOR
**M8.** "block profiles as in Theorem 7.1 exist" literally means *realisable* block profiles, which would make
Cor 7.3 trivial and BC not explicit. The intended reading is: profiles `b_B` with `b_B(x) = t(x)` at non-cut
vertices, `b_B(c) ≡ d_B(c)` and `0 ≤ b_B(c) ≤ d_B(c)` at cut vertices, and the two gluing inequalities. That
is what `blockcrit.h` implements and what Cor 7.3 needs, since PC applies only to PC instances. State it.
Cor 7.3 is correct in both directions. The converse "without the bound on zeros" is right (Lemma 2.2 on each
block). Under the intended definition the BC descriptions of (O1), (O2) and (O3) (ll. 508–511) are correct; I
checked (O2) and (O3) by hand against EP Prop 47.

### 1.11 Proposition 8.1 and Conjecture 8.2, ll. 525–548: OK, MINOR
(L): `K₀` has ≤ 1 even vertex, so Lovász applies (any graph, `lovasz_ends`). (B): Cor 7.3. Then `D₀ ∪ {P}`
has `Q(c₁) = Q(c₂) = P`, and `P` avoids `a₁, a₂`. (C) ⊆ (B): a single block with zeros `c₁, c₂`, where by
Lemma 2.4 (DB) fails only at a universal vertex outside `Z`, i.e. a universal odd vertex.

- **MINOR (M9).** l. 525 defines a joined instance with `F` connected, but CR's instances (CR §1) and
  Conjecture J (CR Conj 5.1) allow disconnected `F`. So "PC ∧ P ⇒ J" (abstract l. 57, table l. 123, l. 551) is
  proved only for connected `F`. The proof of Prop 8.1 never uses connectivity. Drop "and connected" from
  the definition used by Conjecture P (its data scope stays connected `F`), or say "J for connected `F`".
- **MINOR (M10).** l. 566: "every vertex of degree `n − 1` in `F` lies on `P`" holds for every `P` whose
  remainder satisfies (DB) (e.g. BC or tight), not for every joint `P`. Also, the cited statement is in CR §4
  ("The obstruction to tightness"), not §5.

The rest of "Towards Conjecture P" is correct. Cut vertices with `t = 1` and block values in `{1, 2}` satisfy
`M ≥ 1` and `2·max ≤ M + 1`. With those values every failing block must contain both `c₁` and `c₂` as zeros.

### 1.12 Sections 6 and 8, remarks
- **MINOR (M11).** l. 447: "With ≤ 1 zero there is no irreducible instance … (as it must be by Theorem 2.6…)".
  Thm 2.6 is about realisability; irreducibility is about which moves apply. (At two zeros there are
  irreducible instances although all are realisable.) Use "consistent with".
- **MINOR (M12).** ll. 459–460, new paragraph: "181, 11 and 1 graphs with 4, 6 and 8 even vertices". These are
  instances; the 181 lie on 166 distinct graphs. The 69 two-even ones are 69 graphs, since `Z` is then forced.
  All other numbers in the paragraph match `data/irreducible_classes.txt`. `classify_irred.py` reproduces
  that file from `irreducible.txt`. My own classification of my n ≤ 7 lists equals its n ≤ 7 rows.
- The non-twin irreducible instances without DOWN (`EEhw`, `FCpdg`, `FCpfg`, ``FCZ\w``) are exactly my
  non-twin ones at orders 6 and 7. All have both zeros of degree 2 on triangles at a vertex `x` with
  `b(x) = d(x)` adjacent to both zeros, and `B − x` is not 2-connected, as l. 449–452 says.

## 2. Lean

- `lake env lean GallaiLean/Conj31.lean` and `…/Conj31Up.lean` give 0 errors. Warnings: deprecated
  `if_pos`/`if_neg`, and unused section variables in `realisesProfile_newPath`.
- `lake build`: "Build completed successfully (18450 jobs)", matching `data/build.txt` and the README.
- No `sorry`, `admit`, `axiom` or `native_decide` in either file.
- `#print axioms` (`A43-scripts/A43Axioms.lean`, `.out`) gives `[propext, Classical.choice, Quot.sound]` for
  all 16 theorems. These are the 15 in `data/axioms.txt`, plus `sum_profile_mod_two`.

Statement checks:

| Lean | manuscript | verdict |
|---|---|---|
| `RealisesProfile`, `tight_iff_realisesProfile` | Def 2.1; l. 136 | faithful (any graph) |
| `degree_add_le_sum_of_realises` | Lemma 2.2 | faithful |
| `universal_of_not_degreeBound` | Lemma 2.4, ⇒ | weaker conclusion (M2); hypotheses more general (`Z` arbitrary, no `b ≤ d`) |
| `realisesProfile_transfer` | Lemma 5.4, realisation step | **orientation correct.** `a = y` gains an end, `c = x` loses one; the count is over end-free neighbours of the gaining vertex `y` in `G − ac` and must be `< b'(x)`, exactly "fewer than `b'(x) = b(x) + 1` neighbours of `y` in `B − xy` have no end". |
| `realisesProfile_newPath` | Lemma 5.5 | faithful |
| `realisesProfile_suppress` | Lemma 5.3, one-vertex case | faithful; two-vertex case is two applications, as stated |
| `realisesProfile_tri` | Lemma 5.6, realisation step | **the hypothesis is about `B − xy`** (`delEdge G y x`), with `b₁` the profile of `B − u` (`u` isolated, so `b₁(u) = 0` is forced and `u` is counted), as in the proof (l. 381–383). The conclusion moves an end from `x` to `y`, matching `b = b₁ − 1_x + 1_y`. |
| `ProfileConj` | Conj 3.1 | faithful (`Z` with `b = 0` on `Z`, `b ≥ 1` off `Z` forces `Z = Z(b)`; zeros have even degree by parity and positive degree by `TwoConnected`) |
| `Conj31On` | Conj 1.1 | faithful (the extra hypothesis `∀w, 0 < d(w)` follows from `TwoConnected`; "no odd `w` with `d(w) + 1 = n`") |
| `conj31_of_profileConj` | Prop 3.2 | faithful, same vertex type |
| `realisesProfile_up`, `realisesProfile_of_le` | Lemma 2.5, raising step | faithful |
| `realisesProfile_of_no_zero`, `_of_one_zero` | Thm 2.6 | faithful to the restricted scope stated at ll. 202–204 (§1.4) |

`TwoConnected` (`MarkedBlocks.lean`) = ≥ 3 vertices, connected, no cut vertex, which matches the manuscript.
- **MINOR (M13).** The manuscript numbers in Lean docstrings, the Lean README and the data headers predate
  Def 2.3 and are off by one:
  - `Conj31.lean` ll. 14 and 74 ("Lemma 2.3", should be 2.4) and l. 19 ("Section 4", should be 5);
  - `Conj31Up.lean` ll. 7, 88, 140 and 167 ("Lemma 2.4 / Theorem 2.5", should be 2.5 / 2.6);
  - `lean/README.md` l. 9 ("Lemma 2.3", should be 2.4);
  - `data/pc_le1zero.txt` l. 2 ("Lemma 2.3", should be 2.4);
  - `data/irreducible.txt` l. 2 ("DOWN (Lemma 2.4)", should be Lemma 5.9).

## 3. Computations, re-derived

My code shares nothing with `scripts/`. `a43.c` is a transition-system search: at each vertex `b(x)` edges
are left as ends and the rest are paired, with a union-find of fragments (vertex sets) that forbids closing a
cycle or repeating a vertex. It is complete, and it rebuilds and re-checks every witness. It has its own
graph6 decoder. Its block decomposition uses "same block iff the remaining endpoints are in one component of
`G − x` for every `x`", and it has its own BC. `a43_irred.py` implements the moves from the manuscript text.
The census at n ≤ 8 used **no** (DB) pruning, so the (O1) non-tightness is re-derived by exhaustive search.
The PC run at n = 7 and the order-10 samples skip (DB)-failing profiles, which is sound by Lemma 2.2.

| claim | manuscript / data | mine | file |
|---|---|---|---|
| (a) census, connected two-even | n = 4: 3, 2 not tight; n = 6: 47, 17; n = 8: 2,668, 372 (344 O1 + 28 cut) | identical (n = 5, 7: none) | `census_bc_le8.out` |
| (b) Conjecture 31, 2-connected, n ≤ 8 | holds | 2-connected two-even graphs: 1 / 20 / 1,466 at n = 4/6/8; non-tight 1 / 10 / 274, all (O1); 0 non-O1 non-tight | `census_bc_le8.out` |
| (c) PC, two zeros: profiles / with (DB) / realisable | n = 4: 10/7/7; 5: 199/187/187; 6: 2,854/2,808/2,808; 7: 110,865/110,691/110,691 | identical; 0 realisable profiles without (DB); Lemma 2.4 characterisation 0 mismatches | `pc_le6.out`, `pc_n7.out` |
| (c′) PC, one zero / no zero, n = 4..7 | 12, 257, 3,960, 145,714 / 21, 149, 3,643, 89,224 | identical, all realisable | same |
| (d) BC ⇔ tight, n ≤ 8 | n = 4: 1/2; 6: 30/17; 8: 2,296/372; 0 disagreements | identical, 0 disagreements | `census_bc_le8.out` |
| (e) Conjecture J, order 6 | 13 graphs, 428 instances, 374 joined; (L) 204, (C) 94, (B) only 76, none 0 | identical | `conjJ_68.out` |
| (e) Conjecture J, order 8 | 224, 43,400, 40,538; 12,176 / 14,435 / 13,927 / 0; (L)+(C) = 26,611 | identical | `conjJ_68.out` |
| (f) irreducible, two zeros (without DOWN; with DOWN; minimal profile) | n = 5: 4 (4 twin); 2 (2); 2. n = 6: 43 (42); 11 (11); 8. n = 7: 220 (217); 34 (34); 34 | identical, per-move counts too; the n = 5, 6 lists with DOWN are identical line by line; ≤ 1 zero: none at n ≤ 6 | `irred_le6.out`, `irred_n7.out`, `irred_down_le7.out` |

More checks:
- The (L)/(C) split in the table is "the first path found" in `jcert`'s DFS order. At orders 6 and 8 it equals
  the order-independent "some joint path has a leaf end" (204; 12,176).
- The abstract's "a 2-connected remainder (or a leaf end)" omits "without a universal odd vertex". At order 8
  this does not matter: allowing a universal vertex still gives 26,611.
- At orders 6 and 8 *every* joint path whose remainder has a leaf end or satisfies BC has a tight remainder
  (562 and 231,882 paths, all solved exactly; `conjJ_68_all.out`). So the new abstract clause "every such
  remainder is tight" holds there in its strong reading.
- At orders 6 and 8 every joined instance has a joint path whose remainder satisfies BC itself, counting the
  (L) paths (374; 40,538).

Order-10 samples (not reruns):
- **BC ⇔ tight:** `nauty-geng -cq 10 7/2000` gives 49,322 graphs, of which 5,709 are two-even. 5,440 are tight
  and BC; 269 are not tight and not BC (149 O1, 120 non-O1 with a cut vertex); 0 disagreements. Among them,
  351 are 2-connected, and their 60 non-tight ones are all (O1). (`sample10_bc.out`)
- **Conjecture J:** `nauty-geng -cq 10 3/200` gives 151 all-odd graphs. They carry 112,064 instances, of which
  106,985 are joined. Every joined instance is certified: (L)/(C) first 58,959, (B) only 48,026, none 0. For
  every instance the certified remainder was solved by my solver and is tight (106,985 witnesses).
  (`sample10_J.out`; in this fast mode the "some (L) path" and "(L) or 2-connected" lines record only the
  first path found.)
- **Conjecture 31:** `nauty-geng -Cq 10 r/1000` for r = 17 and 777 gives 4,491 2-connected graphs, of which
  563 are two-even. 75 are (O1); my solver proved the other 488 tight, with witnesses rebuilt and checked.
  BC agrees on all 563. Run with `db limit=2e7` and restarts from every start vertex; no solve was left
  undecided. (`sample10_conj31b.out`; `sample10_conj31.out` is a smaller sample with 4 graphs.)

**Witness checkers.** `wcheck31.py` decodes graph6 itself and checks, per line: simple paths, edges of `G`,
edge-disjoint, covering, end profile equal to `d mod 2` (or to the `b=` target). `jwcheck.py` checks: `P`
from `c₁` to `c₂` avoiding `a₁, a₂`; four distinct vertices; `F` all odd; `cᵢ ≁ aᵢ`; and `{P} ∪ D₀` a path
decomposition with exactly one end everywhere, hence a Lovász decomposition with `Q(c₁) = Q(c₂) = P`. Both
check what the manuscript says they check.

`a43_wtest.py` fed them witnesses from my solver: 31 tight, 3,065 profile and 374 joint witnesses, all
accepted. It also fed 186 + 23,784 + 1,562 corruptions, all rejected (`wtest.out`). The corruptions were: a
dropped, duplicated or split path; a closed cycle; a merge at a common end; a changed end vertex; a
one-vertex path; a wrong target; a reversed `P`; swapped pairs; `a₁` on `P`.

Limits (MINOR M14):
- They check witnesses, not completeness. Nothing checks that the witness file lists exactly the 799,993
  graphs, other than the matching count.
- They rely on `assert`, which `python -O` disables.
- `data/pc_le8.txt` (two zeros, 6.85M realisations) has no "checked … witnesses" line, unlike
  `pc_le1zero.txt`. Yet l. 267 says "Every realisation was checked by `wcheck31.py`".
- §9 (l. 582) lists as the only exception "the tight answers for non-2-connected graphs in Prop 7.4". The
  tight answers of `census_le8.txt` and the n ≤ 8 rows of `bc_census.txt` have no recorded witness check
  either. My solver re-derived and re-checked them at n ≤ 8, and PC at n ≤ 7, so the facts stand. Only the
  record is missing.

`psolve.h`'s pruning (l. 270–271) is sound: (DB) per component of the remaining edges, the parity
`rd − re` even, and failed-state memo keyed exactly on remaining edges plus remaining ends (4 bits per
vertex, enough for degree ≤ 15).

## 4. Status, wording, citations

- Abstract, intro, status table, README and Lean README never claim Conjecture 31, PC, P or J. Proved,
  computed and conjectured are labelled, with one OVERCLAIM (V1).
- **MINOR (M15), citations of EP.** In EP as compiled, the two-even problem is §6, not §5:
  - "Tight graphs" is §6.1 and the second step is §6.4 (Thm 37);
  - E-twins are Cor 39; the obstructions, census and the conjecture are §6.8 (Prop 47, Conj 48);
  - "at every order" is Remark 32 in §6.

  The manuscript cites "[EP, §5]" at ll. 198, 226, 228, 274, 365 and 508; at l. 68 §5 is defensible. "Conjecture
  31 of [EP]" (ll. 32, 72) is the project's established name (also in `ln.tex`, `conj-r.tex` and
  `connections.md`), but EP itself numbers it Conjecture 48; say "Conjecture 31 of the project
  (Conjecture 48 of [EP])". All cited results exist and say what is claimed: leaf dictionary Lemma 5 (§2),
  Remark 32, Thm 37, Cor 39, Prop 47, Conj 48, EP §8 "85 random graphs" and CP-SAT. CR §5 (Conj J and its
  equivalent form) is correct; for l. 566 see M10.
- **MINOR (M16), the abstract and intro on J.**
  - "Conjecture 31 alone cannot give J" (l. 53) and "Conjecture 31 alone is not enough" (l. 96–97) assert a
    non-implication. What is shown is that applying it to the remainder of a joint path covers only 26,611 of
    40,538 at order 8; l. 558 says this precisely.
  - "every such remainder is tight" (l. 56): at order 10 only the remainder of the path found was solved
    (`jcert` solves the first certified `P`). Say so. My check of all such paths covers orders 6 and 8 only.
- **MINOR (M17), smaller items.**
  - The abstract's "Reduction (proved)" bullet contains the computed 413/11, and the "Conjecture J
    (computed)" bullet ends with a proved implication.
  - "Four of them are in Lean" (l. 47): only the realisation step, as the table says.
  - The status table row for the paper-only moves omits DOWN (the README lists it).
  - "(O1) boundary" (l. 112) also covers Prop 2.7(ii) with `x` even, which is not (O1).
  - The README contents table lacks `scripts/classify_irred.py` and `data/irreducible_classes.txt`.
  - l. 66–68: when `d_F(cᵢ) = 1`, `F − E(P)` has fewer than two even vertices.
  - The committed `conj31.pdf` was not rebuilt after `f598e2d`.

Numbers against data files: every count in the abstract, §3, §4, §6, Prop 7.4, §8 and both READMEs equals the
data (all shard sums re-added). Examples: 6,849,521 = 7 + 187 + 2,808 + 110,691 + 6,735,828; 14,297,554;
413 = 2 + 11 + 34 + 366 with 402 twin; 26,611; 14,890,194; and 1,114,873 = 1,071,515 + 43,358.

## 5. Findings

**ERROR:** none.

**OVERCLAIM (1):**
- **V1** Abstract ll. 43–44: "PC reduces to the minimal profiles, that is, to `Ev∖{u,v}` for every pair". Prop
  2.7 also needs the (DB)-boundary configuration (b), where `Ev∖{u,v}` is not realisable and non-minimal
  profiles must be realised. Fix in §1.5.

**MINOR (17):**
- M1 Lemma 2.4 "iff" needs `b = 0` on `Z`;
- M2 Lean forward direction is weaker than stated;
- M3 table omits "no isolated vertex" for the Lean PC1;
- M4 "by the leaf dictionary" should be "by definition";
- M5 TW2 subsumed by SUP; l. 426 omits TW2;
- M6 "fewer edges" for DOWN;
- M7 gluing proof's last sentence; isolated vertices;
- M8 Def 7.2 wording (realisable vs. gluing conditions; parity, `≤ d`);
- M9 J only for connected `F`;
- M10 degree-`(n−1)` vertices lie on every *working* `P`; CR §4 not §5;
- M11 "as it must be by Thm 2.6";
- M12 "graphs" should be "instances" (181 on 166 graphs);
- M13 off-by-one manuscript numbers in Lean and data headers;
- M14 witness-check provenance (two-zero PC, n ≤ 8 tight answers), no completeness check, `assert`;
- M15 EP §5 should be §6, Conjecture 48;
- M16 "cannot give J", "every such remainder";
- M17 label mixing, "four in Lean", DOWN missing from table, "(O1) boundary", README contents, l. 66, stale
  PDF.

## 6. Reproduce

    cd research/audit/A43-scripts; gcc -O2 -o a43 a43.c
    for k in 4 5 6 7 8; do nauty-geng -cq $k | ./a43 census; done             # (a), (b), (d)
    for z in 2 1 0; do nauty-geng -Cq 6 | ./a43 pc $z; nauty-geng -Cq 7 | ./a43 pc $z db; done   # (c)
    nauty-geng -cq 8 | ./a43 j all                                             # (e)
    for k in 5 6 7; do nauty-geng -Cq $k | python3 a43_irred.py down; done     # (f)
    nauty-geng -Cq 7 | python3 a43_tw2.py                                       # TW2 vs SUP
    ./a43 ... w  (witness lines) ; python3 -I a43_wtest.py ../../../manuscripts/conj31/scripts tight.w prof.w joint.w

The n ≤ 8 census in `census_bc_le8.out` was run with an earlier build of `a43.c` that ordered vertices by BFS.
The current build orders them by maximum cardinality search, and gives identical n ≤ 8 counts (checked with
`db`). The optional `limit=N` caps the nodes per attempt and retries from every start vertex. It is used
only for the order-10 Conjecture 31 sample, where no solve was left undecided. Without `limit` the search is
complete, so every "not tight" answer at n ≤ 8 is exhaustive.
