# bs-prescribed: Corollary 106 without the unrefereed input

Manuscript `bs-prescribed.tex` (PDF alongside). Main results:

* **The prescribed-end version of Botler–Sambinelli Thm 13 is false.** Counterexamples exist at
  every odd order N ≥ 5, including the family G_{t,t'}. In G_{t,t'} the vertex y has degree 2,
  both its neighbours are odd, and the even subgraph is a matching plus y. This is the joining
  gadget's own configuration.
* **The joining gadget of connections §L fails** on an order-9 graph L that satisfies the floor
  bound.
* **What Cor 106 needs:** every use in MR has ≤ 5 unmarked even vertices.
* **Theorem 1:** odd order, exactly five even vertices, one universal vertex in the even subgraph.
  Then a 2-subset of the even vertices is realisable, so p ≤ (N−1)/2.
  * If the even subgraph is not a bowtie, no further hypothesis is needed.
  * For the bowtie, W needs adjacent odd u, v where u has a neighbour in T and v has none. A leaf
    at an odd support in a connected W supplies them.
  * The proof uses only Lovász and Fan.
* **Corrected Cor 106**, and **MR Thm 144 Shaik-free**.

## Scripts (`scripts/`)

| Script | Purpose |
|---|---|
| `certgen.py` | generates `certs_local.json` (38 labelled non-bowtie rims) and `certs_bowtie.json` (3 labelled bowties × 31 contact sets) |
| `verify_certs.py` | independent checker of both tables in the semantics of Lean's `Prog.ok` (expected output: `OK: 38 local certificates (46 leaves), 93 bowtie certificates (129 leaves)`) |
| `gen_lean.py` | writes `lean/GallaiLean/FiveEvenCerts.lean` from the tables |
| `bowtie_table.py` | Table 2 of the manuscript (11 orbit representatives with supply/blank counts) |
| `sevensite_cert.py` | re-derivation of audit A6's seven-site bank (all 7 cores × 31 contact sets) |
| `exact_prescribed.py` | exact census of the prescribed-end lemma (CP-SAT via `tools/pathnum.py`) |
| `odd_fan_game.py` | the Fan game at odd order, with an optional prescribed end |
| `sample_prescribed.py` | random sample at N = 9: game vs exact (`tools/pathnum2.py`) |
| `random_hosts.py` | end-to-end floor check on random hosts with the five-even cores |

Reproduce:

```
cd scripts
python3 certgen.py && python3 verify_certs.py
python3 gen_lean.py
python3 exact_prescribed.py ../../../data/conn7.g6       # slow (about 35 min)
python3 odd_fan_game.py ../../../data/conn7.g6 4 pres
python3 sample_prescribed.py 9 150 3 1
python3 random_hosts.py 11 40 leaf
```

## Lean

`lean/GallaiLean/FiveEven.lean` and `FiveEvenCerts.lean` contain `five_even_local` and
`five_even_bowtie`. They are sorry-free and use only the standard axioms.
