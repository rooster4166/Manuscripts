# Exact statements cited in `near-dirac`

Quoted from the arXiv LaTeX sources (fetched 2026-11-27) and from the archive PDF `gallai/02-november-25/separating-pairs.pdf` (pdftotext).

## CKLOT: Csaba, Kühn, Lo, Osthus, Treglown, *Proof of the 1-factorization and Hamilton decomposition conjectures*, Mem. Amer. Math. Soc. 244 (2016), arXiv:1401.4159v2

Definitions (§1.3, LaTeX source):

> We say that $G$ is \emph{$\eps$-close to $K_{n/2,n/2}$} if there exists $A\subseteq V(G)$ with $|A|=\lfloor n/2\rfloor$ and such that $e(A)\le \eps n^{2}$. We say that $G$ is \emph{$\eps$-bipartite} if there exists $A\subseteq V(G)$ with $|A|=\lfloor n/2\rfloor$ such that $e(A), e(V(G)\setminus A) \le \eps n^{2}$.

> Here, a \emph{Hamilton decomposition} of a graph~$G$ consists of a set of edge-disjoint Hamilton cycles covering all edges of~$G$.

Theorem 1.3.5 (`\label{1factbip}`):

> There are $\eps_{\rm ex} >0$ and $n_0\in\mathbb{N}$ such that the following holds. Let $n\ge n_0$ and suppose that $D \ge (1/2-\eps_{\rm ex})n$ is even. Suppose that $G$ is a $D$-regular graph on $n$ vertices which is $\eps_{\rm ex}$-bipartite. Then $G$ has a Hamilton decomposition.

Hypotheses used: D even; D ≥ (1/2 − ε_ex)n; D-regular, simple; a part of size exactly ⌊n/2⌋; each part spans ≤ ε_ex n² edges. There is no upper bound on D, and no per-vertex condition.

Theorem 1.3.4 (`\label{undir_decomp}`, from Kühn–Osthus) is not used.

## GGKO: Girão, Granet, Kühn, Osthus, *Path and cycle decompositions of dense graphs*, J. London Math. Soc. 104 (2021) 1085–1134, arXiv:1911.05501v2

> we say an~$n$-vertex graph~$G$ is \emph{weakly-$(\varepsilon, p)$-quasirandom} if for any partition~$A\cup B$ of~$V(G)$ with $|A|, |B|\geq \varepsilon n$ we have $e_G(A, B)\geq p|A||B|$.

Theorem 1.11 (`\label{thm:Delta/2}`):

> For any~$\alpha,\delta, p>0$, there exists~$n_0$ such that if~$G$ is a weakly-$(\frac{\alpha}{2},p)$-quasirandom graph on~$n\geq n_0$ vertices with $\delta(G)\geq \alpha n$, then the following hold.
> (i) $G$ can be decomposed into at most~$\max\left\{ \frac{\odd(G)}{2},\frac{\Delta(G)}{2}\right\} +\delta n$ paths.
> (ii) If~$G$ is Eulerian, then it can be decomposed into at most~$\frac{\Delta(G)}{2} +\delta n$ cycles.

Theorem 1.10 (`\label{thm:n/2}`)(i): for any α, δ > 0 there is n_0 such that every graph on n ≥ n_0 vertices with δ(G) ≥ αn "can be decomposed into at most~$\frac{n}{2}+\delta n$ paths."

## SP: `separating-pairs.pdf` §14 (archive; statements copied from pdftotext)

The statements of Cor 14.24, Cor 14.26, Thm 14.27, Thm 14.37, Cor 14.38 and Cor 14.39 are reproduced verbatim in §2 of `near-dirac.tex`. Thm 14.30, Thm 14.31, Thm 14.33 and the counting obstruction in §14.18 ("The two auxiliary vertices and unequal shores") are described in §§1 and 7 of the manuscript and credited there. SP cites CKLOT as [17] and GGKO as [22].
