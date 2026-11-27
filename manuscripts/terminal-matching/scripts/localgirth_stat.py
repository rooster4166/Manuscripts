"""How often does Corollary 7.2 (local girth form) apply?

Random 3-connected graphs J with degree sequence (4, 3, ..., 3) on n vertices (n odd), z the
vertex of degree 4.  For each of the three pairings {ab, cd} of N(z) with ab, cd not edges of J,
test the hypothesis of stl_of_localgirth / test1_of_localgirth: in J* = (J - z) + ab + cd no
cycle of length <= 4 passes through a, b, c or d, and c is reachable from a.  Compare with the
global form (J* of girth >= 5).

usage: localgirth_stat.py count seed n1 n2 ...     (prints one line per n)
"""
import sys, random, itertools
import networkx as nx


def short_cycle_through(G, S):
    """Is there a triangle or a 4-cycle of G through a vertex of S?"""
    for s in S:
        nb = set(G[s])
        for u, v in itertools.combinations(nb, 2):
            if G.has_edge(u, v):
                return True  # triangle s u v
            if len((set(G[u]) & set(G[v])) - {s}) > 0:
                return True  # 4-cycle s u w v
    return False


def girth_ge5(G):
    return not short_cycle_through(G, list(G))


def main():
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    for n in map(int, sys.argv[3:]):
        made = loc_any = glob_any = loc_pairs = glob_pairs = pairs = 0
        tries = 0
        while made < count and tries < 200 * count:
            tries += 1
            degs = [4] + [3] * (n - 1)
            G = nx.configuration_model(degs, seed=rng.randrange(1 << 30))
            G = nx.Graph(G)
            G.remove_edges_from(nx.selfloop_edges(G))
            if sorted(d for _, d in G.degree()) != sorted(degs):
                continue
            if nx.node_connectivity(G) < 3:
                continue
            made += 1
            z = [v for v in G if G.degree(v) == 4][0]
            a, b, c, d = sorted(G[z])
            ok_l = ok_g = False
            for (p, q), (r, s) in [((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c))]:
                if G.has_edge(p, q) or G.has_edge(r, s):
                    continue
                pairs += 1
                H = G.copy()
                H.remove_node(z)
                H.add_edge(p, q)
                H.add_edge(r, s)
                if not nx.has_path(H, p, r):
                    continue
                if not short_cycle_through(H, [p, q, r, s]):
                    loc_pairs += 1
                    ok_l = True
                    if girth_ge5(H):
                        glob_pairs += 1
                        ok_g = True
            loc_any += ok_l
            glob_any += ok_g
        print(f"n={n} graphs={made} pairings={pairs} local_ok_pairings={loc_pairs} "
              f"girth5_pairings={glob_pairs} graphs_local={loc_any} graphs_girth5={glob_any}",
              flush=True)


if __name__ == '__main__':
    main()
