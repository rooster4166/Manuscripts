"""Independent brute-force check of pee.c (no shared code).

A path decomposition is the same as a transition system: at every vertex v, a partial matching of
the edges at v (paired edges are consecutive on a path through v; unpaired edges end a path at
v), such that following the transitions gives no closed trail and no trail that repeats a vertex.
In a Lovász decomposition the matching at v leaves exactly (deg v mod 2) edges unpaired, and the
terminal edge at an odd vertex x is its unpaired edge.

For every graph read (graph6) with at most one vertex of positive even degree and at most CAP
transition systems, this enumerates all of them and prints, for each odd x of degree >= 3, the
set of edges that occur as terminal edges at x.  Then compares with `pee ed`.
"""
import sys, itertools, subprocess, os
import networkx as nx

CAP = 2_000_000
HERE = os.path.dirname(os.path.abspath(__file__))


def matchings(items):
    """all perfect matchings (even) or near-perfect matchings (odd) of a list, as (pairs, single)"""
    if not items:
        yield [], None
        return
    if len(items) % 2 == 1:
        for i, s in enumerate(items):
            rest = items[:i] + items[i + 1:]
            for pm, _ in matchings(rest):
                yield pm, s
        return
    a = items[0]
    for i in range(1, len(items)):
        b = items[i]
        rest = items[1:i] + items[i + 1:]
        for pm, _ in matchings(rest):
            yield [(a, b)] + pm, None


def valid(G, trans):
    """trans[v] = dict edge->paired edge at v.  Check all trails are paths."""
    seen = set()
    for (u, v) in G.edges():
        e = frozenset((u, v))
        if e in seen:
            continue
        # walk to one end of the trail
        # start from edge e, go towards v repeatedly until unpaired
        cur_e, cur_v = e, v
        steps = 0
        while True:
            nxt = trans[cur_v].get(cur_e)
            if nxt is None:
                break
            (w,) = tuple(nxt - {cur_v})
            cur_e, cur_v = nxt, w
            steps += 1
            if steps > G.number_of_edges():
                return False  # closed trail
        # now cur_v is an end, cur_e the terminal edge; walk the other way collecting vertices
        start = cur_v
        verts = [start]
        e2, v2 = cur_e, (tuple(cur_e - {start})[0])
        while True:
            seen.add(e2)
            verts.append(v2)
            nxt = trans[v2].get(e2)
            if nxt is None:
                break
            (w,) = tuple(nxt - {v2})
            e2, v2 = nxt, w
        if len(set(verts)) != len(verts):
            return False
    return True


def terminal_sets(G):
    V = list(G.nodes())
    per = []
    total = 1
    for v in V:
        inc = [frozenset((v, w)) for w in G[v]]
        ms = list(matchings(inc))
        per.append(ms)
        total *= len(ms)
        if total > CAP:
            return None
    res = {v: set() for v in V if G.degree(v) % 2 == 1}
    count = 0
    for combo in itertools.product(*per):
        trans = {}
        for v, (pm, s) in zip(V, combo):
            d = {}
            for a, b in pm:
                d[a] = b
                d[b] = a
            trans[v] = d
        if valid(G, trans):
            count += 1
            for v, (pm, s) in zip(V, combo):
                if s is not None:
                    (w,) = tuple(s - {v})
                    res[v].add(w)
    return res, count


def main():
    p = subprocess.Popen([os.path.join(HERE, "pee"), "ed"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    ngraphs = nq = disagree = skipped = 0
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        G = nx.from_graph6_bytes(line.encode())
        ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
        if len(ev) > 1:
            continue
        r = terminal_sets(G)
        if r is None:
            skipped += 1
            continue
        res, count = r
        assert count > 0, "Lovasz decomposition must exist"
        ngraphs += 1
        E = list(G.edges())
        for x in res:
            if G.degree(x) < 3:
                continue
            for y in G[x]:
                s = f"{G.number_of_nodes()} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + f" {x} {y}\n"
                p.stdin.write(s); p.stdin.flush()
                ans = int(p.stdout.readline())
                bf = 1 if y in res[x] else 0
                nq += 1
                if ans != bf:
                    disagree += 1
                    print("DISAGREE", line, x, y, ans, bf, flush=True)
    print(f"graphs={ngraphs} queries={nq} disagreements={disagree} skipped(>CAP)={skipped}")


if __name__ == "__main__":
    main()
