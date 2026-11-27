"""ham_frac.py g6 r ...: for a root of degree n-2, enumerate all Lovasz decompositions of B - r
(own Python enumeration) and count how many contain a Hamiltonian path of B - r (length n - 2),
and the distribution of path lengths."""
import sys
from collections import Counter

sys.path.insert(0, __import__("os").path.dirname(__file__))
from g6 import parse_g6  # noqa: E402


def lovasz_decomps(n, adj, r):
    N = set(adj[r])
    R = {v: set(adj[v]) - {r} for v in range(n) if v != r}
    ends = set()
    cur = []

    def rec():
        open_ = sorted(N - ends)
        if not open_:
            if all(not R[v] for v in R):
                yield list(cur)
            return
        x = open_[0]
        path = [x]
        vis = {x}

        def ext():
            c = path[-1]
            if len(path) > 1 and c in N and c not in ends:
                ends.update((x, c))
                for u, v in zip(path, path[1:]):
                    R[u].discard(v); R[v].discard(u)
                cur.append(list(path))
                yield from rec()
                cur.pop()
                for u, v in zip(path, path[1:]):
                    R[u].add(v); R[v].add(u)
                ends.difference_update((x, c))
            for w in sorted(R[c]):
                if w in vis:
                    continue
                path.append(w); vis.add(w)
                yield from ext()
                path.pop(); vis.discard(w)

        yield from ext()

    yield from rec()


def main():
    for i in range(1, len(sys.argv), 2):
        g, r = sys.argv[i], int(sys.argv[i + 1])
        n, adj = parse_g6(g)
        tot = ham = 0
        lens = Counter()
        for D in lovasz_decomps(n, adj, r):
            tot += 1
            L = sorted(len(P) - 1 for P in D)
            lens[tuple(L)] += 1
            ham += any(l == n - 2 for l in L)
        print(g, r, "Lovasz decompositions:", tot, "with a Hamiltonian path:", ham, "length profiles:", dict(lens))


if __name__ == "__main__":
    main()
