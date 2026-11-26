"""Standalone verifier for the endpoint-structure certificates (no solver, stdlib only).

Each certificate: graph edge list, a claimed endpoint profile (even set S doubled,
other even vertices 0, odd vertices 1), and an explicit list of paths.  We check
that the paths are simple, use only graph edges, partition the edge set, and
realise the claimed end counts.
"""
import json
import sys
from collections import Counter


def check(cert):
    E = {frozenset(e) for e in cert["edges"]}
    deg = Counter()
    for e in cert["edges"]:
        deg[e[0]] += 1
        deg[e[1]] += 1
    used = Counter()
    ends = Counter()
    for P in cert["paths"]:
        assert len(P) >= 2 and len(set(P)) == len(P), f"not a simple path: {P}"
        for a, b in zip(P, P[1:]):
            assert frozenset((a, b)) in E, f"non-edge {a}{b}"
            used[frozenset((a, b))] += 1
        ends[P[0]] += 1
        ends[P[-1]] += 1
    assert all(used[e] == 1 for e in E) and sum(used.values()) == len(E), "not a partition"
    S = set(cert["doubled"])
    for v in deg:
        want = 1 if deg[v] % 2 else (2 if v in S else 0)
        assert ends[v] == want, f"vertex {v}: {ends[v]} ends, want {want}"
    assert len(cert["paths"]) == cert["claimed_size"]
    return True


if __name__ == "__main__":
    data = json.load(open(sys.argv[1]))
    for c in data["certificates"]:
        check(c)
    print(f"{sys.argv[1]}: {len(data['certificates'])} certificates verified")
