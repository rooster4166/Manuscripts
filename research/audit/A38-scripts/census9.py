"""A38 census at order 9: 3-connected J with exactly one even vertex z.
Counts graphs, roots, roots with/without triangle data (per d(z)), and roots with all-odd
matching data (a perfect matching of J[N(z)]).  Input: nauty-geng -q -c -d3 9 on stdin.
Writes the one-even 3-connected list to the file given as argv[1]."""
import sys
from collections import Counter
import networkx as nx


def has_pm(H, verts):
    verts = list(verts)
    if not verts:
        return True
    a = verts[0]
    for b in verts[1:]:
        if H.has_edge(a, b):
            if has_pm(H, [x for x in verts[1:] if x != b]):
                return True
    return False


def main(outpath):
    cnt = Counter()
    out = open(outpath, "w")
    for line in sys.stdin:
        s = line.strip()
        H = nx.from_graph6_bytes(s.encode())
        ev = [v for v in H if H.degree(v) % 2 == 0]
        if len(ev) != 1:
            continue
        if nx.node_connectivity(H) < 3:
            continue
        z = ev[0]
        dz = H.degree(z)
        cnt["graphs"] += 1
        cnt[("graphs", dz)] += 1
        out.write(s + "\n")
        Nz = sorted(H[z])
        if has_pm(H, Nz):
            cnt[("graphs_pmNz", dz)] += 1
        for r in Nz:
            cnt[("roots", dz)] += 1
            rest = [v for v in Nz if v != r]
            data = any(has_pm(H, [v for v in rest if v != w]) for w in rest)
            cnt[("data" if data else "nodata", dz)] += 1
            # all-odd matching data: a perfect matching of J[N(z)] (r matched to some a0)
            if has_pm(H, Nz):
                cnt[("ao_matching_root", dz)] += 1
            if H.degree(r) == 8 - 1 + 0 and False:
                pass
            cnt[("deg_r", dz, H.degree(r))] += 1
    out.close()
    for k in sorted(cnt, key=str):
        print(k, cnt[k])


if __name__ == "__main__":
    main(sys.argv[1])
