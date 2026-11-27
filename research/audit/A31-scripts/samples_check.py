"""samples_check.py EC_DATA RT_OUT: the order-12/14/16 sample claims of re-tight section 5."""
import gzip
import sys
from collections import Counter, defaultdict

sys.path.insert(0, __import__("os").path.dirname(__file__))
from g6 import parse_g6, two_connected  # noqa: E402
from recount_conditions import star2  # noqa: E402

EC, RT = sys.argv[1], sys.argv[2]


def info(g):
    n, adj = parse_g6(g)
    deg = [len(a) for a in adj]
    return n, adj, deg


def lines(fn):
    return [l.split() for l in open(fn) if l.strip()]


def main():
    # dense order-12 family
    dense = set()
    for fn in ("dense12_2c.g6.gz", "dense12_m45_2c.g6.gz"):
        for l in gzip.open(EC + "/" + fn, "rt"):
            dense.add(l.strip())
    mid = [l.strip() for l in open(RT + "/mid12_sample.g6")]
    c = Counter()
    nroots = 0
    for g in mid:
        n, adj, deg = info(g)
        u = deg.count(n - 2)
        m = sum(deg) // 2
        c["in dense family"] += g in dense
        c["2c"] += two_connected(n, adj)
        c["eulerian"] += all(d % 2 == 0 for d in deg)
        c["m>=45"] += m >= 45
        c["1<=u<=4"] += 1 <= u <= 4
        nroots += u
    print("mid12_sample: %d graphs, %d distinct, %s, degree-10 roots %d" % (len(mid), len(set(mid)), dict(c), nroots))
    L = lines(RT + "/retL_mid12.txt")
    st = Counter(f[2] for f in L)
    s2 = Counter()
    for f in L:
        n, adj, deg = info(f[0])
        s2[star2(n, adj, int(f[1]))] += 1
    print("  retL_mid12: %d lines %s; (**) holds at %s" % (len(L), dict(st), dict(s2)))
    # near-regular
    for fn in ("nr12.g6", "nr14.g6", "nr16.g6"):
        gs = [l.strip() for l in open(RT + "/" + fn)]
        ok = Counter()
        for g in gs:
            n, adj, deg = info(g)
            ok["shape"] += deg[0] == n - 2 and all(d == n - 4 for d in deg[1:])
            ok["2c"] += two_connected(n, adj)
            ok["(**) at 0"] += star2(n, adj, 0)
        print("%s: %d graphs (%d distinct) %s" % (fn, len(gs), len(set(gs)), dict(ok)))
    L = lines(RT + "/retL_nr.txt")
    print("  retL_nr: %d lines, statuses %s, roots %s, max nodes %d" % (
        len(L), dict(Counter(f[2] for f in L)), dict(Counter(f[1] for f in L)),
        max(int(f[-1].split("=")[1]) for f in L)))
    # mixed order 16
    gs = [l.strip() for l in open(RT + "/mixed16.g6")]
    ug = {}
    for g in gs:
        n, adj, deg = info(g)
        u = deg.count(14)
        assert n == 16 and all(d in (12, 14) for d in deg) and two_connected(n, adj), g
        ug[g] = u
    print("mixed16: %d graphs, u distribution %s" % (len(gs), dict(Counter(ug.values()))))
    for fn in ("retL_mixed16.txt", "ret_mixed16.txt"):
        L = lines(RT + "/" + fn)
        per = defaultdict(Counter)
        nodes = defaultdict(list)
        q = defaultdict(list)
        roots = Counter()
        for f in L:
            u = ug[f[0]]
            per[u][f[2]] += 1
            roots[(f[1], len(info(f[0])[1][int(f[1])]))] += 1
            nodes[(u, f[2])].append(int(f[-1].split("=")[1]))
            if f[2] == "YES":
                q[u].append(int(f[3]))
        print("  %s: roots (r, d(r)) %s" % (fn, dict(roots)))
        for u in sorted(per):
            print("    u=%d %s nontrivial pieces %s" % (u, dict(per[u]), sorted(q[u])))
        for key in sorted(nodes):
            print("    nodes", key, min(nodes[key]), max(nodes[key]))
    # random order 12
    gs = [l.strip() for l in open(RT + "/rand12_n2.g6")]
    rnd = set(l.split()[0] for l in gzip.open(EC + "/out/re_rand_12.tab.gz", "rt"))
    c = Counter()
    roots = 0
    for g in gs:
        n, adj, deg = info(g)
        c["has deg 10"] += 10 in deg
        c["in re_rand_12"] += g in rnd
        roots += deg.count(10)
    print("rand12_n2: %d graphs (%d distinct) %s; degree-10 roots %d; graphs in re_rand_12 with a degree-10 vertex: %d"
          % (len(gs), len(set(gs)), dict(c), roots,
             sum(1 for g in rnd if 10 in [len(a) for a in parse_g6(g)[1]])))


if __name__ == "__main__":
    main()
