"""a_order8.py (audit A37, item 3a): regenerate the order-6 and order-8 rows of the (T2) table from
nauty-geng -c (ALL connected graphs; filters are my own), decide (T2) and the slack p(B) <= k with
my own CP-SAT model at EVERY instance, check every witness with my own checker, and compare with
manuscripts/test2/data/t2_order6_8.txt.  Also counts the 2-connected-not-3-connected and the
cut-vertex instances with delta >= 3 (manuscript Section 2, 'Connectivity').
usage: python3 a_order8.py
"""
import subprocess
import sys
from collections import Counter

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from a37lib import adjacency, check_decomp, cpsat_decomp, delete_vertex, g6_decode, kconn, t2_instances

DATA = "/home/user/Manuscripts/manuscripts/test2/data/t2_order6_8.txt"


def load_session():
    d = {}
    for line in open(DATA):
        g6, tail = line.split(None, 1)
        f = tail.split("|")[0].split()
        z, r, dz, dr, n, slack, t2, emax = map(int, f)
        d[(g6, z, r)] = (slack, t2)
    return d


def canon(g6):
    """nauty canonical label, so that my instance set can be matched with the session's."""
    p = subprocess.run(["nauty-labelg", "-q"], input=g6 + "\n", capture_output=True, text=True)
    return p.stdout.strip()


def main():
    sess = load_session()
    stats = Counter()
    mine = {}
    for n in (6, 8):
        out = subprocess.run(["nauty-geng", "-q", "-c", str(n)], capture_output=True, text=True).stdout.split()
        for g6 in out:
            nn, E = g6_decode(g6)
            A = adjacency(nn, E)
            inst = t2_instances(nn, E)
            if not inst:
                continue
            if min(len(a) for a in A) < 3:
                continue
            k3 = kconn(nn, A, 3)
            k2 = kconn(nn, A, 2)
            cls = "3conn" if k3 else ("2conn" if k2 else "cutvertex")
            stats[(n, cls, "graphs")] += 1
            for z, r in inst:
                B = delete_vertex(E, z)
                k = (nn - 2) // 2
                st, W = cpsat_decomp(B, nn // 2, r=r, minends=3)
                if st == "FEAS":
                    check_decomp(B, W, maxpaths=nn // 2, r=r, minends=3)
                    t2 = 1
                elif st == "INFEAS":
                    t2 = 0
                else:
                    t2 = 2
                st2, W2 = cpsat_decomp(B, k)
                if st2 == "FEAS":
                    check_decomp(B, W2, maxpaths=k)
                    slack = 1
                elif st2 == "INFEAS":
                    slack = 0
                else:
                    slack = 2
                semi = len(B) > 2 * k * k
                stats[(n, cls, "inst")] += 1
                stats[(n, cls, "t2", t2)] += 1
                stats[(n, cls, "slack", slack)] += 1
                if slack == 0:
                    stats[(n, cls, "tight_semi" if semi else "tight_NOT_semi")] += 1
                elif semi:
                    stats[(n, cls, "semi_but_slack!")] += 1
                if cls == "3conn":
                    mine[(g6, z, r)] = (slack, t2)
                if cls == "cutvertex" and t2 != 1:
                    print("cut-vertex failure:", g6, z, r, t2, flush=True)
    # compare with the session's file (by canonical form; z, r mapped through the relabelling)
    # Simplest robust comparison: multiset of (n, slack, t2) and per-canonical-graph counts.
    sc = Counter((len(g6) and g6_decode(g6)[0], v) for (g6, z, r), v in sess.items())
    mc = Counter((g6_decode(g6)[0], v) for (g6, z, r), v in mine.items())
    print("session (n,(slack,t2)) counts:", dict(sc))
    print("mine    (n,(slack,t2)) counts:", dict(mc))
    scan = Counter(canon(g6) for (g6, z, r) in sess)
    mcan = Counter(canon(g6) for (g6, z, r) in mine)
    print("same canonical graph multiset:", scan == mcan, len(scan), len(mcan))
    for kk in sorted(stats, key=str):
        print(kk, stats[kk])


if __name__ == "__main__":
    main()
