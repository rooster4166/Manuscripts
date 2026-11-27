"""A20 spot checks for manuscripts/stl/stl.tex, using pdec.py (independent of the repo's oracle).

usage: python3 check.py {w4|bowtie|n7|n5|fail9|sample9|dz2|stl2_6|cone} [args]
"""
import sys, json, random, time, itertools
import signal
import networkx as nx
from pdec import (Graph, st, stl, bal, pairing, short_at, stl2, test1, test2, perfect_matchings,
                  search, lovasz_prof)

SCR = '/home/user/Manuscripts/manuscripts/stl/scripts/'


class TO(Exception):
    pass


def _h(sig, frm):
    raise TO()


signal.signal(signal.SIGALRM, _h)
TLIM = [0]
PROGRESS = [0]


def timed(f, *a):
    """f(*a), or None if it takes longer than TLIM[0] seconds (0 = no limit)"""
    if not TLIM[0]:
        return f(*a)
    signal.alarm(TLIM[0])
    try:
        return f(*a)
    except TO:
        return None
    finally:
        signal.alarm(0)


def one_even(J):
    ev = [v for v in J if J.degree(v) % 2 == 0]
    return ev[0] if len(ev) == 1 else None


def w4():
    J = nx.wheel_graph(5)  # hub 0, rim 1-2-3-4-1
    g = Graph(J)
    z = 0
    print("W4: edges", g.E)
    rim = [1, 2, 3, 4]
    for M in perfect_matchings(rim):
        w = pairing(g, z, set(M), witness=True)
        print("  pairing", [tuple(sorted(p)) for p in M], "->", "realisable, e.g. " + str(w) if w else "NOT realisable")
    for r in rim:
        print("  STL(W4,z,%d) =" % r, stl(g, z, r), " BAL =", bal(g, z, r), " T1 =", test1(J, z, r))
    # short sets of size 2 (HALF)
    for S in itertools.combinations(rim, 2):
        def step(acc, inf, path, S=S):
            if inf is None:
                return acc
            a, sa, b, sb = inf
            if (a in S) != sa or (b in S) != sb:
                return None
            return acc
        ok = search(g, lovasz_prof(g), z=z, star=True, step=step, acc0=0)
        print("  HALF short set", S, ok)


def bowtie():
    J = nx.Graph()
    for (u, v) in itertools.combinations([0, 1, 2, 3], 2):
        J.add_edge(u, v)
    for (u, v) in itertools.combinations([0, 4, 5, 6], 2):
        J.add_edge(u, v)
    g = Graph(J)
    z = 0
    print("bowtie: one even vertex", one_even(J))
    print("  ST (some star-terminal Lovasz decomposition):", st(g, z))
    print("  Lovasz decomposition exists:", search(g, lovasz_prof(g)))
    for r in range(1, 7):
        print("  r=%d STL" % r, stl(g, z, r), "BAL", bal(g, z, r), "T1", test1(J, z, r))
    # prism with rungs as terminal matching: G = two triangles + perfect matching a_i b_i
    P = nx.circular_ladder_graph(3)
    gp = Graph(P)
    print("  prism: degrees", gp.deg, "3-connected:", nx.node_connectivity(P) >= 3)


def classify_file(fn, limit=None, only3c=False, seed=None, timeout=None, verbose=False):
    lines = [l.strip() for l in open(fn, 'rb') if l.strip()]
    if seed is not None:
        random.Random(seed).shuffle(lines)
    stats = dict(graphs=0, pairs=0, stl_fail=0, bal_fail=0, t1_fail=0, st_fail=0,
                 stl_true_t1_false=0, stl_neq_t1_dr3=0, jz_conn_fail=0, jz_conn_pairs=0)
    rows = []
    for l in lines:
        J = nx.from_graph6_bytes(l)
        z = one_even(J)
        if z is None or J.degree(z) == 0:
            continue
        c3 = nx.node_connectivity(J) >= 3
        if only3c and not c3:
            continue
        g = Graph(J)
        zz = g.lab[z]
        H = J.copy(); H.remove_node(z)
        jzc = nx.is_connected(H)
        stats['graphs'] += 1
        sst = timed(st, g, zz)
        stats['st_fail'] += (sst is False)
        stats['undecided'] = stats.get('undecided', 0) + (sst is None)
        for r in sorted(J[z]):
            rr = g.lab[r]
            t0 = time.time()
            s = timed(stl, g, zz, rr)
            b = timed(bal, g, zz, rr)
            t = timed(test1, J, z, r)
            stats['pairs'] += 1
            if s is None or b is None or t is None:
                stats['undecided'] = stats.get('undecided', 0) + 1
                rows.append(dict(g6=l.decode(), z=z, r=r, undecided=[s, b, t]))
                continue
            stats['stl_fail'] += (not s)
            stats['bal_fail'] += (not b)
            stats['t1_fail'] += (not t)
            if s and not t:
                stats['stl_true_t1_false'] += 1
            if J.degree(r) >= 3 and s != t:
                stats['stl_neq_t1_dr3'] += 1
            if jzc:
                stats['jz_conn_pairs'] += 1
                stats['jz_conn_fail'] += (not s)
            if verbose or not s or (s and not t):
                rows.append(dict(g6=l.decode(), z=z, r=r, dz=J.degree(z), dr=J.degree(r), c3=c3,
                                 jzc=jzc, ST=sst, STL=s, BAL=b, T1=t))
        if PROGRESS[0]:
            print('  graph', stats['graphs'], l.decode(), 'c3', c3, 'ST', sst, 'pairs so far', stats['pairs'],
                  'STL fails', stats['stl_fail'], 'undecided', stats.get('undecided', 0), flush=True)
        if limit and stats['graphs'] >= limit:
            break
    return stats, rows


def n_file(n, limit=None, only3c=False, seed=None):
    st_, rows = classify_file(SCR + 'one_even_%d.g6' % n, limit=limit, only3c=only3c, seed=seed)
    print(json.dumps(st_), flush=True)
    for r in rows:
        print("  ", json.dumps(r))


def fail9(k):
    recs = [json.loads(l) for l in open(SCR + 'out/fail_9.jsonl')]
    picks = [recs[i] for i in k]
    for rec in picks:
        J = nx.from_graph6_bytes(rec['g6'].encode())
        z, r = rec['z'], rec['r']
        g = Graph(J)
        H = J.copy(); H.remove_node(z)
        t0 = time.time()
        s = timed(stl, g, g.lab[z], g.lab[r])
        b = timed(bal, g, g.lab[z], g.lab[r])
        t = timed(test1, J, z, r)
        print(rec['g6'], 'z', z, 'r', r, 'd(z)', J.degree(z), 'd(r)', J.degree(r),
              'one-even', one_even(J) == z, 'J-z components', [len(c) for c in nx.connected_components(H)],
              '| STL', s, 'BAL', b, 'T1', t, '| repo: STL', rec['STL'], 'T1', rec['T1'],
              '(%.1fs)' % (time.time() - t0))


def stl2_file(fn, limit=None, only3c=True, seed=None):
    lines = [l.strip() for l in open(fn, 'rb') if l.strip()]
    if seed is not None:
        random.Random(seed).shuffle(lines)
    cnt = dict(graphs=0, inst=0, stl2_fail=0, t2_fail=0, beta0=0)
    for l in lines:
        J = nx.from_graph6_bytes(l)
        ev = [v for v in J if J.degree(v) % 2 == 0]
        if len(ev) != 2 or not J.has_edge(*ev):
            continue
        if only3c and nx.node_connectivity(J) < 3:
            continue
        cnt['graphs'] += 1
        g = Graph(J)
        for (z, r) in (ev, ev[::-1]):
            cnt['inst'] += 1
            s = stl2(g, g.lab[z], g.lab[r])
            t = test2(J, z, r)
            prof = lovasz_prof(g); prof[g.lab[r]] = 0
            cnt['beta0'] += bool(search(g, prof))
            cnt['stl2_fail'] += (not s)
            cnt['t2_fail'] += (not t)
            if not s or not t:
                print('  ', l.decode(), z, r, 'STL2', s, 'T2', t)
        if limit and cnt['graphs'] >= limit:
            break
    print(json.dumps(cnt))


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'w4':
        w4()
    elif cmd == 'bowtie':
        bowtie()
    elif cmd == 'n':
        PROGRESS[0] = int(__import__('os').environ.get('PROGRESS', '0'))
        if 'TLIM' in __import__('os').environ:
            TLIM[0] = int(__import__('os').environ['TLIM'])
        n = int(sys.argv[2])
        limit = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '-' else None
        only3c = len(sys.argv) > 4 and sys.argv[4] == '3c'
        seed = int(sys.argv[5]) if len(sys.argv) > 5 else None
        n_file(n, limit, only3c, seed)
    elif cmd == 'fail9':
        if 'TLIM' in __import__('os').environ:
            TLIM[0] = int(__import__('os').environ['TLIM'])
        fail9([int(x) for x in sys.argv[2:]])
    elif cmd == 'stl2':
        fn = sys.argv[2]
        limit = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '-' else None
        only3c = not (len(sys.argv) > 4 and sys.argv[4] == 'all')
        seed = int(sys.argv[5]) if len(sys.argv) > 5 else None
        stl2_file(fn, limit, only3c, seed)
