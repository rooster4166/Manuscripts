#!/usr/bin/env python3
"""tamper.py (A36 auditor).

Mode 'strict': run the committed mt_verify.py on SCHED lines, with verify_test1 replaced by a wrapper
that ASSERTS its boolean result (mt_verify.py calls verify_test1 and discards the result, so the
Test1 size bound and the two ends at r are never checked there).

Mode 'tamper': corrupt each schedule once at random in one of several ways; ask mt_verify.check
(accept = no exception) and, independently, the A36 replayer thm42.replay (legality per Definition
2.2 and the end condition).  A corrupted schedule that is still a legal schedule must be accepted
and every other one rejected; report any disagreement.

usage: tamper.py MT_VERIFY_DIR ROUTE_EXT strict|tamper [SEED] < sched.txt
"""
import sys
import os
import random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, sys.argv[1])
import networkx as nx  # noqa: E402
import mt_verify  # noqa: E402
from thm42 import replay  # noqa: E402

_orig = mt_verify.verify_test1


def strict_verify_test1(J, z, r, paths):
    ok = _orig(J, z, r, paths)
    assert ok, 'Test1 lift: size or ends at r fails'
    return ok


def parse(line):
    head, mvs = line.rsplit(' |', 1)
    p = head.split()
    return p, mvs.split()


def to_tuples(mvs):
    out = []
    for m in mvs:
        if m[0] == 'M':
            a, b = map(int, m[1:].split('-'))
            out.append(('M', a, b))
        elif m[0] == 'D':
            out.append(('D', int(m[1:])))
        elif m[0] == 'S':
            pp, ab = m[1:].split(':')
            a, b = map(int, ab.split('-'))
            out.append(('S', int(pp), a, b))
        else:
            raise ValueError(m)
    return out


def my_accepts(p, mvs):
    g6, resid, z, r, w = p[1], int(p[2]), int(p[3]), int(p[4]), int(p[5])
    pairs = [tuple(map(int, s.split(','))) for s in p[6:]]
    J = nx.from_graph6_bytes(g6.encode())
    if resid:
        J.add_edges_from((z, u) for u in range(6))
    try:
        # the S move in SCHED names a, b; check they are the current neighbours (done in replay)
        replay(J, z, w, pairs, to_tuples(mvs))
        return True
    except (AssertionError, KeyError, ValueError):
        return False


def corrupt(mvs, n, rng):
    kind = rng.choice(['dropfirst', 'droplast', 'target', 'swap', 'dropidx', 'supp'])
    m = list(mvs)
    if kind == 'dropfirst' and len(m) > 1:
        m = m[1:]
    elif kind == 'droplast' and len(m) > 1:
        m = m[:-1]
    elif kind == 'swap' and len(m) > 1:
        i = rng.randrange(len(m) - 1)
        m[i], m[i + 1] = m[i + 1], m[i]
    elif kind == 'dropidx':
        ds = [i for i, x in enumerate(m) if x[0] == 'D']
        if not ds:
            return corrupt(mvs, n, rng)
        i = rng.choice(ds)
        m[i] = 'D%d' % (1 - int(m[i][1:]))
    elif kind == 'supp':
        ss = [i for i, x in enumerate(m) if x[0] == 'M']
        if not ss:
            return corrupt(mvs, n, rng)
        i = rng.choice(ss)
        a, b = map(int, m[i][1:].split('-'))
        m[i] = 'S%d:%d-%d' % (a, b, (b + 1) % n)
    else:
        ms = [i for i, x in enumerate(m) if x[0] == 'M']
        if not ms:
            return corrupt(mvs, n, rng)
        i = rng.choice(ms)
        a, b = map(int, m[i][1:].split('-'))
        c = rng.choice([v for v in range(n) if v not in (a, b)])
        m[i] = 'M%d-%d' % (a, c)
        kind = 'target'
    return kind, m


def main():
    mtdir, ora, mode = sys.argv[1], sys.argv[2], sys.argv[3]
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    mt_verify.verify_test1 = strict_verify_test1
    cnt = 0
    stats = {}
    for line in sys.stdin:
        if not line.startswith('SCHED'):
            continue
        line = line.strip()
        if mode == 'strict':
            mt_verify.check(ora, line)
            cnt += 1
            continue
        p, mvs = parse(line)
        n = nx.from_graph6_bytes(p[1].encode()).number_of_nodes() + int(p[2])
        assert my_accepts(p, mvs), ('original rejected by A36 replayer', line)
        kind, m = corrupt(mvs, n, rng)
        bad = p[0] + ' ' + ' '.join(p[1:]) + ' | ' + ' '.join(m)
        try:
            mt_verify.check(ora, bad)
            theirs = True
        except Exception:
            theirs = False
        mine = my_accepts(p, m)
        key = (kind, 'valid' if mine else 'invalid', 'accepted' if theirs else 'rejected')
        stats[key] = stats.get(key, 0) + 1
        if mine != theirs:
            print('DISAGREE', key, bad)
        cnt += 1
    if mode == 'strict':
        print('strict: verified', cnt, 'schedules, Test1 size and ends asserted')
    else:
        for k in sorted(stats):
            print('tamper', k, stats[k])
        print('tamper: corrupted', cnt)


if __name__ == '__main__':
    main()
