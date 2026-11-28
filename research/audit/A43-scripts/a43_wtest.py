#!/usr/bin/env python3
"""Audit A43: do scripts/wcheck31.py and scripts/jwcheck.py reject bad witnesses?

usage: a43_wtest.py SCRIPTS_DIR tight.w profile.w joint.w
The .w files hold valid witness lines from the audit's own solver (a43 ... w, lines "W ...").
For every valid line: (1) the repository checker accepts it; (2) a list of corruptions is
built and each must be rejected (an exception from check(), or a non-zero exit of jwcheck.py).
"""
import sys, subprocess, os, random, tempfile

sd = sys.argv[1]
sys.path.insert(0, sd)
import wcheck31  # noqa: E402

random.seed(43)


def corrupt_paths(g6, paths, n):
    """yield (name, new path list) corruptions of a decomposition"""
    P = [p.split('-') for p in paths]
    if len(P) >= 1:
        yield 'drop a path', [p for i, p in enumerate(paths) if i != 0]
        yield 'duplicate a path', paths + [paths[0]]
    for i, p in enumerate(P):
        if len(p) >= 3:
            # close a cycle: append the first vertex
            yield 'repeat start vertex', paths[:i] + ['-'.join(p + [p[0]])] + paths[i + 1:]
            # split at an interior vertex (valid decomposition, wrong profile)
            yield 'split (profile changes)', paths[:i] + ['-'.join(p[:2]), '-'.join(p[1:])] + paths[i + 1:]
            break
    # merge two paths sharing an end into one (profile changes or repeated vertex)
    for i in range(len(P)):
        for j in range(len(P)):
            if i != j and P[i][-1] == P[j][0]:
                m = P[i] + P[j][1:]
                rest = [paths[k] for k in range(len(P)) if k not in (i, j)]
                yield 'merge at a common end', rest + ['-'.join(m)]
                break
        else:
            continue
        break
    # replace a vertex by another one
    for i, p in enumerate(P):
        v = random.randrange(n)
        q = list(p); q[-1] = str(v)
        if q != p:
            yield 'change an end vertex', paths[:i] + ['-'.join(q)] + paths[i + 1:]
            break
    # one-vertex path
    yield 'single-vertex path', paths + ['0']


def test_wcheck(fn, profile):
    ok = rej = acc_bad = 0
    for line in open(fn):
        if not line.startswith('W '):
            continue
        f = line.split()[1:]
        g6 = f[0]
        tgt = f[-1] if profile else None
        paths = f[1:-1] if profile else f[1:]
        n = ord(g6[0]) - 63
        good = ' '.join([g6] + paths + ([tgt] if profile else []))
        wcheck31.check(good, profile)
        ok += 1
        cands = list(corrupt_paths(g6, paths, n))
        if profile:
            b = [int(t) for t in tgt[2:].split(',')]
            b2 = list(b); b2[0] += 2
            cands.append(('wrong target', paths))
            tgts = {len(cands) - 1: 'b=' + ','.join(map(str, b2))}
        else:
            tgts = {}
        for k, (name, ps) in enumerate(cands):
            t = tgts.get(k, tgt)
            bad = ' '.join([g6] + ps + ([t] if profile else []))
            try:
                wcheck31.check(bad, profile)
                # accepted: only legitimate if the corruption happens to be a valid witness
                if name != 'split (profile changes)' or True:
                    acc_bad += 1
                    print('ACCEPTED corrupted (%s): %s' % (name, bad))
            except (AssertionError, ValueError, IndexError):
                rej += 1
    return ok, rej, acc_bad


def test_jwcheck(fn):
    good_lines, bad_lines = [], []
    for line in open(fn):
        if not line.startswith('W '):
            continue
        f = line.split()[1:]
        g6, P, rest, J = f[0], f[1], f[2:-1], f[-1]
        n = ord(g6[0]) - 63
        c1, a1, c2, a2 = [int(t) for t in J[2:].split(',')]
        good_lines.append(' '.join(f))
        pv = P.split('-')
        # P reversed (ends c2 .. c1): must be rejected (P[0] must be c1)
        bad_lines.append(('P reversed', ' '.join([g6, '-'.join(pv[::-1])] + rest + [J])))
        # avoided vertex swapped with c: J=a1,c1,... (c1 ~ a1 condition or P start fails)
        bad_lines.append(('J pairs swapped', ' '.join([g6, P] + rest + ['J=%d,%d,%d,%d' % (c2, a2, c1, a1)])))
        # a1 placed on P's vertex set by declaring an interior vertex of P avoided
        if len(pv) >= 3:
            bad_lines.append(('a1 on P', ' '.join([g6, P] + rest + ['J=%d,%s,%d,%d' % (c1, pv[1], c2, a2)])))
        # drop a path of K0
        if rest:
            bad_lines.append(('drop a K0 path', ' '.join([g6, P] + rest[1:] + [J])))
        # split P at an interior vertex: P no longer joint
        if len(pv) >= 3:
            bad_lines.append(('split P', ' '.join([g6, '-'.join(pv[:2]), '-'.join(pv[1:])] + rest + [J])))
    td = tempfile.mkdtemp()
    gf = os.path.join(td, 'good.txt')
    open(gf, 'w').write('\n'.join(good_lines) + '\n')
    r = subprocess.run([sys.executable, os.path.join(sd, 'jwcheck.py'), gf], capture_output=True, text=True)
    good_ok = r.returncode == 0
    rej = acc = 0
    for name, bl in bad_lines:
        bf = os.path.join(td, 'bad.txt')
        open(bf, 'w').write(bl + '\n')
        r = subprocess.run([sys.executable, os.path.join(sd, 'jwcheck.py'), bf], capture_output=True, text=True)
        if r.returncode != 0:
            rej += 1
        else:
            acc += 1
            print('ACCEPTED corrupted joint (%s): %s' % (name, bl))
    return len(good_lines), good_ok, rej, acc


if __name__ == '__main__':
    print('wcheck31 tight:', test_wcheck(sys.argv[2], False))
    print('wcheck31 --profile:', test_wcheck(sys.argv[3], True))
    print('jwcheck:', test_jwcheck(sys.argv[4]))
