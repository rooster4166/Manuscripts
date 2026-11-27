"""walksim.py: path decompositions, leaves, Fan transfers with forced chains, and the J-form
un-lift (session claude/t6-dense).

A decomposition is a list of vertex lists.  ends(v) counts path ends at v.  Fan's transfer
`fan(D, u, t)` adds the edge tu, moving one end from t to u, along the forced chain
x0 = t, x_{i+1} = predecessor of u on the path ending at x_i (read from x_i); it is the
construction of Fan's Lemma 3.3/3.4 (Lean `fan_exec`).  It returns (D', info) with
info = {'ok': bool, 'chain': [x0, ..., xk], 'hit': vertex where it failed or None}.
"""
import subprocess


def ends_count(D, v):
    return sum((P[0] == v) + (P[-1] == v) for P in D)


def end_paths(D, v):
    return [i for i, P in enumerate(D) if P[0] == v or P[-1] == v]


def leaf(D, v, l):
    """extend the path ending at v by the new leaf l at v"""
    D = [list(P) for P in D]
    idx = end_paths(D, v)
    assert idx, ('no end at', v)
    i = idx[0]
    P = D[i]
    if P[-1] != v:
        P.reverse()
    P.append(l)
    return D


def fan(D, u, t):
    """add the edge tu; forced chain from t; requires ends(t) >= 1"""
    D = [list(P) for P in D]
    chain = [t]
    x = t
    newp = None          # index of the path just rerouted (it now ends at x and contains u)
    while True:
        idx = [i for i in end_paths(D, x) if i != newp]
        if not idx:
            return D, {'ok': False, 'chain': chain, 'hit': x}
        avoid = [i for i in idx if u not in D[i]]
        if avoid:
            P = D[avoid[0]]
            if P[-1] != x:
                P.reverse()
            P.append(u)
            return D, {'ok': True, 'chain': chain, 'hit': None}
        i = idx[0]
        P = D[i]
        if P[0] != x:
            P.reverse()
        k = P.index(u)
        y = P[k - 1]
        D[i] = P[:k][::-1] + P[k:]
        newp = i
        if y in chain:
            return D, {'ok': False, 'chain': chain + [y], 'hit': y}
        chain.append(y)
        x = y


def static_pred_ok(D, u, src, nbrs, protected):
    """the static condition of walk_step_protected: no vertex of {src} u N(u) has a vertex of
    `protected` as its predecessor of u"""
    S = set([src]) | set(nbrs)
    for P in D:
        if u not in P:
            continue
        k = P.index(u)
        if k > 0 and P[k - 1] in protected and P[0] in S:
            return False
        if k + 1 < len(P) and P[k + 1] in protected and P[-1] in S:
            return False
    return True


def edges_of(P):
    return [frozenset((P[i], P[i + 1])) for i in range(len(P) - 1)]


def check_decomp(D, E, profile):
    """D decomposes the edge set E (set of frozensets), paths simple, ends = profile"""
    seen = set()
    for P in D:
        if len(P) < 2 or len(set(P)) != len(P):
            return 'not a path: %s' % P
        for e in edges_of(P):
            if e not in E:
                return 'non-edge %s' % sorted(e)
            if e in seen:
                return 'edge twice %s' % sorted(e)
            seen.add(e)
    if seen != E:
        return 'missing edges %s' % [sorted(e) for e in E - seen][:5]
    for v, b in profile.items():
        if ends_count(D, v) != b:
            return 'ends(%s)=%d, want %d' % (v, ends_count(D, v), b)
    return None


def unlift_J(D, leaves, xs, z):
    """J-form un-lift: each leaf l_i (an end of exactly one path, through y_i) becomes z, and the
    path is extended by x_i.  Returns the decomposition of J or raises."""
    out = []
    for P in D:
        P = list(P)
        hit = [i for i, l in enumerate(leaves) if l in P]
        if len(hit) > 1:
            raise ValueError('two leaves on one path')
        if hit:
            i = hit[0]
            l = leaves[i]
            if P[0] == l:
                P.reverse()
            if P[-1] != l:
                raise ValueError('leaf not an end')
            if xs[i] in P:
                raise ValueError('x_%d on its leaf path' % (i + 1))
            P[-1] = z
            P.append(xs[i])
        out.append(P)
    return out


def star_ok(D, z):
    """every path through z has an end adjacent to z on it"""
    for P in D:
        if z in P:
            k = P.index(z)
            if not (k == 1 or k == len(P) - 2):
                return False
    return True


class Engine:
    """batch interface to lsearch"""

    def __init__(self, exe):
        self.exe = exe

    def run(self, queries):
        """queries: list of dicts with n, edges, b, sep, ef, ep, es, seed, budget"""
        lines = []
        for q in queries:
            lines.append('%d %d %d %d' % (q['n'], len(q['edges']), q.get('seed', 0), q.get('budget', 0)))
            lines.append(' '.join('%d %d' % e for e in q['edges']))
            lines.append(' '.join(str(x) for x in q['b']))
            sep = q.get('sep', [])
            lines.append(' '.join([str(len(sep))] + ['%d %d' % p for p in sep]))
            ef = q.get('ef', {})
            parts = [str(len(ef))]
            for v, S in ef.items():
                parts.append('%d %d %s' % (v, len(S), ' '.join(map(str, S))))
            lines.append(' '.join(parts))
            ep = q.get('ep', [])
            lines.append(' '.join([str(len(ep))] + ['%d %d' % p for p in ep]))
            es = q.get('es', [])
            parts = [str(len(es))]
            for p, qq, S in es:
                parts.append('%d %d %d %s' % (p, qq, len(S), ' '.join(map(str, S))))
            lines.append(' '.join(parts))
        out = subprocess.run([self.exe], input='\n'.join(lines) + '\n', capture_output=True,
                             text=True, check=True).stdout.split('\n')
        res = []
        i = 0
        for q in queries:
            tok = out[i].split()
            i += 1
            if tok[0] == 'OK':
                k = int(tok[1])
                D = [list(map(int, out[i + j].split())) for j in range(k)]
                i += k
                res.append(('OK', D))
            else:
                res.append((tok[0], None))
        return res
