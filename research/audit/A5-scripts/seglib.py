"""Segment model for two members sharing h contacts (independent replay).
First member: cycle C on contacts 0..h-1 in cyclic order.
Second member: path (order = permutation, trimmed) or cycle (cyclic order).
Each segment is direct (one edge) or subdivided (one new vertex)."""
import itertools, subprocess, os
HERE = os.path.dirname(os.path.abspath(__file__))

def dihedral(h):
    maps = []
    for s in range(h):
        maps.append(tuple((i + s) % h for i in range(h)))
        maps.append(tuple((s - i) % h for i in range(h)))
    return maps

def canon_path(order, D):
    best = None
    for g in D:
        o = tuple(g[v] for v in order)
        for c in (o, o[::-1]):
            if best is None or c < best: best = c
    return best

def canon_cycle(order, D):
    h = len(order); best = None
    for g in D:
        o = [g[v] for v in order]
        for r in (o, o[::-1]):
            for s in range(h):
                c = tuple(r[s:] + r[:s])
                if best is None or c < best: best = c
    return best

def path_orders(h):
    D = dihedral(h); seen = set()
    for p in itertools.permutations(range(h)):
        seen.add(canon_path(p, D))
    return sorted(seen)

def cycle_orders(h):
    D = dihedral(h); seen = set()
    for p in itertools.permutations(range(1, h)):
        seen.add(canon_cycle((0,) + p, D))
    return sorted(seen)

def segments(h, order, kind):
    C = [(i, (i + 1) % h) for i in range(h)]
    if kind == 'path':
        S = [(order[i], order[i + 1]) for i in range(len(order) - 1)]
    else:
        S = [(order[i], order[(i + 1) % h]) for i in range(h)]
    return C + S

def classes(segs):
    cl = {}
    for i, (a, b) in enumerate(segs):
        cl.setdefault(frozenset((a, b)), []).append(i)
    return [v for v in cl.values() if len(v) > 1]

def is_simple(segs, sub):
    for cls in classes(segs):
        if sum(1 for i in cls if i not in sub) > 1: return False
    # loops impossible (distinct contacts) except h==1, not used
    return True

def graph(h, segs, sub):
    edges = []; nxt = h
    for i, (a, b) in enumerate(segs):
        if i in sub:
            edges += [(a, nxt), (nxt, b)]; nxt += 1
        else:
            edges.append((a, b))
    return nxt, edges

class TwoPath:
    def __init__(self):
        self.p = subprocess.Popen([os.path.join(HERE, 'twopath')], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, text=True, bufsize=1)
    def batch(self, graphs):
        out = []
        for i in range(0, len(graphs), 2000):
            out += self._batch(graphs[i:i+2000])
        return out
    def _batch(self, graphs):
        lines = []
        for n, E in graphs:
            lines.append(f"{n} {len(E)} " + " ".join(f"{a} {b}" for a, b in E))
        self.p.stdin.write("\n".join(lines) + "\n"); self.p.stdin.flush()
        return [self.p.stdout.readline().strip() == '1' for _ in graphs]
    def one(self, n, E):
        return self.batch([(n, E)])[0]

def minimal_sets(segs, kind):
    """inclusion-minimal subdivision sets: hit every parallel class (all but <=1
    of each class subdivided; classes have size 2 here) and have size >= 1 (path)
    or >= 2 (cycle)."""
    cls = classes(segs)
    assert all(len(c) == 2 for c in cls), cls
    lb = 1 if kind == 'path' else 2
    nseg = len(segs)
    res = set()
    base_choices = list(itertools.product(*cls)) if cls else [()]
    for ch in base_choices:
        S = frozenset(ch)
        if len(S) >= lb:
            res.add(S)
        else:
            # need to add lb-len(S) more segments
            others = [i for i in range(nseg) if i not in S]
            for add in itertools.combinations(others, lb - len(S)):
                res.add(S | frozenset(add))
    # keep inclusion-minimal ones only
    res = [S for S in res if not any(T < S for T in res)]
    return res
