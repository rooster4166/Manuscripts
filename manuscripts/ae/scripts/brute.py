"""brute.py -- independent brute force for the queries of aesolve (ae session).  Shares no code
with aesolve.c.  Reads query lines '<g6> [A t a] [T w x] [R v k]' on stdin and prints SAT/UNSAT.
Method: the smallest remaining edge must lie on some path; enumerate every simple path of the
remaining graph through it (grown from both of its ends), require each path end to have spare
required ends, recurse; at a full decomposition check the profile and the constraints."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
from lnlib import g6_decode

def solve(n, adj, req, A, T):
    E = sorted((min(u, v), max(u, v)) for u in range(n) for v in adj[u] if u < v)
    rem = set(E)
    ends = [0] * n
    paths = []
    def ok_path(p):
        a, b = p[0], p[-1]
        for (t, x) in A:
            if (t == a or t == b) and x in p: return False
        for (w, x) in T:
            if (p[0] == w and p[1] == x) or (p[-1] == w and p[-2] == x): return False
        return True
    def rec():
        if not rem:
            return all(ends[v] == req[v] for v in range(n))
        x, y = min(rem)
        # grow from y away from x (right part), then from x away from y (left part)
        def grow(path, used, side_done):
            # path is a list of vertices containing x,y consecutively; extend at the right end
            # first (side_done False) then at the left end
            res = []
            if not side_done:
                last = path[-1]
                # option: stop extending right
                yield from grow(path, used, True)
                for z in sorted(adj[last]):
                    e = (min(last, z), max(last, z))
                    if e in rem and e not in used and z not in path:
                        yield from grow(path + [z], used | {e}, False)
            else:
                yield (path, used)
        def grow_left(path, used):
            yield (path, used)
            first = path[0]
            for z in sorted(adj[first]):
                e = (min(first, z), max(first, z))
                if e in rem and e not in used and z not in path:
                    yield from grow_left([z] + path, used | {e})
        for (p1, u1) in grow([x, y], {(x, y)}, False):
            for (p, used) in grow_left(p1, u1):
                a, b = p[0], p[-1]
                if ends[a] + 1 > req[a] or ends[b] + 1 > req[b]: continue
                if not ok_path(p): continue
                ends[a] += 1; ends[b] += 1
                for e in used: rem.discard(e)
                paths.append(p)
                if rec(): return True
                paths.pop()
                for e in used: rem.add(e)
                ends[a] -= 1; ends[b] -= 1
        return False
    return rec(), paths

for line in sys.stdin:
    t = line.split()
    if not t: continue
    n, adj = g6_decode(t[0])
    req = [len(adj[v]) % 2 for v in range(n)]
    A = []; T = []
    i = 1
    while i < len(t):
        k, p, q = t[i], int(t[i + 1]), int(t[i + 2]); i += 3
        if k == 'A': A.append((p, q))
        elif k == 'T': T.append((p, q))
        elif k == 'R': req[p] = q
        else: raise SystemExit('bad token ' + k)
    ok, paths = solve(n, adj, req, A, T)
    print(('SAT ' if ok else 'UNSAT ') + t[0])
