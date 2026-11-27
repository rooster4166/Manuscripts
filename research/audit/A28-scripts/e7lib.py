"""A28: on the common graph M (r = y1, w = x3, M0 = {x1y2, x2y3}), compare
   TB  = triangle base for (r, w, M0)            [(2.1) for both pairs]
   E7  = some of the 8 labellings with these (y1, x3, {pairs}) has an (E1)-(E5)+(E7) base."""
import itertools, os, random, sys
sys.argv = ['x', 'none']
exec(open('/tmp/claude-0/-home-user-Manuscripts/7bcde938-d618-5679-84f3-4739c83be31f/scratchpad/aud28.py').read().split('if __name__')[0])
import networkx as nx


def decomp_exists(E, n, b, ok):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(E):
        adj[u].append((v, i)); adj[v].append((u, i))
    fail = set()
    def solve(rem, bb):
        if rem == 0:
            return all(x == 0 for x in bb)
        if (rem, bb) in fail:
            return False
        bl = list(bb)
        st = [v for v in range(n) if bl[v] > 0]
        if not st:
            fail.add((rem, bb)); return False
        s = st[0]
        def grow(c, vis, rem2):
            for (w, i) in adj[c]:
                if not (rem2 >> i) & 1 or (vis >> w) & 1:
                    continue
                r3 = rem2 & ~(1 << i); vis2 = vis | (1 << w)
                if bl[w] > 0 and ok(s, w, vis2):
                    bl[s] -= 1; bl[w] -= 1
                    good = solve(r3, tuple(bl))
                    bl[s] += 1; bl[w] += 1
                    if good:
                        return True
                if grow(w, vis2, r3):
                    return True
            return False
        if grow(s, 1 << s, rem):
            return True
        fail.add((rem, bb)); return False
    return solve((1 << len(E)) - 1, tuple(b))


def e7_ok(z, x1, x2, y2, x3, y3):
    def ok(s, t, vis):
        ends = {s, t}
        if z in ends:
            if vis >> x1 & 1: return False
            if (ends - {z}) & {y2, y3}: return False
        if y2 in ends and vis >> x2 & 1: return False
        if y3 in ends and vis >> x3 & 1: return False
        if ends == {y2, y3}: return False
        if x2 in ends and vis >> y3 & 1: return False
        if x1 in ends and vis >> y2 & 1: return False
        return True
    return ok


def tb_ok(pairs, orient):
    av = {}
    for (a, c), o in zip(pairs, orient):
        if o == 0: av.setdefault(c, 0); av[c] |= 1 << a
        else: av.setdefault(a, 0); av[a] |= 1 << c
    def ok(s, t, vis):
        return not (vis & av.get(s, 0)) and not (vis & av.get(t, 0))
    return ok


def main(n, count, seed, p, pd):
    rng = random.Random(seed)
    st = dict(graphs=0, choices=0, tb=0, e7=0, tb_not_e7=0, e7_not_tb=0, roots=0, roots_tb=0, roots_e7y1=0)
    for t in range(count):
        J = gen_J(n, 6, rng, p=p, pdense=pd)
        if nx.node_connectivity(J) < 3:
            continue
        st['graphs'] += 1
        for r in sorted(J.neighbors(0)):
            st['roots'] += 1
            rt = re = False
            for w, pm in data_choices(J, 0, r):
                M = J.copy(); M.remove_edges_from([(0, w)] + [(0, x) for q in pm for x in q] + pm)
                E = list(M.edges()); b = [M.degree(v) % 2 for v in range(n)]
                tb = any(decomp_exists(E, n, b, tb_ok(pm, o)) for o in itertools.product([0, 1], repeat=2))
                e7 = False
                for (P1, P2) in (pm, pm[::-1]):
                    for (x1, y2) in (P1, P1[::-1]):
                        for (x2, y3) in (P2, P2[::-1]):
                            if decomp_exists(E, n, b, e7_ok(0, x1, x2, y2, w, y3)):
                                e7 = True; break
                        if e7: break
                    if e7: break
                st['choices'] += 1; st['tb'] += tb; st['e7'] += e7
                st['tb_not_e7'] += int(tb and not e7); st['e7_not_tb'] += int(e7 and not tb)
                if e7 and not tb:
                    print('E7 BUT NOT TB (contradicts Lean lemma)', sorted(J.edges()), r, w, pm, flush=True)
                rt |= tb; re |= e7
            st['roots_tb'] += rt; st['roots_e7y1'] += re
        print(t, st, flush=True)
    print('FINAL', n, p, pd, st, flush=True)


