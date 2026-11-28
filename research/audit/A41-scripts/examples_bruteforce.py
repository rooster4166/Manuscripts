"""A41: brute-force check of the three small examples of nodata.tex Section 5.3.

Independent of ndsolve.h / route_ext / nd.c / fl.c.  For a graph F with no even vertex we
enumerate ALL Lovasz decompositions (partitions of E(F) into paths with exactly one end at every
vertex) by plain recursion over edge-disjoint paths (no constraint pruning, no memo), and then
test the constraints on every one of them.

Constraint semantics (manuscript Section 5 table):
  avoid[v] = set A: the path Q(v) ending at v contains no vertex of A    (condition (i) / routes)
  sib pairs (x, y): Q(x) != Q(y)                                            (condition (ii))
"""
import itertools
import sys


def lovasz_decomps(n, edges):
    """yield every Lovasz decomposition as a list of vertex sequences."""
    adj = {v: [] for v in range(n)}
    for i, (a, b) in enumerate(edges):
        adj[a].append((b, i))
        adj[b].append((a, i))
    for v in range(n):
        assert len(adj[v]) % 2 == 1, ("even vertex", v)
    m = len(edges)

    def rec(used, ended, paths):
        if len(used) == m:
            if len(ended) == n:
                yield [list(p) for p in paths]
            return
        # the smallest unended vertex must be an end of some remaining path
        todo = [v for v in range(n) if v not in ended]
        if not todo:
            return
        s = todo[0]

        def grow(path, vis, used2):
            cur = path[-1]
            for (w, e) in adj[cur]:
                if e in used2 or w in vis:
                    continue
                path.append(w)
                u3 = used2 | {e}
                if w not in ended:
                    paths.append(tuple(path))
                    yield from rec(u3, ended | {s, w}, paths)
                    paths.pop()
                yield from grow(path, vis | {w}, u3)
                path.pop()
        yield from grow([s], {s}, used)

    seen = set()
    for D in rec(frozenset(), frozenset(), []):
        key = frozenset(tuple(p) if p[0] < p[-1] else tuple(reversed(p)) for p in D)
        if key in seen:
            continue
        seen.add(key)
        yield D


def check_decomp(n, edges, D):
    E = {frozenset(e) for e in edges}
    used = []
    ends = [0] * n
    for P in D:
        assert len(set(P)) == len(P) and len(P) >= 2
        for a, b in zip(P, P[1:]):
            assert frozenset((a, b)) in E
            used.append(frozenset((a, b)))
        ends[P[0]] += 1
        ends[P[-1]] += 1
    assert len(used) == len(set(used)) == len(E)
    assert all(e == 1 for e in ends)


def satisfies(D, avoid, sibs):
    Q = {}
    for P in D:
        Q[P[0]] = P
        Q[P[-1]] = P
    for v, A in avoid.items():
        if set(Q[v]) & set(A):
            return False
    for x, y in sibs:
        if Q[x] is Q[y]:
            return False
    return True


def run(name, n, edges, avoid, sibs, nonedges_needed):
    E = {frozenset(e) for e in edges}
    for a, b in nonedges_needed:
        assert frozenset((a, b)) not in E, ("not a non-edge", a, b)
    deg = [0] * n
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    allD = list(lovasz_decomps(n, edges))
    for D in allD:
        check_decomp(n, edges, D)
    good = [D for D in allD if satisfies(D, avoid, sibs)]
    print(f"{name}: degrees {deg}; {len(allD)} Lovasz decompositions; {len(good)} satisfy the constraints")
    # sanity: every single constraint alone is satisfiable? (report)
    for v, A in avoid.items():
        ok = sum(1 for D in allD if satisfies(D, {v: A}, []))
        print(f"   alone: Q({v}) avoids {sorted(A)}: {ok} decompositions")
    for x, y in sibs:
        ok = sum(1 for D in allD if satisfies(D, {}, [(x, y)]))
        print(f"   alone: Q({x}) != Q({y}): {ok} decompositions")
    return len(good)


def hall_H1(n, edges, u, X):
    """(H1) at u with children X: |X cap C| <= (|C| - e(u, C)) / 2 for each component C of F - u."""
    adj = {v: set() for v in range(n)}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    rest = set(range(n)) - {u}
    seen = set()
    res = []
    for v in sorted(rest):
        if v in seen:
            continue
        comp = {v}
        fr = [v]
        while fr:
            x = fr.pop()
            for y in adj[x]:
                if y in rest and y not in comp:
                    comp.add(y)
                    fr.append(y)
        seen |= comp
        k = len(set(X) & comp)
        e = len(adj[u] & comp)
        res.append((sorted(comp), k, e, 2 * k <= len(comp) - e))
    return res


if __name__ == "__main__":
    # Example 5.3: the net; 3-chain 0 <- 1 <- 5 <- 3 and pair 2 <- 4
    net = [(0, 4), (4, 5), (5, 0), (0, 3), (1, 4), (2, 5)]
    g1 = run("net (Ex. 3-chain)", 6, net,
             {1: {0}, 5: {1}, 3: {5}, 2: {4}}, [],
             [(0, 1), (1, 5), (5, 3), (2, 4)])
    # the 3-chain alone and the pair alone are satisfiable?
    allD = list(lovasz_decomps(6, net))
    print("   3-chain alone:", sum(1 for D in allD if satisfies(D, {1: {0}, 5: {1}, 3: {5}}, [])))
    print("   3-chain as two 2-chains-like subsets: 0<-1<-5 plus pair 2<-4:",
          sum(1 for D in allD if satisfies(D, {1: {0}, 5: {1}, 2: {4}}, [])),
          "; 1<-5<-3 plus pair 2<-4:",
          sum(1 for D in allD if satisfies(D, {5: {1}, 3: {5}, 2: {4}}, [])))
    # Example 5.4: double star, centres p=0, q=1; leaves 2,3 at 0 and 4,5 at 1.
    # Route c x b with c a leaf at b: b = 0 (centre), c = 2 (leaf at 0), x = 4 (leaf at the other centre):
    # cx, xb non-edges; the route condition is x, b notin Q(c).
    ds = [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)]
    g2 = run("double star (Ex. routes)", 6, ds, {2: {4, 0}}, [], [(2, 4), (4, 0)])
    # every choice of (c, x, b) with cx, xb non-edges, distinct, on the double star
    E = {frozenset(e) for e in ds}
    allD = list(lovasz_decomps(6, ds))
    fails, failsE = 0, 0
    tot = 0
    for c, x, b in itertools.permutations(range(6), 3):
        if frozenset((c, x)) in E or frozenset((x, b)) in E:
            continue
        tot += 1
        ok = any(satisfies(D, {c: {x, b}}, []) for D in allD)
        ok2 = any(satisfies(D, {x: {c}, b: {x}}, []) for D in allD)   # the 2-chain c <- x <- b
        if not ok:
            fails += 1
            failsE += frozenset((c, b)) in E
        assert ok2, ("2-chain fails on double star", c, x, b)
    print(f"   double star: {tot} route triples, {fails} infeasible, of which {failsE} have cb in E; "
          f"every 2-chain on the same triples is satisfiable")
    # Example 5.6: claw with a 2-chain
    cl = [(0, 5), (0, 6), (0, 7), (1, 5), (2, 6), (3, 7), (4, 7), (5, 7), (6, 7)]
    g3 = run("claw + 2-chain (Ex. claw fails with H1)", 8, cl,
             {6: {5}, 3: {6}, 4: {6}, 1: {7}, 2: {1}}, [(3, 4)],
             [(5, 6), (6, 3), (6, 4), (7, 1), (1, 2)])
    print("   (H1) at 6 with X={3,4}:", hall_H1(8, cl, 6, [3, 4]))
    allD = list(lovasz_decomps(8, cl))
    print("   claw alone:", sum(1 for D in allD if satisfies(D, {6: {5}, 3: {6}, 4: {6}}, [(3, 4)])),
          "; 2-chain alone:", sum(1 for D in allD if satisfies(D, {1: {7}, 2: {1}}, [])))
    # the K_{1,3} star u <- {x, y} (Section 5.3): centre w = 0, leaves 1, 2, 3; star 3 <- {1, 2}
    k13 = [(0, 1), (0, 2), (0, 3)]
    g4 = run("K_{1,3} star 3 <- {1,2}", 4, k13, {1: {3}, 2: {3}}, [(1, 2)], [(3, 1), (3, 2)])
    print("   (H1) at 3 with X={1,2}:", hall_H1(4, k13, 3, [1, 2]))
    assert g1 == 0 and g2 == 0 and g3 == 0 and g4 == 0
    print("ALL EXAMPLES INFEASIBLE (brute force)")
