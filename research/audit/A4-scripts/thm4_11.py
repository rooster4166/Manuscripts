import sys, itertools, time
from common import *

def ham_paths(G):
    n = G.number_of_nodes()
    return [P for P in enumerate_paths(G) if len(P.verts) == n]

def cycles_on(S):
    S = list(S)
    if len(S) == 2:
        a, b = S
        return [[(a, b), (a, b)]]
    first = S[0]
    out = []
    seen = set()
    for perm in itertools.permutations(S[1:]):
        cyc = (first,) + perm
        key = min(cyc[1], cyc[-1])
        if perm[0] > perm[-1]:
            continue
        out.append([(cyc[i], cyc[(i + 1) % len(cyc)]) for i in range(len(cyc))])
    return out

def run(k, do_Q=True, do_S=True, do_cor12=True):
    n = 2 * k + 1
    log = []
    t0 = time.time()
    for m in range(0, k):
        L = k - m
        for H in iso_classes_edge_sets(n, m):
            G = complement_of(n, H)
            allpaths = enumerate_paths(G)
            r = solve(G, paths=allpaths)
            assert r.status == "OPTIMAL" and verify_partition(G, r.paths)
            okp = (r.value == k + 1)
            # (b) every Q of length L completes by k Hamilton paths
            nQ = 0; badQ = []
            if do_Q:
                Qs = [P for P in allpaths if len(P.verts) == L + 1]
                for Q in Qs:
                    GQ = G.copy()
                    GQ.remove_edges_from(zip(Q.verts, Q.verts[1:]))
                    hp = ham_paths(GQ)
                    st, sol = solve_pairs(GQ, None, paths=hp, exact_count=k)
                    nQ += 1
                    if sol is None or not verify_partition(GQ, sol):
                        badQ.append((Q.verts, st))
            # (g) Thm 11 / Cor 12
            nS = 0; badS = []; badC = []; allcyc_fail = 0
            if do_S:
                dH = dict(H.degree())
                for S in itertools.combinations(range(n), L + 1):
                    b = {v: dH[v] + (2 if v in S else 0) for v in range(n)}
                    st, sol = solve_pairs(G, None, exact_ends=b, paths=allpaths, exact_count=k + 1)
                    nS += 1
                    if sol is None or not verify_partition(G, sol):
                        badS.append((S, st)); continue
                    if do_cor12:
                        found = False; nfail = 0
                        for C in cycles_on(S):
                            pc = {}
                            for e in list(H.edges()) + C:
                                pc[frozenset(e)] = pc.get(frozenset(e), 0) + 1
                            st2, sol2 = solve_pairs(G, None, pair_counts=pc, paths=allpaths, exact_count=k + 1)
                            if sol2 is not None and verify_partition(G, sol2):
                                found = True
                            else:
                                nfail += 1
                        if not found:
                            badC.append(S)
                        if nfail:
                            allcyc_fail += 1
            log.append(dict(k=k, m=m, H=sorted(H.edges()), p=r.value, okp=okp, nQ=nQ, badQ=badQ,
                            nS=nS, badS=badS, badCor12=badC, S_with_some_cycle_failing=allcyc_fail))
            print(log[-1], flush=True)
    print("time", time.time() - t0)
    return log

if __name__ == "__main__":
    k = int(sys.argv[1])
    run(k)
