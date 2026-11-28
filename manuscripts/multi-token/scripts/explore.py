"""explore.py: exhaustive exploration of the k-token game (moves M, D, S of Definition 2.2) for the
instances of one graph; reports per instance the number of reachable states and the least
potential Phi = #tokens + #live tails reached (a schedule needs a terminal state, Phi <= 2).
usage: explore.py MODE(g6|resid) MAXSTATES < lines 'g6 [r1,r2,...]'"""
import sys, itertools
import networkx as nx
mode, cap = sys.argv[1], int(sys.argv[2])

def matchings(vs, J):
    if not vs: yield []; return
    a = vs[0]
    for b in vs[1:]:
        if J.has_edge(a, b):
            for pm in matchings([v for v in vs[1:] if v != b], J): yield [(a, b)] + pm

def succ(E, pairs, leaves, N):
    adj = {v: set() for v in range(N)}
    for (a, b) in E: adj[a].add(b); adj[b].add(a)
    toks = {v for v in adj if adj[v] and len(adj[v]) % 2 == 0}
    live = [i for i, (y, x) in enumerate(pairs) if leaves[i] in adj[y]]
    X = set()
    for i in live: X |= {leaves[i], pairs[i][1]}
    out = []
    for p in toks:
        for u in adj[p]:
            if u in X or u in toks or len(adj[u]) % 2 == 0: continue
            if any(t != p and t in adj[u] for t in toks): continue   # u adjacent to another token in K - pu
            out.append(E - {frozenset((p, u))})
        if len(adj[p]) == 2:
            a, b = sorted(adj[p])
            if b not in adj[a] and a not in leaves and b not in leaves and \
               all({a, b} != {pairs[i][0], pairs[i][1]} for i in live):
                out.append((E - {frozenset((p, a)), frozenset((p, b))}) | {frozenset((a, b))})
    for i in live:
        y = pairs[i][0]
        if len(adj[y]) % 2 == 1: out.append(E - {frozenset((y, leaves[i]))})
    return out, len(toks), len(live)

for line in sys.stdin:
    parts = line.split()
    if not parts: continue
    s = parts[0]
    rl = set(map(int, parts[1].split(','))) if len(parts) > 1 else None
    J = nx.from_graph6_bytes(s.encode())
    if mode == 'resid':
        z = J.number_of_nodes(); J.add_edges_from((z, u) for u in range(6))
    else:
        z = [v for v in J if J.degree(v) % 2 == 0][0]
    U = sorted(J[z]); n = J.number_of_nodes()
    for r in U:
        if rl is not None and r not in rl: continue
        if J.degree(r) < 3: continue
        best = None; states = 0; hit = False
        for w in U:
            if w == r: continue
            for pm in matchings([u for u in U if u not in (r, w)], J):
                for o in itertools.product((0, 1), repeat=len(pm)):
                    pairs = [(a, b) if oi else (b, a) for (a, b), oi in zip(pm, o)]
                    E = {frozenset(e) for e in J.edges()}
                    E -= {frozenset((z, w))}
                    for (y, x) in pairs: E -= {frozenset((z, y)), frozenset((z, x)), frozenset((y, x))}
                    leaves = [n + i for i in range(len(pairs))]
                    E |= {frozenset((pairs[i][0], leaves[i])) for i in range(len(pairs))}
                    seen = {frozenset(E)}; stack = [frozenset(E)]; minphi = 99
                    while stack and len(seen) < cap:
                        S = stack.pop()
                        nx_, nt, nl = succ(set(S), pairs, leaves, n + len(pairs))
                        minphi = min(minphi, nt + nl)
                        for S2 in nx_:
                            S2 = frozenset(S2)
                            if S2 not in seen: seen.add(S2); stack.append(S2)
                    states += len(seen); hit = hit or len(seen) >= cap
                    best = minphi if best is None else min(best, minphi)
        print('ROOT %s r=%d states=%d min_phi=%s%s' % (s, r, states, best, ' capped' if hit else ''))
