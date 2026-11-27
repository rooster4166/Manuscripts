#!/usr/bin/env python3
"""Audit A13: Lemma 1 (four forms), Lemma 6 (signed form and its flow statement) and Lemma 7
(parity) checked vertex by vertex on every half-set of every connected graph in a graph6 file.

For each half-set M and vertex v, compare
  (a) b(W) <= |delta(W)| + 2k - d(v) - b(v) for all W subset of V - v;
  (c) e(v, Y) <= b(Y) + |delta_{G-v}(Y)| for all Y subset of V - v;
  (s) x_M(Y) <= |delta_{G^v}(Y)| for all Y subset of V - v;
and, with --flow, also
  (d) an arm system exists: max flow d(v) in the network of Lemma 1;
  (g) Lemma 6's routing in G^v: unmarked even vertices other than v send one unit each to distinct
      marked vertices or to v (uncapacitated).
Lemma 7 is checked on every (v, Y): |delta_{G^v}(Y)| = |Y cap Ev| (mod 2).
Usage: a13_forms.py FILE [--flow]"""
import itertools
import sys

import networkx as nx


def check(G, flow):
    n = G.number_of_nodes()
    deg = [G.degree(v) for v in range(n)]
    Ev = [v for v in range(n) if deg[v] % 2 == 0]
    adj = [set(G[v]) for v in range(n)]
    k2 = n
    N = 1 << n
    cut = [0] * N
    for W in range(N):
        cut[W] = sum(1 for a, c in G.edges() if (W >> a & 1) != (W >> c & 1))
    # per v, Y: |delta_{G-v}(Y)| and |delta_{G^v}(Y)|
    pre = {}
    for v in range(n):
        for Y in range(N):
            if Y >> v & 1:
                continue
            eY = sum(1 for y in adj[v] if Y >> y & 1)
            dGmv = cut[Y] - eY
            nonnb = sum(1 for y in range(n) if Y >> y & 1 and y not in adj[v])
            dGv = dGmv + nonnb
            ev = sum(1 for y in Ev if Y >> y & 1)
            assert (dGv - ev) % 2 == 0, 'Lemma 7'
            pre[(v, Y)] = (eY, dGmv, dGv)
    out = [0, 0]
    for Mt in itertools.combinations(Ev, len(Ev) // 2):
        M = set(Mt)
        b = [1 if deg[v] % 2 else (2 if v in M else 0) for v in range(n)]
        x = [0 if deg[v] % 2 else (-1 if v in M else 1) for v in range(n)]
        for v in range(n):
            a_ok = c_ok = s_ok = True
            for Y in range(N):
                if Y >> v & 1:
                    continue
                bY = sum(b[y] for y in range(n) if Y >> y & 1)
                xY = sum(x[y] for y in range(n) if Y >> y & 1)
                eY, dGmv, dGv = pre[(v, Y)]
                if bY > cut[Y] + k2 - deg[v] - b[v]:
                    a_ok = False
                if eY > bY + dGmv:
                    c_ok = False
                if xY > dGv:
                    s_ok = False
            assert a_ok == c_ok == s_ok, ('forms differ', Mt, v)
            if flow:
                D = nx.DiGraph()
                for p, q in G.edges():
                    if v in (p, q):
                        continue
                    D.add_edge(p, q, capacity=1)
                    D.add_edge(q, p, capacity=1)
                for y in adj[v]:
                    D.add_edge('s', y, capacity=1)
                for z in range(n):
                    if z != v and b[z]:
                        D.add_edge(z, 't', capacity=b[z])
                D.add_node('s')
                D.add_node('t')
                d_ok = nx.maximum_flow_value(D, 's', 't') == deg[v]
                # Lemma 6 routing in G^v
                H = nx.DiGraph()
                Gv = [(p, q) for p, q in G.edges() if v not in (p, q)] + \
                     [(v, w) for w in range(n) if w != v and w not in adj[v]]
                for p, q in Gv:
                    H.add_edge(p, q, capacity=1)
                    H.add_edge(q, p, capacity=1)
                S = [y for y in Ev if y != v and y not in M]
                for y in S:
                    H.add_edge('s', y, capacity=1)
                for y in M:
                    if y != v:
                        H.add_edge(y, 't', capacity=1)
                H.add_edge(v, 't')  # no capacity attribute: infinite
                H.add_node('s')
                H.add_node('t')
                g_ok = nx.maximum_flow_value(H, 's', 't') == len(S)
                assert d_ok == a_ok == g_ok, ('flow forms differ', Mt, v, a_ok, d_ok, g_ok)
            out[a_ok] += 1
    return out


if __name__ == '__main__':
    flow = '--flow' in sys.argv
    tot = [0, 0]
    graphs = 0
    for line in open(sys.argv[1]):
        G = nx.from_graph6_bytes(line.strip().encode())
        if G.number_of_nodes() % 2:
            continue
        r = check(G, flow)
        graphs += 1
        tot[0] += r[0]
        tot[1] += r[1]
    print(sys.argv[1], 'graphs', graphs, '(M, v) pairs:', sum(tot), 'satisfied at v:', tot[1],
          'violated at v:', tot[0], '| forms (a), (c), signed agree' + (', and (d), Lemma 6 flow' if flow else ''),
          '; Lemma 7 holds on every (v, Y)')
