"""A24 (c): trace one PTM instance: for the first successful (orientation, walk, base) of
ptmwalk_audit.py, print each walk-back step: target p_i, source p_{i+1}, whether p_i in N(x),
the path through x p_i and its end e on x's side, N(p_i), and the forced chain."""
import sys, ast
sys.argv += []
import tf, ptmwalk_audit as PW
g6s, a1, b1, a2, b2 = sys.argv[1], *map(int, sys.argv[2:6])
G = tf.add(tf.from_g6(g6s), (a1, b1), (a2, b2))
L1, L2 = PW.L1, PW.L2
for (e, f) in (((a1, b1), (a2, b2)), ((a2, b2), (a1, b1))):
    for a, b in (e, e[::-1]):
        for x, y in (f, f[::-1]):
            import networkx as nx
            H = tf.to_nx(G); Hb = H.copy(); Hb.remove_nodes_from([b, x])
            if not nx.has_path(Hb, y, a): continue
            for P in sorted((tuple(p) for p in nx.all_simple_paths(Hb, y, a, cutoff=7)), key=len):
                K = tf.add(tf.rem(G, (a, b)), (L1, b))
                Mg = tf.rem(K, (x, y), *[(P[i], P[i + 1]) for i in range(len(P) - 1)])
                for D0 in tf.decomps(Mg, tf.lovasz_b(Mg), sep=[(x, y), (a, L1), (L1, y)]):
                    Qy = tf.Qc(D0, y)
                    D = [Pq for Pq in D0 if Pq is not Qy] + [tf._orient(Qy, y)[::-1] + (L2,)]
                    H2 = tf.add(tf.rem(K, (x, y)), (L2, y))
                    log = []; okall = True
                    for i in range(len(P) - 1):
                        Ki = tf.rem(H2, *[(P[j], P[j + 1]) for j in range(i, len(P) - 1)])
                        w = P[i]; t = P[i + 1]
                        tight = x in Ki[w]
                        info = None
                        if tight:
                            Pxw = [Q for Q in D if any({Q[j], Q[j + 1]} == {x, w} for j in range(len(Q) - 1))][0]
                            j = [j for j in range(len(Pxw) - 1) if {Pxw[j], Pxw[j + 1]} == {x, w}][0]
                            eend = Pxw[0] if Pxw[j] == x else Pxw[-1]
                            info = dict(path=Pxw, e=eend, e_in_src=(eend == t or eend in Ki[w]), Nw=sorted(Ki[w]))
                        outs = tf.fan_moves(D, t, w)
                        log.append((i, 'target', w, 'source', t, 'tight', tight, info,
                                    'chains', [ch for _, ch, _ in outs]))
                        if not outs: okall = False; break
                        D = outs[0][0]
                    if not okall: continue
                    D4 = PW.merge(PW.merge(D, L2, x), L1, a)
                    try: tf.check(G, D4, tf.lovasz_b(G))
                    except AssertionError: continue
                    Pa = [Q for Q in D4 if (Q[0] == a and Q[1] == b) or (Q[-1] == a and Q[-2] == b)]
                    Px = [Q for Q in D4 if (Q[0] == x and Q[1] == y) or (Q[-1] == x and Q[-2] == y)]
                    if Pa and Px and Pa[0] != Px[0]:
                        print('orientation a,b,x,y =', (a, b, x, y), 'walk', P)
                        print('base D0', D0)
                        for r in log: print('  step', r)
                        print('result', D4)
                        sys.exit(0)
