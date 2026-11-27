import itertools, sys
exec(open('/tmp/claude-0/-home-user-Manuscripts/7bcde938-d618-5679-84f3-4739c83be31f/scratchpad/e7lib.py').read())
exec(open('/tmp/claude-0/-home-user-Manuscripts/7bcde938-d618-5679-84f3-4739c83be31f/scratchpad/tb9.py').read().split("st = dict")[0].split("ORACLE, FILE")[0])
def shape(J, U):
    D = nx.complement(J.subgraph(U)); m = D.number_of_edges(); degs = sorted(d for _, d in D.degree())
    if m == 0: return 'empty'
    if m == 1: return 'K2'
    if m == 2 and degs[-1] == 2: return 'P3'
    if m == 3 and degs[-3:] == [2, 2, 2]: return 'K3'
    if m == 4 and degs[-4:] == [2, 2, 2, 2] and nx.is_connected(D.subgraph([v for v in D if D.degree(v)])): return 'C4'
    return 'other'
st = dict(graphs=0, choices=0, tb=0, e7=0, tb_not_e7=0, e7_not_tb=0, roots=0, roots_tb=0, roots_e7y1=0, labellings=0, lab_e7=0)
for line in open('/home/user/Manuscripts/manuscripts/terminal-matching/scripts/out/d6_9.g6'):
    line = line.strip()
    if not line: continue
    B = nx.from_graph6_bytes(line.encode()); J = nx.relabel_nodes(B, {v: v+1 for v in B})
    U = sorted(v for v in J if J.degree(v) % 2 == 0)
    for u in U: J.add_edge(0, u)
    if shape(J, U) == 'other': continue
    st['graphs'] += 1; n = 9
    for r in U:
        st['roots'] += 1; rt = re = False
        for w, pm in data_choices(J, 0, r):
            M = J.copy(); M.remove_edges_from([(0, w)] + [(0, x) for q in pm for x in q] + pm)
            E = list(M.edges()); b = [M.degree(v) % 2 for v in range(n)]
            tb = any(decomp_exists(E, n, b, tb_ok(pm, o)) for o in itertools.product([0, 1], repeat=2))
            e7 = False
            for (P1, P2) in (pm, pm[::-1]):
                for (x1, y2) in (P1, P1[::-1]):
                    for (x2, y3) in (P2, P2[::-1]):
                        st['labellings'] += 1
                        g = decomp_exists(E, n, b, e7_ok(0, x1, x2, y2, w, y3))
                        st['lab_e7'] += g; e7 |= g
            st['choices'] += 1; st['tb'] += tb; st['e7'] += e7
            st['tb_not_e7'] += int(tb and not e7); st['e7_not_tb'] += int(e7 and not tb)
            if tb and not e7: print('TB BUT NO E7 LABELLING', line, 'r', r, 'w', w, pm, flush=True)
            if e7 and not tb: print('E7 BUT NOT TB', line, r, w, pm, flush=True)
            rt |= tb; re |= e7
        st['roots_tb'] += rt; st['roots_e7y1'] += re
    print(st, flush=True)
print('FINAL', st)
