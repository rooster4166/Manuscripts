import sys, random
sys.argv = ['x', 'none']
src = open(sys.argv[0] if False else '/tmp/claude-0/-home-user-Manuscripts/7bcde938-d618-5679-84f3-4739c83be31f/scratchpad/aud28.py').read().split('if __name__')[0]
exec(src)
import networkx as nx
def run(n, d, count, seed, p, pdense):
    rng = random.Random(seed)
    st = dict(graphs=0, conn3=0, choices=0, both=0, neither=0, dis=0, roots=0, t1=0, base_root=0, t1_no_base=0, nodata=0)
    for t in range(count):
        J = gen_J(n, d, rng, p=p, pdense=pdense)
        st['graphs'] += 1; c3 = nx.node_connectivity(J) >= 3; st['conn3'] += int(c3)
        B = J.copy(); B.remove_node(0); Bv = sorted(B.nodes()); k = (n - 1) // 2
        for r in sorted(J.neighbors(0)):
            st['roots'] += 1
            t1 = t1_terminal(list(B.edges()), Bv, r, k, []); st['t1'] += int(t1)
            dc = data_choices(J, 0, r); st['nodata'] += int(not dc)
            anyb = False
            for w, pm in dc:
                M = J.copy(); M.remove_edges_from([(0, w)] + [(0, x) for q in pm for x in q] + pm)
                b = [M.degree(v) % 2 for v in range(n)]
                lhs = lovasz_disj(list(M.edges()), n, b, pm)
                rhs = t1_terminal(list(B.edges()), Bv, r, k, pm)
                st['choices'] += 1
                if lhs and rhs: st['both'] += 1
                elif not lhs and not rhs: st['neither'] += 1
                else:
                    st['dis'] += 1; print('DISAGREE', lhs, rhs, sorted(J.edges()), r, w, pm, flush=True)
                anyb |= lhs
            st['base_root'] += int(anyb)
            if t1 and dc and not anyb:
                st['t1_no_base'] += 1
                print('T1 but no base', sorted(J.edges()), 'r', r, 'kappa3', c3, flush=True)
        print(n, d, t, st, flush=True)
    print('FINAL', n, d, p, pdense, st, flush=True)
run(int(sys.argv[1]) if False else int(__import__('os').environ['N']), int(__import__('os').environ['D']), int(__import__('os').environ['C']), int(__import__('os').environ['SEED']), float(__import__('os').environ['P']), float(__import__('os').environ['PD']))
