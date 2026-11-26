import itertools, networkx as nx
def shape(name):
    E={'K0':'ab ac ad ae bc bd be','M':'ab ac ad ae bc de','P':'ab ac ad ae bc cd de','C':'ab ac ad ae bc cd de eb'}
    E['K1']=E['K0']+' cd'; E['K2']=E['K1']+' de'; E['K3']=E['K2']+' ce'
    E['P4']=E['P']; E['C4']=E['C']
    G=nx.Graph(); G.add_nodes_from('abcde'); G.add_edges_from([tuple(s) for s in E[name].split()]); return G
def fe(s): return frozenset(s)
def check_row(S,pq,L,r1,r2,z,verbose=False):
    G=shape(S); errs=[]
    p,q=pq
    # L must be a simple path p..q in G (or reversed)
    if not (L[0]==p and L[-1]==q or L[0]==q and L[-1]==p): errs.append('L ends')
    if len(set(L))!=len(L): errs.append('L not simple')
    LE=[fe(L[i:i+2]) for i in range(len(L)-1)]
    for e in LE:
        if not G.has_edge(*e): errs.append('L edge missing '+''.join(sorted(e)))
    rest={fe(e) for e in G.edges()}-set(LE)
    e1,e2=fe(r1),fe(r2)
    if e1 not in rest or e2 not in rest: errs.append('deleted edge not available')
    if e1 & e2: errs.append('deleted edges not disjoint')
    # parity: all X even after R removal (p,q interior of R). deleting e1,e2 flips 4 sites
    even=[x for x in 'abcde' if x not in e1|e2]
    if even!=[z]: errs.append(f'even sites {even} != z={z}')
    # restoration 1: r1 = x y : receiver x, donor y
    cur=rest-{e1,e2}
    x,y=r1[0],r1[1]
    zeros={z}
    nb={w for e in cur if x in e for w in e if w!=x}
    if nb & zeros: errs.append(f'step1 receiver {x} sees zero {nb&zeros}')
    if y in zeros: errs.append('donor1 zero')
    cur=cur|{e1}; zeros={z,y}
    x2,y2=r2[0],r2[1]
    nb={w for e in cur if x2 in e for w in e if w!=x2}
    if nb & zeros: errs.append(f'step2 receiver {x2} sees zero {nb&zeros}')
    if y2 in zeros: errs.append('donor2 zero')
    if x2==x: errs.append('same receiver twice')
    return errs, (x,x2)
L121=[l.split() for l in """K0 ab acb ad eb c
K0 ac adbc ac be d
K0 cd caebd ad bc e
K1 ab acdb cb da e
K1 ac aebdc ad bc e
K1 ae acdbe bc da e
K1 cd caebd ab dc e
K1 ce cadbe ba cd e
K2 ab acdeb bc da e
K2 ac abedc bd ca e
K2 ce cabde cb da e
K3 ab acdeb bc da e
M ab acb ab de c
M bc bc de ba c
M bd baed ad bc e
P ab adcb ba de c
P ac aedc ad bc e
P bc baedc ad bc e
P bd bcaed ab cd e
P be bacde bc da e
P cd caed ab dc e
C ab acdeb bc da e
C bc baedc ad cb e
C bd bcaed ab cd e""".splitlines()]
bad=0
cov={}
for S,pq,L,a,b,z in L121:
    errs,rec=check_row(S,pq,L,a,b,z)
    if errs: bad+=1; print('L121 row',S,pq,L,a,b,z,'->',errs)
    cov.setdefault(S,set()).add(fe(pq))
print('Lemma 121 rows checked:',len(L121),'bad:',bad)
def autos(G):
    GM=nx.algorithms.isomorphism.GraphMatcher(G,G)
    return list(GM.isomorphisms_iter())
for S in ['K0','K1','K2','K3','M','P','C']:
    G=shape(S); A=autos(G)
    allpairs={fe(p) for p in itertools.combinations('abcde',2)}
    covered=set()
    for pr in cov[S]:
        for f in A: covered.add(fe(f[v] for v in pr))
    print(S,'|Aut|=',len(A),'pairs covered up to Aut:',len(covered),'of 10', '' if covered==allpairs else 'MISSING '+str([''.join(sorted(x)) for x in allpairs-covered]))
# Thm 123 M table (contacts b,c), symmetries b<->c, d<->e
T123=[l.split() for l in """ab acb de ba c
ad aed ad bc e
bc bc de ba c
bd baed ad bc e
de de bc da e""".splitlines()]
bad=0; covered=set()
syms=[{'a':'a','b':'b','c':'c','d':'d','e':'e'},{'a':'a','b':'c','c':'b','d':'d','e':'e'},{'a':'a','b':'b','c':'c','d':'e','e':'d'},{'a':'a','b':'c','c':'b','d':'e','e':'d'}]
for pq,L,a,b,z in T123:
    errs,rec=check_row('M',pq,L,a,b,z)
    if not (set(rec)&{'b','c'}): errs.append('no recipient in {b,c}')
    if errs: bad+=1; print('T123 row',pq,L,a,b,z,errs)
    for f in syms: covered.add(fe(f[v] for v in pq))
print('Thm 123 M rows:',len(T123),'bad:',bad,'pairs covered:',len(covered))
# Thm 130 forest table
T130={'K0':'a b ca da ea','K1':'acb bca cab dab eabc','K2':'abcd bacd cabd dacb eabd','K3':'abcde bacde cabde dabce eabcd',
      'M':'a ba ca da ea','P4':'a ba ca da ea','C4':'abcd bca cba dca eba'}
bad=0
for S,row in T130.items():
    G=shape(S)
    for p,seg in zip('abcde',row.split()):
        e=[]
        if seg[0]!=p: e.append('start')
        if len(set(seg))!=len(seg): e.append('not simple')
        SE=[fe(seg[i:i+2]) for i in range(len(seg)-1)]
        for x in SE:
            if not G.has_edge(*x): e.append('missing edge'+''.join(sorted(x)))
        H=G.copy(); H.remove_edges_from([tuple(x) for x in SE if G.has_edge(*x)]); H.remove_node(seg[-1])
        if not nx.is_forest(H): e.append('not forest')
        if e: bad+=1; print('T130',S,p,seg,e)
print('Thm 130 table entries: 35 bad:',bad)
