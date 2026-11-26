"""Independent Python re-verification of exported Thm 124 certificates (no shared code with the C search)."""
import itertools, sys, networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
PAIRS=[(i,j) for i in range(7) for j in range(i+1,7)]
def E(m): return {frozenset(PAIRS[k]) for k in range(21) if m>>k&1}
def graph(es):
    G=nx.Graph(); G.add_nodes_from(range(7)); G.add_edges_from(tuple(e) for e in es); return G
def struct(es):
    G=graph(es)
    tris=[set(t) for t in itertools.combinations(range(7),3) if all(frozenset(p) in es for p in itertools.combinations(t,2))]
    if any(len(a&b)==1 for a,b in itertools.combinations(tris,2)): return False
    # block with max degree >= 4  <=> some 2-connected induced subgraph has a vertex of degree >= 4 (brute force)
    for r in range(5,8):
        for S in itertools.combinations(range(7),r):
            H=G.subgraph(S)
            if max(d for _,d in H.degree())>=4 and nx.is_biconnected(H): return False
    return True
def parse_tree(s,i=0):
    if s[i]=='L': return ('L',),i+1
    assert s[i]=='('; j=s.index(':',i); w=int(s[i+1:j]); i=j+1; kids=[]
    while s[i]=='[':
        k=s.index(' ',i); t=int(s[i+1:k]); sub,i=parse_tree(s,k+1); assert s[i]==']'; i+=1; kids.append((t,sub))
    assert s[i]==')'; return ('N',w,kids),i+1
def check_tree(G,M,b,T):
    if T[0]=='L': return len(M)==0
    _,w,kids=T
    if not kids: return False
    cur=G-M
    z=sum(1 for e in cur if w in e and b[next(iter(e-{w}))]==0)
    S=[t for t,_ in kids]
    if len(set(S))!=len(S): return False
    for t in S:
        if frozenset((w,t)) not in M or b[t]<=0: return False
    if sum(b[t] for t in S)<=z: return False
    for t,sub in kids:
        b2=dict(b); b2[w]+=1; b2[t]-=1
        if not check_tree(G,M-{frozenset((w,t))},b2,sub): return False
    return True
def is_forest_on(es,Z):
    H=nx.Graph(); H.add_nodes_from(Z); H.add_edges_from(tuple(e) for e in es if e<=Z)
    return nx.is_forest(H)
def admissible_A(Fes,p,q,O):
    out=set()
    O=list(O)
    for assign in itertools.product((0,1,2),repeat=len(O)):
        l1=[O[i] for i in range(len(O)) if assign[i]==1]; l2=[O[i] for i in range(len(O)) if assign[i]==2]
        for o1 in itertools.permutations(l1):
            for o2 in itertools.permutations(l2):
                seq1=[p]+list(o1); seq2=[q]+list(o2)
                cand=[frozenset(x) for s in (seq1,seq2) for x in zip(s,s[1:]) if frozenset(x) in Fes]
                for r in range(len(cand)+1):
                    for sub in itertools.combinations(cand,r): out.add(frozenset(sub))
    return out
def is_simple_path(Les,p,q,Y):
    if not Les: return False
    H=graph(Les); H.remove_nodes_from([v for v in range(7) if H.degree(v)==0])
    if p not in H or q not in H: return False
    if not set(H.nodes())<=set(Y): return False
    return nx.is_connected(H) and H.degree(p)==1 and H.degree(q)==1 and all(d==2 for v,d in H.degree() if v not in (p,q))
recs=[]; cur=None
for line in open(sys.argv[1]):
    t=line.split()
    if t[0] in 'SFX':
        cur={'kind':t[0],'F':int(t[1]),'Y':int(t[2]) if t[0]=='F' else None,'C':[]}; recs.append(cur)
    else:
        cur['C'].append((int(t[1]),int(t[2]),int(t[3]),int(t[4]),int(t[5]),line.split(None,6)[6].strip()))
print('records',len(recs))
# completeness of representatives: pairwise non-isomorphic and orbit sizes sum to 2^21
tot=0
for r in recs:
    G=graph(E(r['F'])); aut=sum(1 for _ in GraphMatcher(G,G).isomorphisms_iter()); tot+=5040//aut
print('sum of orbit sizes',tot,'== 2^21' if tot==2**21 else 'MISMATCH')
nstruct=0; bad=0; nchoice=0; Gs=set(); maxD=0
for r in recs:
    Fes=E(r['F'])
    s=struct(Fes)
    if r['kind']=='S':
        if not s: bad+=1; print('claimed structural but not',r['F'])
        nstruct+=1; continue
    if r['kind']=='X' or s: bad+=1; print('bad kind',r); continue
    Y=[v for v in range(7) if r['Y']>>v&1]; O=[v for v in range(7) if v not in Y]
    if len(Y)<5: bad+=1; print('small Y'); continue
    need={(p,q,A) for p,q in itertools.combinations(Y,2) for A in admissible_A(Fes,p,q,O)}
    have={}
    for p,q,Am,Lm,Dm,tree in r['C']:
        A=frozenset(E(Am)); L=E(Lm); D=E(Dm)
        ok = A<=Fes and is_simple_path(L,p,q,Y) and L<=Fes and not (L&A)
        G=Fes-A-L
        ok = ok and D<=G and len(D)<=5
        b={v:sum(1 for e in D if v in e)%2 for v in range(7)}
        Z={v for v in range(7) if b[v]==0}
        ok = ok and is_forest_on(G-D,Z)
        T,_=parse_tree(tree)
        ok = ok and check_tree(G,D,b,T)
        if not ok: bad+=1; print('bad cert',r['F'],p,q,Am,Lm,Dm,tree)
        have[(p,q,A)]=True; Gs.add((frozenset(G))); maxD=max(maxD,len(D))
    miss=need-set(have)
    if miss: bad+=1; print('missing choices',r['F'],len(miss))
    nchoice+=len(need)
print('structural',nstruct,'certified reps',sum(1 for r in recs if r['kind']=='F'),'choices',nchoice,'distinct G',len(Gs),'max|D|',maxD,'BAD',bad)
