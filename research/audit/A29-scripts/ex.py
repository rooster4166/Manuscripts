"""A29: check Examples FsOrg (10.1), DEk (10.3), FsPzw (10.2) with dllib/enum."""
import sys
sys.path.insert(0,'.')
from dllib import *
def show(name,n,E):
    d=degrees(n,E); print(name,"n=",n,"edges",E); print(" deg",d," even",even_vertices(n,E))
# FsOrg
n,E=g6_decode("FsOrg"); show("FsOrg",n,E)
ref=sorted([(0,1),(0,2),(0,3),(1,4),(1,6),(2,5),(2,6),(3,5),(3,6),(5,6)])
print(" matches stated edges:", sorted(E)==ref)
g,a,b=6,1,5
Dc=[[0,3,5],[1,0,2,5,6],[3,6,1,4]]
E2=remove_edge(E,6,2)
print(" child decomposition Lovasz:",is_lovasz(n,E2,Dc)," Q(b)=",Q(Dc,b)," Q(a)=",Q(Dc,a))
D2,ch=fan_transfer(Dc,6,2); print(" transfer:",D2,"chain",ch,"Lovasz in G:",is_lovasz(n,E,D2)," Q(b)=",Q(D2,b)," Q(a)=",Q(D2,a)," good:",dl_good(D2,a,b))
for u in (2,3):
    E2=remove_edge(E,g,u); Ds,c=enum_decomps(n,E2)
    good=[D for D in Ds if dl_good(D,a,b)]
    bad=0; badSa=0
    for D in good:
        D2,ch=fan_transfer(D,g,u)
        assert is_lovasz(n,E,D2)
        if not dl_good(D2,a,b): bad+=1
    print(" target",u,": child decomps",len(Ds),"complete",c,"good",len(good),"bad transfers",bad)
# DEk
n,E=g6_decode("DEk"); show("DEk",n,E)
print(" matches stated:",sorted(E)==sorted([(0,3),(0,4),(1,3),(2,4),(3,4)]))
Ds,c=enum_decomps(n,E); print(" all decomps:",Ds)
print(" Q(3) avoiding 2:",[Q(D,3) for D in Ds if 2 not in Q(D,3)])
# FsPzw
n,E=g6_decode("FsPzw"); show("FsPzw",n,E)
g,a,b=1,0,4
A=adjsets(n,E); print(" N(g)",A[g]," N(a)",A[a]," N(b)",A[b]," common",A[a]&A[b])
Dp=[[1,5,2,6,4],[2,0,3,5,6],[3,6,1,4,5]]
E2=remove_edge(E,0,1)
print(" G-01 decomposition Lovasz:",is_lovasz(n,E2,Dp))
print(" separates a,b:",all(not(a in P and b in P) for P in Dp)," Q'(g)=",Q(Dp,g)," Q'(b)=",Q(Dp,b))
D2,ch=fan_transfer(Dp,g,a); print(" transfer:",D2,ch,is_lovasz(n,E,D2),"good",dl_good(D2,a,b))
