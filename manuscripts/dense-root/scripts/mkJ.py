# resid format: graph6 of B with N(z) = {0..5}; emit graph6 of J = B + z (z = last vertex)
import sys, networkx as nx
for line in sys.stdin:
    s=line.split()[0]
    B=nx.from_graph6_bytes(s.encode()); n=B.number_of_nodes()
    J=B.copy(); J.add_node(n)
    for u in range(6): J.add_edge(n,u)
    ev=[v for v in J if J.degree(v)%2==0]
    assert ev==[n], (s, ev)
    print(nx.to_graph6_bytes(J,header=False).decode().strip())
