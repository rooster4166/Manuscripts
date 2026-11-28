# emit graph6 of B = J - z (vertex order kept, z removed), with a header comment of J g6 and the map
import sys, networkx as nx
for line in sys.stdin:
    s=line.split()[0]
    J=nx.from_graph6_bytes(s.encode())
    ev=[v for v in J if J.degree(v)%2==0]; z=ev[0]
    B=J.copy(); B.remove_node(z)
    B=nx.convert_node_labels_to_integers(B, ordering='sorted')
    print(nx.to_graph6_bytes(B,header=False).decode().strip())
