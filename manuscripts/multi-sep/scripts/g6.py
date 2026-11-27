"""graph6 decoding."""
def g6_to_adj(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        x = ord(ch) - 63
        bits += [(x >> (5 - i)) & 1 for i in range(6)]
    K = {v: set() for v in range(n)}
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                K[i].add(j); K[j].add(i)
            k += 1
    return K
