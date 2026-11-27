"""Audit A22c: recount the 3-connected J of order n (7, 9) with a unique even vertex z, d(z) = 6.
Own code (no networkx connectivity); two routes:
  A: nauty-geng -c -d3 n, keep J with exactly one even vertex, of degree 6, J 3-connected;
  B: nauty-geng -c (n-1) as G' = J - z; keep G' with exactly six even vertices; J = G' + z(evens)
     must be 3-connected.  Iso classes of J <-> iso classes of G' (z is determined).
Compares the G' sets (canonical labelling by nauty-labelg) with the repo's out/d6_<n>.g6.
Also counts perfect matchings of N(z) and the simple ones (no pair adjacent in J - z)."""
import subprocess, sys, itertools

REPO_OUT = '/home/user/Manuscripts/manuscripts/terminal-matching/scripts/out'


def g6_decode(s):
    s = s.strip()
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        x = ord(ch) - 63
        for k in range(5, -1, -1):
            bits.append((x >> k) & 1)
    A = [[0] * n for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                A[i][j] = A[j][i] = 1
            k += 1
    return n, A


def g6_encode(n, A):
    bits = [A[i][j] for j in range(1, n) for i in range(j)]
    while len(bits) % 6:
        bits.append(0)
    s = chr(n + 63)
    for k in range(0, len(bits), 6):
        x = 0
        for b in bits[k:k + 6]:
            x = 2 * x + b
        s += chr(x + 63)
    return s


def connected_without(n, A, gone):
    vs = [v for v in range(n) if v not in gone]
    if not vs:
        return True
    seen = {vs[0]}; st = [vs[0]]
    while st:
        x = st.pop()
        for y in range(n):
            if A[x][y] and y not in gone and y not in seen:
                seen.add(y); st.append(y)
    return len(seen) == len(vs)


def three_connected(n, A):
    if n < 4:
        return False
    if not connected_without(n, A, set()):
        return False
    for v in range(n):
        if not connected_without(n, A, {v}):
            return False
    for u, v in itertools.combinations(range(n), 2):
        if not connected_without(n, A, {u, v}):
            return False
    return True


def geng(args):
    p = subprocess.run(['nauty-geng', '-q'] + args, capture_output=True, text=True, check=True)
    return [l for l in p.stdout.split('\n') if l.strip()]


def canon(lines):
    p = subprocess.run(['nauty-labelg', '-q'], input='\n'.join(lines) + '\n', capture_output=True, text=True, check=True)
    return sorted(l for l in p.stdout.split('\n') if l.strip())


def pairings(xs):
    if not xs:
        yield []
        return
    a = xs[0]
    for i in range(1, len(xs)):
        for p in pairings(xs[1:i] + xs[i + 1:]):
            yield [(a, xs[i])] + p


def main(N):
    # route A
    GA = []
    for s in geng(['-c', '-d3', str(N)]):
        n, A = g6_decode(s)
        deg = [sum(r) for r in A]
        ev = [v for v in range(n) if deg[v] % 2 == 0]
        if len(ev) != 1 or deg[ev[0]] != 6:
            continue
        if not three_connected(n, A):
            continue
        z = ev[0]
        keep = [v for v in range(n) if v != z]
        B = [[A[u][v] for v in keep] for u in keep]
        GA.append(g6_encode(n - 1, B))
    # route B
    GB = []
    for s in geng(['-c', str(N - 1)]):
        n, B = g6_decode(s)
        deg = [sum(r) for r in B]
        ev = [v for v in range(n) if deg[v] % 2 == 0]
        if len(ev) != 6:
            continue
        A = [row[:] + [1 if v in ev else 0] for v, row in enumerate(B)]
        A.append([1 if v in ev else 0 for v in range(n)] + [0])
        if not three_connected(n + 1, A):
            continue
        GB.append(s)
    cA, cB = canon(GA), canon(GB)
    repo = canon([l.strip() for l in open(f'{REPO_OUT}/d6_{N}.g6') if l.strip()])
    print(f'order {N}: route A {len(GA)} J, route B {len(GB)} J; canonical sets equal: A=B {cA == cB}, A=repo {cA == repo} (repo {len(repo)})')
    # pairings
    tot = simple = par = nosimple = 0
    for s in GB:
        n, B = g6_decode(s)
        deg = [sum(r) for r in B]
        ev = [v for v in range(n) if deg[v] % 2 == 0]
        k = 0
        for p in pairings(ev):
            tot += 1
            if any(B[a][b] for a, b in p):
                par += 1
            else:
                simple += 1; k += 1
        nosimple += (k == 0)
    print(f'order {N}: pairings {tot}, with a pair adjacent in J-z {par}, simple {simple}; J with no simple pairing {nosimple}')
    # compare with repo simple-pairing file
    rs = [l.split()[0] for l in open(f'{REPO_OUT}/d6_{N}_simple.txt') if l.strip()]
    print(f'order {N}: repo d6_{N}_simple.txt lines {len(rs)}')


if __name__ == '__main__':
    for N in map(int, sys.argv[1:]):
        main(N)
