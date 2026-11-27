"""Thin wrapper around tools/route_ext.c (compiled locally as ./route_ext)."""
import subprocess, os
_P = None
def _proc():
    global _P
    if _P is None:
        _P = subprocess.Popen([os.path.join(os.path.dirname(os.path.abspath(__file__)), "route_ext")],
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    return _P
def _graph(K):
    V = sorted(K)
    assert V == list(range(len(V)))
    E = [(u, v) for u in K for v in K[u] if u < v]
    return len(V), E
def query(tag, K, b, sep=None, avoid=None, seed=1, budget=0):
    n, E = _graph(K)
    s = f"{tag} {n} {len(E)} " + " ".join(f"{u} {v}" for u, v in E) + " " + " ".join(str(b[v]) for v in range(n))
    if 'S' in tag:
        s += f" {len(sep)} " + " ".join(f"{a} {c}" for a, c in sep)
    if 'A' in tag:
        s += " " + " ".join(str(sum(1 << x for x in avoid.get(v, ()))) for v in range(n))
    if 'B' in tag:
        s += f" {seed} {budget}"
    p = _proc()
    p.stdin.write(s + "\n"); p.stdin.flush()
    out = p.stdout.readline().split()
    r = int(out[0])
    if tag.startswith('W') and r == 1:
        txt = " ".join(out[1:])
        paths = [list(map(int, seg.split())) for seg in txt.split('|') if seg.strip()]
        return r, paths
    return r
