"""Python front end for tools/realis.c (exact realisability oracle, n <= 16, m <= 64).

family(G)      -> (Ev, list of frozensets): every realisable set S of even vertices
profile_ok(G, b) -> bool: E(G) partitions into paths with exactly b(v) ends at v
The binary is compiled on first use into $REALIS_BIN or a temporary directory.
"""
import os
import subprocess
import tempfile

_HERE = os.path.dirname(os.path.abspath(__file__))
_proc = None
_bin = None


def _start():
    global _proc, _bin
    if _proc is not None:
        return
    _bin = os.environ.get("REALIS_BIN") or os.path.join(tempfile.gettempdir(), "realis_bin")
    src = os.path.join(_HERE, "realis.c")
    if not os.path.exists(_bin) or os.path.getmtime(_bin) < os.path.getmtime(src):
        subprocess.check_call(["gcc", "-O2", "-o", _bin, src])
    _proc = subprocess.Popen([_bin], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
                             bufsize=1)


def _encode(G):
    nodes = sorted(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    E = [(idx[a], idx[b]) for a, b in G.edges()]
    return nodes, idx, f"{len(nodes)} {len(E)} " + " ".join(f"{a} {b}" for a, b in E)


def family(G):
    _start()
    nodes, idx, enc = _encode(G)
    _proc.stdin.write("F " + enc + "\n")
    _proc.stdin.flush()
    parts = list(map(int, _proc.stdout.readline().split()))
    fam = [frozenset(nodes[i] for i in range(len(nodes)) if mask >> i & 1) for mask in parts[1:]]
    Ev = [v for v in nodes if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    return Ev, fam


def profile_ok(G, b):
    _start()
    nodes, idx, enc = _encode(G)
    _proc.stdin.write("P " + enc + " " + " ".join(str(b[v]) for v in nodes) + "\n")
    _proc.stdin.flush()
    return _proc.stdout.readline().strip() == "1"
