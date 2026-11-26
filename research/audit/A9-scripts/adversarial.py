"""Independent adversarial check of the step tables of d6-frontier.tex (audit A9).

Model.  Only the "special" vertices named in a certificate are tracked; every other vertex
is odd, keeps one end throughout (it is never a donor or a receiver) and is never blank.
The adjacency of the special vertices in B is given by the theorem's hypotheses: forced
edges are present, forbidden pairs are absent, and every pair the hypotheses leave free is
taken PRESENT (this only increases blank counts, so it is the worst case for Fan's
inequality; donor-receiver pairs are always held edges, so their adjacency in the current
graph is "absent" regardless).  Grouped transfers branch over EVERY donor with b >= 1
(the donor is adversarial).  Every Fan inequality is checked, and also that the actual
worst-case blank count is at most the bound printed in the paper's table.

All labelled configurations allowed by the hypotheses are enumerated (e.g. every subset
N(y) & T with |N(y) & T| <= 2 in Thm 4.1(i))."""
import itertools

class Fail(Exception):
    pass

class Cert:
    def __init__(self, special, b, held, adjB):
        self.b = dict(b)                    # special vertex -> ends
        self.held = set(map(frozenset, held))
        self.adjB = adjB                    # function(u, v) -> bool, edge of B
        self.special = list(special)
        self.trace = []

    def copy(self):
        c = Cert.__new__(Cert)
        c.b = dict(self.b); c.held = set(self.held); c.adjB = self.adjB
        c.special = self.special; c.trace = list(self.trace)
        return c

    def adj_now(self, u, v):
        return u != v and self.adjB(u, v) and frozenset((u, v)) not in self.held

    def bl(self, v):
        return sum(1 for w in self.special if self.b[w] == 0 and self.adj_now(v, w))

    def step(self, recv, donors, bound):
        """Fan transfer donors -> recv.  Returns list of (donor, new Cert)."""
        donors = list(donors)
        for d in donors:
            if frozenset((d, recv)) not in self.held:
                raise Fail(f"{d}{recv} is not a held edge (donor adjacent to receiver or not an edge of B)")
        sup = sum(self.b[d] for d in donors)
        bl = self.bl(recv)
        if not sup > bl:
            raise Fail(f"Fan inequality fails: {donors}->{recv} supply {sup} blanks {bl}; trace {self.trace}")
        if bound is not None and bl > bound:
            raise Fail(f"paper bound too small: {donors}->{recv} blanks {bl} > bound {bound}; trace {self.trace}")
        out = []
        for d in donors:
            if self.b[d] < 1:
                continue
            c = self.copy()
            c.b[d] -= 1; c.b[recv] += 1
            c.held.discard(frozenset((d, recv)))
            c.trace.append((tuple(donors), recv, sup, bl, d))
            out.append((d, c))
        return out

    def single(self, recv, donor, bound):
        (d, c), = self.step(recv, [donor], bound)
        return c


def mkadj(forced, forbidden):
    F = set(map(frozenset, forced)); X = set(map(frozenset, forbidden))
    assert not (F & X)
    def adj(u, v):
        e = frozenset((u, v))
        if e in X: return False
        return True                      # forced or free: present (worst case)
    return adj


def finish(c, U, r, odd_special, expect_doubled=3):
    if c.held:
        raise Fail(f"held edges remain {c.held}")
    if c.b[r] < 2:
        raise Fail(f"b(r) = {c.b[r]}")
    for v in odd_special:
        if c.b[v] != 1:
            raise Fail(f"odd vertex {v} has {c.b[v]} ends")
    dbl = [u for u in U if c.b[u] == 2]
    if len(dbl) != expect_doubled or any(c.b[u] not in (0, 2) for u in U):
        raise Fail(f"profile on U {[c.b[u] for u in U]}")
    return True
