"""Per-step worst case (over all hypothesis configurations and adversarial donors) of the
blank count, next to the supply, for each step table (audit A9)."""
import check_tables as ct
from adversarial import Cert
orig_finish = ct.finish
rec = {}
def finish(c, *a, **k):
    orig_finish(c, *a, **k)
    for i, (donors, recv, sup, bl, d) in enumerate(c.trace):
        key = i
        lo = rec.setdefault(key, [10**9, -1, -1])
        lo[0] = min(lo[0], sup); lo[1] = max(lo[1], sup); lo[2] = max(lo[2], bl)
    return True
ct.finish = finish
for name, f, args in [("4.1(i)", ct.roothub_i, ()), ("4.1(ii)", ct.roothub_ii, ()), ("4.1(iii)", ct.roothub_iii, ()),
                      ("4.3", ct.two_resources, ()), ("4.4 m=2", ct.relay, (2,)), ("5.2 two batteries", ct.full_hub_two, ()),
                      ("5.2 battery+pendant", ct.full_hub_pendant, ())]:
    rec.clear(); f(*args)
    print(name, " ".join(f"{i+1}:(sup {a if a==b else f'{a}-{b}'}, worst |Z| {c})" for i, (a, b, c) in sorted(rec.items())))
