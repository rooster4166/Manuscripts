"""A42: check solver answers against queries with a42lib.check (own checker). usage: checkqa.py Q A"""
import sys, collections
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import check_qa
C = collections.Counter()
Q = [l for l in open(sys.argv[1]) if l.strip()]; A = [l for l in open(sys.argv[2])][:len(Q)]
assert len(Q) == len(A), (len(Q), len(A))
for q, a in zip(Q, A):
    r = check_qa(q, a); C[r] += 1
    if r not in ('OK',): print(r, q.strip())
print(sys.argv[2], dict(C))
