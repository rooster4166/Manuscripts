#!/bin/sh
# run_all.sh: regenerates the data of manuscripts/re-tight (Sections 5-6).
# Needs gcc, python3 with networkx; the inputs are the graph lists of eulerian-cone
# (2-connected Eulerian graphs of even order <= 10, made with nauty-geng there).
# Run from manuscripts/re-tight/scripts.  Times are for one core.
set -e
E=../../eulerian-cone/data; O=../data/out; mkdir -p $O
gcc -O2 -march=native -o ret ret.c
gcc -O2 -march=native -o re ../../eulerian-cone/scripts/re.c

# the degree-(n-2) form of RE at every root of degree n - 2 (positive validation)
for n in 4 6 8 10; do ./ret < $E/euler2c_$n.g6 > $O/ret_$n.txt; done           # n = 10: ~1 min
for n in 4 6 8 10; do python3 verify_family.py < $O/ret_$n.txt; done
# re.c agrees: every root of degree n - 2 has p_r = n/2 in eulerian-cone's tables
# (the 8 order-10 minima left UNK by re.c's budget were decided OK with -d: budget8_decide.txt)
for n in 4 6 8 10; do zcat $E/out/re_${n}_min.tab.gz; done > $O/re_min_all.txt
python3 -c "
ok = {}
for l in open('$O/re_min_all.txt'):
    g6, r, p, k, st = l.split(); ok[(g6, int(r))] = (st == 'OK' and int(p) <= int(k))
for l in open('$E/out/budget8_decide.txt'):
    g6, rest = l.split(None, 1); f = rest.split()
    if f[3] == 'OK' and int(f[1]) <= int(f[2]): ok[(g6, int(f[0]))] = True
bad = cnt = 0
for n in (4, 6, 8, 10):
    for l in open('$O/ret_%d.txt' % n):
        g6, rest = l.split(None, 1); f = rest.split(); cnt += 1
        if (f[1] == 'YES') != ok[(g6, int(f[0]))]: bad += 1
print('ret vs re.c on degree-(n-2) roots:', cnt, 'roots,', bad, 'disagreements')"
rm $O/re_min_all.txt

# negative validation: -z (k - 1 pairs) iff p(B) <= k - 1, against re.c -p
python3 -c "
import networkx as nx
for n in (6, 8, 10):
    o = open('$O/hasn2_%d.g6' % n, 'w')
    for l in open('$E/euler2c_%d.g6' % n):
        B = nx.from_graph6_bytes(l.strip().encode())
        if any(d == n - 2 for _, d in B.degree()): o.write(l)"
for n in 6 8; do ./re -p -m < $O/hasn2_$n.g6 > $O/p_$n.txt; ./ret -z < $O/hasn2_$n.g6 > $O/retz_$n.txt
  python3 compare_z.py $O/p_$n.txt $O/retz_$n.txt; python3 verify_family.py -z < $O/retz_$n.txt; done
./re -p -m -b 5000000 < $O/hasn2_10.g6 > $O/p_10.txt
# order 10 was run with a budget and stopped early (Section 6.1); to repeat:
#   ./ret -z -b 20000000 < $O/hasn2_10.g6 > $O/retz_10_partial.txt; python3 compare_z.py $O/p_10.txt $O/retz_10_partial.txt

# the Lovasz-plus-matching method (-L) and Theorem 3.1 against every Lovasz decomposition (-T)
for n in 6 8 10; do ./ret -L -b 200000000 < $O/hasn2_$n.g6 > $O/retL_$n.txt; done   # n = 10: ~15 min
python3 verify_family.py < $O/retL_10.txt
for n in 6 8 10; do ./ret -T -b 50000000 < $O/hasn2_$n.g6 > $O/retT_$n.txt; python3 check_star.py $O/retT_$n.txt; done
for n in 6 8 10; do python3 coverage.py $n $O/retL_$n.txt $O/cov_$n.txt; done
