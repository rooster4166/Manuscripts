#!/bin/sh
# run_all.sh: regenerates the data of manuscripts/eulerian-cone (Section 6).
# Needs nauty (geng, complg; Debian package 'nauty', binaries nauty-geng, nauty-complg), gcc,
# python3 with networkx and ortools (for the CP-SAT cross-checks via tools/pathnum2.py).
# Run from manuscripts/eulerian-cone/scripts.  Long steps are marked; all use the 4-core budget.
set -e
D=../data; O=../data/out; mkdir -p $O
gcc -O2 -march=native -o re re.c
gcc -O2 -march=native -DWIDE -o rew re.c           # up to 128 edges
gcc -O2 -o evenfilter evenfilter.c
gcc -O2 -o oddfilter oddfilter.c
gcc -O2 -o mcut mcut.c

# validation against the brute force (connected graphs of order 3..7 with <= 10 edges)
for n in 3 4 5 6 7; do nauty-geng -cq $n 0:10; done > $O/small.g6
python3 bf.py < $O/small.g6 > $O/small.bf
./re -x < $O/small.g6 > $O/small.re; ./re -p < $O/small.g6 > $O/small.rep
python3 verify_witness.py < $O/small.re; python3 compare_bf.py $O/small.bf $O/small.re $O/small.rep

# inputs: 2-connected Eulerian graphs of even order <= 10, connected Eulerian of order <= 10
for n in 4 6 8 10; do nauty-geng -Cq -d2 $n | ./evenfilter > $D/euler2c_$n.g6; done
for n in 3 4 5 6 7 8 9 10; do nauty-geng -cq $n | ./evenfilter > $D/euler_conn_$n.g6; done

# exact rooted path numbers (minimum mode, with witnesses), n <= 10
for n in 4 6 8 10; do ./re -b 5000000 < $D/euler2c_$n.g6 > $O/re_${n}_min.txt; done   # n=10: ~10 min
for n in 3 4 5 6 7 8 9; do ./re -x -b 20000000 < $D/euler_conn_$n.g6 > $O/reconn_$n.txt; done
python3 -c "
import networkx as nx
o=open('$D/euler_conn_not2c_10.g6','w')
for l in open('$D/euler_conn_10.g6'):
    if not nx.is_biconnected(nx.from_graph6_bytes(l.strip().encode())): o.write(l)"
./re -x -b 20000000 < $D/euler_conn_not2c_10.g6 > $O/reconn_10_not2c.txt
cat $O/re_*_min.txt $O/reconn_*.txt | python3 verify_witness.py
python3 countbound.py $O/re_4_min.txt $O/re_6_min.txt $O/re_8_min.txt $O/re_10_min.txt
python3 uc_check.py $O/reconn_*.txt
# the roots above the counting bound, re-decided by CP-SAT (independent exact method)
python3 -c "
import sys; sys.argv=['x']
exec(open('countbound.py').read().split('cnt = Counter()')[0])
o=open('$O/above_cb.txt','w')
for n in (4,6,8,10):
    for line in open('$O/re_%d_min.txt'%n):
        g6, rest = line.split(None, 1); f = rest.split()
        if f[3]!='OK': continue
        B=nx.from_graph6_bytes(g6.encode())
        if int(f[1])>cb([d for _,d in B.degree()],B.degree(int(f[0]))): o.write('%s %s %s\n'%(g6,f[0],f[1]))"
python3 cpsat_check.py $O/above_cb.txt > $O/above_cb_cpsat.txt                      # ~10 min

# order 12, dense: complements with <= 20 edges and all degrees odd (~1 min to generate)
nauty-geng -d1 -q 12 0:20 | ./oddfilter | nauty-complg -q > $O/dense12.g6
python3 -c "
import networkx as nx
o=open('$D/dense12_2c.g6','w')
for l in open('$O/dense12.g6'):
    if nx.is_biconnected(nx.from_graph6_bytes(l.strip().encode())): o.write(l)"
./re -d -b 50000000 < $D/dense12_2c.g6 > $O/re_dense12_decide.txt
./re -u -q -m -b 2000000 < $D/dense12_2c.g6 > $O/uc12.txt                             # ~1 h
grep OKUNK $O/uc12.txt | awk '{sub("cb=","",$6); print $1, $2, $6}' > $O/uc12_unk.txt
python3 cpsat_decide.py $O/uc12_unk.txt 900 > $O/uc12_unk_cpsat.txt                    # ~30 min
python3 verify_witness.py < $O/uc12_unk_cpsat.txt

# regular graphs, complete multipartite graphs, random graphs
for d in 4 6 8 10; do nauty-geng -Cq -d$d -D$d 12 > $D/reg12_$d.g6; done
nauty-geng -Cq -d4 -D4 14 > $D/reg14_4.g6
nauty-geng -q -d3 -D3 14 | nauty-complg -q > $D/reg14_10.g6
python3 multipartite.py > $D/multipartite.g6
for n in 12 14 16; do python3 random_euler.py $n 300 $n > $D/rand_$n.g6; done
for f in reg12_4 reg12_6 reg12_8 reg12_10 reg14_4 reg14_10 multipartite rand_12 rand_14 rand_16; do
  ./rew -d -b 50000000 < $D/$f.g6 > $O/re_$f.txt; done
cat $O/re_reg*.txt $O/re_multipartite.txt $O/re_rand_*.txt $O/re_dense12_decide.txt | python3 verify_witness.py

# the reduction lemmas executed on real decompositions (Section 5)
python3 reductions_check.py ./re $D/euler_conn_[4-9].g6 > $O/reductions_check_le9.txt
head -3000 $D/euler2c_10.g6 > $O/e10_head.g6
python3 reductions_check.py ./re $O/e10_head.g6 $D/euler_conn_not2c_10.g6 > $O/reductions_check_10.txt

# matching cuts
for n in 4 6 8 10; do ./mcut < $D/euler2c_$n.g6 | awk '{c[$2]++} END {print c[1]+0, c[0]+0}'; done
