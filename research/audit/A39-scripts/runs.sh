#!/bin/sh
# A39 (dense-root): every command the auditor ran. Scratch outputs go to $SP (not committed).
M=/home/user/Manuscripts
A=$M/research/audit/A39-scripts
D=$M/manuscripts/dense-root
SP=${SP:-/tmp/a39}
mkdir -p $SP

# Lean: compile, axioms, signatures, non-vacuity (C4, k = 2)
export PATH=$HOME/.elan/bin:$PATH
(cd $M/lean && lake env lean GallaiLean/DenseRoot.lean && lake env lean $A/axioms.lean \
  && lake env lean $A/nonvacuous.lean)

# independent coverage (own graph6 parser, own conditions; connectors enumerated generically)
python3 $A/indep_cov.py J9
python3 $A/indep_cov.py resid

# Theorems A and B run literally: every Lovasz decomposition, every tie-break, every claim checked
python3 $A/literal_AB.py J9
python3 $A/literal_AB.py rand 5 1500 11 300 400000
python3 $A/literal_AB.py rand 6 600 12 300 400000
python3 $A/literal_AB.py rand 7 200 13 300 400000

# the shipped method checker: rebuild, rerun, compare with the shipped data
cp $D/scripts/drm.cpp $SP/ && g++ -O2 -o $SP/drm $SP/drm.cpp
$SP/drm    < $M/manuscripts/multi-token/data/J9_d6.g6 > $SP/drm9_noG.out   # == data/drm9.out
$SP/drm -G < $M/manuscripts/multi-token/data/J9_d6.g6 > $SP/drm9_G.out     # 1756 YES
$SP/drm -A -m 0 < $M/manuscripts/multi-token/data/J9_d6.g6 > $SP/drmA_m0.out  # == data/drmA9_m0.out
$SP/drm -G < $D/data/frozen9.txt > $SP/frz_G.out                            # == data/frz9.out
$SP/drm -G -C 60 -L 6 < $D/data/frozen9.txt > $SP/frz_L6.out                # same statuses
# witnesses, verified from scratch
$SP/drm -G -v < $M/manuscripts/multi-token/data/J9_d6.g6 > $SP/drm9_v.out
python3 $A/verify_drm.py $SP/drm9_v.out x 3                                 # 1756 ok
grep -v 'Huv]z' $D/data/frozen9.txt > $SP/frozen112.txt
$SP/drm -G -v < $SP/frozen112.txt > $SP/frz_v.out
python3 $A/verify_drm.py $SP/frz_v.out                                      # 112 ok
# at most one free piece (patched copy of drm: option -F)
sed -e 's/static int freeOK = 0; static int pieceFree\[40\];/static int freeOK = 0; static int pieceFree[40]; static int optF = 99;/' \
    -e 's/        int nN = popc(Nmask);/        if (F > optF) return 0;\n        int nN = popc(Nmask);/' \
    -e 's/else if (!strcmp(argv\[i\], "-C")) capSys = atoi(argv\[++i\]);/else if (!strcmp(argv[i], "-C")) capSys = atoi(argv[++i]);\n        else if (!strcmp(argv[i], "-F")) optF = atoi(argv[++i]);/' \
    $SP/drm.cpp > $SP/drmF.cpp && g++ -O2 -o $SP/drmF $SP/drmF.cpp
$SP/drmF -G -F 1 < $D/data/frozen9.txt > $SP/frzF1.out                      # 105 YES / 8 NO

# shipped ret.c witnesses, verified from scratch
python3 $A/verify_ret.py $D/data/ret9.out $D/data/ret_resid_O8.out $D/data/ret_resid_O10.out \
  $D/data/ret_e28_hard.out $D/data/ret_clt_hard.out

python3 $A/misc_checks.py
# the two-connector extension (§8 item 1) and the frozen exception (Test1 holds there)
python3 $A/two_connectors.py 5
python3 $A/frozen_exception.py

# shipped scripts, for comparison
(cd $D/scripts && python3 crosscheck.py ../../multi-token/data/J9_d6.g6 && python3 cov1597.py \
  && python3 coverage.py J9 ../../multi-token/data/J9_d6.g6 && python3 look.py)
