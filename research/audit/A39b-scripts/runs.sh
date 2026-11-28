#!/bin/sh
# Audit A39b: every command run (from /home/user/Manuscripts/lean unless stated).
set -e
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/Manuscripts/lean
A=../research/audit/A39b-scripts
MT=/home/user/Manuscripts/manuscripts/multi-token/data
md5sum GallaiLean/DenseRootB.lean GallaiLean/DenseRoot.lean ../manuscripts/dense-root/dense-root.tex
grep -nE 'sorry|admit|native_decide|\baxiom\b' GallaiLean/DenseRootB.lean GallaiLean/DenseRoot.lean || true
lake env lean GallaiLean/DenseRootB.lean            # exit 0; 59 linter warnings, no errors
lake build                                           # Build completed successfully (18436 jobs)
lake env lean $A/axioms.lean                         # axioms + signatures
lake env lean $A/unused_hyps.lean                    # binders unused by the proof terms
lake env lean $A/nonvacuous.lean                     # 8 instances, incl. three order-9 spine instances
! lake env lean $A/sanity_fail.lean                  # must fail: decide rejects a false count
python3 -I $A/lean_hyp_cov.py $MT/J9_d6.g6           # Lean hypotheses, literally, at order 9
python3 -I $A/len3_roots.py $MT/J9_d6.g6 $MT/runs/J9_none.txt
python3 -I $A/dist_check.py $MT/J9_d6.g6 $MT/runs/J9_none.txt
python3 -I $A/gen_len3_instances.py $MT/J9_d6.g6 > $A/len3_instances.lean
lake env lean $A/len3_instances.lean                 # 28 Test1At theorems, standard axioms
