#!/bin/sh
# Section 7 (the inductive template for EMM): every log of Proposition 7.1, Theorem 7.5 and Proposition 7.9.
# Run from the repository root.
O=manuscripts/missing-move/scripts/outputs
for n in 4 5 6 7; do python3 tools/gemm_test.py data/conn$n.g6 20 > $O/gemm$n.log; done
python3 tools/gemm_test.py data/conn8.g6 30 half > $O/gemm8_half.log
python3 tools/gemm_test.py data/conn8.g6 30 x sample=200,seed=5 > $O/gemm8_sample200.log
python3 tools/gemm_test.py data/conn8.g6 40 pmax=3 > $O/gemm8_lowp.log
for n in 4 5 6; do
  python3 tools/emm_template.py data/conn$n.g6 100 > $O/tmpl$n.log
  python3 tools/emm_template.py data/conn$n.g6 100 reduced > $O/tmpl${n}_red.log
  python3 tools/emm_template.py data/conn$n.g6 100 reduced peel3 > $O/tmpl${n}_red_peel3.log
  python3 tools/emm_template.py data/conn$n.g6 100 reduced atleasthalf > $O/tmpl${n}_plus.log
  python3 tools/emm_template.py data/conn$n.g6 100 reduced atleasthalf peel5 > $O/tmpl${n}_plus_peel5.log
done

# diagnostics of the stuck instances (Remark 7.10)
python3 tools/emm_template.py data/conn6.g6 100 reduced diag > $O/tmpl6_red_diag.log
python3 tools/emm_template.py data/conn6.g6 100 reduced atleasthalf diag > $O/tmpl6_plus_diag.log
python3 tools/emm_reduction_check.py data/conn4.g6 data/conn5.g6 data/conn6.g6 > $O/reduction_d_check.log
# Theorem 7.5 and Example 7.4: counterexamples to EMM+ and EMM
python3 tools/emm_glue_search.py GsOeBW 0,0,1,1,2,0,0,0 3 data/conn5.g6 > $O/emm_glue_GsOeBW.log
python3 tools/emm_glue_search.py GqGUDg 0,1,1,1,1,0,0,0 4 data/conn5.g6 > $O/emm_glue_GqGUDg.log
cat $O/emm_glue_GsOeBW.log $O/emm_glue_GqGUDg.log | grep CUT-FEASIBLE | awk '{print $3}' | sort -u > $O/emm_counterexamples12.g6
python3 tools/cut_test.py $O/emm_counterexamples12.g6 > $O/emm_counterexamples12_cut_test.log
python3 tools/emm_lift_search.py > $O/emm_lift_search.log
# guarded splits and the simple class (Proposition 7.9)
for n in 4 5 6; do
  python3 tools/emm_template.py data/conn$n.g6 100 reduced atleasthalf split > $O/tmpl${n}_plus_split.log
  python3 tools/emm_template.py data/conn$n.g6 100 reduced atleasthalf simpleclass diag > $O/tmpl${n}_simple.log
  python3 tools/emm_template.py data/conn$n.g6 100 reduced atleasthalf simpleclass diag split peel5 > $O/tmpl${n}_simplesplitpeel5.log
done
for n in 5 6; do python3 tools/emm_template.py data/conn$n.g6 100 reduced atleasthalf split peel5 diag > $O/tmpl${n}_plus_split_peel5.log; done
python3 tools/emm_split.py --stuck $O/tmpl6_plus.log > $O/split_stuck6.log
python3 tools/emm_split.py --lift $O/tmpl6_plus.log > $O/split_lift6.log
for n in 4 5; do python3 tools/emm_split.py data/conn$n.g6 > $O/split$n.log; done
# Remark 7.7 (EMM_3)
python3 tools/emm3_core_search.py one data/conn6.g6 data/conn7.g6 data/conn8.g6 > $O/emm3_cores_one.log
python3 tools/emm3_core_search.py data/conn6.g6 data/conn7.g6 data/conn8.g6 > $O/emm3_cores.log
python3 tools/emm3_random.py cores 9 2000 12 22 2 > $O/emm3_cores9_random.log
python3 tools/emm3_random.py cores 10 2000 14 26 3 > $O/emm3_cores10_random.log
python3 tools/emm3_random.py emm3 10 3000 15 30 1 > $O/emm3_random10.log
python3 tools/emm3_random.py emm3 12 300 18 30 4 > $O/emm3_random12.log
echo DONE
