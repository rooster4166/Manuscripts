#!/bin/sh
# Section 7 (the inductive template for EMM): every log of Proposition 7.2 and Proposition 7.6.
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
echo DONE
