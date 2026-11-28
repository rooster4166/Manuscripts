#!/bin/sh
# reverify.sh: run the independent executor mt_verify.py on every committed schedule file.
# usage (from scripts/, after building route_ext):  sh reverify.sh
R=../data/runs
v() { python3 mt_verify.py ./route_ext > "$R/$1" 2>&1; echo "$1: $(tail -1 "$R/$1")"; }
zcat $R/J9_s1_all.txt.gz | grep '^SCHED ' | v J9_s1_verify.txt &
zcat $R/J9_aodd_all.txt.gz | grep '^SCHEDA ' | v J9_aodd_verify.txt &
grep '^SCHED ' $R/J7_s1_sched.txt | v J7_s1_verify.txt
grep '^SCHED ' $R/J7_pattern.txt | v J7_pattern_verify.txt
grep '^SCHED ' $R/J9_pattern.txt | v J9_pattern_verify.txt
grep '^SCHED ' $R/resid_O8_s1_b2e6.txt | v resid_O8_verify.txt
grep '^SCHED ' $R/resid_O10_s1_b2e6.txt | v resid_O10_verify.txt
cat $R/resid_O10_undec_open_seed7.txt $R/resid_O10_undec_open_seed11.txt | grep '^SCHED ' | v resid_O10_seed_verify.txt
grep '^SCHED ' $R/e28_hard_s1_b2e6.txt | v e28_hard_verify.txt
for f in resid_O8_aodd_b2e6 resid_O10_aodd_b2e6 resid_O8_aodd_b2e5 resid_O10_aodd_b2e5; do
  grep '^SCHEDA ' $R/$f.txt | v ${f}_verify.txt
done
wait
