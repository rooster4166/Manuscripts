#!/bin/bash
# Lemma 5.9 / Prop 5.10 with the independent rf implementation (audit A12)
cd "$(dirname "$0")"
for g in 'I~~~wF{~?' 'I~~~wF{~G' 'Gr~v~w' 'I]~v~z~~o'; do nice -n 15 python3 rf_check.py "$g" 0; done
