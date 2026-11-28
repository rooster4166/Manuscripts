#!/bin/sh
# random_nobudget.sh: re-run the random orders-11/13 TRN tests graph by graph, with the budget
# (2*10^6 nodes) and with no budget (per-graph time limit $1 seconds, default 300), to decide the
# tests that the budgeted run left undecided.
# One line per graph: index g6 | budgeted SUMMARY | unbudgeted SUMMARY (or TIMEOUT).
T=${1:-300}
python3 randg.py 400 11 11 13 > /tmp/trn_r1113.g6
awk '{print NR " " $0}' /tmp/trn_r1113.g6 | xargs -P 3 -d '\n' -n 1 sh -c '
  i=${1%% *}; g=${1#* }
  b=$(printf "%s\n" "$g" | ./trnbud 2000000 | grep SUMMARY)
  n=$(printf "%s\n" "$g" | timeout '"$T"' ./trnbud 0 | grep SUMMARY); [ -z "$n" ] && n="TIMEOUT"
  printf "%s %s | %s | %s\n" "$i" "$g" "$b" "$n"' sh | sort -n
