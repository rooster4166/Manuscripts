#!/bin/sh
# per_graph.sh G6 OUTDIR BIN TIMEOUT: run indep9 on one graph with a time limit (audit A34)
h=$(printf '%s' "$1" | md5sum | cut -c1-12)
printf '%s\n' "$1" | timeout "$4" "$3" > "$2/$h.txt" 2>/dev/null || echo "TIMEOUT $1" > "$2/$h.txt"
