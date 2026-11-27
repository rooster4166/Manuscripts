#!/bin/bash
# make_variants.sh (auditor, conj-n audit).  Builds, in a scratch directory $1, auditor variants of
# the authors' ext.h (the repository is not modified):
#   var1: move (b) without its far-end conditions  (u notin B, N(u) & B = 0 dropped)  -- must FAIL movecheck
#   var2: move (c) without N(u) & B = 0                                               -- must FAIL movecheck
#   var3: move (x) with B + N(u) - g instead of B + N(u)                               -- must FAIL movecheck
#   full: Lemma 3.1 leaf paths up to length 8 (not 2) and all g--c routes for (h) (not <= 8 shortest)
# and the binaries movecheck_varK, xcert_full, closure2_full, ncert_allroutes.
set -e
D=${1:?scratch dir}; mkdir -p "$D"
SC=/home/user/Manuscripts/manuscripts/conj-n/scripts
L=/home/user/Manuscripts/manuscripts/l1-induction/scripts
A=/home/user/Manuscripts/research/audit/A32-scripts
for v in var1 var2 var3 full; do mkdir -p "$D/$v"; cp "$SC/ext.h" "$SC/orcb.h" "$SC/xcert.cpp" "$SC/closure2.cpp" "$D/$v/"; done
sed -i 's/if (!(A >> u \& 1) \&\& !(B >> u \& 1) \&\& !(G.adj\[u\] \& B)) out.push_back({H, c, A, B, .b.});/if (!(A >> u \& 1)) out.push_back({H, c, A, B, '"'"'b'"'"'});/' "$D/var1/ext.h"
sed -i 's/if (!(G.adj\[u\] \& B)) out.push_back({H, u, A | (1u << c), B, .c.});/out.push_back({H, u, A | (1u << c), B, '"'"'c'"'"'});/' "$D/var2/ext.h"
sed -i "s/out.push_back({H, c, A, B | G.adj\[u\], 'x'});/out.push_back({H, c, A, B | (G.adj[u] \& ~(1u << g)), 'x'});/" "$D/var3/ext.h"
python3 -I - "$D/full/ext.h" <<'EOF'
import sys
p = sys.argv[1]; s = open(p).read()
a = s.index('    std::vector<std::vector<int>> paths; std::vector<int> cur{g};\n    if (dist[g] >= 2) {')
b = s.index('    for (auto& P : paths) {\n      Gr H = G; uint32_t A2 = A;')
new = '''    std::vector<std::vector<int>> paths; std::vector<int> cur{g};
    { uint32_t vis = 1u << g;
      std::function<void(int)> go = [&](int x) {
        for (int y = 0; y < G.N; y++) if (G.has(x, y) && !(vis >> y & 1) && !(A >> y & 1)) {
          if (y == c) { if (cur.size() >= 2) { cur.push_back(y); paths.push_back(cur); cur.pop_back(); } continue; }
          vis |= 1u << y; cur.push_back(y); go(y); cur.pop_back(); vis &= ~(1u << y);
        }
      };
      go(g);
    }
'''
s = s[:a] + new + s[b:]
s = s.replace('static int XMV_LEAFPATH_MAXLEN = 2;', 'static int XMV_LEAFPATH_MAXLEN = 8;')
open(p, 'w').write(s)
EOF
for v in var1 var2 var3 full; do g++ -O2 -I "$D/$v" -I "$L" -o "$D/movecheck_$v" "$A/movecheck.cpp"; done
g++ -O2 -I "$L" -o "$D/xcert_full" "$D/full/xcert.cpp"
g++ -O2 -I "$L" -o "$D/closure2_full" "$D/full/closure2.cpp"
sed 's/int main(int argc, char\*\* argv) {/int main(int argc, char** argv) { MV_ROUTE_ALL = 1;/' "$SC/ncert.cpp" > "$D/ncert_allroutes.cpp"
g++ -O2 -I "$L" -o "$D/ncert_allroutes" "$D/ncert_allroutes.cpp"
echo "built in $D"
