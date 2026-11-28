#!/bin/sh
# A39c (dense-root fix-up 2660c7e): every command the auditor ran. Scratch outputs go to $SP.
M=/home/user/Manuscripts
A=$M/research/audit/A39c-scripts
D=$M/manuscripts/dense-root
SP=${SP:-/tmp/a39c}
mkdir -p $SP
cd $M

# the diff
git diff be56355 2660c7e -- lean manuscripts/dense-root/README.md manuscripts/dense-root/scripts
git diff --word-diff=plain be56355 2660c7e -- manuscripts/dense-root/dense-root.tex

# Lean: code unchanged (comments only), build, fresh compiles, axioms, unused binders, the 28 instances
for f in DenseRoot DenseRootB; do
  git show be56355:lean/GallaiLean/$f.lean > $SP/$f.old.lean
  git show 2660c7e:lean/GallaiLean/$f.lean > $SP/$f.new.lean
  python3 $A/strip_lean_comments.py $SP/$f.old.lean > $SP/$f.old.code
  python3 $A/strip_lean_comments.py $SP/$f.new.lean > $SP/$f.new.code
  diff $SP/$f.old.code $SP/$f.new.code && echo "$f: code identical"
done
export PATH=$HOME/.elan/bin:$PATH
(cd lean && lake build)                                     # 18436 jobs, exit 0
(cd lean && lake env lean GallaiLean/DenseRoot.lean)        # exit 0, 11 warnings
(cd lean && lake env lean GallaiLean/DenseRootB.lean)       # exit 0, 59 warnings
(cd lean && lake env lean ../research/audit/A39b-scripts/axioms.lean)
(cd lean && lake env lean ../research/audit/A39b-scripts/unused_hyps.lean)      # [hjU], [hy]
(cd lean && lake env lean ../research/audit/A39b-scripts/len3_instances.lean)   # 28 x std axioms
grep -nE "sorry|admit|native_decide|^axiom" lean/GallaiLean/DenseRoot.lean lean/GallaiLean/DenseRootB.lean

# shipped scripts
(cd $D/scripts && python3 coverage.py order9 ../../multi-token/data/J9_d6.g6 && python3 cov1597.py \
  && python3 look.py && python3 crosscheck.py ../../multi-token/data/J9_d6.g6)

# independent recount (own parser, every path, Lean hypotheses literally); writes new28.txt
python3 -I $A/indep_cov.py $M
# new28.txt == the 28 roots of A39b-scripts/len3_instances.lean (compared by theorem name t1_L<line>_r<r>)

# the proof of Theorem 4.1 run literally on length-3 connectors (patched A39 checker)
python3 $A/literal_len3.py J9
python3 $A/literal_len3.py rand 5 1000 31 300 400000
python3 $A/literal_len3.py rand 6 400 32 300 400000
python3 $A/literal_len3.py rand 7 150 33 300 400000

# PDF: committed PDF = current tex; Table 1 overfull (also at be56355); page 7 rendered
mkdir -p $SP/tex && cp $D/dense-root.tex $SP/tex/ && (cd $SP/tex && pdflatex -interaction=nonstopmode dense-root.tex \
  && pdflatex -interaction=nonstopmode dense-root.tex && grep Overfull dense-root.log \
  && pdftotext dense-root.pdf fresh.txt && pdftotext $D/dense-root.pdf committed.txt && diff fresh.txt committed.txt \
  && pdftoppm -f 7 -l 7 -r 70 -png $D/dense-root.pdf p7)

# stale numbers / phrases
grep -rnE "1,602|1\{,\}602|1,445|1\{,\}445|1,041|1\{,\}041|1,658|1\{,\}658|1,501|1\{,\}501|\b154\b|\b52\b|distance at most two|short connector|length <= 2|length ≤ 2|length \\\$\\\\le ?2" \
  $D/dense-root.tex $D/README.md $D/scripts lean/GallaiLean/DenseRoot.lean lean/GallaiLean/DenseRootB.lean
