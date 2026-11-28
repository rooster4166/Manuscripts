#!/usr/bin/env python3
"""Compute amsthm numbering (shared counter, per section unless flat) for a tex file.
Usage: thmnum.py file.tex [flat]"""
import re, sys
src = open(sys.argv[1]).read()
flat = len(sys.argv) > 2
envs = ['theorem','lemma','proposition','corollary','conjecture','definition','remark','example','question']
tok = re.compile(r'\\section\{([^}]*)\}|\\appendix|\\begin\{(' + '|'.join(envs) + r')\}(\[[^\]]*\])?\s*(\\label\{([^}]*)\})?')
sec = 0; n = 0; appendix=False
for m in tok.finditer(src):
    if m.group(0).startswith('\\appendix'):
        appendix=True; sec=0; continue
    if m.group(1) is not None:
        sec += 1; 
        if not flat: n = 0
        print(f"--- Section {chr(64+sec) if appendix else sec}: {m.group(1)}")
        continue
    n += 1
    num = f"{n}" if flat else f"{chr(64+sec) if appendix else sec}.{n}"
    lab = m.group(5) or ''
    opt = (m.group(3) or '')[:60]
    # look for label shortly after
    if not lab:
        mm = re.search(r'\\label\{([^}]*)\}', src[m.end():m.end()+300])
        if mm: lab = mm.group(1)+'?'
    print(f"{m.group(2):12s} {num:6s} {lab:25s} {opt}")
