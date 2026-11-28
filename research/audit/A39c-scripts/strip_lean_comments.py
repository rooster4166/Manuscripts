"""A39c: strip Lean comments (nested /- -/ incl. docstrings, and -- line comments) and whitespace,
so that two versions of a file can be compared for code changes only.  usage: strip_lean_comments.py FILE"""
import sys, re
s = open(sys.argv[1], encoding='utf-8').read()
out, i, depth = [], 0, 0
while i < len(s):
    if s.startswith('/-', i): depth += 1; i += 2; continue
    if depth and s.startswith('-/', i): depth -= 1; i += 2; continue
    if depth: i += 1; continue
    if s.startswith('--', i):
        j = s.find('\n', i); i = len(s) if j < 0 else j; continue
    out.append(s[i]); i += 1
code = ''.join(out)
print('\n'.join(l.rstrip() for l in code.split('\n') if l.strip()))
