#!/usr/bin/env python3
"""Check that every Lean name cited in paper.tex is checked by lean/P1.lean.

Collects the identifiers inside \\lean{...}, \\leanst{...} and \\texttt{...} of paper.tex, drops the
`Gallai.` prefix, and compares them with the names that lean/P1.lean resolves (its `#cited` list and
the library declarations used in Part 1). Tokens that are not Lean declarations (file names, Lean
keywords, axioms, commands) are listed in NON_DECLS below. Exit status 1 if some cited name is not
checked, or if NON_DECLS contains a stale entry.
Usage: python3 -I scripts/check_names.py   (from papers/P1-spine)
"""
import re, sys, pathlib

here = pathlib.Path(__file__).resolve().parent.parent
tex = (here / "paper.tex").read_text()
lean = (here / "lean" / "P1.lean").read_text()

NON_DECLS = {
    # tokens of \\texttt that are not library declarations
    "Classical.choice", "Quot.sound", "sorryAx", "GallaiLean", "Type", "V", "D.ends", "Option",
    "Bool", "v4.36.0", "fc4f59e577feb1a4956671bc04ac18aaaf8cd842", "P1.cone_matchingCut_iff",
}

def tokens(arg):
    arg = arg.replace("\\_", "_").replace("\\allowbreak", "").replace("{\\small", "")
    for t in re.split(r"[,\s()]+", arg):
        t = t.strip("{}~ .;:[]")
        if re.fullmatch(r"[A-Za-z][A-Za-z0-9_.']*", t):
            yield t

cited = set()
for m in re.finditer(r"\\(?:leanst|lean|texttt)\{((?:[^{}]|\{[^{}]*\})*)\}", tex):
    for t in tokens(m.group(1)):
        cited.add(t[len("Gallai."):] if t.startswith("Gallai.") else t)

checked = set()
block = re.search(r"^#cited\n(.*?)^/-!", lean, re.S | re.M).group(1)
checked |= {t[len("Gallai."):] for t in block.split() if t.startswith("Gallai.")}
part1 = lean.split("## Part 1")[1].split("## Part 2")[0]
checked |= set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", part1))

def ok(t):
    if t in checked or t in NON_DECLS:
        return True
    if re.search(r"\.(lean|tex|md|json|sh|py|pdf|expected)$", t) or "/" in t:
        return True          # file names and paths
    if t.startswith("\\") or t.startswith("#") or t.startswith("$"):
        return True          # TeX macros, Lean commands, shell variables
    if re.fullmatch(r"[a-z]+", t):
        ignored.add(t)       # plain lower-case words: prose inside \leanst, or short names
        return True
    return False

ignored = set()

# tokens of \texttt that are plainly not identifiers (e.g. ``KConnected 2'') split into words above;
missing = sorted(t for t in cited if not ok(t))
stale = sorted(t for t in NON_DECLS if t not in cited)
if missing:
    print("Cited in paper.tex but not checked by P1.lean:")
    for t in missing:
        print("  ", t)
if stale:
    print("Stale entries in NON_DECLS:", ", ".join(stale))
if missing or stale:
    sys.exit(1)
if ignored:
    print("Ignored plain words (prose, or names checked by hand):", " ".join(sorted(ignored - checked)))
print(f"OK: {len(cited)} cited tokens, every Lean name among them is checked by P1.lean.")
