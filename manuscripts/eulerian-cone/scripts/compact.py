"""compact.py IN OUT: strip the witnesses from re.c output, keeping 'g6 r p k status' per line."""
import sys
with open(sys.argv[1]) as f, open(sys.argv[2], "w") as g:
    for line in f:
        g6, rest = line.split(None, 1)
        g.write(g6 + " " + " ".join(rest.split("|")[0].split()[:4]) + "\n")
