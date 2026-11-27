"""run_roots.py RET_BINARY ARGS... < ROOTS: run ret.c on a list of 'graph6 root' lines.

Each line is passed to RET_BINARY with '-r root' and the extra ARGS, the graph6 string on stdin.
This avoids shell 'read', which mangles backslashes in graph6.  Output: ret.c's lines, in order.
"""
import subprocess
import sys


def main():
    binary, args = sys.argv[1], sys.argv[2:]
    for line in sys.stdin:
        f = line.split()
        if len(f) != 2:
            continue
        g6, r = f
        out = subprocess.run([binary] + args + ["-r", r], input=g6 + "\n", capture_output=True,
                             text=True, check=True).stdout
        sys.stdout.write(out)
        sys.stdout.flush()


if __name__ == "__main__":
    main()
