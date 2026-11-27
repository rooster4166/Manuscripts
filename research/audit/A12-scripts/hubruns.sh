#!/bin/bash
# Order-10 hub-shaped runs of missing-move Section 5 (game.py, no rf/flower/orbit). Audit A12.
cd "$(dirname "$0")"
nice -n 15 python3 hubrun.py 'I~~~wF{~G' 3 3      # B' (B2): star + 3
nice -n 15 python3 hubrun.py 'I~~~wF{~?' 0 3      # A_{6,2}: star + <= 3
nice -n 15 python3 hubrun.py 'Inv~|~zbw' 0 3      # Inv~|~zbw
