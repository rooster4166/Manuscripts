"""Gqz~vw at the root 3: the original game (no path insertion) for |F| = 0..8, and the game with
path insertion for |F| = 0..5 (independent solver game.py)."""
import time, game
n, E = game.from_g6('Gqz~vw')
print("Gqz~vw complement:", sorted(set((a, b) for a in range(8) for b in range(a + 1, 8)) - set(map(tuple, map(sorted, E)))))
g = game.Game(n, E, newpath=True)
for k in range(0, 6):
    t = time.time(); r = g.solve(k, kmin=k, roots=[3])
    print("np   |F| =", k, "root 3:", r[3], round(time.time() - t, 1), "s", flush=True)
g = game.Game(n, E, newpath=False)
for k in range(0, 9):
    t = time.time(); r = g.solve(k, kmin=k, roots=[3])
    print("nonp |F| =", k, "root 3:", r[3], round(time.time() - t, 1), "s, states", len(g.memo), flush=True)
