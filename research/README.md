# Research process

The collection's verification layer (code, certificates, Lean) is not in the repository, and almost every paper in it is very new. So this work follows four rules:

1. **Map before extending.** `../STATUS.md` and `notes/` record what each paper proves, what it depends on, and what is still open.
2. **Falsify before proving.** Before any attempt at a proof, every proposed generalization is checked on all small graphs and on structured families with `../tools/`. Results go in `experiments.md`, including the negative ones.
3. **Replay what is load-bearing.** A step that depends on an enumeration counts as verified only once our own independent code has reproduced it.
4. **Claims are graded:**
   - **proved:** written proof, checked;
   - **verified (n ≤ N):** exhaustive computation up to order N;
   - **conjectured:** tested, but with no proof;
   - **refuted:** a counterexample has been found.

## Files

| File | Purpose |
|---|---|
| `notes/reader-*.md` | Structured reader notes for each part of the collection. |
| `experiments.md` | Log of computational tests. |
| `connections.md` | Cross-paper connections and candidate uniform statements. |
