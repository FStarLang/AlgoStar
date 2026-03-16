# Timestamp Tracking for stack_dfs

## Status: RESOLVED (2026-03-16)

The `assume_` originally documented here has been **fully eliminated**. The
current `DFS.Impl.fst` has zero admits, zero assumes. All four properties
(all-BLACK, d > 0, f > 0, d < f) are proven via the `dfs_ok` and `gray_ok`
invariants maintained through `dfs_visit` and `stack_dfs`.

The notes below are retained for historical reference on the proof strategy.

---

## Original Goal
Eliminate the `assume_` at line 748 in `stack_dfs` by adding timestamp tracking invariants.

The assume originally covered 4 properties:
1. All vertices BLACK: `forall u. color[u] == 2`
2. All d > 0: `forall u. d[u] > 0`
3. All f > 0: `forall u. f[u] > 0`
4. Discovery < finish: `forall u. d[u] < f[u]`

## Resolution Strategy Used
- Invariants `dfs_ok` (BLACK ⟹ d > 0, f > 0, d < f) and `gray_ok`
  (GRAY ⟹ d > 0, d ≤ time) track timestamps through DFS
- `count_ones` bijection tracks stack size = GRAY count to prove all vertices
  finish (become BLACK) when the outer loop completes
- `nonwhite_below` tracks outer loop progress to establish all-BLACK at exit
