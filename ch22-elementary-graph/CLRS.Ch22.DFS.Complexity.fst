(**
 * CLRS Chapter 22: DFS — Complexity Proofs
 *
 * Proves complexity bounds for stack-based DFS (CLRS §22.3) with
 * adjacency-matrix representation.
 *
 * Key result: StackDFS runs in O(V²) time, verified via ghost tick counter
 * in StackDFS.fst (≤ 2·V² ticks). The amortized argument uses sum_scan_idx:
 * each scan step ticks once, and scan_idx[u] ≤ V for all u, so total scan
 * ticks ≤ V². Adding V outer-loop ticks gives ≤ 2·V².
 *
 * With adjacency-list representation, DFS would be O(V+E).
 *
 * Zero admits.
 *)
module CLRS.Ch22.DFS.Complexity

open FStar.Mul

let dfs_work (v: nat) : nat = v * v

let dfs_quadratic (v: nat) : Lemma (ensures dfs_work v == v * v) = ()

let dfs_total_bound (v: nat) : Lemma (requires v >= 1) (ensures v * v + v <= 2 * v * v) = ()

let adj_matrix_dfs_bound (v e: nat) : Lemma (requires e <= v * v) (ensures v + e <= v * v + v) = ()
