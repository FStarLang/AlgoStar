(**
 * CLRS Chapter 22: DFS — Complexity Interface
 *
 * Complexity bounds for stack-based DFS with adjacency-matrix representation.
 * DFS processes each vertex once and scans all V neighbors via scan_idx,
 * yielding O(V²) total work. The ghost tick counter in StackDFS proves ≤ 2·V².
 *
 * Amortized argument: each scan step ticks once, scan_idx[u] ≤ V for all u,
 * so total scan ticks ≤ V × V = V². Plus V outer-loop ticks → ≤ 2·V².
 *)
module CLRS.Ch22.DFS.Complexity

open FStar.Mul

(*** DFS Complexity Bounds ***)

/// DFS iteration count with adjacency matrix: V × V neighbor scans
val dfs_work (v: nat) : nat

/// DFS is O(V²) for adjacency-matrix representation
val dfs_quadratic (v: nat) : Lemma (ensures dfs_work v == v * v)

/// Total DFS work including overhead: ≤ 2·V² for V ≥ 1
/// (V outer-loop iterations + V² amortized scan steps)
val dfs_total_bound (v: nat) : Lemma (requires v >= 1) (ensures v * v + v <= 2 * v * v)

/// For adjacency-matrix, O(V+E) ≤ O(V²) since E ≤ V²
val adj_matrix_dfs_bound (v e: nat) : Lemma (requires e <= v * v) (ensures v + e <= v * v + v)
