(**
 * CLRS Chapter 22: BFS — Complexity Interface
 *
 * Complexity bounds for queue-based BFS with adjacency-matrix representation.
 * BFS processes each vertex once and scans all V potential neighbors per vertex,
 * yielding O(V²) total work. The ghost tick counter in QueueBFS proves ≤ 2·V².
 *)
module CLRS.Ch22.BFS.Complexity

open FStar.Mul

(*** BFS Complexity Bounds ***)

/// BFS iteration count with adjacency matrix: V × V neighbor checks
val bfs_work (v: nat) : nat

/// BFS is O(V²) for adjacency-matrix representation
val bfs_quadratic (v: nat) : Lemma (ensures bfs_work v == v * v)

/// Total BFS work including overhead: ≤ 2·V² for V ≥ 1
/// (Each of V vertices dequeued once: V ticks; scanning V neighbors per vertex: V² ticks)
val bfs_total_bound (v: nat) : Lemma (requires v >= 1) (ensures v * v + v <= 2 * v * v)

/// For adjacency-matrix, O(V+E) ≤ O(V²) since E ≤ V²
val adj_matrix_bfs_bound (v e: nat) : Lemma (requires e <= v * v) (ensures v + e <= v * v + v)
