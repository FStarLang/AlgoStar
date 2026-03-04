(**
 * CLRS Chapter 22: Topological Sort — Complexity Interface
 *
 * Complexity bounds for Kahn's topological sort with adjacency-matrix
 * representation. The outer loop processes each vertex once, and for each
 * dequeued vertex scans V neighbors to decrement in-degrees, yielding O(V²).
 * The ghost tick counter in TopologicalSort.Impl.fst proves ≤ V².
 *)
module CLRS.Ch22.TopologicalSort.Complexity

open FStar.Mul

(*** Topological Sort Complexity Bounds ***)

/// Kahn's algorithm iteration count with adjacency matrix: V × V
val topo_sort_work (v: nat) : nat

/// Kahn's algorithm is O(V²) for adjacency-matrix representation
val topo_sort_quadratic (v: nat) : Lemma (ensures topo_sort_work v == v * v)

/// For adjacency-matrix, O(V+E) ≤ O(V²) since E ≤ V²
val adj_matrix_topo_bound (v e: nat) : Lemma (requires e <= v * v) (ensures v + e <= v * v + v)
