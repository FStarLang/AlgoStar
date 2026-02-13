module CLRS.Ch22.Graph.Complexity

open FStar.Mul

(**
 * Complexity Analysis for BFS and DFS with Adjacency Matrix Representation
 *
 * This module proves complexity bounds for graph algorithms using adjacency
 * matrix representation, where each vertex's neighbors are found by scanning
 * all V vertices.
 *)

(** 
 * BFS with adjacency matrix: V rounds × V neighbor checks per round
 * Each of V vertices is processed once, and for each vertex we check
 * all V potential neighbors in the matrix.
 *)
let bfs_iterations (v: nat) : nat = v * v

(**
 * BFS is O(V²) for adjacency matrix representation.
 * This is a direct consequence of the definition.
 *)
let bfs_quadratic (v: nat) : Lemma
  (ensures bfs_iterations v == v * v)
  = ()

(**
 * DFS similarly: each vertex processed once, V neighbors checked per vertex.
 * The adjacency matrix requires checking all V columns for each vertex.
 *)
let dfs_iterations (v: nat) : nat = v * v

(**
 * For adjacency list representation, BFS/DFS would be O(V+E).
 * With adjacency matrix, since E ≤ V², we have O(V+E) ≤ O(V²).
 * 
 * This lemma shows that V + E ≤ V² + V when E ≤ V².
 *)
let adj_matrix_subsumes (v e: nat) : Lemma
  (requires e <= v * v)
  (ensures v + e <= v * v + v)
  = ()

(**
 * The total work is bounded by 2V² for V ≥ 1.
 * This is useful for establishing the O(V²) bound more explicitly.
 *)
let bfs_total_bound (v: nat) : Lemma
  (requires v >= 1)
  (ensures v * v + v <= 2 * v * v)
  = ()

(**
 * DFS has the same complexity bound as BFS with adjacency matrix.
 *)
let dfs_total_bound (v: nat) : Lemma
  (requires v >= 1)
  (ensures v * v + v <= 2 * v * v)
  = ()

(**
 * For dense graphs (E close to V²), adjacency matrix is efficient.
 * This lemma captures when matrix representation doesn't add overhead.
 *)
let dense_graph_efficient (v e: nat) : Lemma
  (requires e >= v * v / 2 /\ v >= 1)
  (ensures 2 * (v + e) >= v * v)
  = ()
