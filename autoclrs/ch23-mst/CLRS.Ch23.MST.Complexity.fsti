(*
   CLRS Chapter 23: MST Complexity Analysis — Interface

   Signatures for complexity bounds of MST algorithms
   using adjacency matrix representation (CLRS §23.2).
*)

module CLRS.Ch23.MST.Complexity


/// Kruskal iterations with adjacency matrix: (V-1) × V²
val kruskal_iterations (v: nat) : nat

//SNIPPET_START: kruskal_cubic
/// Kruskal is O(V³) with adjacency matrix
val kruskal_cubic (v: nat) : Lemma
  (requires v >= 1)
  (ensures kruskal_iterations v <= v * v * v)
//SNIPPET_END: kruskal_cubic

/// Prim iterations with adjacency matrix: V × 2V
val prim_iterations (v: nat) : nat

//SNIPPET_START: prim_quadratic
/// Prim is O(V²) with adjacency matrix
val prim_quadratic (v: nat) : Lemma
  (ensures prim_iterations v <= 2 * v * v)
//SNIPPET_END: prim_quadratic

/// For V ≥ 4, Prim's quadratic bound beats Kruskal's cubic bound
val prim_better_than_kruskal (v: nat) : Lemma
  (requires v >= 4)
  (ensures prim_iterations v < kruskal_iterations v)
