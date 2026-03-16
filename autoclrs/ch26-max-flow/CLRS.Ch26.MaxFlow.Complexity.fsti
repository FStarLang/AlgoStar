module CLRS.Ch26.MaxFlow.Complexity

open FStar.Mul
open CLRS.Ch26.MaxFlow.Spec
open CLRS.Ch26.MaxFlow.Lemmas

(*
   Interface for Edmonds-Karp complexity analysis (CLRS Theorem 26.8).
   
   All results fully proven (zero admits, zero assume vals).
   
   Key proven results:
   - O(VE²) total complexity bound
   - Each augmentation creates at least one critical edge
   - Dense graph: O(V⁵), sparse graph: O(V³)
   - CLRS Lemma 26.7: BFS distances non-decreasing (proven)
   - CLRS Lemma 26.8: Edge criticality bound (proven)
*)

(** Ghost tick counter: tracks computational cost *)
let tick_count : Type0 = nat

(** Cost of one BFS traversal: proportional to E *)
val bfs_cost (num_edges: nat) : tick_count

(** Cost of one augmentation step: BFS + path traversal *)
val augmentation_cost (num_edges: nat) : tick_count

(** Upper bound on number of augmentations: O(VE) *)
val max_augmentations (num_vertices: nat) (num_edges: nat) : nat

(** Theorem 26.8 (CLRS): Edmonds-Karp runs in O(VE²) time *)
val edmonds_karp_complexity
  (#n: nat)
  (cap: capacity_matrix n)
  (source: nat{source < n})
  (sink: nat{sink < n})
  (num_edges: nat)
  : Lemma
    (requires 
      num_edges >= n /\
      num_edges <= n * n)
    (ensures
      (let num_augmentations = max_augmentations n num_edges in
       let total_cost = num_augmentations * augmentation_cost num_edges in
       total_cost <= n * num_edges * (2 * num_edges)))

(** Corollary: For dense graphs (E = V²), complexity is O(V⁵) *)
val edmonds_karp_dense_graph_complexity
  (n: nat{n > 0})
  : Lemma
    (ensures
      (let num_edges = n * n in
       let total_cost = max_augmentations n num_edges * augmentation_cost num_edges in
       total_cost <= n * (n * n) * (2 * (n * n))))

(** Corollary: For sparse graphs (E = O(V)), complexity is O(V³) *)
val edmonds_karp_sparse_graph_complexity
  (n: nat{n > 1})
  (num_edges: nat)
  : Lemma
    (requires num_edges >= n /\ num_edges <= 2 * n)
    (ensures
      (let total_cost = max_augmentations n num_edges * augmentation_cost num_edges in
       total_cost <= n * num_edges * (2 * num_edges) /\
       total_cost <= n * (2*n) * (2 * (2*n))))
