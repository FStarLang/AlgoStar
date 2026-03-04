(*
   Dijkstra triangle inequality — Interface

   Exposes the public types and key theorems from the triangle inequality proof.
   Internal lemmas (relax_edge_*, find_min_*, etc.) are hidden.
*)

module CLRS.Ch24.Dijkstra.TriangleInequality

open FStar.Seq
open FStar.Mul

let inf : int = 1000000

(* Distance vector: current distance estimates *)
type dist_vec (n: nat) = d:Seq.seq int{Seq.length d == n}

(* Weight matrix: n×n adjacency matrix (flattened) *)
type weight_matrix (n: nat) = w:Seq.seq int{Seq.length w == n * n}

(* All weights are non-negative (required for Dijkstra) *)
let all_weights_non_negative (#n: nat) (weights: weight_matrix n) : prop =
  forall (i: nat). i < n * n ==> Seq.index weights i >= 0

(* Triangle inequality for a single edge (u,v) *)
let edge_satisfies_triangle (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) 
                           (u v: nat{u < n /\ v < n}) : prop =
  let d_u = Seq.index dist u in
  let d_v = Seq.index dist v in
  let w = Seq.index weights (u * n + v) in
  (w < inf /\ d_u < inf) ==> d_v <= d_u + w

(* Triangle inequality holds for all edges *)
let triangle_inequality (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) : prop =
  forall (u v: nat). u < n /\ v < n ==> edge_satisfies_triangle dist weights u v

(* A vertex has been "processed" if all its outgoing edges have been relaxed *)
type processed_set = nat -> bool

(* Initially no vertices are processed *)
let initial_processed : processed_set = fun _ -> false

(* Triangle inequality restricted to processed vertices *)
val triangle_inequality_from_processed
  (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) (processed: processed_set) : prop

(* Pure Dijkstra simulation: process n vertices *)
val process_vertices
  (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
  (processed: processed_set) (remaining: nat)
  : Tot (dist_vec n) (decreases remaining)

(* Processed vertices have distances ≤ all unprocessed *)
val processed_le_unprocessed
  (#n: nat) (dist: dist_vec n) (processed: processed_set) : prop

(* Main theorem: Dijkstra's greedy process establishes triangle inequality *)
val dijkstra_establishes_triangle_inequality
  (#n: nat) (dist_init: dist_vec n) (weights: weight_matrix n)
  : Lemma
    (requires
      n > 0 /\
      all_weights_non_negative weights /\
      triangle_inequality_from_processed dist_init weights initial_processed /\
      processed_le_unprocessed dist_init initial_processed)
    (ensures (
      let dist_final = process_vertices dist_init weights initial_processed n in
      triangle_inequality dist_final weights))

(* Corollary: starting from standard init (dist[source]=0, rest=inf) *)
val dijkstra_algorithm_establishes_triangle
  (#n: nat) (source: nat{source < n}) (weights: weight_matrix n)
  : Lemma
    (requires n > 0 /\ all_weights_non_negative weights)
    (ensures
      (let dist_init = Seq.upd (Seq.create n inf) source 0 in
       let dist_final = process_vertices dist_init weights initial_processed n in
       triangle_inequality dist_final weights))
