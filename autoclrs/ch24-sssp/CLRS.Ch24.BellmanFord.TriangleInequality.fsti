(*
   Bellman-Ford triangle inequality — Interface

   Exposes public types and key theorems:
   - no_violations_implies_triangle:  no relaxable edge ⇒ triangle inequality
   - stable_distances_have_triangle:  bf_round fixpoint ⇒ triangle inequality
   - bellman_ford_stable_establishes_triangle: standard BF (n-1 rounds stable) ⇒ triangle
*)

module CLRS.Ch24.BellmanFord.TriangleInequality

open FStar.Seq

let inf : int = CLRS.Ch24.ShortestPath.Inf.inf

(* Distance vector: current distance estimates *)
type dist_vec (n: nat) = d:Seq.seq int{Seq.length d == n}

(* Weight matrix: n×n adjacency matrix (flattened) *)
type weight_matrix (n: nat) = w:Seq.seq int{Seq.length w == n * n}

(* Triangle inequality for a single edge (u,v) *)
let edge_satisfies_triangle (dist: dist_vec 'n) (weights: weight_matrix 'n) (u v: nat{u < 'n /\ v < 'n}) : prop =
  let d_u = Seq.index dist u in
  let d_v = Seq.index dist v in
  let w = Seq.index weights (u * 'n + v) in
  (w < inf /\ d_u < inf) ==> d_v <= d_u + w

(* Triangle inequality holds for all edges *)
let triangle_inequality (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) : prop =
  forall (u v: nat). u < n /\ v < n ==> edge_satisfies_triangle dist weights u v

(* If the negative cycle check passes (no violations), triangle inequality holds *)
val no_violations_implies_triangle (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
  : Lemma
    (requires (
      forall (u v: nat). u < n /\ v < n ==>
        (let d_u = Seq.index dist u in
         let d_v = Seq.index dist v in
         let w = Seq.index weights (u * n + v) in
         w >= inf \/ d_u >= inf \/ d_v <= d_u + w)))
    (ensures triangle_inequality dist weights)

(* One round of Bellman-Ford relaxation *)
val bf_round (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) : dist_vec n

(* k rounds of Bellman-Ford *)
val bf_k_rounds (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) (k: nat)
  : Tot (dist_vec n) (decreases k)

(* If bf_round is a fixpoint, triangle inequality holds *)
val stable_distances_have_triangle (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
  : Lemma
    (requires Seq.equal (bf_round dist weights) dist)
    (ensures triangle_inequality dist weights)

(* Main theorem: after n-1 rounds with no change, triangle inequality holds *)
val bellman_ford_stable_establishes_triangle (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
  : Lemma
    (requires 
      n >= 1 /\
      Seq.equal (bf_k_rounds dist weights n) (bf_k_rounds dist weights (n - 1)))
    (ensures triangle_inequality (bf_k_rounds dist weights (n - 1)) weights)
