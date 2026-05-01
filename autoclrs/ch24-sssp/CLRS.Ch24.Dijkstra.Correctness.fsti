(*
   CLRS Theorem 24.6: Greedy Choice Property for Dijkstra's Algorithm — Interface

   Exposes the key correctness lemmas used by Dijkstra.Lemmas:
   - greedy_choice_invariant: dist[u] = δ(s,u) when u is extracted
   - relax_establishes_triangle_inequality: relaxation from settled vertex x
     ensures triangle inequality for edges from x

   NO admits. NO assumes.
*)

module CLRS.Ch24.Dijkstra.Correctness

open FStar.Seq

module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec

(* ===== Definitions ===== *)

type settled_set = nat -> bool

let is_settled (s: settled_set) (v: nat) : bool = s v

let initial_settled (source: nat) : settled_set =
  fun v -> v = source

let add_to_settled (s: settled_set) (u: nat) : settled_set =
  fun v -> s v || v = u

let all_settled_optimal 
  (dist: Seq.seq int) 
  (weights: Seq.seq int) 
  (n source: nat) 
  (settled: settled_set)
  : prop =
  n > 0 /\
  source < n /\
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (v: nat). v < n /\ is_settled settled v ==>
    Seq.index dist v == SP.sp_dist weights n source v)

let all_distances_upper_bounds
  (dist: Seq.seq int)
  (weights: Seq.seq int)
  (n source: nat)
  : prop =
  n > 0 /\
  source < n /\
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (v: nat). v < n ==>
    Seq.index dist v >= SP.sp_dist weights n source v)

let triangle_inequality
  (dist: Seq.seq int)
  (weights: Seq.seq int)
  (n: nat)
  (settled: settled_set)
  : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (u v: nat). u < n /\ v < n /\ is_settled settled u ==>
    (let w_uv = Seq.index weights (u * n + v) in
     let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     (w_uv < SP.inf /\ d_u < SP.inf) ==> d_v <= d_u + w_uv))

let all_weights_non_negative (weights: Seq.seq int) : prop =
  forall (i: nat). i < Seq.length weights ==> Seq.index weights i >= 0

(* ===== Key Lemmas ===== *)

/// CLRS Theorem 24.6: when u is extracted as minimum unvisited,
/// dist[u] == δ(s, u).
val greedy_choice_invariant
  (dist: Seq.seq int)
  (weights: Seq.seq int)
  (n source: nat)
  (settled: settled_set)
  (u: nat)
  : Lemma
  (requires
    n > 0 /\
    source < n /\
    u < n /\
    Seq.length dist == n /\
    Seq.length weights == n * n /\
    Seq.index dist source == 0 /\
    is_settled settled source /\
    all_weights_non_negative weights /\
    not (is_settled settled u) /\
    (forall (v: nat). v < n /\ not (is_settled settled v) ==>
      Seq.index dist u <= Seq.index dist v) /\
    all_settled_optimal dist weights n source settled /\
    triangle_inequality dist weights n settled /\
    all_distances_upper_bounds dist weights n source /\
    SP.has_triangle_inequality dist weights n)
  (ensures
    Seq.index dist u == SP.sp_dist weights n source u)

/// After relaxing all edges from settled vertex x, triangle inequality
/// holds for edges from x.
val relax_establishes_triangle_inequality
  (dist_before dist_after: Seq.seq int)
  (weights: Seq.seq int)
  (n x: nat)
  (settled: settled_set)
  : Lemma
  (requires
    x < n /\
    is_settled settled x /\
    Seq.length dist_before == n /\
    Seq.length dist_after == n /\
    Seq.length weights == n * n /\
    Seq.index dist_before x == Seq.index dist_after x /\
    (forall (v: nat). v < n ==>
      (let w_xv = Seq.index weights (x * n + v) in
       let d_x = Seq.index dist_before x in
       let d_v_before = Seq.index dist_before v in
       let d_v_after = Seq.index dist_after v in
       d_v_after == (if d_x < SP.inf && w_xv < SP.inf && d_x + w_xv < d_v_before
                     then d_x + w_xv
                     else d_v_before))))
  (ensures
    forall (v: nat). v < n ==>
      (let w_xv = Seq.index weights (x * n + v) in
       let d_x = Seq.index dist_after x in
       let d_v = Seq.index dist_after v in
       (w_xv < SP.inf /\ d_x < SP.inf) ==> d_v <= d_x + w_xv))
