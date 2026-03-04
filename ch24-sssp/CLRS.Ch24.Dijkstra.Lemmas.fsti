module CLRS.Ch24.Dijkstra.Lemmas

(*
   Interface for Dijkstra lemmas.

   Re-exports key results from:
   - CLRS.Ch24.Dijkstra.Correctness  (Theorem 24.6: greedy choice property)
   - CLRS.Ch24.Dijkstra.TriangleInequality  (relaxation ⇒ triangle inequality)
*)

open FStar.Mul

module DC  = CLRS.Ch24.Dijkstra.Correctness
module DTI = CLRS.Ch24.Dijkstra.TriangleInequality
module SP  = CLRS.Ch24.ShortestPath.Spec

/// CLRS Theorem 24.6: when vertex u is extracted as minimum unvisited,
/// dist[u] = δ(s,u)
val greedy_choice_invariant
  (dist: FStar.Seq.seq int)
  (weights: FStar.Seq.seq int)
  (n source: nat)
  (settled: DC.settled_set)
  (u: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ u < n /\
      FStar.Seq.length dist == n /\
      FStar.Seq.length weights == n * n /\
      FStar.Seq.index dist source == 0 /\
      DC.is_settled settled source /\
      DC.all_weights_non_negative weights /\
      not (DC.is_settled settled u) /\
      (forall (v: nat). v < n /\ not (DC.is_settled settled v) ==>
        FStar.Seq.index dist u <= FStar.Seq.index dist v) /\
      DC.all_settled_optimal dist weights n source settled /\
      DC.triangle_inequality dist weights n settled /\
      DC.all_distances_upper_bounds dist weights n source /\
      SP.has_triangle_inequality dist weights n)
    (ensures
      FStar.Seq.index dist u == SP.sp_dist weights n source u)

/// Relaxation establishes triangle inequality for settled edges
val relax_establishes_triangle_inequality
  (dist_before dist_after: FStar.Seq.seq int)
  (weights: FStar.Seq.seq int)
  (n x: nat)
  (settled: DC.settled_set)
  : Lemma
    (requires
      x < n /\
      DC.is_settled settled x /\
      FStar.Seq.length dist_before == n /\
      FStar.Seq.length dist_after == n /\
      FStar.Seq.length weights == n * n /\
      FStar.Seq.index dist_before x == FStar.Seq.index dist_after x /\
      (forall (v: nat). v < n ==>
        (let w_xv = FStar.Seq.index weights (x * n + v) in
         let d_x = FStar.Seq.index dist_before x in
         let d_v_before = FStar.Seq.index dist_before v in
         let d_v_after = FStar.Seq.index dist_after v in
         d_v_after == (if d_x < SP.inf && w_xv < SP.inf && d_x + w_xv < d_v_before
                       then d_x + w_xv
                       else d_v_before))))
    (ensures
      forall (v: nat). v < n ==>
        (let w_xv = FStar.Seq.index weights (x * n + v) in
         let d_x = FStar.Seq.index dist_after x in
         let d_v = FStar.Seq.index dist_after v in
         (w_xv < SP.inf /\ d_x < SP.inf) ==> d_v <= d_x + w_xv))

/// After processing all vertices, triangle inequality holds
val dijkstra_algorithm_establishes_triangle
  (#n: nat) (source: nat{source < n})
  (weights: DTI.weight_matrix n)
  : Lemma
    (requires n > 0 /\ DTI.all_weights_non_negative weights)
    (ensures (
      let dist_init = FStar.Seq.upd (FStar.Seq.create n DTI.inf) source 0 in
      let dist_final = DTI.process_vertices dist_init weights DTI.initial_processed n in
      DTI.triangle_inequality dist_final weights))

/// After full Dijkstra run, triangle inequality holds
val dijkstra_establishes_triangle_inequality
  (#n: nat) (dist_init: DTI.dist_vec n) (weights: DTI.weight_matrix n)
  : Lemma
    (requires
      n > 0 /\
      DTI.all_weights_non_negative weights /\
      DTI.triangle_inequality_from_processed dist_init weights DTI.initial_processed /\
      DTI.processed_le_unprocessed dist_init DTI.initial_processed)
    (ensures (
      let dist_final = DTI.process_vertices dist_init weights DTI.initial_processed n in
      DTI.triangle_inequality dist_final weights))
