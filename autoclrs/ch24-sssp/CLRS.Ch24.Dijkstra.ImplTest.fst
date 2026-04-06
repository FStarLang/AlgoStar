(*
   CLRS Chapter 24: Dijkstra — Spec Validation Test

   Validates the Impl.fsti API for CLRS §24.3 Dijkstra's algorithm
   by calling it on a small concrete instance and proving that the
   postcondition is precise enough to determine the output.

   Test instance:
     3 vertices, source = 0
     Edges: 0→1 (weight 3), 0→2 (weight 7), 1→2 (weight 2)
     Expected shortest paths from 0:
       dist[0] = 0, dist[1] = 3, dist[2] = 5 (via 0→1→2: 3+2)
     Expected predecessor tree:
       pred[0] = 0 (source), pred[1] = 0 (via 0→1), pred[2] = 1 (via 1→2)

   Attribution: Pattern inspired by
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   NO admits. NO assumes.
*)
module CLRS.Ch24.Dijkstra.ImplTest
#lang-pulse

friend CLRS.Ch24.ShortestPath.Inf

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec
module DI = CLRS.Ch24.Dijkstra.Impl

(* ========== Concrete test instance ========== *)

(* 3-vertex graph, adjacency matrix (row-major):
     0→0: inf,  0→1: 3,    0→2: 7
     1→0: inf,  1→1: inf,  1→2: 2
     2→0: inf,  2→1: inf,  2→2: inf *)
let tw_list : list int = [SP.inf; 3; 7; SP.inf; SP.inf; 2; SP.inf; SP.inf; SP.inf]
let tw_seq : Seq.seq int = Seq.seq_of_list tw_list

(* ========== Precondition lemmas ========== *)

(* weights_in_range: each finite weight w satisfies |w|*(n-1) < inf.
   With inf=1000000 (visible via friend): 3*2=6, 7*2=14, 2*2=4, all < 1000000. *)
let tw_weights_in_range () : Lemma (SP.weights_in_range tw_seq 3) =
  assert_norm (Seq.length tw_seq == 9);
  assert_norm (Seq.index tw_seq 0 == SP.inf);
  assert_norm (Seq.index tw_seq 1 == 3);
  assert_norm (Seq.index tw_seq 2 == 7);
  assert_norm (Seq.index tw_seq 3 == SP.inf);
  assert_norm (Seq.index tw_seq 4 == SP.inf);
  assert_norm (Seq.index tw_seq 5 == 2);
  assert_norm (Seq.index tw_seq 6 == SP.inf);
  assert_norm (Seq.index tw_seq 7 == SP.inf);
  assert_norm (Seq.index tw_seq 8 == SP.inf)

(* all_weights_non_negative: all entries ≥ 0 *)
let tw_all_nonneg () : Lemma (SP.all_weights_non_negative tw_seq) =
  assert_norm (Seq.length tw_seq == 9);
  assert_norm (Seq.index tw_seq 0 == SP.inf);
  assert_norm (Seq.index tw_seq 1 == 3);
  assert_norm (Seq.index tw_seq 2 == 7);
  assert_norm (Seq.index tw_seq 3 == SP.inf);
  assert_norm (Seq.index tw_seq 4 == SP.inf);
  assert_norm (Seq.index tw_seq 5 == 2);
  assert_norm (Seq.index tw_seq 6 == SP.inf);
  assert_norm (Seq.index tw_seq 7 == SP.inf);
  assert_norm (Seq.index tw_seq 8 == SP.inf)

(* ========== Postcondition precision: sp_dist normalization ========== *)

(* With friend CLRS.Ch24.ShortestPath.Inf, the normalizer can fully evaluate
   sp_dist on our concrete graph since inf = 1000000 is visible. *)
#push-options "--z3rlimit 40 --split_queries always"
let sp_dist_v0 () : Lemma (SP.sp_dist tw_seq 3 0 0 == 0) =
  assert_norm (SP.sp_dist tw_seq 3 0 0 == 0)

let sp_dist_v1 () : Lemma (SP.sp_dist tw_seq 3 0 1 == 3) =
  assert_norm (SP.sp_dist tw_seq 3 0 1 == 3)

let sp_dist_v2 () : Lemma (SP.sp_dist tw_seq 3 0 2 == 5) =
  assert_norm (SP.sp_dist tw_seq 3 0 2 == 5)
#pop-options

(* SZ.t equality check — computational, survives extraction to C *)
inline_for_extraction
let sz_eq (a b: SZ.t) : (r:bool{r <==> SZ.v a = SZ.v b}) =
  let open FStar.SizeT in not (a <^ b || b <^ a)

(* Completeness: Dijkstra's postcondition (dist[v] == sp_dist(0,v) for all v)
   uniquely determines dist = [0; 3; 5] for this input. *)
let completeness_dijkstra_3 (sdist: Seq.seq int) (sw: Seq.seq int)
  : Lemma
    (requires
      Seq.length sdist == 3 /\
      sw `Seq.equal` tw_seq /\
      (forall (v: nat). v < 3 ==> Seq.index sdist v == SP.sp_dist sw 3 0 v))
    (ensures
      Seq.index sdist 0 == 0 /\
      Seq.index sdist 1 == 3 /\
      Seq.index sdist 2 == 5)
  = sp_dist_v0 (); sp_dist_v1 (); sp_dist_v2 ()

(* Completeness: Dijkstra's postcondition (shortest_path_tree)
   uniquely determines pred = [0sz; 0sz; 1sz] for this input.

   Proof: For each non-source vertex v, shortest_path_tree gives
     sp_dist(0,v) == sp_dist(0, pred[v]) + w(pred[v], v)
   with pred[v] < 3. Case analysis on pred[v] ∈ {0,1,2} using
   concrete sp_dist and weight values eliminates all but one option:
     pred[1] = 0 (only 0+3=3 works), pred[2] = 1 (only 3+2=5 works). *)
#push-options "--z3rlimit 40 --split_queries always"
let completeness_pred_3 (spred: Seq.seq SZ.t) (sw: Seq.seq int)
  : Lemma
    (requires
      sw `Seq.equal` tw_seq /\
      DI.shortest_path_tree spred sw 3 0)
    (ensures
      SZ.v (Seq.index spred 0) == 0 /\
      SZ.v (Seq.index spred 1) == 0 /\
      SZ.v (Seq.index spred 2) == 1)
  = sp_dist_v0 (); sp_dist_v1 (); sp_dist_v2 ();
    // Weight values for Z3 case analysis on predecessors
    assert_norm (Seq.index tw_seq 1 == 3);      // w(0,1) = 3
    assert_norm (Seq.index tw_seq 4 == SP.inf);  // w(1,1) = inf
    assert_norm (Seq.index tw_seq 7 == SP.inf);  // w(2,1) = inf
    assert_norm (Seq.index tw_seq 2 == 7);       // w(0,2) = 7
    assert_norm (Seq.index tw_seq 5 == 2);       // w(1,2) = 2
    assert_norm (Seq.index tw_seq 8 == SP.inf)   // w(2,2) = inf
#pop-options

(* Build the concrete weight sequence from array writes *)
let seq_after_weight_writes ()
  : Lemma (let s0 = Seq.create 9 0 in
           let s1 = Seq.upd s0 0 SP.inf in
           let s2 = Seq.upd s1 1 3 in
           let s3 = Seq.upd s2 2 7 in
           let s4 = Seq.upd s3 3 SP.inf in
           let s5 = Seq.upd s4 4 SP.inf in
           let s6 = Seq.upd s5 5 2 in
           let s7 = Seq.upd s6 6 SP.inf in
           let s8 = Seq.upd s7 7 SP.inf in
           let s9 = Seq.upd s8 8 SP.inf in
           s9 `Seq.equal` tw_seq)
  = assert_norm (tw_seq `Seq.equal` Seq.seq_of_list tw_list)

(* ========== Main Test ========== *)

#push-options "--z3rlimit 20 --fuel 4 --ifuel 2"
```pulse
fn test_dijkstra_3 ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // --- Allocate weights array (3×3 = 9 entries) ---
  let wv = V.alloc 0 9sz;
  V.to_array_pts_to wv;
  let weights = V.vec_to_array wv;
  rewrite (A.pts_to (V.vec_to_array wv) (Seq.create 9 0))
       as (A.pts_to weights (Seq.create 9 0));
  weights.(0sz) <- SP.inf;
  weights.(1sz) <- 3;
  weights.(2sz) <- 7;
  weights.(3sz) <- SP.inf;
  weights.(4sz) <- SP.inf;
  weights.(5sz) <- 2;
  weights.(6sz) <- SP.inf;
  weights.(7sz) <- SP.inf;
  weights.(8sz) <- SP.inf;

  // --- Allocate dist array (3 entries) ---
  let dv = V.alloc 0 3sz;
  V.to_array_pts_to dv;
  let dist = V.vec_to_array dv;
  rewrite (A.pts_to (V.vec_to_array dv) (Seq.create 3 0))
       as (A.pts_to dist (Seq.create 3 0));

  // --- Allocate pred array (3 entries of SZ.t) ---
  let pv = V.alloc 0sz 3sz;
  V.to_array_pts_to pv;
  let pred = V.vec_to_array pv;
  rewrite (A.pts_to (V.vec_to_array pv) (Seq.create 3 0sz))
       as (A.pts_to pred (Seq.create 3 0sz));

  // --- Ghost counter ---
  let ctr = GR.alloc #nat 0;

  // --- Bind ghost sequences ---
  with sw. assert (A.pts_to weights sw);

  // --- Prove weights == tw_seq ---
  seq_after_weight_writes ();
  assert (pure (sw `Seq.equal` tw_seq));

  // --- Prove preconditions ---
  tw_weights_in_range ();
  tw_all_nonneg ();

  // --- Call Dijkstra ---
  DI.dijkstra weights 3sz 0sz dist pred ctr;

  // --- Read postcondition ---
  with sdist'. assert (A.pts_to dist sdist');
  with spred'. assert (A.pts_to pred spred');
  with (cf: nat). assert (GR.pts_to ctr cf);

  // --- Prove completeness: output is uniquely determined ---
  completeness_dijkstra_3 sdist' sw;
  completeness_pred_3 spred' sw;

  // --- Read back and verify each distance ---
  let d0 = dist.(0sz);
  let d1 = dist.(1sz);
  let d2 = dist.(2sz);
  assert (pure (d0 == 0));
  assert (pure (d1 == 3));
  assert (pure (d2 == 5));

  // --- Read back and verify each predecessor ---
  let p0 = pred.(0sz);
  let p1 = pred.(1sz);
  let p2 = pred.(2sz);
  assert (pure (SZ.v p0 == 0));
  assert (pure (SZ.v p1 == 0));
  assert (pure (SZ.v p2 == 1));

  // --- Computational check (survives extraction to C) ---
  let pass = (d0 = 0 && d1 = 3 && d2 = 5
           && sz_eq p0 0sz && sz_eq p1 0sz && sz_eq p2 1sz);

  // --- Cleanup ---
  with sw'. assert (A.pts_to weights sw');
  rewrite (A.pts_to weights sw') as (A.pts_to (V.vec_to_array wv) sw');
  V.to_vec_pts_to wv;
  V.free wv;

  with sd'. assert (A.pts_to dist sd');
  rewrite (A.pts_to dist sd') as (A.pts_to (V.vec_to_array dv) sd');
  V.to_vec_pts_to dv;
  V.free dv;

  with sp'. assert (A.pts_to pred sp');
  rewrite (A.pts_to pred sp') as (A.pts_to (V.vec_to_array pv) sp');
  V.to_vec_pts_to pv;
  V.free pv;

  GR.free ctr;
  pass
}
```
#pop-options
