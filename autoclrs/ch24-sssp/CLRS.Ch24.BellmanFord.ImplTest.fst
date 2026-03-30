(*
   CLRS Chapter 24: Bellman-Ford — Spec Validation Test

   Validates the Impl.fsti API for CLRS §24.1 Bellman-Ford algorithm
   by calling it on a small concrete instance and proving that the
   postcondition is precise enough to determine the output.

   Test instance:
     3 vertices, source = 0
     Edges: 0→1 (weight 4), 0→2 (weight 5), 1→2 (weight -2)
     Expected shortest paths from 0:
       dist[0] = 0, dist[1] = 4, dist[2] = 2 (via 0→1→2: 4+(-2))
       no_neg_cycle = true

   Attribution: Pattern inspired by
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   NO admits. NO assumes.
*)
module CLRS.Ch24.BellmanFord.ImplTest
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
module BF = CLRS.Ch24.BellmanFord.Impl

(* ========== Concrete test instance ========== *)

(* 3-vertex graph, adjacency matrix (row-major):
     0→0: inf,  0→1: 4,    0→2: 5
     1→0: inf,  1→1: inf,  1→2: -2
     2→0: inf,  2→1: inf,  2→2: inf
   Contains a negative-weight edge (1→2: -2) but no negative cycles. *)
let tw_list : list int = [SP.inf; 4; 5; SP.inf; SP.inf; (-2); SP.inf; SP.inf; SP.inf]
let tw_seq : Seq.seq int = Seq.seq_of_list tw_list

(* ========== Precondition lemmas ========== *)

(* weights_in_range: each finite weight w satisfies |w|*(n-1) < inf.
   With inf=1000000 (visible via friend): 4*2=8, 5*2=10, |-2|*2=4, all < 1000000.
   Also need w*(n-1) > -inf: 4*2=8 > -1000000, 5*2=10 > -1000000, (-2)*2=-4 > -1000000. *)
let tw_weights_in_range () : Lemma (SP.weights_in_range tw_seq 3) =
  assert_norm (Seq.length tw_seq == 9);
  assert_norm (Seq.index tw_seq 0 == SP.inf);
  assert_norm (Seq.index tw_seq 1 == 4);
  assert_norm (Seq.index tw_seq 2 == 5);
  assert_norm (Seq.index tw_seq 3 == SP.inf);
  assert_norm (Seq.index tw_seq 4 == SP.inf);
  assert_norm (Seq.index tw_seq 5 == (-2));
  assert_norm (Seq.index tw_seq 6 == SP.inf);
  assert_norm (Seq.index tw_seq 7 == SP.inf);
  assert_norm (Seq.index tw_seq 8 == SP.inf)

(* ========== Postcondition precision: sp_dist normalization ========== *)

(* With friend CLRS.Ch24.ShortestPath.Inf, the normalizer can fully evaluate
   sp_dist on our concrete graph since inf = 1000000 is visible.
   - sp_dist(0,0) = 0
   - sp_dist(0,1) = 4  (direct edge 0→1)
   - sp_dist(0,2) = 2  (path 0→1→2: 4+(-2) < 5) *)
#push-options "--z3rlimit 40 --split_queries always"
let sp_dist_v0 () : Lemma (SP.sp_dist tw_seq 3 0 0 == 0) =
  assert_norm (SP.sp_dist tw_seq 3 0 0 == 0)

let sp_dist_v1 () : Lemma (SP.sp_dist tw_seq 3 0 1 == 4) =
  assert_norm (SP.sp_dist tw_seq 3 0 1 == 4)
#pop-options

(* Normalizer needs concrete element values to evaluate sp_dist_k comparisons *)
let tw_idx5 () : Lemma (Seq.index tw_seq 5 == (-2)) =
  assert_norm (Seq.index tw_seq 5 == (-2))

(* Intermediate sp_dist_k values needed by the normalizer for sp_dist(2).
   sp_dist_k(1,1)=4 and sp_dist_k(2,1)=5 are needed as subcomputations
   when evaluating sp_dist_k(2,2) = min(5, 4+(-2)) = 2. *)
let sp_dist_k_v1_1 () : Lemma (SP.sp_dist_k tw_seq 3 0 1 1 == 4) =
  assert_norm (SP.sp_dist_k tw_seq 3 0 1 1 == 4)

let sp_dist_k_v2_1 () : Lemma (SP.sp_dist_k tw_seq 3 0 2 1 == 5) =
  assert_norm (SP.sp_dist_k tw_seq 3 0 2 1 == 5)

(* sp_dist(2) = 2 via path 0→1→2: 4+(-2) = 2 < 5.
   The normalizer struggles with this computation, so we help Z3
   by providing concrete element values and intermediate sp_dist_k results. *)
#push-options "--z3rlimit 20 --fuel 8 --ifuel 4"
let sp_dist_v2 () : Lemma (SP.sp_dist tw_seq 3 0 2 == 2) =
  sp_dist_k_v1_1 ();
  sp_dist_k_v2_1 ();
  sp_dist_v0 ();
  sp_dist_v1 ();
  assert_norm (Seq.length tw_seq == 9);
  assert_norm (Seq.index tw_seq 0 == SP.inf);
  assert_norm (Seq.index tw_seq 1 == 4);
  assert_norm (Seq.index tw_seq 2 == 5);
  assert_norm (Seq.index tw_seq 3 == SP.inf);
  assert_norm (Seq.index tw_seq 4 == SP.inf);
  assert_norm (Seq.index tw_seq 5 == (-2));
  assert_norm (Seq.index tw_seq 6 == SP.inf);
  assert_norm (Seq.index tw_seq 7 == SP.inf);
  assert_norm (Seq.index tw_seq 8 == SP.inf)
#pop-options

(* no_neg_cycles_flat: sp_dist_k(v, n) == sp_dist_k(v, n-1) for all v.
   An extra relaxation pass doesn't improve any distance.
   Strategy: use sp_dist (which normalizes) as a bridge to sp_dist_k(v, 2),
   then use fuel for Z3 to unfold sp_dist_k(v, 3) = min(sp_dist_k(v, 2), ...). *)
#push-options "--z3rlimit 20 --fuel 8 --ifuel 4"
let tw_no_neg_cycles () : Lemma (SP.no_neg_cycles_flat tw_seq 3 0) =
  sp_dist_v0 (); sp_dist_v1 (); sp_dist_v2 ();
  assert_norm (Seq.length tw_seq == 9);
  assert_norm (Seq.index tw_seq 0 == SP.inf);
  assert_norm (Seq.index tw_seq 1 == 4);
  assert_norm (Seq.index tw_seq 2 == 5);
  assert_norm (Seq.index tw_seq 3 == SP.inf);
  assert_norm (Seq.index tw_seq 4 == SP.inf);
  assert_norm (Seq.index tw_seq 5 == (-2));
  assert_norm (Seq.index tw_seq 6 == SP.inf);
  assert_norm (Seq.index tw_seq 7 == SP.inf);
  assert_norm (Seq.index tw_seq 8 == SP.inf)
#pop-options

(* Completeness: BF's postcondition under no-neg-cycles
   (dist[v] == sp_dist(0,v) for all v)
   uniquely determines dist = [0; 4; 2] for this input. *)
let completeness_bf_3 (sdist: Seq.seq int) (sw: Seq.seq int)
  : Lemma
    (requires
      Seq.length sdist == 3 /\
      sw `Seq.equal` tw_seq /\
      (forall (v: nat). v < 3 ==> Seq.index sdist v == SP.sp_dist sw 3 0 v))
    (ensures
      Seq.index sdist 0 == 0 /\
      Seq.index sdist 1 == 4 /\
      Seq.index sdist 2 == 2)
  = sp_dist_v0 (); sp_dist_v1 (); sp_dist_v2 ()

(* Build the concrete weight sequence from array writes *)
let seq_after_weight_writes ()
  : Lemma (let s0 = Seq.create 9 0 in
           let s1 = Seq.upd s0 0 SP.inf in
           let s2 = Seq.upd s1 1 4 in
           let s3 = Seq.upd s2 2 5 in
           let s4 = Seq.upd s3 3 SP.inf in
           let s5 = Seq.upd s4 4 SP.inf in
           let s6 = Seq.upd s5 5 (-2) in
           let s7 = Seq.upd s6 6 SP.inf in
           let s8 = Seq.upd s7 7 SP.inf in
           let s9 = Seq.upd s8 8 SP.inf in
           s9 `Seq.equal` tw_seq)
  = assert_norm (tw_seq `Seq.equal` Seq.seq_of_list tw_list)

(* ========== Main Test ========== *)

#push-options "--z3rlimit 20 --fuel 4 --ifuel 2"
```pulse
fn test_bellman_ford_3 ()
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
  weights.(1sz) <- 4;
  weights.(2sz) <- 5;
  weights.(3sz) <- SP.inf;
  weights.(4sz) <- SP.inf;
  weights.(5sz) <- (-2);
  weights.(6sz) <- SP.inf;
  weights.(7sz) <- SP.inf;
  weights.(8sz) <- SP.inf;

  // --- Allocate dist array (3 entries) ---
  let dv = V.alloc 0 3sz;
  V.to_array_pts_to dv;
  let dist = V.vec_to_array dv;
  rewrite (A.pts_to (V.vec_to_array dv) (Seq.create 3 0))
       as (A.pts_to dist (Seq.create 3 0));

  // --- Allocate result ref ---
  let mut result = false;

  // --- Ghost counter ---
  let ctr = GR.alloc #nat 0;

  // --- Bind ghost sequences ---
  with sw. assert (A.pts_to weights sw);

  // --- Prove weights == tw_seq ---
  seq_after_weight_writes ();
  assert (pure (sw `Seq.equal` tw_seq));

  // --- Prove preconditions ---
  tw_weights_in_range ();

  // --- Call Bellman-Ford ---
  BF.bellman_ford weights 3sz 0sz dist result ctr;

  // --- Read postcondition ---
  with sdist'. assert (A.pts_to dist sdist');
  with no_neg_cycle. assert (R.pts_to result no_neg_cycle);
  with (cf: nat). assert (GR.pts_to ctr cf);

  // --- Read concrete values ---
  let d0 = dist.(0sz);
  let d1 = dist.(1sz);
  let d2 = dist.(2sz);
  let nc = !result;

  // --- Prove no_neg_cycles_flat for our graph ---
  tw_no_neg_cycles ();
  sp_dist_v0 (); sp_dist_v1 (); sp_dist_v2 ();

  // --- Ghost proof: output is uniquely determined ---
  assert (pure (no_neg_cycle == true));
  assert (pure (d0 == 0 /\ d1 == 4 /\ d2 == 2));
  assert (pure (nc == true));

  // --- Computational check (survives extraction to C) ---
  let pass = (d0 = 0 && d1 = 4 && d2 = 2 && nc);

  // --- Cleanup ---
  with sw'. assert (A.pts_to weights sw');
  rewrite (A.pts_to weights sw') as (A.pts_to (V.vec_to_array wv) sw');
  V.to_vec_pts_to wv;
  V.free wv;

  with sd'. assert (A.pts_to dist sd');
  rewrite (A.pts_to dist sd') as (A.pts_to (V.vec_to_array dv) sd');
  V.to_vec_pts_to dv;
  V.free dv;

  GR.free ctr;
  pass
}
```
#pop-options
