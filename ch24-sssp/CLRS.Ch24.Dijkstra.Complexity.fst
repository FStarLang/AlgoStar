(*
   Dijkstra's Algorithm with Complexity Bound

   Proves O(V²) complexity for Dijkstra with adjacency-matrix representation.
   Specifically: exactly n initialization operations + n rounds of
   (n find-min comparisons + n relaxation operations) = n + 2·n² total.

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each comparison/relaxation gets one ghost tick.

   Also proves functional correctness (source dist == 0, non-negative, bounded).

   NO admits. NO assumes.
*)

module CLRS.Ch24.Dijkstra.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Vec
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Definitions (same as Dijkstra.fst) ==========

let all_weights_non_negative (sweights: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sweights ==> Seq.index sweights i >= 0

let all_non_negative (sdist: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sdist ==> Seq.index sdist i >= 0

let all_bounded (sdist: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sdist ==>
    Seq.index sdist i >= 0 /\ Seq.index sdist i <= 1000000

// ========== Find min with tick counting ==========

fn find_min_unvisited_complexity
  (dist: A.array int)
  (visited: V.vec int)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#sdist: erased (Seq.seq int))
  (#svisited: erased (Seq.seq int))
  (#vc0: erased nat)
  requires
    A.pts_to dist sdist **
    V.pts_to visited svisited **
    GR.pts_to ctr vc0 **
    pure (
      SZ.v n > 0 /\
      Seq.length sdist == SZ.v n /\
      Seq.length svisited == SZ.v n
    )
  returns min_idx:SZ.t
  ensures
    A.pts_to dist sdist **
    V.pts_to visited svisited **
    GR.pts_to ctr (hide (reveal vc0 + SZ.v n)) **
    pure (SZ.v min_idx < SZ.v n)
{
  let mut min_idx: SZ.t = 0sz;
  let mut min_val: int = 1000000;
  let mut i: SZ.t = 0sz;

  while (
    let vi = !i;
    vi <^ n
  )
  invariant exists* vi vmin_idx vmin_val (vc : nat).
    R.pts_to i vi **
    R.pts_to min_idx vmin_idx **
    R.pts_to min_val vmin_val **
    A.pts_to dist sdist **
    V.pts_to visited svisited **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      SZ.v vmin_idx < SZ.v n /\
      // Complexity: vc == vc0 + vi
      vc == reveal vc0 + SZ.v vi
    )
  {
    let vi = !i;
    let visited_i = V.op_Array_Access visited vi;

    if (visited_i = 0)
    {
      let dist_i = A.op_Array_Access dist vi;
      let curr_min = !min_val;

      if (dist_i < curr_min)
      {
        min_idx := vi;
        min_val := dist_i;
      };
    };

    // Count each vertex scan — one ghost tick
    tick ctr;

    i := vi +^ 1sz;
  };

  let _ = !i;
  let result = !min_idx;
  let _ = !min_val;
  result
}

// ========== Main Algorithm with Complexity ==========

// Complexity bound predicate
let dijkstra_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n + 2 * n * n

fn dijkstra_complexity
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      all_weights_non_negative sweights
    )
  ensures exists* sdist' (cf: nat).
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    GR.pts_to ctr cf **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      Seq.index sdist' (SZ.v source) == 0 /\
      all_non_negative sdist' /\
      all_bounded sdist' /\
      dijkstra_complexity_bounded cf (reveal c0) (SZ.v n)
    )
{
  // Initialization
  let mut init_i: SZ.t = 0sz;

  while (
    let vi = !init_i;
    vi <^ n
  )
  invariant exists* vi sdist_current (vc : nat).
    R.pts_to init_i vi **
    A.pts_to dist sdist_current **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      (SZ.v vi > SZ.v source ==> Seq.index sdist_current (SZ.v source) == 0) /\
      (forall (j:nat). j < SZ.v vi ==>
        Seq.index sdist_current j >= 0 /\ Seq.index sdist_current j <= 1000000) /\
      // Complexity: vc == c0 + vi
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi
    )
  {
    let vi = !init_i;
    let new_val: int = (if vi = source then 0 else 1000000);
    A.op_Array_Assignment dist vi new_val;
    tick ctr;
    init_i := vi +^ 1sz;
  };

  let _ = !init_i;

  let visited = V.alloc 0 n;

  // Main loop: n rounds
  let mut round: SZ.t = 0sz;

  while (
    let vround = !round;
    vround <^ n
  )
  invariant exists* vround sdist_current svisited_current (vc : nat).
    R.pts_to round vround **
    A.pts_to dist sdist_current **
    V.pts_to visited svisited_current **
    GR.pts_to ctr vc **
    pure (
      SZ.v vround <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      Seq.length svisited_current == SZ.v n /\
      Seq.index sdist_current (SZ.v source) == 0 /\
      all_non_negative sdist_current /\
      all_bounded sdist_current /\
      // Complexity: vc == c0 + n + 2*vround*n
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v n + 2 * SZ.v vround * SZ.v n
    )
  {
    let vround = !round;

    // Find minimum distance unvisited vertex — n ticks
    let u = find_min_unvisited_complexity dist visited n ctr;

    // Mark u as visited
    V.op_Array_Assignment visited u 1;

    let dist_u = A.op_Array_Access dist u;

    // Relax all neighbors — n ticks
    let mut v: SZ.t = 0sz;

    while (
      let vv = !v;
      vv <^ n
    )
    invariant exists* vv sdist_v svisited_v (vc_v : nat).
      R.pts_to v vv **
      A.pts_to dist sdist_v **
      V.pts_to visited svisited_v **
      GR.pts_to ctr vc_v **
      pure (
        SZ.v vv <= SZ.v n /\
        Seq.length sdist_v == SZ.v n /\
        Seq.length svisited_v == SZ.v n /\
        Seq.index sdist_v (SZ.v source) == 0 /\
        all_non_negative sdist_v /\
        all_bounded sdist_v /\
        // Complexity: vc == c0 + n + (2*vround+1)*n + vv
        vc_v >= reveal c0 /\
        vc_v - reveal c0 == SZ.v n + 2 * SZ.v vround * SZ.v n + SZ.v n + SZ.v vv
      )
    {
      let vv = !v;

      let w_idx = u *^ n +^ vv;
      let w = A.op_Array_Access weights w_idx;
      let visited_v = V.op_Array_Access visited vv;
      let old_dist = A.op_Array_Access dist vv;

      let can_relax = (visited_v = 0 && w < 1000000 && dist_u < 1000000);
      let sum = dist_u + w;
      let should_update = (can_relax && sum < old_dist);
      let new_dist: int = (if should_update then sum else old_dist);

      A.op_Array_Assignment dist vv new_dist;

      // Count the relaxation — one ghost tick
      tick ctr;

      v := vv +^ 1sz;
    };

    let _ = !v;
    round := vround +^ 1sz;
  };

  let _ = !round;

  // At exit: cf - c0 == n + 2n²
  V.free visited;
  ()
}
