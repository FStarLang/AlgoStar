(*
   Bellman-Ford with Complexity Bound

   Proves O(V²·(V-1)) = O(n³) complexity for the Bellman-Ford algorithm.
   Specifically: exactly (n-1)*n*n relaxation operations in the main loop,
   plus n initialization operations — total (n-1)*n² + n.

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each relaxation step (check + potential update) gets one ghost tick.

   Also proves functional correctness (source dist == 0, valid distances).

   NO admits. NO assumes.
*)

module CLRS.Ch24.BellmanFord.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
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

// ========== Definitions (same as BellmanFord.fst) ==========

let valid_distances (dist: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  forall (v: nat). v < n /\ v < Seq.length dist ==>
    (let d = Seq.index dist v in d < 1000000 \/ d == 1000000)

// ========== Main Algorithm with Complexity ==========

fn bellman_ford_complexity
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    pure (
      SZ.v n > 1 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* sdist'.
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      Seq.index sdist' (SZ.v source) == 0 /\
      valid_distances sdist' (SZ.v n)
    )
{
  let ctr = GR.alloc #nat 0;

  // Initialization: dist[source] = 0, all others = 1000000
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
      (forall (j: nat). j < SZ.v vi ==>
        (if j = SZ.v source
         then Seq.index sdist_current j == 0
         else Seq.index sdist_current j == 1000000)) /\
      // Complexity: vc == vi (init operations)
      vc == SZ.v vi
    )
  {
    let vi = !init_i;
    let new_val: int = (if vi = source then 0 else 1000000);
    A.op_Array_Assignment dist vi new_val;
    tick ctr;
    init_i := vi +^ 1sz;
  };

  let _ = !init_i;

  // Relaxation: n-1 rounds
  let mut round: SZ.t = 1sz;

  while (
    let vround = !round;
    vround <^ n
  )
  invariant exists* vround sdist_current (vc : nat).
    R.pts_to round vround **
    A.pts_to dist sdist_current **
    GR.pts_to ctr vc **
    pure (
      SZ.v vround >= 1 /\
      SZ.v vround <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      Seq.index sdist_current (SZ.v source) == 0 /\
      valid_distances sdist_current (SZ.v n) /\
      // Complexity: vc == n + (vround-1)*n*n
      vc == SZ.v n + (SZ.v vround - 1) * SZ.v n * SZ.v n
    )
  {
    let vround = !round;

    let mut u: SZ.t = 0sz;

    while (
      let vu = !u;
      vu <^ n
    )
    invariant exists* vu sdist_u (vc_u : nat).
      R.pts_to u vu **
      A.pts_to dist sdist_u **
      GR.pts_to ctr vc_u **
      pure (
        SZ.v vu <= SZ.v n /\
        Seq.length sdist_u == SZ.v n /\
        Seq.index sdist_u (SZ.v source) == 0 /\
        valid_distances sdist_u (SZ.v n) /\
        // Complexity: vc == n + (vround-1)*n*n + vu*n
        vc_u == SZ.v n + (SZ.v vround - 1) * SZ.v n * SZ.v n + SZ.v vu * SZ.v n
      )
    {
      let vu = !u;
      let dist_u = A.op_Array_Access dist vu;
      assert pure (dist_u < 1000000 \/ dist_u == 1000000);

      let mut v: SZ.t = 0sz;

      while (
        let vv = !v;
        vv <^ n
      )
      invariant exists* vv sdist_v (vc_v : nat).
        R.pts_to v vv **
        A.pts_to dist sdist_v **
        GR.pts_to ctr vc_v **
        pure (
          SZ.v vv <= SZ.v n /\
          Seq.length sdist_v == SZ.v n /\
          Seq.index sdist_v (SZ.v source) == 0 /\
          valid_distances sdist_v (SZ.v n) /\
          // Complexity: vc == n + (vround-1)*n*n + vu*n + vv
          vc_v == SZ.v n + (SZ.v vround - 1) * SZ.v n * SZ.v n + SZ.v vu * SZ.v n + SZ.v vv
        )
      {
        let vv = !v;

        let w_idx = vu *^ n +^ vv;
        let w_uv = A.op_Array_Access weights w_idx;
        let old_dist_v = A.op_Array_Access dist vv;

        assert pure (old_dist_v < 1000000 \/ old_dist_v == 1000000);

        let can_relax = (w_uv < 1000000 && dist_u < 1000000);
        let sum = dist_u + w_uv;
        let should_update = (can_relax && sum < old_dist_v && vv <> source);
        let new_dist_v: int = (if should_update then sum else old_dist_v);

        assert pure (new_dist_v < 1000000 \/ new_dist_v == 1000000);

        if (vv = source) {
          assert pure (old_dist_v == 0);
          assert pure (new_dist_v == 0);
        };

        A.op_Array_Assignment dist vv new_dist_v;

        // Count the relaxation — one ghost tick
        tick ctr;

        v := vv +^ 1sz;
      };

      let _ = !v;
      u := vu +^ 1sz;
    };

    let _ = !u;
    round := vround +^ 1sz;
  };

  let _ = !round;

  // At exit: vc == n + (n-1)*n*n == n + (n-1)·n²
  let final_ctr = GR.op_Bang ctr;
  assert (pure (reveal final_ctr == SZ.v n + (SZ.v n - 1) * SZ.v n * SZ.v n));

  GR.free ctr;
  ()
}
