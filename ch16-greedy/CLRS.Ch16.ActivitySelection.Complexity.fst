(*
   Activity Selection with Complexity Bound

   Proves O(n) comparison complexity for the greedy activity selection algorithm.
   Specifically: exactly (n - 1) iterations, one comparison per candidate activity.

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each comparison (start >= last_finish) gets one ghost tick.

   Also proves functional correctness (greedy selection properties).

   NO admits. NO assumes.
*)

module CLRS.Ch16.ActivitySelection.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

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

// ========== Definitions (same as ActivitySelection.fst) ==========

let finish_sorted (f: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\ j < Seq.length f ==> Seq.index f i <= Seq.index f j

let valid_activity (s f: Seq.seq int) (i: nat) : prop =
  i < Seq.length s /\ i < Seq.length f /\ Seq.index s i <= Seq.index f i

let compatibility_maintained (s f: Seq.seq int) (last_finish: int) (processed: nat) : prop =
  processed <= Seq.length s /\
  processed <= Seq.length f /\
  Seq.length f > 0 /\
  last_finish >= Seq.index f 0 /\
  (exists (k:nat). k < processed /\ Seq.index f k == last_finish) /\
  (forall (k:nat). k >= processed /\ k < Seq.length f ==> last_finish <= Seq.index f k)

// ========== Complexity bound predicate ==========

let complexity_bounded_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1

// ========== Activity Selection with Complexity ==========

fn activity_selection_complexity
  (#p: perm)
  (start_times finish_times: A.array int)
  (n: SZ.t)
  (#ss #sf: Ghost.erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to start_times #p ss ** A.pts_to finish_times #p sf **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length ss /\
      SZ.v n == Seq.length sf /\
      SZ.v n == A.length start_times /\
      SZ.v n == A.length finish_times /\
      SZ.v n > 0 /\
      finish_sorted sf /\
      (forall (i:nat). i < Seq.length ss ==> valid_activity ss sf i)
    )
  returns count: SZ.t
  ensures exists* (cf: nat).
    A.pts_to start_times #p ss **
    A.pts_to finish_times #p sf **
    GR.pts_to ctr cf **
    pure (
      SZ.v count >= 1 /\
      SZ.v count <= SZ.v n /\
      (exists (last_finish:int).
         compatibility_maintained ss sf last_finish (SZ.v n)) /\
      complexity_bounded_linear cf (reveal c0) (SZ.v n)
    )
{
  let mut count: SZ.t = 1sz;
  let first_finish = finish_times.(0sz);
  let mut last_finish: int = first_finish;
  let mut i: SZ.t = 1sz;

  while (!i <^ n)
  invariant exists* vi vcount vlast_finish (vc : nat).
    R.pts_to i vi **
    R.pts_to count vcount **
    R.pts_to last_finish vlast_finish **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi > 0 /\
      SZ.v vi <= SZ.v n /\
      SZ.v vcount >= 1 /\
      SZ.v vcount <= SZ.v vi /\
      compatibility_maintained ss sf vlast_finish (SZ.v vi) /\
      // Complexity: exactly (i - 1) comparisons so far
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi - 1
    )
  {
    let vi = !i;
    let curr_start = start_times.(vi);
    let curr_finish = finish_times.(vi);
    let vlast_finish = !last_finish;

    assert pure (finish_sorted sf);
    assert pure (exists (k:nat). k < SZ.v vi /\ Seq.index sf k == vlast_finish);
    assert pure (Seq.index sf (SZ.v vi) == curr_finish);
    assert pure (vlast_finish <= curr_finish);

    // Count the comparison — one ghost tick
    tick ctr;

    if (curr_start >= vlast_finish) {
      assert pure (curr_start >= vlast_finish);
      count := !count + 1sz;
      last_finish := curr_finish;
      assert pure (Seq.index sf (SZ.v vi) == curr_finish);
    };

    i := vi + 1sz;
  };

  !count
}
