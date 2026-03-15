module CLRS.Ch25.FloydWarshall.NegCycleDetect

(**
 * Negative-cycle detection for Floyd-Warshall (CLRS §25.2).
 *
 * Provides:
 * 1. check_no_negative_cycle: runtime diagonal check after FW computation
 * 2. floyd_warshall_safe: wrapper with weights_bounded + non_negative_diagonal
 *    in the precondition, closing the specification gap
 *
 * NO admits. NO assumes.
 *)

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open CLRS.Ch25.FloydWarshall.Spec
open CLRS.Ch25.FloydWarshall.Impl

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Negative-cycle detection ==========

//SNIPPET_START: check_no_negative_cycle
fn check_no_negative_cycle
  (dist: array int)
  (#contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires
    A.pts_to dist contents **
    pure (
      Seq.length contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns b:bool
  ensures
    A.pts_to dist contents **
    pure (b == true ==> non_negative_diagonal contents (SZ.v n))
{
  let mut v : SZ.t = 0sz;
  let mut ok : bool = true;

  while (!v <^ n)
  invariant exists* vv vok.
    R.pts_to v vv **
    R.pts_to ok vok **
    A.pts_to dist contents **
    pure (
      SZ.v vv <= SZ.v n /\
      Seq.length contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      (vok == true ==>
        (forall (v': nat). v' < SZ.v vv ==>
          Seq.index contents (v' * SZ.v n + v') >= 0))
    )
  {
    let vv = !v;
    let idx = vv *^ n +^ vv;
    let d_vv = A.op_Array_Access dist idx;
    if (d_vv < 0) {
      ok := false
    };
    v := vv +^ 1sz;
  };

  !ok
}
//SNIPPET_END: check_no_negative_cycle

// ========== Safe wrapper with full precondition ==========

//SNIPPET_START: floyd_warshall_safe
fn floyd_warshall_safe
  (dist: array int)
  (#contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to dist contents **
    GR.pts_to ctr c0 **
    pure (
      Seq.length contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      weights_bounded contents (SZ.v n) /\
      non_negative_diagonal contents (SZ.v n)
    )
  returns _:unit
  ensures exists* contents' (cf: nat).
    A.pts_to dist contents' **
    GR.pts_to ctr cf **
    pure (
      Seq.length contents' == SZ.v n * SZ.v n /\
      contents' == fw_outer contents (SZ.v n) 0 /\
      fw_complexity_bounded cf (reveal c0) (SZ.v n)
    )
{
  floyd_warshall dist n ctr
}
//SNIPPET_END: floyd_warshall_safe
