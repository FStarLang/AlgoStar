module WithPureCallTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.WithPure
open FStar.SizeT
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* Function using with_pure in requires, Seq.index in ensures *)
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn set_and_report
  (arr: A.array int) (idx: SZ.t) (value: int) (n: SZ.t)
  (#s: erased (Seq.seq int))
  requires
    A.pts_to arr s **
    with_pure (SZ.v idx < SZ.v n /\ Seq.length s == SZ.v n)
  ensures exists* s'.
    A.pts_to arr s' **
    pure (
      Seq.length s' == SZ.v n /\
      Seq.index s' (SZ.v idx) == value /\
      (forall (j:nat). j < SZ.v n /\ j <> SZ.v idx ==> Seq.index s' j == Seq.index s j)
    )
{
  A.op_Array_Assignment arr idx value
}
#pop-options

(* Test: while loop with quantified invariant that chains through postconditions *)
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn caller (arr: A.array int) (n: SZ.t)
  (#s0: erased (Seq.seq int))
  requires A.pts_to arr s0 ** pure (SZ.v n > 0 /\ Seq.length s0 == SZ.v n)
  ensures exists* s'.
    A.pts_to arr s' **
    pure (
      Seq.length s' == SZ.v n /\
      (forall (j:nat). j < SZ.v n ==> Seq.index s' j == 42)
    )
{
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi si.
    R.pts_to i vi **
    A.pts_to arr si **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length si == SZ.v n /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index si j == 42)
    )
  {
    let vi = !i;
    // Call set_and_report; use its preservation postcondition
    // to re-establish the quantified invariant
    set_and_report arr vi 42 n;
    i := SZ.add vi 1sz
  }
}
#pop-options
