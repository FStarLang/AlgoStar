/// Minimal repro: calling Seq.index-based lemma after Pulse while loop
module ISSUE_05_ghost_erased_lemma_call
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open Pulse.Lib.Reference
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

let simple_lemma (s1 s2: Seq.seq SZ.t) (n: nat)
  : Lemma
    (requires Seq.length s1 == n /\ Seq.length s2 == n /\
              (forall (v:nat). v < n ==> Seq.index s1 v == Seq.index s2 v))
    (ensures Seq.equal s1 s2)
  = ()

#push-options "--z3rlimit 200"
fn test
  (arr: array SZ.t) (#s_orig: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  requires A.pts_to arr s_orig ** pure (SZ.v n > 0 /\ Seq.length s_orig == SZ.v n)
  returns _r: unit
  ensures A.pts_to arr s_orig ** pure (Seq.length s_orig == SZ.v n)
{
  let mut i: SZ.t = 0sz;
  while (let vi = !i; vi <^ n)
  invariant exists* vi s_cur.
    R.pts_to i vi ** A.pts_to arr s_cur **
    pure (SZ.v vi <= SZ.v n /\ Seq.length s_cur == SZ.v n /\
          Seq.length s_orig == SZ.v n /\
          (forall (v:nat). v < SZ.v n ==> Seq.index s_orig v == Seq.index s_cur v))
  decreases (SZ.v n - SZ.v !i)
  { let vi = !i; let _ = A.op_Array_Access arr vi; i := vi +^ 1sz };
  with s_final. assert (A.pts_to arr s_final);
  simple_lemma s_orig s_final (SZ.v n);
  rewrite (A.pts_to arr s_final) as (A.pts_to arr s_orig)
}
#pop-options
