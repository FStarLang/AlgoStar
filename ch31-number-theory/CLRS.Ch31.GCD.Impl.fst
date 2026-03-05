(*
   GCD Pulse Implementation

   Implements the classic recursive GCD algorithm iteratively:
   gcd(a, b) = gcd(b, a mod b) with base case gcd(a, 0) = a

   Proves both functional correctness and O(log b) complexity bound.

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open FStar.Math.Lemmas
open CLRS.Ch31.GCD.Spec
open CLRS.Ch31.GCD.Complexity
open CLRS.Common.Complexity

module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Classical = FStar.Classical

#set-options "--z3rlimit 10"

//SNIPPET_START: gcd_impl_sig
fn gcd_impl (a_init b_init: SZ.t)
  (ctr: GR.ref nat) (#c0: erased nat)
  requires GR.pts_to ctr c0 ** pure (SZ.v a_init > 0 \/ SZ.v b_init > 0)
  returns result: SZ.t
  ensures exists* (cf: nat). GR.pts_to ctr cf ** pure (
    SZ.v result == gcd_spec (SZ.v a_init) (SZ.v b_init) /\
    cf >= reveal c0 /\
    cf - reveal c0 == gcd_steps (SZ.v a_init) (SZ.v b_init) /\
    (SZ.v b_init > 0 ==> cf - reveal c0 <= op_Multiply 2 (num_bits (SZ.v b_init)) + 1)
  )
//SNIPPET_END: gcd_impl_sig
{
  let mut a: SZ.t = a_init;
  let mut b: SZ.t = b_init;
  
//SNIPPET_START: gcd_loop
  while (!b >^ 0sz)
  invariant exists* va vb (vc : nat).
    R.pts_to a va **
    R.pts_to b vb **
    GR.pts_to ctr vc **
    pure (
      gcd_spec (SZ.v va) (SZ.v vb) == gcd_spec (SZ.v a_init) (SZ.v b_init) /\
      (SZ.v va > 0 \/ SZ.v vb > 0) /\
      vc - reveal c0 + gcd_steps (SZ.v va) (SZ.v vb) == gcd_steps (SZ.v a_init) (SZ.v b_init) /\
      vc >= reveal c0
    )
  decreases (SZ.v !b)
  {
    let va = !a;
    let vb = !b;
    
    let temp = SZ.rem va vb;
    
    assert pure (gcd_spec (SZ.v va) (SZ.v vb) == gcd_spec (SZ.v vb) (SZ.v temp));
    assert pure (gcd_steps (SZ.v va) (SZ.v vb) == 1 + gcd_steps (SZ.v vb) (SZ.v temp));
    
    a := vb;
    b := temp;
    tick ctr;
  };
//SNIPPET_END: gcd_loop
  
  let va = !a;
  assert pure (gcd_spec (SZ.v va) 0 == SZ.v va);
  assert pure (gcd_steps (SZ.v va) 0 == 0);
  
  Classical.move_requires (lemma_gcd_steps_log (SZ.v a_init)) (SZ.v b_init);
  
  va
}
