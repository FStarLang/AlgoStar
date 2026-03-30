(*
   Extended Euclidean Algorithm — Pulse Implementation

   Iterative loop computing d = gcd(a, b) with machine-width SZ.t,
   reusing the same Euclidean loop structure as GCD.Impl.

   The Bézout coefficients x, y are proven to exist via the
   extended_gcd_correctness lemma — they are ghost values that don't
   need to appear in the extracted C code, since d is the concrete
   output.

   Postcondition: d = gcd(a, b), a*x + b*y = d, d | a, d | b.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ExtendedGCD.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open FStar.Math.Euclid
open FStar.Math.Lemmas
open CLRS.Ch31.GCD.Spec
open CLRS.Ch31.GCD.Complexity
open CLRS.Ch31.ExtendedGCD.Spec
open CLRS.Ch31.ExtendedGCD.Lemmas
open CLRS.Common.Complexity

module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Classical = FStar.Classical

//SNIPPET_START: extended_gcd_impl_sig
fn extended_gcd_impl (a_init b_init: SZ.t)
  (ctr: GR.ref nat) (#c0: erased nat)
  requires GR.pts_to ctr c0 ** pure (SZ.v a_init > 0 \/ SZ.v b_init > 0)
  returns result: SZ.t
  ensures exists* (cf: nat). GR.pts_to ctr cf ** pure (
    let (| d, x, y |) = extended_gcd (SZ.v a_init) (SZ.v b_init) in
    SZ.v result == d /\
    SZ.v result > 0 /\
    SZ.v a_init * x + SZ.v b_init * y == SZ.v result /\
    divides (SZ.v result) (SZ.v a_init) /\
    divides (SZ.v result) (SZ.v b_init) /\
    cf >= reveal c0 /\
    cf - reveal c0 == gcd_steps (SZ.v a_init) (SZ.v b_init)
  )
//SNIPPET_END: extended_gcd_impl_sig
{
  let mut a: SZ.t = a_init;
  let mut b: SZ.t = b_init;

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

  let va = !a;
  assert pure (gcd_spec (SZ.v va) 0 == SZ.v va);
  assert pure (gcd_steps (SZ.v va) 0 == 0);

  // Enrich postcondition: connect gcd_spec to extended_gcd
  extended_gcd_computes_gcd (SZ.v a_init) (SZ.v b_init);
  bezout_identity (SZ.v a_init) (SZ.v b_init);
  extended_gcd_divides_both (SZ.v a_init) (SZ.v b_init);
  gcd_spec_divides (SZ.v a_init) (SZ.v b_init);

  va
}
