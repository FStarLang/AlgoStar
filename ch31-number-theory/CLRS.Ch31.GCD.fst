(*
   Euclid's GCD Algorithm - Verified implementation in Pulse
   
   Implements the classic recursive GCD algorithm iteratively:
   gcd(a, b) = gcd(b, a mod b) with base case gcd(a, 0) = a
   
   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.SizeT

module R = Pulse.Lib.Reference
module SZ = FStar.SizeT

// ========== Pure Specification ==========

// The pure recursive GCD specification
let rec gcd_spec (a b: nat) : Tot nat (decreases b) =
  if b = 0 then a else gcd_spec b (a % b)

// Basic properties of GCD
let rec gcd_spec_comm (a b: nat)
  : Lemma (ensures gcd_spec a b == gcd_spec b a)
          (decreases (a + b))
  = if a = 0 then ()
    else if b = 0 then ()
    else if a >= b then (
      gcd_spec_comm b (a % b);
      assert (gcd_spec a b == gcd_spec b (a % b));
      assert (gcd_spec b a == gcd_spec a (b % a))
    )
    else (
      gcd_spec_comm a (b % a);
      assert (gcd_spec b a == gcd_spec a (b % a));
      assert (gcd_spec a b == gcd_spec b (a % b))
    )

// ========== Pulse Implementation ==========

// Iterative implementation using a while loop
fn gcd_impl (a_init b_init: SZ.t)
  requires pure (SZ.v a_init > 0 \/ SZ.v b_init > 0)
  returns result: SZ.t
  ensures pure (SZ.v result == gcd_spec (SZ.v a_init) (SZ.v b_init))
{
  let mut a: SZ.t = a_init;
  let mut b: SZ.t = b_init;
  
  while (!b >^ 0sz)
  invariant exists* va vb.
    R.pts_to a va **
    R.pts_to b vb **
    pure (
      gcd_spec (SZ.v va) (SZ.v vb) == gcd_spec (SZ.v a_init) (SZ.v b_init) /\
      (SZ.v va > 0 \/ SZ.v vb > 0)
    )
  {
    let va = !a;
    let vb = !b;
    
    // Compute remainder: temp = a % b
    let temp = SZ.rem va vb;
    
    // GCD invariant: gcd(a, b) = gcd(b, a % b)
    // This follows directly from the definition of gcd_spec
    assert pure (gcd_spec (SZ.v va) (SZ.v vb) == gcd_spec (SZ.v vb) (SZ.v temp));
    
    // Update: a := b, b := temp
    a := vb;
    b := temp;
  };
  
  // When loop exits, b = 0, so gcd(a, 0) = a
  let va = !a;
  assert pure (gcd_spec (SZ.v va) 0 == SZ.v va);
  
  va
}
