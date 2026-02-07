(*
   GCD with Complexity Bound

   Proves that Euclid's algorithm performs at most b_init iterations
   (divisions), establishing an O(b) bound on the number of mod operations.

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each mod operation in the loop body gets one ghost tick.

   The key insight: a % b < b for b > 0, so b strictly decreases each
   iteration. The invariant tracks vc + vb <= b_init as a decreasing measure.

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.SizeT

module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Pure Specification ==========

let rec gcd_spec (a b: nat) : Tot nat (decreases b) =
  if b = 0 then a else gcd_spec b (a % b)

// ========== Pulse Implementation with Complexity ==========

#set-options "--z3rlimit 10"

fn gcd_complexity (a_init b_init: SZ.t)
  requires pure (SZ.v a_init > 0 \/ SZ.v b_init > 0)
  returns result: SZ.t
  ensures pure (SZ.v result == gcd_spec (SZ.v a_init) (SZ.v b_init))
{
  let mut a: SZ.t = a_init;
  let mut b: SZ.t = b_init;
  let ctr = GR.alloc #nat 0;
  
  while (!b >^ 0sz)
  invariant exists* va vb (vc : nat).
    R.pts_to a va **
    R.pts_to b vb **
    GR.pts_to ctr vc **
    pure (
      gcd_spec (SZ.v va) (SZ.v vb) == gcd_spec (SZ.v a_init) (SZ.v b_init) /\
      (SZ.v va > 0 \/ SZ.v vb > 0) /\
      // Complexity: vc + remaining steps (bounded by vb) <= b_init
      vc + SZ.v vb <= SZ.v b_init
    )
  {
    let va = !a;
    let vb = !b;
    
    let temp = SZ.rem va vb;
    
    assert pure (gcd_spec (SZ.v va) (SZ.v vb) == gcd_spec (SZ.v vb) (SZ.v temp));
    
    a := vb;
    b := temp;
    
    // Count the division — one ghost tick
    tick ctr;
  };
  
  let va = !a;
  assert pure (gcd_spec (SZ.v va) 0 == SZ.v va);
  
  // Complexity assertion
  let final_ctr = GR.op_Bang ctr;
  assert (pure (reveal final_ctr <= SZ.v b_init));
  
  GR.free ctr;
  va
}
