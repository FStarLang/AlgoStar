(*
   Euclid's GCD Algorithm - Verified implementation in Pulse
   
   Implements the classic recursive GCD algorithm iteratively:
   gcd(a, b) = gcd(b, a mod b) with base case gcd(a, 0) = a
   
   Proves both functional correctness and O(log b) complexity bound.
   Complexity analysis uses a direct mod-halving argument (a % b ≤ a/2),
   capturing the same O(log b) bound as CLRS Theorem 31.11 (Lamé's theorem).

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open FStar.Math.Euclid
open FStar.Math.Lemmas

module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Classical = FStar.Classical

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

//SNIPPET_START: gcd_spec
// The pure recursive GCD specification
let rec gcd_spec (a b: nat) : Tot nat (decreases b) =
  if b = 0 then a else gcd_spec b (a % b)
//SNIPPET_END: gcd_spec

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

// ========== Divisibility Properties ==========

// gcd_spec computes the actual greatest common divisor
let rec gcd_spec_divides (a b: nat)
  : Lemma (ensures divides (gcd_spec a b) a /\ divides (gcd_spec a b) b)
          (decreases b)
  = if b = 0 then (
      divides_reflexive a;
      divides_0 a
    )
    else (
      gcd_spec_divides b (a % b);
      let d = gcd_spec a b in
      let q = a / b in
      let r = a % b in
      euclidean_division_definition a b;
      divides_mult_right q b d;
      divides_plus (op_Multiply q b) r d
    )

// ========== Complexity Analysis: Pure Functions and Lemmas ==========

//SNIPPET_START: gcd_steps
// Count the number of Euclidean steps
let rec gcd_steps (a b: nat) : Tot nat (decreases b) =
  if b = 0 then 0
  else 1 + gcd_steps b (a % b)

// Number of bits needed to represent n (= 1 + floor(log2(n)) for n > 0)
let rec num_bits (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0
  else 1 + num_bits (n / 2)
//SNIPPET_END: gcd_steps

// num_bits is monotone
let rec lemma_num_bits_monotone (a b: nat)
  : Lemma (requires a <= b)
          (ensures num_bits a <= num_bits b)
          (decreases b)
  = if a = 0 then ()
    else if b = 0 then ()
    else lemma_num_bits_monotone (a / 2) (b / 2)

// Halving reduces bits by exactly 1 (for n > 0)
let lemma_num_bits_half (n: nat)
  : Lemma (requires n > 0)
          (ensures num_bits (n / 2) == num_bits n - 1)
  = ()

// Key lemma: a % b ≤ a / 2 when a ≥ b > 0
#push-options "--z3rlimit 20"
let lemma_mod_le_half (a b: nat)
  : Lemma (requires a >= b /\ b > 0)
          (ensures a % b <= a / 2)
  = ()
#pop-options

// Arithmetic helper: if x <= y - 1 then 2x + 3 <= 2y + 1
let lemma_arithmetic_helper (x y: nat)
  : Lemma (requires x <= y - 1 /\ y > 0)
          (ensures (2 + (op_Multiply 2 x) + 1) <= (op_Multiply 2 y + 1))
  = ()

// Transitivity helper: combine IH with arithmetic
let lemma_gcd_steps_bound_step (a b r r2: nat)
  : Lemma (requires b > 0 /\ r2 < b /\
                    gcd_steps a b == 2 + gcd_steps r r2 /\
                    gcd_steps r r2 <= op_Multiply 2 (num_bits r2) + 1 /\
                    num_bits r2 <= num_bits b - 1)
          (ensures gcd_steps a b <= op_Multiply 2 (num_bits b) + 1)
  = lemma_arithmetic_helper (num_bits r2) (num_bits b)

//SNIPPET_START: lemma_gcd_steps_log
// Main theorem: Euclid's algorithm takes at most 2*log2(b) + 1 steps (Lamé's theorem)
#push-options "--z3rlimit 150 --fuel 3 --ifuel 2"
let rec lemma_gcd_steps_log (a b: nat)
  : Lemma (requires b > 0)
          (ensures gcd_steps a b <= op_Multiply 2 (num_bits b) + 1)
          (decreases b)
//SNIPPET_END: lemma_gcd_steps_log
  = let r = a % b in
    if r = 0 then ()
    else (
      let r2 = b % r in
      if r2 = 0 then ()
      else (
        lemma_mod_le_half b r;
        lemma_num_bits_monotone r2 (b / 2);
        lemma_num_bits_half b;
        lemma_gcd_steps_log r r2;
        lemma_gcd_steps_bound_step a b r r2
      )
    )
#pop-options

//SNIPPET_START: gcd_complexity_bounded
// Complexity bound predicate
let gcd_complexity_bounded (cf c0: nat) (a_init b_init: nat) : prop =
  cf >= c0 /\
  cf - c0 == gcd_steps a_init b_init /\
  (b_init > 0 ==> cf - c0 <= op_Multiply 2 (num_bits b_init) + 1)
//SNIPPET_END: gcd_complexity_bounded

// O(log min(a,b)) bound: combines the O(log b) bound with commutativity
let gcd_steps_log_min (a b: nat)
  : Lemma (requires a > 0 /\ b > 0)
          (ensures gcd_steps a b <= op_Multiply 2 (num_bits (if a <= b then a else b)) + 2)
  = if a >= b then
      lemma_gcd_steps_log a b
    else (
      FStar.Math.Lemmas.small_mod a b;
      lemma_gcd_steps_log b a
    )

// ========== Pulse Implementation ==========

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
