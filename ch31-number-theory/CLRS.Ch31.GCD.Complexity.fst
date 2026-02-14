(*
   GCD with Complexity Bound - O(log b) bound using Lamé's Theorem

   Proves that Euclid's algorithm performs at most O(log b) iterations
   (divisions), establishing a logarithmic bound on the number of mod operations.

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each mod operation in the loop body gets one ghost tick.

   The key insight (Lamé's theorem, CLRS Theorem 31.11): After every TWO
   iterations, b decreases by at least half. Specifically, a % b ≤ a/2 when
   a ≥ b, so after two steps (a,b) → (b, a%b) → (a%b, b%(a%b)), the new
   b-value is at most half the original a-value.

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

let rec gcd_spec (a b: nat) : Tot nat (decreases b) =
  if b = 0 then a else gcd_spec b (a % b)

// ========== Complexity Analysis: Pure Functions and Lemmas ==========

// Count the number of Euclidean steps
let rec gcd_steps (a b: nat) : Tot nat (decreases b) =
  if b = 0 then 0
  else 1 + gcd_steps b (a % b)

// Number of bits needed to represent n (= 1 + floor(log2(n)) for n > 0)
let rec num_bits (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0
  else 1 + num_bits (n / 2)

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
// Proof: if b ≤ a/2, then a%b < b ≤ a/2
//        if b > a/2, then a/b = 1, so a%b = a - b < a - a/2 = a/2
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
  = lemma_arithmetic_helper (num_bits r2) (num_bits b);
    // gcd_steps a b = 2 + gcd_steps r r2
    //               <= 2 + (2 * num_bits r2 + 1)
    //               =  3 + 2 * num_bits r2
    // By arithmetic helper: 2 + 2 * num_bits r2 + 1 <= 2 * num_bits b + 1
    // Therefore: gcd_steps a b <= 2 * num_bits b + 1
    ()

// Main theorem: Euclid's algorithm takes at most 2*log2(b) + 1 steps
// Proof: By induction using two-step analysis. After two steps, b reduces
// by at least half (using lemma_mod_le_half).
#push-options "--z3rlimit 150 --fuel 3 --ifuel 2"
let rec lemma_gcd_steps_log (a b: nat)
  : Lemma (requires b > 0)
          (ensures gcd_steps a b <= op_Multiply 2 (num_bits b) + 1)
          (decreases b)
  = let r = a % b in
    if r = 0 then (
      // Base case: gcd_steps a b = 1 + gcd_steps b 0 = 1 + 0 = 1
      // Need: 1 <= 2 * num_bits b + 1, trivially true
      ()
    ) else (
      // After step 1: (a, b) → (b, r) where r = a % b < b
      // Consider step 2: (b, r) → (r, r2) where r2 = b % r
      let r2 = b % r in
      if r2 = 0 then (
        // Two steps: gcd_steps a b = 1 + gcd_steps b r = 1 + 1 = 2
        // Need: 2 <= 2 * num_bits b + 1, trivially true
        ()
      ) else (
        // Key: r2 = b % r ≤ b / 2 (by lemma_mod_le_half since b ≥ r)
        lemma_mod_le_half b r;
        
        // Therefore: num_bits(r2) ≤ num_bits(b / 2) = num_bits(b) - 1
        lemma_num_bits_monotone r2 (b / 2);
        lemma_num_bits_half b;
        
        // By IH on (r, r2) where r2 < b:
        lemma_gcd_steps_log r r2;
        
        // Check preconditions for bound step lemma
        // 1. b > 0: already in context
        // 2. r2 < b: follows from r2 = b % r < r < b
        // 3. gcd_steps a b == 2 + gcd_steps r r2: by definition
        // 4. gcd_steps r r2 <= 2 * num_bits r2 + 1: from IH
        // 5. num_bits r2 <= num_bits b - 1: proved above
        
        // Apply bound step lemma
        lemma_gcd_steps_bound_step a b r r2;
        ()
      )
    )
#pop-options

// ========== Complexity bound predicate ==========
let gcd_complexity_bounded (cf c0: nat) (a_init b_init: nat) : prop =
  cf >= c0 /\
  cf - c0 == gcd_steps a_init b_init /\
  (b_init > 0 ==> cf - c0 <= op_Multiply 2 (num_bits b_init) + 1)

// ========== Pulse Implementation with Complexity ==========

#set-options "--z3rlimit 10"

fn gcd_complexity (a_init b_init: SZ.t)
  (ctr: GR.ref nat) (#c0: erased nat)
  requires GR.pts_to ctr c0 ** pure (SZ.v a_init > 0 \/ SZ.v b_init > 0)
  returns result: SZ.t
  ensures exists* (cf: nat). GR.pts_to ctr cf ** pure (
    SZ.v result == gcd_spec (SZ.v a_init) (SZ.v b_init) /\
    cf >= reveal c0 /\
    cf - reveal c0 == gcd_steps (SZ.v a_init) (SZ.v b_init) /\
    (SZ.v b_init > 0 ==> cf - reveal c0 <= op_Multiply 2 (num_bits (SZ.v b_init)) + 1)
  )
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
      // Track number of steps taken + steps remaining = total steps
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
  
  let va = !a;
  assert pure (gcd_spec (SZ.v va) 0 == SZ.v va);
  assert pure (gcd_steps (SZ.v va) 0 == 0);
  
  // Apply logarithmic bound theorem
  Classical.move_requires (lemma_gcd_steps_log (SZ.v a_init)) (SZ.v b_init);
  
  va
}
