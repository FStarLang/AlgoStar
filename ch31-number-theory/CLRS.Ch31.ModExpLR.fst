(*
   Left-to-Right Modular Exponentiation - Verified implementation in Pulse

   Implements the primary MODULAR-EXPONENTIATION from CLRS p. 957,
   scanning bits from MSB to LSB (left-to-right).

   The algorithm maintains d = a^c mod n where c is the prefix of the binary
   representation of b processed so far. At each step, we square d (doubling c)
   and optionally multiply by a (incrementing c by 1 if the current bit is 1).

   Functional correctness: result == mod_exp_spec b e m == pow b e % m
   Complexity bound: at most num_bits(e) squarings.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExpLR
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.Mul
open FStar.Math.Lemmas
open CLRS.Ch31.ModExp

module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference

// ========== Bit manipulation lemmas ==========

// e / pow2(i+1) = (e / pow2 i) / 2
let lemma_div_pow2_succ (e: nat) (i: nat)
  : Lemma (e / pow2 (i + 1) == (e / pow2 i) / 2)
  = pow2_double_mult i;
    division_multiplication_lemma e (pow2 i) 2

// Bit decomposition: e / pow2 i = 2 * (e / pow2(i+1)) + (e / pow2 i) % 2
let lemma_bit_decompose (e: nat) (i: nat)
  : Lemma (e / pow2 i == 2 * (e / pow2 (i + 1)) + (e / pow2 i) % 2)
  = lemma_div_pow2_succ e i;
    lemma_div_mod (e / pow2 i) 2

// e / pow2(num_bits e) == 0
let rec lemma_prefix_zero (e: nat)
  : Lemma (ensures e / pow2 (CLRS.Ch31.GCD.num_bits e) == 0)
          (decreases e)
  = if e = 0 then ()
    else (
      lemma_prefix_zero (e / 2);
      pow2_double_mult (CLRS.Ch31.GCD.num_bits (e / 2));
      division_multiplication_lemma e 2 (pow2 (CLRS.Ch31.GCD.num_bits (e / 2)))
    )

// ========== Modular arithmetic helper ==========

// ((a % m) * (b % m)) % m == (a * b) % m
let lemma_mod_mul_both (a b: int) (m: pos)
  : Lemma (((a % m) * (b % m)) % m == (a * b) % m)
  = lemma_mod_mul_distr_l a (b % m) m;
    lemma_mod_mul_distr_r a b m

// ========== Left-to-right step lemma ==========

// After squaring d and optionally multiplying by b, the result is
// pow b (2 * prefix + bit) % m, where bit is 0 or 1.
#push-options "--z3rlimit 20"
let mod_exp_lr_step (b: int) (prefix: nat) (m: pos) (bit: nat{bit <= 1})
  : Lemma (
      let d = pow b prefix % m in
      let d_sq = (d * d) % m in
      let d_new = (if bit = 0 then d_sq else (d_sq * b) % m) in
      d_new == pow b (2 * prefix + bit) % m
    )
  = // Square step: (d * d) % m == pow b (2 * prefix) % m
    lemma_mod_mul_both (pow b prefix) (pow b prefix) m;
    pow_add b prefix prefix;
    assert (prefix + prefix == 2 * prefix);
    if bit = 1 then (
      // Multiply step: (d_sq * b) % m == pow b (2 * prefix + 1) % m
      lemma_mod_mul_distr_l (pow b (2 * prefix)) b m
    ) else ()
#pop-options

// ========== Complexity bound predicate ==========

let modexp_lr_complexity_bounded (cf c0: nat) (e_init: nat) : prop =
  cf >= c0 /\ cf - c0 <= CLRS.Ch31.GCD.num_bits e_init

// ========== Pulse Implementation ==========

#push-options "--z3rlimit 30"
fn mod_exp_lr_impl (b_init: int) (e_init: nat) (m_init: pos)
  (ctr: GR.ref nat) (#c0: erased nat)
  requires GR.pts_to ctr c0
  returns result: int
  ensures exists* (cf: nat). GR.pts_to ctr cf ** pure (
    result == mod_exp_spec b_init e_init m_init /\
    modexp_lr_complexity_bounded cf (reveal c0) e_init
  )
{
  lemma_prefix_zero e_init;

  let mut d : int = 1 % m_init;
  let mut i : int = CLRS.Ch31.GCD.num_bits e_init - 1;

  while (
    let vi = !i;
    vi >= 0
  )
  invariant exists* (vd: int) (vi_val: int) (vc: nat).
    R.pts_to d vd **
    R.pts_to i vi_val **
    GR.pts_to ctr vc **
    pure (
      vi_val >= -1 /\
      vi_val + 1 <= CLRS.Ch31.GCD.num_bits e_init /\
      vd >= 0 /\ vd < m_init /\
      vd == pow b_init (e_init / pow2 (vi_val + 1)) % m_init /\
      vc >= reveal c0 /\
      vc - reveal c0 + (vi_val + 1) == CLRS.Ch31.GCD.num_bits e_init
    )
  decreases (!i + 1)
  {
    let vi = !i;
    let vd = !d;

    // Key lemmas for the step
    lemma_bit_decompose e_init vi;
    mod_exp_lr_step b_init (e_init / pow2 (vi + 1)) m_init ((e_init / pow2 vi) % 2);

    // Square d, then conditionally multiply by b_init
    if ((e_init / pow2 vi) % 2 = 1) {
      d := ((vd * vd) % m_init * b_init) % m_init;
    } else {
      d := (vd * vd) % m_init;
    };

    tick ctr;
    i := vi - 1;
  };

  !d
}
#pop-options
