(*
   Left-to-Right Modular Exponentiation — Lemmas Implementation

   Proves bit manipulation and step lemmas for the left-to-right
   modular exponentiation (CLRS p. 957, Alg 31.6).

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExpLR.Lemmas

open FStar.Math.Lemmas
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.ModExp.Lemmas
open CLRS.Ch31.GCD.Complexity

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
  : Lemma (ensures e / pow2 (num_bits e) == 0)
          (decreases e)
  = if e = 0 then ()
    else (
      lemma_prefix_zero (e / 2);
      pow2_double_mult (num_bits (e / 2));
      division_multiplication_lemma e 2 (pow2 (num_bits (e / 2)))
    )

// ((a % m) * (b % m)) % m == (a * b) % m
let lemma_mod_mul_both (a b: int) (m: pos)
  : Lemma (((a % m) * (b % m)) % m == (a * b) % m)
  = lemma_mod_mul_distr_l a (b % m) m;
    lemma_mod_mul_distr_r a b m

// Left-to-right step lemma
#push-options "--z3rlimit 10 --split_queries always"
let mod_exp_lr_step (b: int) (prefix: nat) (m: pos) (bit: nat{bit <= 1})
  : Lemma (
      let d = pow b prefix % m in
      let d_sq = (d * d) % m in
      let d_new = (if bit = 0 then d_sq else (d_sq * b) % m) in
      d_new == pow b (2 * prefix + bit) % m
    )
  = lemma_mod_mul_both (pow b prefix) (pow b prefix) m;
    pow_add b prefix prefix;
    assert (prefix + prefix == 2 * prefix);
    if bit = 1 then (
      lemma_mod_mul_distr_l (pow b (2 * prefix)) b m
    ) else ()
#pop-options
