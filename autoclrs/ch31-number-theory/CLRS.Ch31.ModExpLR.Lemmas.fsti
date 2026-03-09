(*
   Left-to-Right Modular Exponentiation — Lemmas Interface

   Signatures for bit manipulation and step lemmas used in the
   left-to-right modular exponentiation (CLRS p. 957, Alg 31.6).

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExpLR.Lemmas

open FStar.Mul
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.GCD.Complexity

// e / pow2(i+1) = (e / pow2 i) / 2
val lemma_div_pow2_succ (e: nat) (i: nat)
  : Lemma (e / pow2 (i + 1) == (e / pow2 i) / 2)

// Bit decomposition: e / pow2 i = 2 * (e / pow2(i+1)) + (e / pow2 i) % 2
val lemma_bit_decompose (e: nat) (i: nat)
  : Lemma (e / pow2 i == 2 * (e / pow2 (i + 1)) + (e / pow2 i) % 2)

// e / pow2(num_bits e) == 0
val lemma_prefix_zero (e: nat)
  : Lemma (ensures e / pow2 (num_bits e) == 0)

// ((a % m) * (b % m)) % m == (a * b) % m
val lemma_mod_mul_both (a b: int) (m: pos)
  : Lemma (((a % m) * (b % m)) % m == (a * b) % m)

// Left-to-right step: after squaring and optionally multiplying by b
val mod_exp_lr_step (b: int) (prefix: nat) (m: pos) (bit: nat{bit <= 1})
  : Lemma (
      let d = pow b prefix % m in
      let d_sq = (d * d) % m in
      let d_new = (if bit = 0 then d_sq else (d_sq * b) % m) in
      d_new == pow b (2 * prefix + bit) % m
    )
