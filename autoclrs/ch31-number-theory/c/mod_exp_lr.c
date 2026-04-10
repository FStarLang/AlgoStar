/*
 * Left-to-Right Modular Exponentiation — C with c2pulse verification.
 *
 * Proves:
 *   1. The result equals mod_exp_spec(b, e, m) = pow(b, e) % m.
 *   2. The result is in [0, m).
 *   3. Complexity bound: at most num_bits(e) loop iterations.
 *
 * Based on CLRS p. 957, Alg 31.6.
 * Scans bits from MSB to LSB. Maintains d = pow(b, prefix) % m
 * where prefix is the binary prefix of e processed so far.
 *
 * Precondition: m > 0 and m*m fits in size_t (overflow safety).
 *
 * A concrete variable k tracks log2(mask) so the invariant can
 * state mask == pow2(k) without ghost references.
 */

#include "c2pulse.h"
#include <stddef.h>

_include_pulse(
  open CLRS.Ch31.ModExp.Spec
  open CLRS.Ch31.ModExpLR.Lemmas
  open CLRS.Ch31.GCD.Complexity
  open CLRS.Ch31.ModExpLR.Complexity
  open FStar.Mul
  open FStar.Math.Lemmas
)

/* Helper lemmas (from the Pulse reference implementation) */

_include_pulse(
  let lemma_bit_decompose_div (e: nat) (d: pos)
    : Lemma (e / d == 2 * (e / (op_Multiply 2 d)) + (e / d) % 2)
    = lemma_div_mod (e / d) 2;
      division_multiplication_lemma e d 2

  let pow2_half (k: pos)
    : Lemma (pow2 k / 2 == pow2 (k - 1))
    = pow2_double_mult (k - 1)

  let pow2_even (k: pos)
    : Lemma (op_Multiply 2 (pow2 k / 2) == pow2 k)
    = pow2_half k

  let rec lemma_k_le_pow2 (k: nat)
    : Lemma (ensures k + 1 <= pow2 k)
            (decreases k)
    = if k = 0 then ()
      else (lemma_k_le_pow2 (k - 1); pow2_double_mult (k - 1))

  let rec lemma_num_bits_le (n: nat)
    : Lemma (requires n >= 1) (ensures num_bits n <= n) (decreases n)
    = if n <= 1 then () else lemma_num_bits_le (n / 2)

  let rec mask_loop_done (n: pos) (k: nat)
    : Lemma (requires pow2 k <= n /\ pow2 k > n / 2)
            (ensures k == num_bits n - 1)
            (decreases n)
    = if n <= 1 then ()
      else if k = 0 then ()
      else (pow2_double_mult (k - 1); mask_loop_done (n / 2) (k - 1))
)

_include_pulse(
  let mod_exp_lr_step_bmod (b: int) (prefix: nat) (m: pos) (bit: nat{bit <= 1})
    : Lemma (
        let d = pow b prefix % m in
        let d_sq = (d * d) % m in
        let b_mod = b % m in
        let d_new = (if bit = 0 then d_sq else (d_sq * b_mod) % m) in
        d_new == pow b (2 * prefix + bit) % m
      )
    = let d = pow b prefix % m in
      let d_sq = (d * d) % m in
      mod_exp_lr_step b prefix m bit;
      if bit = 1 then (
        lemma_mod_mul_distr_r d_sq b m
      )

  let step_result_lemma (b: int) (e: nat) (mask: pos) (m: pos)
    : Lemma (
        let prefix = e / (op_Multiply 2 mask) in
        let bit = (e / mask) % 2 in
        let d = pow b prefix % m in
        let d_sq = (d * d) % m in
        let b_mod = b % m in
        let d_new = (if bit = 0 then d_sq else (d_sq * b_mod) % m) in
        d_new == pow b (e / mask) % m
      )
    = let prefix = e / (op_Multiply 2 mask) in
      let bit = (e / mask) % 2 in
      mod_exp_lr_step_bmod b prefix m bit;
      lemma_bit_decompose_div e mask
)

size_t mod_exp_lr(size_t b_init, size_t e_init, size_t m)
  _requires((bool) _inline_pulse(
    SizeT.v $(m) > 0
    /\ SizeT.fits (op_Multiply (SizeT.v $(m)) (SizeT.v $(m)))
  ))
  _ensures((bool) _inline_pulse(
    mod_exp_spec (SizeT.v $(b_init)) (SizeT.v $(e_init)) (SizeT.v $(m)) = SizeT.v $(return)
    /\ SizeT.v $(return) >= 0
    /\ SizeT.v $(return) < SizeT.v $(m)
  ))
{
  _ghost_stmt(lemma_prefix_zero (SizeT.v $(e_init)));

  if (e_init == 0) {
    return 1 % m;
  }

  size_t b_mod = b_init % m;

  /* Phase 1: find mask = pow2(k) where pow2(k) <= e_init < 2*pow2(k) */
  size_t mask = 1;
  size_t k = 0;
  while (mask <= e_init / 2)
    _invariant(_live(mask) && _live(k))
    _invariant((bool) _inline_pulse(
      SizeT.v $(mask) >= 1
      /\ SizeT.v $(mask) <= SizeT.v $(e_init)
      /\ SizeT.v $(mask) == pow2 (SizeT.v $(k))
      /\ pow2 (SizeT.v $(k)) <= SizeT.v $(e_init)
    ))
  {
    _ghost_stmt(pow2_double_mult (SizeT.v $(k)));
    _assert((bool) _inline_pulse(SizeT.v $(mask) * 2 <= SizeT.v $(e_init)));
    mask = mask * 2;
    _ghost_stmt(lemma_k_le_pow2 (SizeT.v $(k) + 1));
    k = k + 1;
  }

  /* After Phase 1: mask > e/2, so k == num_bits(e) - 1 */
  _ghost_stmt(mask_loop_done (SizeT.v $(e_init)) (SizeT.v $(k)));

  /* d starts at 1 % m == pow(b, 0) % m */
  size_t d = 1 % m;
  size_t steps = 0;

  /* Phase 2: process bits from MSB to LSB */
  while (mask > 0)
    _invariant(_live(d) && _live(mask) && _live(k) && _live(steps))
    _invariant((bool) _inline_pulse(
      SizeT.v $(d) >= 0 /\ SizeT.v $(d) < SizeT.v $(m)
      /\ SizeT.v $(mask) <= SizeT.v $(e_init)
      /\ (SizeT.v $(mask) > 0 ==>
            SizeT.v $(mask) == pow2 (SizeT.v $(k))
            /\ SizeT.v $(d) == pow (SizeT.v $(b_init)) (SizeT.v $(e_init) / (op_Multiply 2 (SizeT.v $(mask)))) % SizeT.v $(m))
      /\ (SizeT.v $(mask) == 0 ==>
            mod_exp_spec (SizeT.v $(b_init)) (SizeT.v $(e_init)) (SizeT.v $(m)) == SizeT.v $(d))
      /\ (SizeT.v $(mask) > 0 ==>
            SizeT.v $(steps) + SizeT.v $(k) + 1 == num_bits (SizeT.v $(e_init)))
      /\ (SizeT.v $(mask) == 0 ==>
            SizeT.v $(steps) == num_bits (SizeT.v $(e_init)))
    ))
  {
    _ghost_stmt(step_result_lemma (SizeT.v $(b_init)) (SizeT.v $(e_init)) (SizeT.v $(mask)) (SizeT.v $(m)));
    size_t bit = (e_init / mask) % 2;

    _assert((bool) _inline_pulse(
      op_Multiply (SizeT.v $(d)) (SizeT.v $(d))
        <= op_Multiply (SizeT.v $(d)) (SizeT.v $(m))));
    _assert((bool) _inline_pulse(
      op_Multiply (SizeT.v $(d)) (SizeT.v $(m))
        < op_Multiply (SizeT.v $(m)) (SizeT.v $(m))));
    size_t sq = (d * d) % m;

    if (bit == 1) {
      _assert((bool) _inline_pulse(
        op_Multiply (SizeT.v $(sq)) (SizeT.v $(b_mod))
          <= op_Multiply (SizeT.v $(sq)) (SizeT.v $(m))));
      _assert((bool) _inline_pulse(
        op_Multiply (SizeT.v $(sq)) (SizeT.v $(m))
          < op_Multiply (SizeT.v $(m)) (SizeT.v $(m))));
      d = (sq * b_mod) % m;

      _ghost_stmt(lemma_num_bits_le (SizeT.v $(e_init)));
      steps = steps + 1;
      mask = mask / 2;
      if (mask > 0) {
        _ghost_stmt(pow2_half (SizeT.v $(k)));
        _ghost_stmt(pow2_even (SizeT.v $(k)));
        k = k - 1;
      }
    } else {
      d = sq;

      _ghost_stmt(lemma_num_bits_le (SizeT.v $(e_init)));
      steps = steps + 1;
      mask = mask / 2;
      if (mask > 0) {
        _ghost_stmt(pow2_half (SizeT.v $(k)));
        _ghost_stmt(pow2_even (SizeT.v $(k)));
        k = k - 1;
      }
    }
  }

  return d;
}
