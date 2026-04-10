/*
 * Extended GCD — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. The result d equals gcd(a, b) via extended_gcd.
 *   2. d is positive (> 0).
 *   3. Bézout's identity: a*x + b*y = d for the extended_gcd coefficients.
 *   4. d divides both a and b.
 *   5. O(log b) complexity bound: gcd_steps(a,b) <= 2*num_bits(b)+1.
 *
 * Based on CLRS p. 937, Alg 31.3 (Extended Euclidean Algorithm).
 * Uses recursive form matching the mathematical specification.
 * The Bézout coefficients x, y are ghost values — only d is returned.
 */

#include "c2pulse.h"
#include <stddef.h>

_include_pulse(
  open CLRS.Ch31.GCD.Spec
  open CLRS.Ch31.GCD.Complexity
  open CLRS.Ch31.ExtendedGCD.Spec
  open CLRS.Ch31.ExtendedGCD.Lemmas
  open FStar.Math.Euclid
  open FStar.Mul

  let egcd_d (a b: nat) : nat =
    match extended_gcd a b with (| d, _, _ |) -> d
  let egcd_x (a b: nat) : int =
    match extended_gcd a b with (| _, x, _ |) -> x
  let egcd_y (a b: nat) : int =
    match extended_gcd a b with (| _, _, y |) -> y
)

_rec size_t extended_gcd_impl(size_t a, size_t b)
  _requires((bool) _inline_pulse(SizeT.v $(a) > 0 \/ SizeT.v $(b) > 0))
  _ensures((bool) _inline_pulse(
    SizeT.v $(return) = egcd_d (SizeT.v $(a)) (SizeT.v $(b))
    /\ SizeT.v $(return) > 0
    /\ op_Multiply (SizeT.v $(a)) (egcd_x (SizeT.v $(a)) (SizeT.v $(b)))
       + op_Multiply (SizeT.v $(b)) (egcd_y (SizeT.v $(a)) (SizeT.v $(b)))
       = SizeT.v $(return)
    /\ divides (SizeT.v $(return)) (SizeT.v $(a))
    /\ divides (SizeT.v $(return)) (SizeT.v $(b))
    /\ (SizeT.v $(b) > 0 ==> gcd_steps (SizeT.v $(a)) (SizeT.v $(b)) <= op_Multiply 2 (num_bits (SizeT.v $(b))) + 1)
  ))
  _decreases((_specint) b)
{
  if (b == 0) {
    _ghost_stmt(extended_gcd_computes_gcd (SizeT.v $(a)) (SizeT.v $(b)));
    _ghost_stmt(bezout_identity (SizeT.v $(a)) (SizeT.v $(b)));
    _ghost_stmt(extended_gcd_divides_both (SizeT.v $(a)) (SizeT.v $(b)));
    return a;
  }
  _ghost_stmt(lemma_gcd_steps_log (SizeT.v $(a)) (SizeT.v $(b)));
  size_t r = a % b;
  size_t d = extended_gcd_impl(b, r);
  _ghost_stmt(extended_gcd_computes_gcd (SizeT.v $(a)) (SizeT.v $(b)));
  _ghost_stmt(bezout_identity (SizeT.v $(a)) (SizeT.v $(b)));
  _ghost_stmt(extended_gcd_divides_both (SizeT.v $(a)) (SizeT.v $(b)));
  _ghost_stmt(gcd_spec_divides (SizeT.v $(a)) (SizeT.v $(b)));
  return d;
}
