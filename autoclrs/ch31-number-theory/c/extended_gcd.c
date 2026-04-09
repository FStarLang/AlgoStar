/*
 * Extended GCD — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. The result d equals gcd(a_init, b_init) via extended_gcd.
 *   2. d is positive (> 0).
 *   3. Bézout's identity: a_init*x + b_init*y = d for the extended_gcd coefficients.
 *   4. d divides both a_init and b_init.
 *
 * Based on CLRS p. 937, Alg 31.3 (Extended Euclidean Algorithm).
 * The Bézout coefficients x, y are ghost values — only d is returned.
 */

#include "c2pulse.h"
#include <stddef.h>

_include_pulse(
  open CLRS.Ch31.GCD.Spec
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

size_t extended_gcd_impl(size_t a_init, size_t b_init)
  _requires((bool) _inline_pulse(SizeT.v $(a_init) > 0 \/ SizeT.v $(b_init) > 0))
  _ensures((bool) _inline_pulse(
    SizeT.v $(return) = egcd_d (SizeT.v $(a_init)) (SizeT.v $(b_init))
    /\ SizeT.v $(return) > 0
    /\ op_Multiply (SizeT.v $(a_init)) (egcd_x (SizeT.v $(a_init)) (SizeT.v $(b_init)))
       + op_Multiply (SizeT.v $(b_init)) (egcd_y (SizeT.v $(a_init)) (SizeT.v $(b_init)))
       = SizeT.v $(return)
    /\ divides (SizeT.v $(return)) (SizeT.v $(a_init))
    /\ divides (SizeT.v $(return)) (SizeT.v $(b_init))
  ))
{
  size_t a = a_init;
  size_t b = b_init;

  while (b > 0)
    _invariant(_live(a) && _live(b))
    _invariant((bool) _inline_pulse(
      gcd_spec (SizeT.v $(a)) (SizeT.v $(b)) = gcd_spec (SizeT.v $(a_init)) (SizeT.v $(b_init))
      /\ (SizeT.v $(a) > 0 \/ SizeT.v $(b) > 0)
    ))
  {
    size_t temp = a % b;
    a = b;
    b = temp;
  }

  _ghost_stmt(extended_gcd_computes_gcd (SizeT.v $(a_init)) (SizeT.v $(b_init)));
  _ghost_stmt(bezout_identity (SizeT.v $(a_init)) (SizeT.v $(b_init)));
  _ghost_stmt(extended_gcd_divides_both (SizeT.v $(a_init)) (SizeT.v $(b_init)));
  _ghost_stmt(gcd_spec_divides (SizeT.v $(a_init)) (SizeT.v $(b_init)));
  return a;
}
