/*
 * GCD — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. The result equals gcd_spec(a_init, b_init).
 *   2. The result is positive (> 0).
 *   3. The result divides both a_init and b_init.
 *   4. O(log b) complexity bound: gcd_steps(a,b) <= 2*num_bits(b)+1.
 *
 * Based on CLRS p. 935, Alg 31.2 (Euclid's algorithm).
 * Uses recursive form matching the mathematical specification.
 */

#include "c2pulse.h"
#include <stddef.h>

_include_pulse(
  open CLRS.Ch31.GCD.Spec
  open CLRS.Ch31.GCD.Complexity
  open FStar.Math.Euclid
)

_rec size_t gcd(size_t a, size_t b)
  _requires((bool) _inline_pulse(SizeT.v $(a) > 0 \/ SizeT.v $(b) > 0))
  _ensures((bool) _inline_pulse(
    SizeT.v $(return) = gcd_spec (SizeT.v $(a)) (SizeT.v $(b))
    /\ SizeT.v $(return) > 0
    /\ divides (SizeT.v $(return)) (SizeT.v $(a))
    /\ divides (SizeT.v $(return)) (SizeT.v $(b))
    /\ (SizeT.v $(b) > 0 ==> gcd_steps (SizeT.v $(a)) (SizeT.v $(b)) <= op_Multiply 2 (num_bits (SizeT.v $(b))) + 1)
  ))
  _decreases((_specint) b)
{
  if (b == 0) {
    _ghost_stmt(gcd_spec_divides (SizeT.v $(a)) (SizeT.v $(b)));
    return a;
  }
  _ghost_stmt(lemma_gcd_steps_log (SizeT.v $(a)) (SizeT.v $(b)));
  size_t r = a % b;
  size_t d = gcd(b, r);
  _ghost_stmt(gcd_spec_divides (SizeT.v $(a)) (SizeT.v $(b)));
  return d;
}
