/*
 * GCD — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. The result equals gcd_spec(a_init, b_init).
 *   2. The result is positive (> 0).
 *   3. The result divides both a_init and b_init.
 *
 * Based on CLRS p. 935, Alg 31.2 (Euclid's algorithm).
 * Uses recursive form matching the mathematical specification.
 */

#include "c2pulse.h"
#include <stddef.h>

_include_pulse(
  open CLRS.Ch31.GCD.Spec
  open FStar.Math.Euclid
)

_rec size_t gcd(size_t a, size_t b)
  _requires((bool) _inline_pulse(SizeT.v $(a) > 0 \/ SizeT.v $(b) > 0))
  _ensures((bool) _inline_pulse(
    SizeT.v $(return) = gcd_spec (SizeT.v $(a)) (SizeT.v $(b))
    /\ SizeT.v $(return) > 0
    /\ divides (SizeT.v $(return)) (SizeT.v $(a))
    /\ divides (SizeT.v $(return)) (SizeT.v $(b))
  ))
  _decreases((_specint) b)
{
  if (b == 0) {
    _ghost_stmt(gcd_spec_divides (SizeT.v $(a)) (SizeT.v $(b)));
    return a;
  }
  size_t r = a % b;
  size_t d = gcd(b, r);
  _ghost_stmt(gcd_spec_divides (SizeT.v $(a)) (SizeT.v $(b)));
  return d;
}
