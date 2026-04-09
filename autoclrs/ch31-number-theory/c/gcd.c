/*
 * GCD — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. The result equals gcd_spec(a_init, b_init).
 *   2. The result is positive (> 0).
 *   3. The result divides both a_init and b_init.
 *
 * Based on CLRS p. 935, Alg 31.2 (Euclid's algorithm).
 */

#include "c2pulse.h"
#include <stddef.h>

_include_pulse(
  open CLRS.Ch31.GCD.Spec
  open FStar.Math.Euclid
)

size_t gcd(size_t a_init, size_t b_init)
  _requires((bool) _inline_pulse(SizeT.v $(a_init) > 0 \/ SizeT.v $(b_init) > 0))
  _ensures((bool) _inline_pulse(
    SizeT.v $(return) = gcd_spec (SizeT.v $(a_init)) (SizeT.v $(b_init))
    /\ SizeT.v $(return) > 0
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

  _ghost_stmt(gcd_spec_divides (SizeT.v $(a_init)) (SizeT.v $(b_init)));
  return a;
}
