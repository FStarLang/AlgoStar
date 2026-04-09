/*
 * Modular Exponentiation (Right-to-Left) — C with c2pulse verification.
 *
 * Proves:
 *   1. The result equals mod_exp_spec(b, e, m) = pow(b, e) % m.
 *   2. The result is in [0, m).
 *
 * Based on CLRS Exercise 31.6-2.
 * Precondition: m > 0 and m*m fits in size_t (overflow safety).
 */

#include "c2pulse.h"
#include <stddef.h>

_include_pulse(
  open CLRS.Ch31.ModExp.Spec
  open CLRS.Ch31.ModExp.Lemmas
  open FStar.Mul
  open FStar.Math.Lemmas
)

size_t mod_exp(size_t b_init, size_t e_init, size_t m)
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
  _ghost_stmt(pow_mod_base (SizeT.v $(b_init)) (SizeT.v $(e_init)) (SizeT.v $(m)));
  _ghost_stmt(FStar.Math.Lemmas.lemma_mod_mul_distr_l 1 (pow (SizeT.v $(b_init) % SizeT.v $(m)) (SizeT.v $(e_init))) (SizeT.v $(m)));

  size_t result = 1 % m;
  size_t base = b_init % m;
  size_t exp = e_init;

  while (exp > 0)
    _invariant(_live(result) && _live(base) && _live(exp))
    _invariant((bool) _inline_pulse(
      SizeT.v $(exp) <= SizeT.v $(e_init)
      /\ SizeT.v $(result) >= 0 /\ SizeT.v $(result) < SizeT.v $(m)
      /\ SizeT.v $(base) >= 0 /\ SizeT.v $(base) < SizeT.v $(m)
      /\ (op_Multiply (SizeT.v $(result)) (pow (SizeT.v $(base)) (SizeT.v $(exp)))) % SizeT.v $(m)
         = mod_exp_spec (SizeT.v $(b_init)) (SizeT.v $(e_init)) (SizeT.v $(m))
    ))
  {
    _ghost_stmt(mod_exp_step (SizeT.v $(result)) (SizeT.v $(base)) (SizeT.v $(exp)) (SizeT.v $(m)));

    if (exp % 2 == 1) {
      _assert((bool) _inline_pulse(
        op_Multiply (SizeT.v $(result)) (SizeT.v $(base))
          <= op_Multiply (SizeT.v $(result)) (SizeT.v $(m))));
      _assert((bool) _inline_pulse(
        op_Multiply (SizeT.v $(result)) (SizeT.v $(m))
          < op_Multiply (SizeT.v $(m)) (SizeT.v $(m))));
      result = (result * base) % m;
    }

    _assert((bool) _inline_pulse(
      op_Multiply (SizeT.v $(base)) (SizeT.v $(base))
        <= op_Multiply (SizeT.v $(base)) (SizeT.v $(m))));
    _assert((bool) _inline_pulse(
      op_Multiply (SizeT.v $(base)) (SizeT.v $(m))
        < op_Multiply (SizeT.v $(m)) (SizeT.v $(m))));
    base = (base * base) % m;
    exp = exp / 2;
  }

  return result;
}
