#include "c2pulse.h"
#include <stdint.h>

// Multiply x * y by repeated addition.
// Precondition: the product must fit in uint32_t.
// Postcondition: the result equals x * y.
uint32_t multiply(uint32_t x, uint32_t y)
  _requires((_specint) x * y <= UINT32_MAX)
  _ensures(return == x * y)
{
  uint32_t ctr = 0;
  uint32_t acc = 0;
  while (ctr < x)
    _invariant(_live(ctr) && _live(acc))
    _invariant(ctr <= x && acc == ctr * y)
  {
      ctr = ctr + 1;
      acc = acc + y;
  }
  return acc;
}
