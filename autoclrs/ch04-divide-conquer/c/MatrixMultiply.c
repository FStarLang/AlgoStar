/*
 * Matrix Multiply — C implementation with c2pulse verification.
 *
 * Proves memory safety, array bounds, and absence of integer overflow
 * for the standard O(n^3) matrix multiplication algorithm.
 *
 * Matrices are stored in row-major flat arrays of size n*n.
 * Precondition: n <= 46 and max_val <= 46 ensures all intermediate
 * Int32 arithmetic stays within bounds (n * max_val^2 <= 97336 < 2^31).
 *
 * The algorithm is split into two functions to keep Pulse elaboration
 * tractable: dot_product handles the inner k-loop with its overflow
 * proof, while matrix_multiply handles the outer i,j loops.
 *
 * Equivalent structural properties to CLRS.Ch04.MatrixMultiply.Impl.fsti
 * (minus functional dot-product correctness).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Compute dot product of row i of A and column j of B.
 * Uses a 'bound' variable to track k * max_val^2 without _specint
 * in the sum invariant, avoiding Pulse elaboration divergence.
 */
int dot_product(
    _array int *a, _array int *b,
    size_t n, size_t i, size_t j, int max_val)
  _requires(n > 0 && n <= 46 && i < n && j < n)
  _requires(max_val > 0 && max_val <= 46)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) `op_Multiply` SizeT.v $(n))))
  _preserves(a._length == n * n && b._length == n * n)
  _requires(_forall(size_t idx, idx < n * n ==> a[idx] >= -max_val && a[idx] <= max_val))
  _requires(_forall(size_t idx, idx < n * n ==> b[idx] >= -max_val && b[idx] <= max_val))
  _ensures(_forall(size_t idx, idx < n * n ==> a[idx] >= -max_val && a[idx] <= max_val))
  _ensures(_forall(size_t idx, idx < n * n ==> b[idx] >= -max_val && b[idx] <= max_val))
{
  int sum = 0;
  int mv2 = max_val * max_val;
  int bound = 0;
  for (size_t k = 0; k < n; k = k + 1)
    _invariant(_live(k) && _live(sum) && _live(bound) && _live(mv2) && _live(*a) && _live(*b))
    _invariant(a._length == n * n && b._length == n * n)
    _invariant(i < n && j < n && k <= n && n <= 46 && max_val <= 46)
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) `op_Multiply` SizeT.v $(n))))
    _invariant(mv2 == max_val * max_val && mv2 >= 1 && mv2 <= 2116)
    _invariant((_specint) bound == (_specint) k * (_specint) mv2)
    _invariant(sum >= -bound && sum <= bound)
    _invariant(_forall(size_t idx, idx < n * n ==> a[idx] >= -max_val && a[idx] <= max_val))
    _invariant(_forall(size_t idx, idx < n * n ==> b[idx] >= -max_val && b[idx] <= max_val))
  {
    int av = a[i * n + k];
    int bv = b[k * n + j];
    _assert(av >= -max_val && av <= max_val);
    _assert(bv >= -max_val && bv <= max_val);
    int prod = av * bv;
    sum = sum + prod;
    bound = bound + mv2;
  }
  return sum;
}

/*
 * Standard O(n^3) matrix multiplication: C = A * B.
 * All matrices are n*n stored in row-major order as flat arrays.
 */
void matrix_multiply(
    _array int *a, _array int *b, _array int *c,
    size_t n, int max_val)
  _requires(n > 0 && n <= 46)
  _requires(max_val > 0 && max_val <= 46)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) `op_Multiply` SizeT.v $(n))))
  _preserves(a._length == n * n && b._length == n * n && c._length == n * n)
  _requires(_forall(size_t idx, idx < n * n ==> a[idx] >= -max_val && a[idx] <= max_val))
  _requires(_forall(size_t idx, idx < n * n ==> b[idx] >= -max_val && b[idx] <= max_val))
{
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i) && _live(*a) && _live(*b) && _live(*c))
    _invariant(a._length == n * n && b._length == n * n && c._length == n * n)
    _invariant(i <= n && n <= 46 && max_val <= 46)
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) `op_Multiply` SizeT.v $(n))))
    _invariant(_forall(size_t idx, idx < n * n ==> a[idx] >= -max_val && a[idx] <= max_val))
    _invariant(_forall(size_t idx, idx < n * n ==> b[idx] >= -max_val && b[idx] <= max_val))
  {
    for (size_t j = 0; j < n; j = j + 1)
      _invariant(_live(i) && _live(j) && _live(*a) && _live(*b) && _live(*c))
      _invariant(a._length == n * n && b._length == n * n && c._length == n * n)
      _invariant(i < n && j <= n && n <= 46 && max_val <= 46)
      _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) `op_Multiply` SizeT.v $(n))))
      _invariant(_forall(size_t idx, idx < n * n ==> a[idx] >= -max_val && a[idx] <= max_val))
      _invariant(_forall(size_t idx, idx < n * n ==> b[idx] >= -max_val && b[idx] <= max_val))
    {
      c[i * n + j] = dot_product(a, b, n, i, j, max_val);
    }
  }
}
