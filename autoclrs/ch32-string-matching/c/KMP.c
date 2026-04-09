/*
 * KMP String Matching — C implementation with c2pulse verification.
 * (CLRS §32.4)
 *
 * Two phases: compute_prefix fills the prefix (failure) function,
 * then kmp_count uses it for linear-time matching.
 *
 * Proves: memory safety, pi bounds (0 <= pi[j] <= j), count <= n-m+1.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/* Compute the prefix (failure) function for pattern[0..m-1].
 * Stores pi[j] = length of longest proper prefix of pattern[0..j]
 * that is also a suffix, for each j in [0, m). */
void compute_prefix(_array int *pattern, size_t m, _array int *pi)
  _preserves(pattern._length == m)
  _requires(pi._length == m && m > 0)
  _requires((_specint) m < 2147483647)
  _ensures(pi._length == m)
  _ensures(_forall(size_t j, j < m ==> pi[j] >= 0))
  _ensures(_forall(size_t j, j < m ==> (_specint) pi[j] <= (_specint) j))
  _ensures(pattern._length == m)
{
  pi[0] = 0;
  int k = 0;
  for (size_t q = 1; q < m; q = q + 1)
    _invariant(_live(q) && _live(k))
    _invariant(_live(*pattern) && _live(*pi))
    _invariant(pattern._length == m && pi._length == m)
    _invariant(q <= m && m > 0)
    _invariant(k >= 0)
    _invariant((_specint) k < (_specint) q)
    _invariant((_specint) m < 2147483647)
    _invariant(_forall(size_t j, j < q ==> pi[j] >= 0))
    _invariant(_forall(size_t j, j < q ==> (_specint) pi[j] <= (_specint) j))
  {
    /* Follow failure chain until match or k == 0 */
    while (k > 0)
      _invariant(_live(k))
      _invariant(_live(*pattern) && _live(*pi))
      _invariant(pattern._length == m && pi._length == m)
      _invariant(k >= 0)
      _invariant((_specint) k < (_specint) q && q < m)
      _invariant((_specint) m < 2147483647)
      _invariant(m > 0)
      _invariant(_forall(size_t j, j < q ==> pi[j] >= 0))
      _invariant(_forall(size_t j, j < q ==> (_specint) pi[j] <= (_specint) j))
      _ensures(k >= 0)
      _ensures((_specint) k < (_specint) q)
      _ensures(pattern._length == m && pi._length == m)
      _ensures(_forall(size_t j, j < q ==> pi[j] >= 0))
      _ensures(_forall(size_t j, j < q ==> (_specint) pi[j] <= (_specint) j))
      _ensures((_specint) m < 2147483647)
      _ensures(m > 0 && q < m)
    {
      if (pattern[(size_t)k] == pattern[q]) break;
      k = pi[(size_t)(k - 1)];
    }
    if (pattern[(size_t)k] == pattern[q]) {
      k = k + 1;
    }
    pi[q] = k;
  }
}

/* Count pattern occurrences in text using prefix function pi. */
size_t kmp_count(_array int *text, size_t n,
                 _array int *pattern, size_t m,
                 _array int *pi)
  _preserves(text._length == n)
  _preserves(pattern._length == m)
  _preserves(pi._length == m)
  _requires(m > 0 && m <= n)
  _requires((_specint) m < 2147483647)
  _requires(_forall(size_t j, j < m ==> pi[j] >= 0))
  _requires(_forall(size_t j, j < m ==> (_specint) pi[j] <= (_specint) j))
  _ensures(return <= n - m + 1)
  _ensures(_forall(size_t j, j < m ==> pi[j] >= 0))
  _ensures(_forall(size_t j, j < m ==> (_specint) pi[j] <= (_specint) j))
{
  int q = 0;
  size_t count = 0;
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i) && _live(q) && _live(count))
    _invariant(_live(*text) && _live(*pattern) && _live(*pi))
    _invariant(text._length == n && pattern._length == m && pi._length == m)
    _invariant(i <= n)
    _invariant(q >= 0 && (_specint) q < (_specint) m)
    _invariant((_specint) q <= (_specint) i)
    _invariant(m > 0 && m <= n)
    _invariant((_specint) m < 2147483647)
    _invariant(_forall(size_t j, j < m ==> pi[j] >= 0))
    _invariant(_forall(size_t j, j < m ==> (_specint) pi[j] <= (_specint) j))
    _invariant((_specint) i < (_specint) m ==> count == 0)
    _invariant((_specint) i >= (_specint) m ==> (_specint) count <= (_specint) i - (_specint) m + 1)
  {
    /* Follow failure chain */
    while (q > 0)
      _invariant(_live(q))
      _invariant(_live(*text) && _live(*pattern) && _live(*pi))
      _invariant(text._length == n && pattern._length == m && pi._length == m)
      _invariant(q >= 0 && (_specint) q < (_specint) m)
      _invariant((_specint) q <= (_specint) i)
      _invariant(i < n)
      _invariant(m > 0 && m <= n)
      _invariant((_specint) m < 2147483647)
      _invariant(_forall(size_t j, j < m ==> pi[j] >= 0))
      _invariant(_forall(size_t j, j < m ==> (_specint) pi[j] <= (_specint) j))
      _ensures(q >= 0 && (_specint) q < (_specint) m)
      _ensures((_specint) q <= (_specint) i)
      _ensures(text._length == n && pattern._length == m && pi._length == m)
      _ensures(_forall(size_t j, j < m ==> pi[j] >= 0))
      _ensures(_forall(size_t j, j < m ==> (_specint) pi[j] <= (_specint) j))
      _ensures((_specint) m < 2147483647)
      _ensures(m > 0 && m <= n)
      _ensures(i < n)
    {
      if (pattern[(size_t)q] == text[i]) break;
      q = pi[(size_t)(q - 1)];
    }

    if (pattern[(size_t)q] == text[i]) {
      q = q + 1;
    }

    if ((size_t)q == m) {
      count = count + 1;
      q = pi[(size_t)(q - 1)];
    }
  }
  return count;
}
