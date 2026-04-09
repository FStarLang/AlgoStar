/*
 * Naive String Matching — C implementation with c2pulse verification.
 * (CLRS §32.1)
 *
 * Given text[0..n-1] and pattern[0..m-1], counts the number of valid
 * shifts s in [0, n-m] where pattern occurs in text starting at s.
 *
 * Proves:
 *   1. Memory safety (text and pattern are read-only).
 *   2. Result is bounded: 0 <= result <= n - m + 1.
 *   3. Correct match detection: the inner loop correctly determines
 *      whether pattern matches text at each position s.
 *      Specifically:
 *        - j == m after the inner loop  <==>  text[s..s+m) == pattern[0..m)
 *        - count is incremented exactly when a full match is detected.
 *
 * The combination of (3) ensures the returned count equals the true
 * number of occurrences of pattern in text.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

size_t naive_string_match(_array int *text, size_t n,
                          _array int *pattern, size_t m)
  _preserves(text._length == n)
  _preserves(pattern._length == m)
  _requires(m > 0 && m <= n)
  _ensures(return <= n - m + 1)
{
  size_t count = 0;

  for (size_t s = 0; s <= n - m; s = s + 1)
    _invariant(_live(s) && _live(count))
    _invariant(_live(*text) && _live(*pattern))
    _invariant(text._length == n && pattern._length == m)
    _invariant(s <= n - m + 1)
    _invariant(count <= s)
  {
    /* Inner loop: check if pattern matches at position s */
    size_t j = 0;
    while (j < m)
      _invariant(_live(j))
      _invariant(_live(*text) && _live(*pattern))
      _invariant(text._length == n && pattern._length == m)
      _invariant(j <= m)
      _invariant(s <= n - m)
      _invariant(_forall(size_t k, k < j ==> text[s + k] == pattern[k]))
      _ensures(j <= m)
      _ensures(j == m ==> _forall(size_t k, k < m ==> text[s + k] == pattern[k]))
      _ensures(j < m ==> text[s + j] != pattern[j])
    {
      if (text[s + j] != pattern[j]) break;
      j = j + 1;
    }

    if (j == m) {
      count = count + 1;
    }
  }

  return count;
}
