/*
 * Rabin-Karp String Matching — C implementation with c2pulse verification.
 * (CLRS §32.2)
 *
 * Proves: memory safety, count bounds, no false positives,
 *         hash values in [0,q), overflow safety.
 *
 * Split into helper functions so each Pulse proof is manageable.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/* Horner hash of arr[0..hash_len-1] with base d, modulus q */
int horner_hash(_array int *arr, size_t arr_len, size_t hash_len, int d, int q)
  _preserves(arr._length == arr_len)
  _requires(hash_len > 0 && hash_len <= arr_len)
  _requires(d > 0 && q > 1)
  _requires((_specint) (d + 1) * q < 2147483647)
  _requires(_forall(size_t k, k < arr_len ==> arr[k] >= 0 && arr[k] < q))
  _ensures(return >= 0 && return < q)
  _ensures(_forall(size_t k, k < arr_len ==> arr[k] >= 0 && arr[k] < q))
{
  int h = 0;
  for (size_t i = 0; i < hash_len; i = i + 1)
    _invariant(_live(i) && _live(h))
    _invariant(_live(*arr))
    _invariant(arr._length == arr_len && hash_len <= arr_len)
    _invariant(i <= hash_len)
    _invariant(h >= 0 && h < q)
    _invariant(d > 0 && q > 1)
    _invariant((_specint) (d + 1) * q < 2147483647)
    _invariant(_forall(size_t k, k < arr_len ==> arr[k] >= 0 && arr[k] < q))
  {
    h = (d * h + arr[i]) % q;
  }
  return h;
}

/* Compute d^(len-1) mod q */
int compute_h(size_t len, int d, int q)
  _requires(len > 0)
  _requires(d > 0 && q > 1)
  _requires((_specint) (d + 1) * q < 2147483647)
  _ensures(return >= 0 && return < q)
{
  int h = 1 % q;
  for (size_t i = 1; i < len; i = i + 1)
    _invariant(_live(i) && _live(h))
    _invariant(i <= len)
    _invariant(h >= 0 && h < q)
    _invariant(d > 0 && q > 1)
    _invariant((_specint) (d + 1) * q < 2147483647)
  {
    h = (d * h) % q;
  }
  return h;
}

/* Check whether pattern matches text at position s; returns 0 or 1 */
size_t check_match(_array int *text, size_t n,
                   _array int *pattern, size_t m,
                   size_t s, int q)
  _preserves(text._length == n)
  _preserves(pattern._length == m)
  _requires(m > 0 && m <= n)
  _requires(s <= n - m)
  _requires(q > 1)
  _requires(_forall(size_t k, k < n ==> text[k] >= 0 && text[k] < q))
  _requires(_forall(size_t k, k < m ==> pattern[k] >= 0 && pattern[k] < q))
  _ensures(return <= 1)
  _ensures(_forall(size_t k, k < n ==> text[k] >= 0 && text[k] < q))
  _ensures(_forall(size_t k, k < m ==> pattern[k] >= 0 && pattern[k] < q))
{
  size_t j = 0;
  while (j < m)
    _invariant(_live(j))
    _invariant(_live(*text) && _live(*pattern))
    _invariant(text._length == n && pattern._length == m)
    _invariant(j <= m && s <= n - m)
    _invariant(_forall(size_t k, k < j ==> text[s + k] == pattern[k]))
    _invariant(m > 0 && m <= n)
    _invariant(_forall(size_t k, k < n ==> text[k] >= 0 && text[k] < q))
    _invariant(_forall(size_t k, k < m ==> pattern[k] >= 0 && pattern[k] < q))
    _ensures(j <= m)
    _ensures(j == m ==> _forall(size_t k, k < m ==> text[s + k] == pattern[k]))
    _ensures(text._length == n && pattern._length == m)
    _ensures(_forall(size_t k, k < n ==> text[k] >= 0 && text[k] < q))
    _ensures(_forall(size_t k, k < m ==> pattern[k] >= 0 && pattern[k] < q))
  {
    if (text[s + j] != pattern[j]) break;
    j = j + 1;
  }
  size_t result = 0;
  if (j == m) {
    result = 1;
  }
  return result;
}

/* One step of the rolling hash update: compute hash for text[s+1..s+m] */
int rolling_hash_step(_array int *text, size_t n,
                      int t_hash, size_t s, size_t m,
                      int h, int d, int q)
  _preserves(text._length == n)
  _requires(m > 0 && m <= n)
  _requires(s < n - m)
  _requires(t_hash >= 0 && t_hash < q)
  _requires(h >= 0 && h < q)
  _requires(d > 0 && q > 1)
  _requires((_specint) (d + 1) * q < 2147483647)
  _requires((_specint) q * q < 2147483647)
  _requires(_forall(size_t k, k < n ==> text[k] >= 0 && text[k] < q))
  _ensures(return >= 0 && return < q)
  _ensures(_forall(size_t k, k < n ==> text[k] >= 0 && text[k] < q))
{
  int old_char = text[s];
  int new_char = text[s + m];
  int sub = (old_char * h) % q;
  int tmp = (t_hash + q - sub) % q;
  int new_t_hash = (d * tmp) % q;
  new_t_hash = (new_t_hash + new_char) % q;
  return new_t_hash;
}

size_t rabin_karp(_array int *text, size_t n,
                  _array int *pattern, size_t m,
                  int d, int q)
  _preserves(text._length == n)
  _preserves(pattern._length == m)
  _requires(m > 0 && m <= n)
  _requires(d > 0 && q > 1)
  _requires((_specint) q * q < 2147483647)
  _requires((_specint) (d + 1) * q < 2147483647)
  _requires(_forall(size_t i, i < n ==> text[i] >= 0 && text[i] < q))
  _requires(_forall(size_t i, i < m ==> pattern[i] >= 0 && pattern[i] < q))
  _ensures(return <= n - m + 1)
{
  int p_hash = horner_hash(pattern, m, m, d, q);
  int t_hash = horner_hash(text, n, m, d, q);
  int h = compute_h(m, d, q);

  size_t count = 0;

  /* Phase 1: positions 0..n-m-1 — rolling hash + character check */
  for (size_t s = 0; s < n - m; s = s + 1)
    _invariant(_live(s) && _live(count) && _live(t_hash))
    _invariant(_live(*text) && _live(*pattern))
    _invariant(text._length == n && pattern._length == m)
    _invariant(s <= n - m)
    _invariant(count <= s)
    _invariant(t_hash >= 0 && t_hash < q)
    _invariant(h >= 0 && h < q)
    _invariant(d > 0 && q > 1)
    _invariant((_specint) (d + 1) * q < 2147483647)
    _invariant((_specint) q * q < 2147483647)
    _invariant(_forall(size_t k, k < n ==> text[k] >= 0 && text[k] < q))
    _invariant(_forall(size_t k, k < m ==> pattern[k] >= 0 && pattern[k] < q))
    _invariant(m > 0 && m <= n)
  {
    int new_t_hash = rolling_hash_step(text, n, t_hash, s, m, h, d, q);
    size_t match = check_match(text, n, pattern, m, s, q);
    count = count + match;
    t_hash = new_t_hash;
  }

  /* Phase 2: last position n-m */
  size_t match2 = check_match(text, n, pattern, m, n - m, q);
  count = count + match2;

  return count;
}
