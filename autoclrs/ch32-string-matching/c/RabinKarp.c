/*
 * Rabin-Karp String Matching — C implementation with c2pulse verification.
 * (CLRS §32.2)
 *
 * Proves: memory safety, count bounds, no false positives,
 *         hash values in [0,q), overflow safety,
 *         functional correctness: count == count_matches_up_to.
 *
 * Split into helper functions so each Pulse proof is manageable.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open CLRS.Ch32.RabinKarp.Spec)
_include_pulse(open CLRS.Ch32.RabinKarp.C.BridgeLemmas)

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
  _ensures((_slprop) _inline_pulse(
    with_pure (
      SizeT.v return_1 =
        count_matches_up_to
          (unwrap_nat_seq (array_value_of var_text) (SizeT.v var_n))
          (unwrap_nat_seq (array_value_of var_pattern) (SizeT.v var_m))
          ((SizeT.v var_n) - (SizeT.v var_m) + 1)
    )
  ))
{
  int p_hash = horner_hash(pattern, m, m, d, q);
  int t_hash = horner_hash(text, n, m, d, q);
  int h = compute_h(m, d, q);

  _ghost_stmt(let _vt = array_value_of (!var_text));
  _ghost_stmt(let _vp = array_value_of (!var_pattern));

  size_t count = 0;

  for (size_t s = 0; s <= n - m; s = s + 1)
    _invariant(_live(s) && _live(count) && _live(t_hash))
    _invariant((_slprop) _inline_pulse(
      exists* (mask_t: (nat -> prop)).
        (array_pts_to (!var_text) 1.0R _vt mask_t)
    ))
    _invariant((_slprop) _inline_pulse(
      exists* (mask_p: (nat -> prop)).
        (array_pts_to (!var_pattern) 1.0R _vp mask_p)
    ))
    _invariant(text._length == n && pattern._length == m)
    _invariant(s <= n - m + 1)
    _invariant(count <= s)
    _invariant(m > 0 && m <= n)
    _invariant(t_hash >= 0 && t_hash < q)
    _invariant(h >= 0 && h < q)
    _invariant(d > 0 && q > 1)
    _invariant((_specint) (d + 1) * q < 2147483647)
    _invariant((_specint) q * q < 2147483647)
    _invariant(_forall(size_t k, k < n ==> text[k] >= 0 && text[k] < q))
    _invariant(_forall(size_t k, k < m ==> pattern[k] >= 0 && pattern[k] < q))
    _invariant((_slprop) _inline_pulse(
      with_pure (
        SizeT.v (!var_count) =
          count_matches_up_to
            (unwrap_nat_seq _vt (SizeT.v (!var_n)))
            (unwrap_nat_seq _vp (SizeT.v (!var_m)))
            (SizeT.v (!var_s))
      )
    ))
  {
    /* Character-by-character comparison (inlined check_match) */
    size_t j = 0;
    int all_match = 1;
    while (j < m && all_match == 1)
      _invariant(_live(j) && _live(all_match))
      _invariant((_slprop) _inline_pulse(
        exists* (mask_t: (nat -> prop)).
          (array_pts_to (!var_text) 1.0R _vt mask_t)
      ))
      _invariant((_slprop) _inline_pulse(
        exists* (mask_p: (nat -> prop)).
          (array_pts_to (!var_pattern) 1.0R _vp mask_p)
      ))
      _invariant(text._length == n && pattern._length == m)
      _invariant(j <= m)
      _invariant(s <= n - m)
      _invariant(all_match == 0 || all_match == 1)
      _invariant(_forall(size_t k, k < j ==> text[s + k] == pattern[k]))
      _invariant(m > 0 && m <= n)
      _invariant(_forall(size_t k, k < n ==> text[k] >= 0 && text[k] < q))
      _invariant(_forall(size_t k, k < m ==> pattern[k] >= 0 && pattern[k] < q))
      _invariant((_slprop) _inline_pulse(
        with_pure (
          ((id #int (Int32.v (!var_all_match))) = 0) ==>
            (SizeT.v (!var_s) + SizeT.v (!var_j) < Seq.length _vt) ==>
            (SizeT.v (!var_j) < Seq.length _vp) ==>
            Seq.index _vt (SizeT.v (!var_s) + SizeT.v (!var_j)) <>
            Seq.index _vp (SizeT.v (!var_j))
        )
      ))
    {
      if (text[s + j] != pattern[j]) {
        all_match = 0;
      } else {
        j = j + 1;
      }
    }

    _ghost_stmt(
      match_connection _vt _vp
        (SizeT.v (!var_n)) (SizeT.v (!var_m)) (SizeT.v (!var_s)) (SizeT.v (!var_j))
        (Int32.v (!var_all_match))
    );
    if (j == m) { count = count + 1; }
    _ghost_stmt(
      count_matches_up_to_unfold
        (unwrap_nat_seq _vt (SizeT.v (!var_n)))
        (unwrap_nat_seq _vp (SizeT.v (!var_m)))
        ((SizeT.v (!var_s)) + 1)
    );

    /* Rolling hash update (skip at last position).
       Variables declared here (not inside the if) to avoid Pulse
       "mutable local in un-annotated block" error. */
    int old_char = 0;
    int new_char = 0;
    int rh_sub = 0;
    int rh_tmp = 0;
    int new_t_hash = 0;
    if (s < n - m) {
      old_char = text[s];
      new_char = text[s + m];
      rh_sub = (old_char * h) % q;
      rh_tmp = (t_hash + q - rh_sub) % q;
      new_t_hash = (d * rh_tmp) % q;
      new_t_hash = (new_t_hash + new_char) % q;
      t_hash = new_t_hash;
    }
  }

  return count;
}
