#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open CLRS.Ch32.NaiveStringMatch.Spec)
_include_pulse(open CLRS.Ch32.NaiveStringMatch.Lemmas)
_include_pulse(open CLRS.Ch32.NaiveStringMatch.C.BridgeLemmas)

size_t naive_string_match(_array int *text, size_t n,
                          _array int *pattern, size_t m)
  _preserves(text._length == n)
  _preserves(pattern._length == m)
  _requires(m > 0 && m <= n)
  _ensures(return <= n - m + 1)
  _ensures((_slprop) _inline_pulse(
    with_pure (
      SizeT.v return_1 =
        count_matches_up_to
          (unwrap_seq (array_value_of var_text) (SizeT.v var_n))
          (unwrap_seq (array_value_of var_pattern) (SizeT.v var_m))
          ((SizeT.v var_n) - (SizeT.v var_m) + 1)
    )
  ))
{
  size_t count = 0;
  _ghost_stmt(let _vt = array_value_of (!var_text));
  _ghost_stmt(let _vp = array_value_of (!var_pattern));

  for (size_t s = 0; s <= n - m; s = s + 1)
    _invariant(_live(s) && _live(count))
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
    _invariant((_slprop) _inline_pulse(
      with_pure (
        SizeT.v (!var_count) =
          count_matches_up_to
            (unwrap_seq _vt (SizeT.v (!var_n)))
            (unwrap_seq _vp (SizeT.v (!var_m)))
            (SizeT.v (!var_s))
      )
    ))
  {
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
        (unwrap_seq _vt (SizeT.v (!var_n)))
        (unwrap_seq _vp (SizeT.v (!var_m)))
        ((SizeT.v (!var_s)) + 1)
    );
  }
  return count;
}
