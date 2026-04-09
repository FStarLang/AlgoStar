#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

void merge_into(_array int *a, _array int *buf, size_t len,
                size_t lo, size_t mid, size_t hi, size_t width)
  _requires(a._length == len && buf._length == len)
  _requires(lo <= mid && mid <= hi && hi <= len)
  _requires(width >= 1)
  _requires(_forall(size_t k, lo <= k && k + 1 < mid ==> a[k] <= a[k + 1]))
  _requires(_forall(size_t k, mid <= k && k + 1 < hi ==> a[k] <= a[k + 1]))
  _requires(_forall(size_t k, k + 1 < lo ==>
               buf[k] <= buf[k + 1] || (bool) _inline_pulse((SizeT.v $(k) + 1) % (2 * SizeT.v $(width)) = 0)))
  _requires((bool) _inline_pulse(SizeT.v $(lo) % (2 * SizeT.v $(width)) = 0 \/ SizeT.v $(lo) = 0))
  _requires(_forall(size_t k, k + 1 < len ==>
               a[k] <= a[k + 1] || (bool) _inline_pulse((SizeT.v $(k) + 1) % SizeT.v $(width) = 0)))
  _preserves_value(a._length)
  _preserves_value(buf._length)
  _ensures(_forall(size_t k, k + 1 < hi ==>
               buf[k] <= buf[k + 1] || (bool) _inline_pulse((SizeT.v $(k) + 1) % (2 * SizeT.v $(width)) = 0)))
  _ensures(_forall(size_t k, k + 1 < len ==>
               a[k] <= a[k + 1] || (bool) _inline_pulse((SizeT.v $(k) + 1) % SizeT.v $(width) = 0)))
{
  size_t i = lo;
  size_t j = mid;
  for (size_t k = lo; k < hi; k = k + 1)
    _invariant(_live(k) && _live(i) && _live(j))
    _invariant(_live(*buf))
    _invariant(buf._length == len)
    _invariant(lo <= k && k <= hi && hi <= len)
    _invariant(lo <= i && i <= mid)
    _invariant(mid <= j && j <= hi)
    _invariant((bool) _inline_pulse(SizeT.v $(i) + SizeT.v $(j) = SizeT.v $(k) + SizeT.v $(mid)))
    _invariant(_forall(size_t p, lo <= p && p + 1 < k ==> buf[p] <= buf[p + 1]))
    _invariant(k > lo && i < mid ==> buf[k - 1] <= a[i])
    _invariant(k > lo && j < hi ==> buf[k - 1] <= a[j])
    _invariant(_forall(size_t p, p + 1 < lo ==>
                 buf[p] <= buf[p + 1] || (bool) _inline_pulse((SizeT.v $(p) + 1) % (2 * SizeT.v $(width)) = 0)))
  {
    if (i >= mid) {
      buf[k] = a[j];
      j = j + 1;
    } else if (j >= hi) {
      buf[k] = a[i];
      i = i + 1;
    } else if (a[i] <= a[j]) {
      buf[k] = a[i];
      i = i + 1;
    } else {
      buf[k] = a[j];
      j = j + 1;
    }
  }
}

void merge_sort(_array int *a, size_t len)
  _preserves(a._length == len)
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
{
  if (len <= 1) return;

  int *buf = (int *)calloc(len, sizeof(int));
  _assert(buf._length == len);

  size_t width = 1;
  while (width < len)
    _invariant(_live(width))
    _invariant(_live(*a) && _live(*buf))
    _invariant(a._length == len && buf._length == len)
    _invariant(width >= 1)
    _invariant(_forall(size_t k, k + 1 < len ==>
                 a[k] <= a[k + 1] || (bool) _inline_pulse((SizeT.v $(k) + 1) % SizeT.v $(width) = 0)))
  {
    size_t lo = 0;
    while (lo < len)
      _invariant(_live(lo) && _live(width))
      _invariant(_live(*a) && _live(*buf))
      _invariant(a._length == len && buf._length == len)
      _invariant(width >= 1 && width < len)
      _invariant(lo <= len)
      _invariant((bool) _inline_pulse(
        SizeT.v $(lo) % (2 * SizeT.v $(width)) = 0
        \/ SizeT.v $(lo) = SizeT.v $(len)))
      _invariant(_forall(size_t k, k + 1 < lo ==>
                   buf[k] <= buf[k + 1] || (bool) _inline_pulse((SizeT.v $(k) + 1) % (2 * SizeT.v $(width)) = 0)))
      _invariant(_forall(size_t k, k + 1 < len ==>
                   a[k] <= a[k + 1] || (bool) _inline_pulse((SizeT.v $(k) + 1) % SizeT.v $(width) = 0)))
    {
      _assert((bool) _inline_pulse(SizeT.v $(lo) % (2 * SizeT.v $(width)) = 0));
      _ghost_stmt(FStar.Math.Lemmas.mod_mult_exact (SizeT.v $(lo)) (SizeT.v $(width)) 2);
      _assert((bool) _inline_pulse(SizeT.v $(lo) % SizeT.v $(width) = 0));

      if (len - lo < width) {
        _ghost_stmt(Classical.forall_intro (Classical.move_requires (MergeSortHelper.mod_range (SizeT.v $(lo)) (SizeT.v $(width)))));
        _assert(_forall(size_t k, lo <= k && k + 1 < len ==> a[k] <= a[k + 1]));
        merge_into(a, buf, len, lo, len, len, width);
        lo = len;
      } else {
        size_t mid_v = lo + width;
        _ghost_stmt(Classical.forall_intro (Classical.move_requires (MergeSortHelper.mod_range (SizeT.v $(lo)) (SizeT.v $(width)))));
        _assert(_forall(size_t k, lo <= k && k + 1 < mid_v ==> a[k] <= a[k + 1]));

        if (len - mid_v < width) {
          _ghost_stmt(FStar.Math.Lemmas.lemma_mod_plus (SizeT.v $(lo)) 1 (SizeT.v $(width)));
          _ghost_stmt(Classical.forall_intro (Classical.move_requires (MergeSortHelper.mod_range (SizeT.v $(mid_v)) (SizeT.v $(width)))));
          _assert(_forall(size_t k, mid_v <= k && k + 1 < len ==> a[k] <= a[k + 1]));
          merge_into(a, buf, len, lo, mid_v, len, width);
          lo = len;
        } else {
          size_t hi_v = mid_v + width;
          _ghost_stmt(FStar.Math.Lemmas.lemma_mod_plus (SizeT.v $(lo)) 1 (SizeT.v $(width)));
          _ghost_stmt(Classical.forall_intro (Classical.move_requires (MergeSortHelper.mod_range (SizeT.v $(mid_v)) (SizeT.v $(width)))));
          _assert(_forall(size_t k, mid_v <= k && k + 1 < hi_v ==> a[k] <= a[k + 1]));
          merge_into(a, buf, len, lo, mid_v, hi_v, width);
          _ghost_stmt(FStar.Math.Lemmas.lemma_mod_plus (SizeT.v $(lo)) 1 (2 * SizeT.v $(width)));
          lo = hi_v;
        }
      }
    }

    for (size_t p = 0; p < len; p = p + 1)
      _invariant(_live(p))
      _invariant(_live(*a))
      _invariant(a._length == len)
      _invariant(p <= len)
      _invariant(_forall(size_t q, q < p ==> a[q] == buf[q]))
    {
      a[p] = buf[p];
    }

    _assert(_forall(size_t k, k + 1 < len ==>
              a[k] <= a[k + 1] || (bool) _inline_pulse((SizeT.v $(k) + 1) % (2 * SizeT.v $(width)) = 0)));

    size_t half = len / 2;
    if (width <= half) {
      width = width * 2;
    } else {
      _assert(_forall(size_t k, k + 1 < len ==> a[k] <= a[k + 1]));
      width = len;
    }
  }

  free(buf);
}
