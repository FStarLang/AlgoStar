#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

/* Merge a[lo..mid) and a[mid..hi) into buf[lo..hi), preserving sortedness */
void merge_rec(_array int *a, _array int *buf, size_t len,
               size_t lo, size_t mid, size_t hi)
  _requires(a._length == len && buf._length == len)
  _requires(lo <= mid && mid <= hi && hi <= len)
  _requires(_forall(size_t k, lo <= k && k + 1 < mid ==> a[k] <= a[k + 1]))
  _requires(_forall(size_t k, mid <= k && k + 1 < hi ==> a[k] <= a[k + 1]))
  _preserves_value(a._length)
  _preserves_value(buf._length)
  _ensures(_forall(size_t k, lo <= k && k + 1 < hi ==> buf[k] <= buf[k + 1]))
  _ensures(_forall(size_t k, k < len ==> a[k] == _old(a[k])))
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

/* Recursive top-down merge sort: sort a[lo..hi) using buf as scratch */
_rec void merge_sort_rec(_array int *a, _array int *buf, size_t len,
                         size_t lo, size_t hi)
  _requires(a._length == len && buf._length == len)
  _requires(lo <= hi && hi <= len)
  _preserves_value(a._length)
  _preserves_value(buf._length)
  _ensures(_forall(size_t k, lo <= k && k + 1 < hi ==> a[k] <= a[k + 1]))
  _ensures(_forall(size_t k, k < len && (k < lo || k >= hi) ==> a[k] == _old(a[k])))
  _decreases(hi - lo)
{
  if (hi - lo <= 1) return;
  size_t mid = lo + (hi - lo) / 2;
  merge_sort_rec(a, buf, len, lo, mid);
  merge_sort_rec(a, buf, len, mid, hi);
  merge_rec(a, buf, len, lo, mid, hi);
  /* Copy buf[lo..hi) back to a[lo..hi) */
  for (size_t p = lo; p < hi; p = p + 1)
    _invariant(_live(p))
    _invariant(_live(*a))
    _invariant(a._length == len)
    _invariant(lo <= p && p <= hi)
    _invariant(_forall(size_t q, lo <= q && q < p ==> a[q] == buf[q]))
    _invariant(_forall(size_t q, q < len && (q < lo || q >= hi) ==> a[q] == _old(a[q])))
  {
    a[p] = buf[p];
  }
}

void merge_sort(_array int *a, size_t len)
  _preserves(a._length == len)
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
{
  if (len <= 1) return;
  int *buf = (int *)calloc(len, sizeof(int));
  _assert(buf._length == len);
  merge_sort_rec(a, buf, len, 0, len);
  free(buf);
}
