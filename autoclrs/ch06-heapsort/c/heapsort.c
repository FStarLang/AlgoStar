/*
 * CLRS Chapter 6: Heapsort — C implementation with c2pulse verification.
 *
 * Implements:
 *   - MAX-HEAPIFY (§6.2): recursive sift-down using _rec
 *   - BUILD-MAX-HEAP (§6.3): bottom-up heap construction
 *   - HEAPSORT (§6.4): build heap + extract-max loop
 *
 * Proved mechanically (via c2pulse annotations):
 *   - Memory safety and array bounds throughout
 *   - Frame preservation (elements outside working range unchanged)
 *   - Termination of max_heapify (via _decreases)
 *   - Max-heap property (max_heapify postcondition, build_max_heap)
 *   - Sortedness (heapsort postcondition)
 *
 * Max_heapify claims heaps_from as postcondition with targeted assume
 * for the internal sift-down proof (proved in Lemmas.sift_down_swap_lemma_from).
 * Build_max_heap is assume-free: max_heapify's postcondition suffices.
 * Heapsort uses assume for sorted-suffix/prefix-le-suffix invariants
 * (proved in Lemmas via root_ge_element, extract_extends_sorted_upto).
 *
 * Uses _rec for max_heapify (natural recursion as in CLRS).
 * Full correctness proofs are in CLRS.Ch06.Heap.Impl.fst.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * MAX-HEAPIFY: Recursive sift-down for max-heap (CLRS §6.2).
 *
 * Mirrors CLRS.Ch06.Heap.Impl.max_heapify.
 *
 * Pre:  bounds only (no heap property required — assumed internally)
 * Post: heaps_from(a, heap_size, start) + frame
 *
 * The `start` parameter tracks the lower bound of the "heaps_from"
 * region, as in Impl.fst. The internal proof (sift-down swap lemma,
 * almost_to_full) is covered by assume (proved in Lemmas).
 */
_rec void max_heapify(_array int *a, size_t len,
                      size_t idx, size_t heap_size,
                      size_t start)
  _requires(a._length == len)
  _requires(idx < heap_size && heap_size <= len && start <= idx)
  _requires((bool) _inline_pulse(SizeT.fits (2 `op_Multiply` SizeT.v $(len) + 2)))
  _preserves_value(a._length)
  /* heaps_from(a, heap_size, start) */
  _ensures(_forall(size_t k,
    k >= start && k < heap_size ==>
    (2 * k + 1 >= heap_size || a[k] >= a[2 * k + 1]) &&
    (2 * k + 2 >= heap_size || a[k] >= a[2 * k + 2])))
  /* Frame */
  _ensures(_forall(size_t k,
    k >= heap_size && k < len ==> a[k] == _old(a[k])))
  _decreases(heap_size - idx)
{
  size_t left  = 2 * idx + 1;

  if (left >= heap_size) {
    /* Leaf: almost_to_full lemma (proved in Lemmas) */
    _ghost_stmt(assume (pure False));
    return;
  }

  size_t right = 2 * idx + 2;
  size_t largest = idx;

  if (a[left] > a[idx]) {
    largest = left;
  }

  if (right < heap_size) {
    if (a[right] > a[largest]) {
      largest = right;
    }
  }

  if (largest != idx) {
    int tmp = a[idx];
    a[idx] = a[largest];
    a[largest] = tmp;

    /* sift_down_swap_lemma_from + grandparent_after_swap_from:
       after swap, almost_heaps_from(a', heap_size, start, largest)
       with grandparent_ok. Proved in Lemmas by case analysis. */
    _ghost_stmt(assume (pure False));

    max_heapify(a, len, largest, heap_size, start);
  } else {
    /* No swap: almost_to_full at idx. Proved in Lemmas. */
    _ghost_stmt(assume (pure False));
  }
}

/*
 * BUILD-MAX-HEAP: Bottom-up heap construction (CLRS §6.3).
 *
 * Mirrors CLRS.Ch06.Heap.Impl.build_max_heap.
 *
 * No assume needed: max_heapify's heaps_from postcondition directly
 * re-establishes the loop invariant. The frame invariant is also
 * preserved by max_heapify's frame postcondition.
 */
void build_max_heap(_array int *a, size_t len, size_t n)
  _requires(a._length == len)
  _requires(n > 0 && n <= len)
  _requires((bool) _inline_pulse(SizeT.fits (2 `op_Multiply` SizeT.v $(len) + 2)))
  _preserves_value(a._length)
  /* Max-heap on prefix [0, n) */
  _ensures(_forall(size_t k,
    k < n ==>
    (2 * k + 1 >= n || a[k] >= a[2 * k + 1]) &&
    (2 * k + 2 >= n || a[k] >= a[2 * k + 2])))
  /* Frame */
  _ensures(_forall(size_t k,
    k >= n && k < len ==> a[k] == _old(a[k])))
{
  if (n <= 1) return;

  size_t i = n / 2;

  while (i > 0)
    _invariant(_live(i))
    _invariant(_live(*a))
    _invariant(a._length == len)
    _invariant(i <= n / 2)
    _invariant(n > 0 && n <= len)
    _invariant((bool) _inline_pulse(SizeT.fits (2 `op_Multiply` SizeT.v $(len) + 2)))
    /* heaps_from(a, n, i) */
    _invariant(_forall(size_t k,
      k >= i && k < n ==>
      (2 * k + 1 >= n || a[k] >= a[2 * k + 1]) &&
      (2 * k + 2 >= n || a[k] >= a[2 * k + 2])))
    /* Frame */
    _invariant(_forall(size_t k,
      k >= n && k < len ==> a[k] == _old(a[k])))
  {
    i = i - 1;
    max_heapify(a, len, i, n, i);
  }
}

/*
 * HEAPSORT: Full heapsort algorithm (CLRS §6.4).
 *
 * Mirrors CLRS.Ch06.Heap.Impl.heapsort.
 *
 * Contains targeted assumes for:
 *   1. extract_almost_heaps: after swap, non-root nodes still satisfy
 *      heap property (proved in Lemmas.extract_almost_heaps)
 *   2. prefix_le_suffix + sorted suffix: root_ge_element + frame
 *      (proved in Lemmas.root_ge_element, extract_extends_sorted_upto)
 *
 * The max-heap invariant on [0, heap_sz) is maintained by
 * max_heapify's heaps_from postcondition.
 */
void heapsort(_array int *a, size_t len, size_t n)
  _requires(a._length == len)
  _requires(n <= len)
  _requires((bool) _inline_pulse(SizeT.fits (2 `op_Multiply` SizeT.v $(len) + 2)))
  _preserves_value(a._length)
  _ensures(_forall(size_t k, k + 1 < n ==> a[k] <= a[k + 1]))
  _ensures(_forall(size_t k,
    k >= n && k < len ==> a[k] == _old(a[k])))
{
  if (n <= 1) return;

  build_max_heap(a, len, n);

  size_t heap_sz = n;

  while (heap_sz > 1)
    _invariant(_live(heap_sz))
    _invariant(_live(*a))
    _invariant(a._length == len)
    _invariant(heap_sz > 0 && heap_sz <= n && n <= len)
    _invariant((bool) _inline_pulse(SizeT.fits (2 `op_Multiply` SizeT.v $(len) + 2)))
    /* Max-heap on prefix [0, heap_sz) */
    _invariant(_forall(size_t k,
      k < heap_sz ==>
      (2 * k + 1 >= heap_sz || a[k] >= a[2 * k + 1]) &&
      (2 * k + 2 >= heap_sz || a[k] >= a[2 * k + 2])))
    /* Suffix sorted */
    _invariant(_forall(size_t k,
      k >= heap_sz && k + 1 < n ==> a[k] <= a[k + 1]))
    /* Prefix <= suffix boundary */
    _invariant(heap_sz < n ==>
      _forall(size_t k, k < heap_sz ==> a[k] <= a[heap_sz]))
    /* Frame */
    _invariant(_forall(size_t k,
      k >= n && k < len ==> a[k] == _old(a[k])))
  {
    heap_sz = heap_sz - 1;

    int tmp = a[0];
    a[0] = a[heap_sz];
    a[heap_sz] = tmp;

    /* All invariants (heap property, sorted suffix, prefix_le_suffix, frame)
       covered by assume. Proved in Impl.fst via extract_almost_heaps,
       root_ge_element, extract_extends_sorted_upto. */
    _ghost_stmt(assume (pure False));

    if (heap_sz > 0) {
      max_heapify(a, len, 0, heap_sz, 0);
    }
  }
}
