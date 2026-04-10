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
 *   - Element bounding (max_heapify bounded postcondition)
 *   - Sortedness (heapsort postcondition)
 *
 * All three functions are ASSUME-FREE.
 *
 * max_heapify: heaps_from + bounded postconditions proved via
 *   almost_heaps_from + grandparent_ok preconditions. The bounded
 *   postcondition (a[k] <= bound) carries through the recursion.
 * build_max_heap: assume-free; max_heapify's postcondition suffices.
 * heapsort: assume-free; uses root_ge_element_bridge (inductive lemma)
 *   to establish bounded precondition for max_heapify after swap.
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
 * Pre:  almost_heaps_from + grandparent_ok + bounded
 * Post: heaps_from + bounded + frame
 *
 * The `start` parameter tracks the lower bound of the "heaps_from"
 * region, as in Impl.fst. The `bound` parameter carries an upper
 * bound on element values through the recursion (used by heapsort
 * to establish prefix_le_suffix after extract-max).
 */
_rec void max_heapify(_array int *a, size_t len,
                      size_t idx, size_t heap_size,
                      size_t start, int bound)
  _requires(a._length == len)
  _requires(idx < heap_size && heap_size <= len && start <= idx)
  _requires((bool) _inline_pulse(SizeT.fits (2 `op_Multiply` SizeT.v $(len) + 2)))
  /* almost_heaps_from(a, heap_size, start, idx) */
  _requires(_forall(size_t k,
    !(k >= start && k < heap_size && k != idx) ||
    ((2 * k + 1 >= heap_size || a[k] >= a[2 * k + 1]) &&
     (2 * k + 2 >= heap_size || a[k] >= a[2 * k + 2]))))
  /* grandparent_ok */
  _requires(idx == 0 || (idx - 1) / 2 < start ||
    ((2 * idx + 1 >= heap_size || a[(idx - 1) / 2] >= a[2 * idx + 1]) &&
     (2 * idx + 2 >= heap_size || a[(idx - 1) / 2] >= a[2 * idx + 2])))
  /* bounded: all elements in [start, heap_size) are <= bound */
  _requires(_forall(size_t k,
    !(k >= start && k < heap_size) || a[k] <= bound))
  _preserves_value(a._length)
  /* heaps_from(a, heap_size, start) */
  _ensures(_forall(size_t k,
    k >= start && k < heap_size ==>
    (2 * k + 1 >= heap_size || a[k] >= a[2 * k + 1]) &&
    (2 * k + 2 >= heap_size || a[k] >= a[2 * k + 2])))
  /* bounded preserved */
  _ensures(_forall(size_t k,
    !(k >= start && k < heap_size) || a[k] <= bound))
  /* Frame */
  _ensures(_forall(size_t k,
    k >= heap_size && k < len ==> a[k] == _old(a[k])))
  _decreases(heap_size - idx)
{
  size_t left  = 2 * idx + 1;

  if (left >= heap_size) {
    /* Leaf: heap_down_at(idx) trivially true (no children in range),
       combined with almost_heaps_from ==> heaps_from. Bounded unchanged. */
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

    /* After swap: bounded preserved since both idx and largest are
       in [start, heap_size) and we just exchanged their values.
       heap_down_at(idx) holds, almost_heaps_from for recursive call,
       grandparent_ok from old heap_down_at(largest). */

    max_heapify(a, len, largest, heap_size, start, bound);
  } else {
    /* No swap: a[idx] >= children, heap_down_at(idx) holds.
       Combined with almost_heaps_from ==> heaps_from. Bounded unchanged. */
  }
}

/*
 * BUILD-MAX-HEAP: Bottom-up heap construction (CLRS §6.3).
 *
 * Mirrors CLRS.Ch06.Heap.Impl.build_max_heap.
 *
 * No assume needed: max_heapify's heaps_from postcondition directly
 * re-establishes the loop invariant. Passes INT32_MAX as bound
 * (trivially satisfied for all Int32 values).
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
    max_heapify(a, len, i, n, i, 2147483647);
  }
}

/*
 * HEAPSORT: Full heapsort algorithm (CLRS §6.4).
 *
 * Mirrors CLRS.Ch06.Heap.Impl.heapsort.
 *
 * ASSUME-FREE: Uses root_ge_element_bridge to establish that the
 * root dominates all heap elements (an inductive fact that SMT
 * cannot derive alone). This provides the bounded precondition
 * for max_heapify, which in turn gives prefix_le_suffix.
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
    /* Root dominance: forall k < heap_sz: a[k] <= a[0].
       This is an inductive fact (root_ge_element) that SMT cannot
       derive from heap_down_at alone. The bridge lemma converts
       the c2pulse heap invariant to the Spec predicate and calls
       the inductive root_ge_element lemma. */
#undef assert
    _ghost_stmt(let _va = array_value_of (!var_a));
    _ghost_stmt(
      CLRS.Ch06.Heap.C.BridgeLemmas.root_ge_element_bridge _va (!var_heap_sz)
    );
#define assert(x) __c2pulse_c_assert(x)

    heap_sz = heap_sz - 1;

    int tmp = a[0];
    a[0] = a[heap_sz];
    a[heap_sz] = tmp;

    /* After swap, all elements in [0, heap_sz) are <= tmp = old root.
       - tmp = old a[0], the max-heap root
       - root_ge_element: forall k < old_heap_sz: a_old[k] <= a_old[0] = tmp
       - After swap: a'[0] = a_old[heap_sz] <= tmp, a'[k] = a_old[k] <= tmp
       - max_heapify bounded postcondition preserves: a_new[k] <= tmp
       - Frame: a_new[heap_sz] = tmp
       - prefix_le_suffix: a_new[k] <= tmp = a_new[heap_sz]
       - suffix_sorted at boundary: tmp = a_old[0] <= a_old[old_heap_sz]
         = a_new[heap_sz+1] from old prefix_le_suffix */
    max_heapify(a, len, 0, heap_sz, 0, tmp);
  }
}
