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
  /* Permutation: result is a rearrangement of input */
  _ensures((bool) _inline_pulse(
    FStar.Seq.Properties.permutation (option Int32.t)
      (old (array_value_of $(a)))
      (array_value_of $(a))))
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
    /* Capture pre-swap state for permutation proof */
#undef assert
    _ghost_stmt(let _pre_swap = array_value_of (!var_a));
#define assert(x) __c2pulse_c_assert(x)

    int tmp = a[idx];
    a[idx] = a[largest];
    a[largest] = tmp;

    /* After swap: establish permutation pre_swap -> current */
#undef assert
    _ghost_stmt(
      CLRS.Ch06.Heap.C.BridgeLemmas.swap_option_perm _pre_swap (SizeT.v (!var_idx)) (SizeT.v (!var_largest))
    );
#define assert(x) __c2pulse_c_assert(x)

    max_heapify(a, len, largest, heap_size, start, bound);

    /* Compose: permutation pre_swap post_swap (swap_option_perm)
               + permutation post_swap current (recursive postcondition)
               = permutation pre_swap current */
#undef assert
    _ghost_stmt(
      CLRS.Ch06.Heap.C.BridgeLemmas.option_perm_trans
        _pre_swap
        (Seq.upd (Seq.upd _pre_swap (SizeT.v (!var_idx)) (Seq.index _pre_swap (SizeT.v (!var_largest)))) (SizeT.v (!var_largest)) (Seq.index _pre_swap (SizeT.v (!var_idx))))
        (array_value_of (!var_a))
    );
#define assert(x) __c2pulse_c_assert(x)
  } else {
    /* No swap: permutation is reflexive */
#undef assert
    _ghost_stmt(
      CLRS.Ch06.Heap.C.BridgeLemmas.option_perm_refl (array_value_of (!var_a))
    );
#define assert(x) __c2pulse_c_assert(x)
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
  /* Permutation */
  _ensures((bool) _inline_pulse(
    FStar.Seq.Properties.permutation (option Int32.t)
      (old (array_value_of $(a)))
      (array_value_of $(a))))
{
  if (n <= 1) return;

  /* Capture initial state for permutation composition in loop body */
#undef assert
  _ghost_stmt(let _init_seq = array_value_of (!var_a));
#define assert(x) __c2pulse_c_assert(x)

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
    /* Permutation: current array is a permutation of initial */
    _invariant((bool) _inline_pulse(
      FStar.Seq.Properties.permutation (option Int32.t)
        _init_seq
        (array_value_of $(a))))
  {
#undef assert
    _ghost_stmt(let _pre_iter = array_value_of (!var_a));
#define assert(x) __c2pulse_c_assert(x)
    i = i - 1;
    max_heapify(a, len, i, n, i, 2147483647);
    /* Compose: permutation _init_seq pre_iter (invariant) +
                permutation pre_iter post_iter (max_heapify postcondition) */
#undef assert
    _ghost_stmt(
      CLRS.Ch06.Heap.C.BridgeLemmas.option_perm_trans
        _init_seq
        _pre_iter
        (array_value_of (!var_a))
    );
#define assert(x) __c2pulse_c_assert(x)
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
  /* Permutation */
  _ensures((bool) _inline_pulse(
    FStar.Seq.Properties.permutation (option Int32.t)
      (old (array_value_of $(a)))
      (array_value_of $(a))))
{
  if (n <= 1) return;

  /* Capture pre-build state for final permutation composition */
#undef assert
  _ghost_stmt(let _orig_seq = array_value_of (!var_a));
#define assert(x) __c2pulse_c_assert(x)

  build_max_heap(a, len, n);

  /* Capture state after build_max_heap for permutation composition */
#undef assert
  _ghost_stmt(let _init_seq = array_value_of (!var_a));
#define assert(x) __c2pulse_c_assert(x)

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
    /* Permutation: current is permutation of post-build_max_heap */
    _invariant((bool) _inline_pulse(
      FStar.Seq.Properties.permutation (option Int32.t)
        _init_seq
        (array_value_of $(a))))
  {
    /* Root dominance: forall k < heap_sz: a[k] <= a[0]. */
#undef assert
    _ghost_stmt(let _pre_iter = array_value_of (!var_a));
    _ghost_stmt(
      CLRS.Ch06.Heap.C.BridgeLemmas.root_ge_element_bridge _pre_iter (!var_heap_sz)
    );
#define assert(x) __c2pulse_c_assert(x)

    heap_sz = heap_sz - 1;

    /* Capture pre-swap state */
#undef assert
    _ghost_stmt(let _pre_swap = array_value_of (!var_a));
#define assert(x) __c2pulse_c_assert(x)

    int tmp = a[0];
    a[0] = a[heap_sz];
    a[heap_sz] = tmp;

    /* swap permutation proof */
#undef assert
    _ghost_stmt(
      CLRS.Ch06.Heap.C.BridgeLemmas.swap_option_perm _pre_swap 0 (SizeT.v (!var_heap_sz))
    );
#define assert(x) __c2pulse_c_assert(x)

    max_heapify(a, len, 0, heap_sz, 0, tmp);

    /* Compose permutation chain:
       pre_swap -> post_swap (swap_option_perm)
       post_swap -> current (max_heapify postcondition)
       pre_iter -> pre_swap (equal, heap_sz decrement doesn't change array)
       _init_seq -> pre_iter (loop invariant) */
#undef assert
    _ghost_stmt(
      CLRS.Ch06.Heap.C.BridgeLemmas.option_perm_trans
        _pre_swap
        (Seq.upd (Seq.upd _pre_swap 0 (Seq.index _pre_swap (SizeT.v (!var_heap_sz)))) (SizeT.v (!var_heap_sz)) (Seq.index _pre_swap 0))
        (array_value_of (!var_a))
    );
    _ghost_stmt(
      CLRS.Ch06.Heap.C.BridgeLemmas.option_perm_trans
        _pre_iter
        _pre_swap
        (array_value_of (!var_a))
    );
    _ghost_stmt(
      CLRS.Ch06.Heap.C.BridgeLemmas.option_perm_trans
        _init_seq
        _pre_iter
        (array_value_of (!var_a))
    );
#define assert(x) __c2pulse_c_assert(x)
  }

  /* Final composition: old -> post_build (build_max_heap postcond)
                         + post_build -> final (loop) */
#undef assert
  _ghost_stmt(
    CLRS.Ch06.Heap.C.BridgeLemmas.option_perm_trans
      _orig_seq
      _init_seq
      (array_value_of (!var_a))
  );
#define assert(x) __c2pulse_c_assert(x)
}
