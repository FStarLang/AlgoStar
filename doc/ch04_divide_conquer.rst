.. _Ch04_DivideConquer:

######################################################
Divide & Conquer: Binary Search & Maximum Subarray
######################################################

This chapter covers two divide-and-conquer algorithms from CLRS
Chapter 4: binary search and the maximum subarray problem (§4.1).
Binary search is fully verified with **zero admits** in both its
correctness and O(log n) complexity proofs. The maximum subarray
problem is treated with two algorithms — Kadane's linear-time scan
(zero admits) and the classic divide-and-conquer approach — both
**fully verified with zero admits**, including a proven equivalence
between the two.

Binary Search
=============

CLRS presents binary search as the prototypical divide-and-conquer
search algorithm. Our Pulse implementation follows the standard
pattern: maintain a search interval ``[lo, hi)`` that shrinks by half
at every step.

Specification
~~~~~~~~~~~~~

The sortedness predicate is the standard definition:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_sorted
   :end-before: //SNIPPET_END: is_sorted

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The main theorem is the type signature of ``binary_search``:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.fst
   :language: pulse
   :start-after: //SNIPPET_START: binary_search_sig
   :end-before: //SNIPPET_END: binary_search_sig

Reading this signature:

- **Input**: a sorted array ``a`` with ghost contents ``s0``, length
  ``len``, and search ``key``.
- **Postcondition**: the result is either a valid index where
  ``s0[result] == key``, or ``len`` if the key is absent from the
  entire array.

The implementation uses a *found flag* pattern to simulate early
exit from a Pulse ``while`` loop. This is a key Pulse idiom: the
loop condition is ``!lo <^ !hi && not !found``, and the invariant
tracks two cases depending on the flag.

Loop Invariant
~~~~~~~~~~~~~~

The loop invariant maintains that the key, if present, must lie in
the interval ``[lo, hi)``:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.fst
   :language: pulse
   :start-after: //SNIPPET_START: binary_search_loop
   :end-before: //SNIPPET_END: binary_search_loop

The invariant splits into two cases:

1. **Found** (``vfound = true``): ``result`` is a valid index with
   ``s0[result] == key``.
2. **Not found** (``vfound = false``): the key is not in
   ``[0, lo)`` or ``[hi, len)``, and any occurrence must lie in
   ``[lo, hi)``.

When the loop exits with ``not found`` and ``lo >= hi``, the
interval is empty, so the key is absent from the entire array.

Note the sorted property is restated in the invariant with an
explicit SMT pattern ``{:pattern Seq.index s0 i; Seq.index s0 j}``
to help the solver efficiently reason about element ordering.

Complexity
~~~~~~~~~~

The complexity-instrumented version proves an O(log n) bound — at
most ⌊log₂ n⌋ + 1 comparisons:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: log2f
   :end-before: //SNIPPET_END: log2f

The complexity bound predicate:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bounded_log
   :end-before: //SNIPPET_END: complexity_bounded_log

The full signature threads a ghost counter:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: binary_search_complexity_sig
   :end-before: //SNIPPET_END: binary_search_complexity_sig

The proof relies on ``lemma_log2f_step``: when the search range
shrinks from ``old_range`` to at most ``old_range / 2``, one
comparison is consumed and ``log2f`` decreases by at least 1. The
loop invariant tracks a *remaining budget*: the comparisons used
so far plus ``log2f`` of the remaining range never exceeds
``log2f`` of the original length.

Maximum Subarray — Kadane's Algorithm
=====================================

CLRS §4.1 introduces the maximum subarray problem and solves it
with a divide-and-conquer algorithm in O(n lg n). Kadane's
algorithm is the well-known O(n) improvement. We verify Kadane's
algorithm in Pulse with full correctness and complexity proofs.

Pure Specification
~~~~~~~~~~~~~~~~~~

The specification models Kadane's recurrence as a pure recursive
function:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.Kadane.fst
   :language: fstar
   :start-after: //SNIPPET_START: kadane_spec
   :end-before: //SNIPPET_END: kadane_spec

At each position ``i``, ``current_sum`` tracks the maximum subarray
sum ending at ``i`` (either extend the previous subarray or start
fresh), and ``best_sum`` tracks the global maximum seen so far.

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The Pulse implementation signature:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.Kadane.fst
   :language: pulse
   :start-after: //SNIPPET_START: max_subarray_sig
   :end-before: //SNIPPET_END: max_subarray_sig

The postcondition states that the returned value equals
``max_subarray_spec s0`` — the pure specification applied to the
input sequence. The proof strategy is *specification matching*:
the loop invariant asserts that ``kadane_spec`` applied from the
current position with the current accumulators equals ``kadane_spec``
applied from position 0 with initial values. When the loop
completes, this collapses to the desired postcondition.

Complexity
~~~~~~~~~~

The complexity-instrumented version proves the Θ(n) bound:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.Kadane.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bounded_linear
   :end-before: //SNIPPET_END: complexity_bounded_linear

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.Kadane.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: max_subarray_complexity_sig
   :end-before: //SNIPPET_END: max_subarray_complexity_sig

The bound is tight: exactly ``n`` operations (one ghost tick per
element). The loop invariant tracks ``vc == c0 + i``, which at
exit gives ``cf - c0 == n``.

Maximum Subarray — Divide and Conquer
=====================================

The divide-and-conquer algorithm from CLRS §4.1 is implemented as
a pure F* function (not Pulse). It splits the array at the
midpoint, recursively finds the maximum subarray in each half, and
also finds the maximum crossing subarray.

Algorithm Structure
~~~~~~~~~~~~~~~~~~~

The ``sum_range`` helper computes the sum of a contiguous range:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: sum_range
   :end-before: //SNIPPET_END: sum_range

The main recursive function follows CLRS exactly — split, recurse
on left and right, find the crossing subarray, and return the
maximum of the three:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: find_maximum_subarray_dc
   :end-before: //SNIPPET_END: find_maximum_subarray_dc

Correctness
~~~~~~~~~~~

The correctness theorem proves that the returned range has the
claimed sum:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_sum_correct
   :end-before: //SNIPPET_END: dc_sum_correct

The proof proceeds by structural induction on the recursion,
using ``lemma_crossing_sum_correct`` to handle the crossing case
and ``lemma_sum_range_append`` for compositional reasoning about
sums.

Complexity
~~~~~~~~~~

The recurrence ``T(n) = 2T(n/2) + n`` with ``T(1) = 1`` gives
O(n log n):

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_ops_count
   :end-before: //SNIPPET_END: dc_ops_count

The bound ``T(n) ≤ 4n(⌈log₂ n⌉ + 1)`` is proved by induction:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_complexity_bound
   :end-before: //SNIPPET_END: dc_complexity_bound

Equivalence (Proven)
~~~~~~~~~~~~~~~~~~~~~~~~~

The equivalence between the divide-and-conquer result and Kadane's
specification is fully proven — both algorithms compute the unique
maximum over all contiguous subarrays:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_kadane_equivalence
   :end-before: //SNIPPET_END: dc_kadane_equivalence

All proofs in this chapter — binary search correctness and complexity,
Kadane's correctness and complexity, D&C structural correctness and
complexity, and the equivalence theorem — are fully verified with
**zero admits**.

Proof Techniques Summary
=========================

1. **Found-flag early exit**: Pulse ``while`` loops cannot return
   values directly. The pattern uses mutable ``found`` and
   ``result`` variables with the loop condition
   ``!lo <^ !hi && not !found``.

2. **Logarithmic budget tracking**: The binary search complexity
   proof maintains ``comparisons_used + log2f(remaining_range)``
   as a non-increasing quantity, consuming one unit per iteration.

3. **Specification matching**: Rather than proving properties of
   the loop state directly, the Kadane invariant asserts that the
   pure specification evaluated from the current state equals the
   specification from the initial state.

4. **Pure vs. Pulse complexity**: Binary search and Kadane use
   ghost counters in Pulse. The D&C algorithm is pure F*, so its
   complexity is proved by defining ``dc_ops_count`` as a separate
   pure function and bounding it algebraically.
