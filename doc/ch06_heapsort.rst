.. _Ch06_Heapsort:

########################################
Heapsort
########################################

This chapter covers the heapsort algorithm from CLRS Chapter 6.
The implementation follows the textbook structure: BUILD-MAX-HEAP
(§6.3) followed by the extract-max loop (§6.4). The algorithm is
fully verified in Pulse with **zero admits, assumes, or assume_
calls**. We prove:

1. The output is sorted.
2. The output is a permutation of the input.
3. The number of comparisons is O(n log n).

Additionally, an enhanced complexity module proves BUILD-MAX-HEAP
runs in O(n) (CLRS Theorem 6.3) and that heapsort beats quadratic
sorting for n ≥ 11.

Heap Predicates
===============

The formalization uses implicit (array-based) binary heaps. The
standard index arithmetic maps parent-child relationships:

.. literalinclude:: ../ch06-heapsort/CLRS.Ch06.Heap.fst
   :language: fstar
   :start-after: //SNIPPET_START: heap_indices
   :end-before: //SNIPPET_END: heap_indices

The max-heap property and its relaxed variants are defined as
predicates over a prefix of length ``len``:

.. literalinclude:: ../ch06-heapsort/CLRS.Ch06.Heap.fst
   :language: fstar
   :start-after: //SNIPPET_START: heap_predicates
   :end-before: //SNIPPET_END: heap_predicates

``heap_down_at s len i`` says node ``i`` dominates its children
(within the heap boundary). ``is_max_heap`` requires this for all
nodes. ``almost_heaps_from s len k bad`` relaxes the property: all
nodes from ``k`` onward satisfy it *except* possibly at index
``bad``. This is the key abstraction for the sift-down loop — after
a swap, only the swapped child may violate the heap property.

MAX-HEAPIFY
===========

``max_heapify`` is a recursive Pulse function that restores the
heap property at a single node by sifting it down:

.. literalinclude:: ../ch06-heapsort/CLRS.Ch06.Heap.fst
   :language: pulse
   :start-after: //SNIPPET_START: max_heapify_sig
   :end-before: //SNIPPET_END: max_heapify_sig

Reading this signature:

- **Precondition**: the heap property holds everywhere from
  ``start`` onward except at ``idx`` (``almost_heaps_from``). A
  *grandparent condition* ensures the parent of ``idx`` (if it
  exists and is in range) still dominates ``idx``'s children.
- **Postcondition**: the heap property holds for all nodes from
  ``start`` (``heaps_from``), the result is a permutation, and
  elements outside the heap prefix are unchanged.

The implementation examines the left and right children of ``idx``,
swaps with the larger child if it exceeds the current node, and
recurses. The proof uses ``sift_down_swap_lemma_from`` to show that
after swapping parent ``p`` with child ``ch``:

- ``heap_down_at`` holds at ``p`` (the parent now has the larger
  value).
- ``heap_down_at`` is preserved at all other nodes (via case
  analysis on whether their children overlap with ``{p, ch}``).
- The defect moves to ``ch`` (giving ``almost_heaps_from`` with
  ``bad = ch``).

Heapsort
========

The main ``heapsort`` function:

.. literalinclude:: ../ch06-heapsort/CLRS.Ch06.Heap.fst
   :language: pulse
   :start-after: //SNIPPET_START: heapsort_sig
   :end-before: //SNIPPET_END: heapsort_sig

The postcondition guarantees both sortedness and that the result
is a permutation of the input. The implementation proceeds in two
phases.

Phase 1: BUILD-MAX-HEAP
~~~~~~~~~~~~~~~~~~~~~~~~

The bottom-up loop starts at ``⌊n/2⌋`` and calls ``max_heapify``
on each node down to index 0:

.. literalinclude:: ../ch06-heapsort/CLRS.Ch06.Heap.fst
   :language: pulse
   :start-after: //SNIPPET_START: build_max_heap_loop
   :end-before: //SNIPPET_END: build_max_heap_loop

The invariant maintains ``heaps_from s_cur n vi`` — all nodes from
``vi`` onward satisfy the heap property. Initially ``vi = ⌊n/2⌋``,
and leaves (indices ≥ ⌊n/2⌋) trivially satisfy the property. Each
iteration decrements ``vi`` and calls ``max_heapify`` to establish
the property at the new node. At loop exit, ``vi = 0`` gives
``is_max_heap``.

Phase 2: Extract-Max Loop
~~~~~~~~~~~~~~~~~~~~~~~~~

The extract-max loop repeatedly swaps the root (maximum) to the
end of the heap, shrinks the heap, and calls ``max_heapify`` to
restore the property:

.. literalinclude:: ../ch06-heapsort/CLRS.Ch06.Heap.fst
   :language: pulse
   :start-after: //SNIPPET_START: extract_max_loop
   :end-before: //SNIPPET_END: extract_max_loop

The invariant maintains three properties simultaneously:

- ``is_max_heap s_cur vsz``: the prefix is a valid max-heap.
- ``suffix_sorted s_cur vsz``: elements at indices ≥ ``vsz`` are
  sorted.
- ``prefix_le_suffix s_cur vsz``: every element in the heap prefix
  is ≤ every element in the sorted suffix.

At each iteration, the root (the maximum of the prefix) is swapped
to position ``vsz - 1``. Since it is ≥ all prefix elements and ≤
all existing suffix elements (by ``prefix_le_suffix``), it extends
the sorted suffix by one position.

The lemma ``perm_preserves_sorted_suffix`` is the most intricate
proof in this module: it shows that when ``max_heapify`` permutes
the prefix, the suffix remains sorted and the cross-region ordering
is preserved. This uses element counting (``SeqP.count``) to argue
that every element in the new prefix also appeared in the old
prefix, and hence is bounded by the suffix elements.

Complexity
==========

The basic complexity module defines the comparison count and proves
the O(n log n) bound:

.. literalinclude:: ../ch06-heapsort/CLRS.Ch06.Heap.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: heapsort_comparisons
   :end-before: //SNIPPET_END: heapsort_comparisons

.. literalinclude:: ../ch06-heapsort/CLRS.Ch06.Heap.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: heapsort_simplified_bound
   :end-before: //SNIPPET_END: heapsort_simplified_bound

The bound 2n(1 + ⌊log₂ n⌋) follows from bounding each
``max_heapify`` call by 2⌊log₂ n⌋ comparisons and summing over
n − 1 extract-max iterations plus the build-heap cost of 2n.

Enhanced Complexity Analysis
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The enhanced module proves tighter results following CLRS more
closely.

**BUILD-MAX-HEAP is O(n)** (CLRS Theorem 6.3): the sum
∑ ⌈n/2^(h+1)⌉ · 2h over all heights h converges to at most 4n.
The proof decomposes the ceiling into a floor term and a correction,
bounds the floor sum using the identity
∑ h·2^(H−h) = 2^(H+1) − H − 2, and bounds the correction by
h(h+1) ≤ 2·2^h ≤ 2n:

.. literalinclude:: ../ch06-heapsort/CLRS.Ch06.Heap.Complexity.Enhanced.fst
   :language: fstar
   :start-after: //SNIPPET_START: build_heap_ops_linear
   :end-before: //SNIPPET_END: build_heap_ops_linear

**Overall O(n log n)** with constant 6:

.. literalinclude:: ../ch06-heapsort/CLRS.Ch06.Heap.Complexity.Enhanced.fst
   :language: fstar
   :start-after: //SNIPPET_START: heapsort_ops_simplified
   :end-before: //SNIPPET_END: heapsort_ops_simplified

**Heapsort beats quadratic sorting** for n ≥ 11:

.. literalinclude:: ../ch06-heapsort/CLRS.Ch06.Heap.Complexity.Enhanced.fst
   :language: fstar
   :start-after: //SNIPPET_START: heapsort_better_than_quadratic
   :end-before: //SNIPPET_END: heapsort_better_than_quadratic

Proof Techniques Summary
=========================

1. **Almost-heap abstraction**: The ``almost_heaps_from`` predicate
   localizes the heap violation to a single index, enabling clean
   inductive reasoning in ``max_heapify``.

2. **Sift-down swap lemma**: Case analysis over parent-child
   relationships (using injectivity of ``left_idx`` and
   ``right_idx``, plus ``left_neq_right``) proves that a swap
   only disturbs the heap property at the child.

3. **Three-property extract-max invariant**: Tracking
   ``is_max_heap``, ``suffix_sorted``, and ``prefix_le_suffix``
   simultaneously lets the proof argue that each extracted maximum
   correctly extends the sorted suffix.

4. **Permutation via element counting**: The
   ``perm_preserves_sorted_suffix`` lemma uses ``SeqP.count`` and
   ``SeqP.lemma_mem_count`` to show that permuting the prefix
   preserves the cross-region ordering — a technique applicable
   whenever one region is fixed and the other is permuted.

5. **Geometric series for BUILD-MAX-HEAP**: The O(n) proof
   evaluates the weighted power-of-two sum exactly
   (2^(H+1) − H − 2) and uses it to bound the floor-division
   terms, following the CLRS Theorem 6.3 argument.
