.. _Ch06_Heapsort:

########################################
Heapsort
########################################

This chapter covers the heapsort algorithm from CLRS Chapter 6.
The implementation follows the textbook structure: MAX-HEAPIFY
(§6.2), BUILD-MAX-HEAP (§6.3), and the full HEAPSORT (§6.4). The
algorithm is fully verified in Pulse with **zero admits, assumes,
or assume\_ calls**. We prove:

1. The output is sorted.
2. The output is a permutation of the input.
3. The number of comparisons is O(n log n).

Additionally, an enhanced Complexity module proves BUILD-MAX-HEAP
runs in O(n) (CLRS Theorem 6.3) and that heapsort beats quadratic
sorting for n ≥ 11.

Heap Predicates
===============

The formalization uses implicit (array-based) binary heaps. The
standard index arithmetic maps parent-child relationships:

.. literalinclude:: ../autoclrs/ch06-heapsort/CLRS.Ch06.Heap.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: heap_indices
   :end-before: //SNIPPET_END: heap_indices

The max-heap property and its relaxed variants are defined as
predicates over a prefix of length ``len``:

.. literalinclude:: ../autoclrs/ch06-heapsort/CLRS.Ch06.Heap.Spec.fst
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

.. literalinclude:: ../autoclrs/ch06-heapsort/CLRS.Ch06.Heap.Impl.fsti
   :language: pulse
   :start-after: //SNIPPET_START: max_heapify_sig
   :end-before: //SNIPPET_END: max_heapify_sig

Reading this signature:

- **Precondition**: the heap property holds everywhere from
  ``start`` onward except at ``idx`` (``almost_heaps_from``). A
  *grandparent condition* ensures the parent of ``idx`` (if it
  exists and is in range) still dominates ``idx``'s children.
- **Postcondition**: the heap property holds for all nodes from
  ``start`` (``heaps_from``), the result is a permutation, elements
  outside the heap prefix are unchanged, and the cost is bounded by
  ``max_heapify_bound(heap_size, idx) = 2·⌊log₂(heap_size/(idx+1))⌋``.

The implementation examines the left and right children of ``idx``,
swaps with the larger child if it exceeds the current node, and
recurses. The proof uses ``sift_down_swap_lemma_from`` to show that
after swapping parent ``p`` with child ``ch``:

- ``heap_down_at`` holds at ``p`` (the parent now has the larger
  value).
- ``heap_down_at`` is preserved at all other nodes.
- The defect moves to ``ch`` (giving ``almost_heaps_from`` with
  ``bad = ch``).

Strongest Guarantee
~~~~~~~~~~~~~~~~~~~

The postcondition fully restores the heap property from ``start``
onward (not just at ``idx``). The permutation guarantee chains
through all recursive swap steps.

Limitations
~~~~~~~~~~~

The ``start`` ghost parameter is not in CLRS — it tracks the lower
bound of the ``heaps_from`` region. The ``SZ.fits(2n+2)``
precondition prevents SizeT overflow in child index computation.
The cost bound counts 2 comparisons per non-leaf level (finding
the maximum of ``{parent, left, right}``).

BUILD-MAX-HEAP
==============

``build_max_heap`` converts an arbitrary array into a max-heap via
bottom-up heapification (CLRS §6.3):

.. literalinclude:: ../autoclrs/ch06-heapsort/CLRS.Ch06.Heap.Impl.fsti
   :language: pulse
   :start-after: //SNIPPET_START: build_max_heap_sig
   :end-before: //SNIPPET_END: build_max_heap_sig

The loop starts at ``⌊n/2⌋`` and calls ``max_heapify``
on each node down to index 0. The invariant maintains
``heaps_from s_cur n vi`` — all nodes from ``vi`` onward satisfy
the heap property. At loop exit, ``vi = 0`` gives ``is_max_heap``.

Strongest Guarantee
~~~~~~~~~~~~~~~~~~~

A full ``is_max_heap`` is established over the entire prefix.
The permutation guarantee chains through all max_heapify calls.

Limitations
~~~~~~~~~~~

The linked cost bound ``build_cost_bound(n) = (n/2) × max_heapify_bound(n, 0)``
is O(n log n), **not** the tight O(n) from CLRS Theorem 6.3. The
O(n) analysis is proven separately in the pure Complexity module
(see below) but uses a different cost model.

HEAPSORT
========

The main ``heapsort`` function:

.. literalinclude:: ../autoclrs/ch06-heapsort/CLRS.Ch06.Heap.Impl.fsti
   :language: pulse
   :start-after: //SNIPPET_START: heapsort_sig
   :end-before: //SNIPPET_END: heapsort_sig

The postcondition guarantees ``sorted s``, ``permutation s0 s``,
and the cost bound ``cf - c0 <= heapsort_cost_bound(n)``. The
implementation proceeds in two phases.

Phase 1: BUILD-MAX-HEAP
~~~~~~~~~~~~~~~~~~~~~~~~

Calls ``build_max_heap`` as a standalone function to establish
``is_max_heap`` over the entire array.

Phase 2: Extract-Max Loop
~~~~~~~~~~~~~~~~~~~~~~~~~

The extract-max loop repeatedly swaps the root (maximum) to the
end of the heap, shrinks the heap, and calls ``max_heapify`` to
restore the property:

.. literalinclude:: ../autoclrs/ch06-heapsort/CLRS.Ch06.Heap.Impl.fst
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
all existing suffix elements, it extends the sorted suffix by one.

The lemma ``perm_preserves_sorted_suffix`` is the most intricate
proof: it shows that when ``max_heapify`` permutes the prefix, the
suffix remains sorted and the cross-region ordering is preserved.

Strongest Guarantee
~~~~~~~~~~~~~~~~~~~

Full functional correctness: ``sorted`` + ``permutation``. The cost
is bounded by ``heapsort_cost_bound(n) = build_cost_bound(n) + extract_cost_bound(n)``.

Limitations
~~~~~~~~~~~

The linked cost bound expands to ``(n/2 + n-1) × max_heapify_bound(n, 0)``.
The CostBound module proves ``heapsort_cost_bound n <= 4n·log₂ n``.
The pure Complexity module proves tighter bounds (6n(1+log₂ n), beats
n² for n≥11) but these are for a different cost model.

Complexity
==========

The Complexity module defines pure operation counts for each phase
and proves O(n log n) bounds following CLRS §6.3–6.4.

BUILD-MAX-HEAP is O(n)
~~~~~~~~~~~~~~~~~~~~~~~

CLRS Theorem 6.3: the sum ∑ ⌈n/2^(h+1)⌉ · 2h over all heights h
converges to at most 4n. The proof decomposes the ceiling into a
floor term and a correction, bounds the floor sum using the identity
∑ h·2^(H−h) = 2^(H+1) − H − 2, and bounds the correction by
h(h+1) ≤ 2·2^h ≤ 2n:

.. literalinclude:: ../autoclrs/ch06-heapsort/CLRS.Ch06.Heap.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: build_heap_ops_linear
   :end-before: //SNIPPET_END: build_heap_ops_linear

HEAPSORT O(n log n)
~~~~~~~~~~~~~~~~~~~

Overall bound with constant 6:

.. literalinclude:: ../autoclrs/ch06-heapsort/CLRS.Ch06.Heap.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: heapsort_ops_simplified
   :end-before: //SNIPPET_END: heapsort_ops_simplified

The bound 6n(1 + ⌊log₂ n⌋) follows from combining the O(n)
build-heap cost (≤ 4n) with the extract-max loop cost
(≤ 2n·⌊log₂ n⌋).

Heapsort Beats Quadratic
~~~~~~~~~~~~~~~~~~~~~~~~~

For n ≥ 11:

.. literalinclude:: ../autoclrs/ch06-heapsort/CLRS.Ch06.Heap.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: heapsort_better_than_quadratic
   :end-before: //SNIPPET_END: heapsort_better_than_quadratic

The proof uses ``heapsort_practical_bound`` (≤ 2n·log₂ n + 4n)
and then shows 2·log₂ n + 4 < n for n ≥ 11.

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
   preserves the cross-region ordering.

5. **Geometric series for BUILD-MAX-HEAP**: The O(n) proof
   evaluates the weighted power-of-two sum exactly
   (2^(H+1) − H − 2) and uses it to bound the floor-division
   terms, following the CLRS Theorem 6.3 argument.

6. **Dual cost models**: The CostBound module provides ghost-counter-linked
   bounds per max_heapify call. The Complexity module provides tighter
   pure bounds by summing over heights. Both are proven correct; they
   serve different purposes.

All proofs in this chapter are fully verified with **zero admits**.
