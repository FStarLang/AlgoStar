.. _Ch09_OrderStats:

############################
Order Statistics (Selection)
############################

This chapter covers algorithms from CLRS Chapter 9 for finding order
statistics — the *k*-th smallest element of an array. We provide three
verified implementations:

- **Min/Max finding** (§9.1): linear-time minimum and maximum with a
  simultaneous min/max variant.
- **Quickselect** (§9.2, CLRS ``RANDOMIZED-SELECT``): partition-based
  selection, O(n²) worst case, O(n) expected.
- **Partial selection sort**: a selection-sort variant (not from CLRS)
  that finds the *k*-th smallest via *k* rounds of min-finding and
  swapping, O(nk) worst case.

All implementations are **fully verified with zero admits**. A rich
pure specification layer (``Spec``, ``Correctness``, ``SortedPerm``)
connects the imperative results to a functional ``select_spec``
defined as the *k*-th element of a sorted permutation.

Min/Max Finding
===============

CLRS §9.1 discusses finding the minimum or maximum of an array in
Θ(n) comparisons. ``find_minimum`` and ``find_maximum`` scan the
array once, proving that the returned value both exists in the array
and is a universal bound.

.. literalinclude:: ../ch09-order-statistics/CLRS.Ch09.MinMax.fst
   :language: pulse
   :start-after: //SNIPPET_START: find_minimum
   :end-before: //SNIPPET_END: find_minimum

.. literalinclude:: ../ch09-order-statistics/CLRS.Ch09.MinMax.fst
   :language: pulse
   :start-after: //SNIPPET_START: find_maximum
   :end-before: //SNIPPET_END: find_maximum

The postconditions use two conjuncts: an existential witness (the
value is *in* the array) and a universal bound (every element is ≥
or ≤ the result). Both functions are read-only — the array permission
``#p`` is returned unchanged.

Simultaneous Min/Max
~~~~~~~~~~~~~~~~~~~~

``SimultaneousMinMax`` computes both minimum and maximum in a single
pass using 2(n − 1) comparisons. A ghost counter tracks the exact
comparison count:

.. literalinclude:: ../ch09-order-statistics/CLRS.Ch09.SimultaneousMinMax.fst
   :language: pulse
   :start-after: //SNIPPET_START: find_minmax
   :end-before: //SNIPPET_END: find_minmax

The complexity bound is proved exactly:

.. literalinclude:: ../ch09-order-statistics/CLRS.Ch09.SimultaneousMinMax.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bounded_minmax
   :end-before: //SNIPPET_END: complexity_bounded_minmax

Quickselect
===========

CLRS §9.2 presents ``RANDOMIZED-SELECT``, a partition-based selection
algorithm. Our ``quickselect`` uses the last element as pivot (rather
than a random element), giving O(n²) worst case but the same expected
O(n). It is fully verified with zero admits.

Partition
~~~~~~~~~

The in-place partition rearranges ``a[lo..hi)`` around the pivot
``a[hi-1]`` and returns the pivot's final position:

.. literalinclude:: ../ch09-order-statistics/CLRS.Ch09.Quickselect.fst
   :language: fstar
   :start-after: //SNIPPET_START: partition_ordered
   :end-before: //SNIPPET_END: partition_ordered

.. literalinclude:: ../ch09-order-statistics/CLRS.Ch09.Quickselect.fst
   :language: pulse
   :start-after: //SNIPPET_START: partition_in_range
   :end-before: //SNIPPET_END: partition_in_range

The postcondition guarantees that the output is a permutation and that
elements left of the pivot are ≤ and elements right are ≥ the pivot
value.

Main Algorithm
~~~~~~~~~~~~~~

``quickselect`` iteratively narrows the search range ``[lo, hi)``
around position *k*:

.. literalinclude:: ../ch09-order-statistics/CLRS.Ch09.Quickselect.fst
   :language: pulse
   :start-after: //SNIPPET_START: quickselect
   :end-before: //SNIPPET_END: quickselect

The postcondition says the output array is a permutation of the input
and the returned value is the element at position *k* in the final
array. The ``Correctness`` module (a separate pure F* file) proves
that this element equals ``select_spec s0 k`` — the *k*-th element
of the sorted input.

Partial Selection Sort
======================

This is **not** a CLRS algorithm. It finds the *k*-th smallest
element by performing *k* rounds of selection sort: in each round it
finds the minimum of the unsorted suffix and swaps it to the front.
After *k* rounds, ``a[0..k−1]`` holds the *k* smallest elements in
sorted order, and ``a[k−1]`` is the answer.

Specification
~~~~~~~~~~~~~

The predicates used for correctness:

.. literalinclude:: ../ch09-order-statistics/CLRS.Ch09.PartialSelectionSort.fst
   :language: fstar
   :start-after: //SNIPPET_START: selection_defs
   :end-before: //SNIPPET_END: selection_defs

``sorted_prefix`` asserts that the first *k* positions are sorted.
``prefix_leq_suffix`` asserts a cut: every element in the sorted
prefix is ≤ every element in the remaining suffix. Together they
imply that ``a[k−1]`` is the *k*-th smallest.

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch09-order-statistics/CLRS.Ch09.PartialSelectionSort.fst
   :language: pulse
   :start-after: //SNIPPET_START: select
   :end-before: //SNIPPET_END: select

The postcondition guarantees a permutation, a sorted prefix up to *k*,
a prefix-leq-suffix cut, and that the returned value is exactly
``s_final[k − 1]``.

Pure Specification
~~~~~~~~~~~~~~~~~~

The ``Spec`` module defines the reference answer functionally:

.. literalinclude:: ../ch09-order-statistics/CLRS.Ch09.PartialSelectionSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: select_spec
   :end-before: //SNIPPET_END: select_spec

``select_spec`` sorts the sequence with a pure insertion sort and
returns the element at index *k*. The module also proves that
``count_lt`` and ``count_le`` are permutation-invariant, establishing
a partition-property characterization of the *k*-th order statistic.

Sorted Permutations are Equal
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A key auxiliary result lives in the ``SortedPerm`` module:

.. literalinclude:: ../ch09-order-statistics/CLRS.Ch09.PartialSelectionSort.SortedPerm.fst
   :language: fstar
   :start-after: //SNIPPET_START: sorted_permutation_equal
   :end-before: //SNIPPET_END: sorted_permutation_equal

This lemma is used in the ``Correctness`` module to show that the
result of quickselect matches ``select_spec``: since permutations of
sorted sequences are equal element-wise, the pivot at position *k*
must equal the *k*-th element of the reference sorted sequence.

Proof Techniques Summary
=========================

1. **Opaque permutation**: Both the Quickselect and PartialSelectionSort
   modules wrap ``Seq.Properties.permutation`` with ``opaque_to_smt``
   and reveal it only in targeted lemmas (``swap_is_permutation``,
   ``compose_permutations``).

2. **Two-layer specification**: The imperative Pulse code proves
   structural invariants (permutation, sorted prefix, partition
   ordering). A separate pure F* specification layer connects those
   invariants to the functional ``select_spec`` via counting arguments
   and the ``sorted_permutation_equal`` lemma.

3. **Ghost comparison counters**: The ``SimultaneousMinMax.Complexity``
   variant threads a ``GhostReference.ref nat`` through the loop,
   proving the exact comparison count 2(n − 1).
