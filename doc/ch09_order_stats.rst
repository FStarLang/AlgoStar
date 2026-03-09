.. _Ch09_OrderStats:

############################
Order Statistics (Selection)
############################

This chapter covers algorithms from CLRS Chapter 9 for finding order
statistics — the *k*-th smallest element of an array. We provide four
verified implementations:

- **Min/Max finding** (§9.1): linear-time minimum and maximum with
  exactly n−1 comparisons.
- **Simultaneous min-max** (§9.1): two variants — naïve with 2(n−1)
  comparisons and pair-processing with ⌊3n/2⌋ comparisons.
- **Quickselect** (§9.2, CLRS ``RANDOMIZED-SELECT``): partition-based
  selection, O(n²) worst case, O(n) expected.
- **Partial selection sort**: a selection-sort variant that finds the
  *k*-th smallest via *k* rounds of min-finding and swapping, O(nk).

All implementations are **fully verified with zero admits**. A rich
pure specification layer (``PartialSelectionSort.Spec``) connects the
imperative results to a functional ``select_spec`` defined as the
*k*-th element of a sorted permutation.

Min/Max Finding
===============

CLRS §9.1 discusses finding the minimum or maximum of an array in
Θ(n) comparisons. ``find_minimum`` and ``find_maximum`` scan the
array once, proving that the returned value both exists in the array
and is a universal bound.

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.MinMax.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: find_minimum
   :end-before: //SNIPPET_END: find_minimum

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.MinMax.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: find_maximum
   :end-before: //SNIPPET_END: find_maximum

The postconditions use three conjuncts:

1. An existential witness — the value is *in* the array
   (``∃k. k < length s0 ∧ s0[k] == min_val``).
2. A universal bound — every element is ≥ or ≤ the result
   (``∀k. min_val ≤ s0[k]``).
3. An exact complexity bound — the ghost counter records exactly
   n−1 comparisons.

Both functions are read-only — the array permission ``#p`` is returned
unchanged.

Complexity
~~~~~~~~~~

The complexity predicates from ``MinMax.Spec`` express exact bounds:

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.MinMax.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: minmax_complexity_bound
   :end-before: //SNIPPET_END: minmax_complexity_bound

Both are exact: ``cf - c0 == n - 1``, not "at most n − 1". This
matches the information-theoretic lower bound for finding the minimum
(or maximum) of an unsorted array.

Simultaneous Min/Max
====================

``SimultaneousMinMax`` computes both minimum and maximum in a single
pass. Two variants are provided.

Naïve Scan
~~~~~~~~~~

``find_minmax`` processes each element against both the current min
and max, using 2(n − 1) comparisons:

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.SimultaneousMinMax.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: find_minmax
   :end-before: //SNIPPET_END: find_minmax

The exact complexity bound:

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.SimultaneousMinMax.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bounded_minmax
   :end-before: //SNIPPET_END: complexity_bounded_minmax

Pair-Processing
~~~~~~~~~~~~~~~

``find_minmax_pairs`` implements the CLRS optimal algorithm that
processes elements in pairs: compare the pair, then compare the smaller
against the current min and the larger against the current max. This
uses at most ⌊3n/2⌋ comparisons:

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.SimultaneousMinMax.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: find_minmax_pairs
   :end-before: //SNIPPET_END: find_minmax_pairs

The tighter complexity bound:

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.SimultaneousMinMax.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bounded_minmax_pairs
   :end-before: //SNIPPET_END: complexity_bounded_minmax_pairs

The bound is expressed without integer division: ``2 * (cf - c0) ≤ 3 * n``.
This matches CLRS Theorem 9.1.

.. note::

   The ``find_minmax_pairs`` bound is slightly loose: it proves
   ``2*(cf-c0) ≤ 3*n`` rather than the tighter ``⌊3(n-1)/2⌋``.
   The slack is at most 1 comparison for even *n*.

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

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.Quickselect.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: partition_in_range
   :end-before: //SNIPPET_END: partition_in_range

The postcondition guarantees:

1. ``permutation s0 s1`` — a rearrangement of the input.
2. ``partition_ordered s1 lo pivot_pos hi`` — elements left of the
   pivot are ≤ and elements right are ≥ the pivot value.
3. ``unchanged_outside s0 s1 lo hi`` — elements outside ``[lo, hi)``
   are untouched.
4. ``cf - c0 == hi - lo - 1`` — exactly ``hi - lo - 1`` comparisons.

Main Algorithm
~~~~~~~~~~~~~~

``quickselect`` iteratively narrows the search range ``[lo, hi)``
around position *k*:

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.Quickselect.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: quickselect
   :end-before: //SNIPPET_END: quickselect

**Postcondition conjuncts:**

1. ``permutation s0 s_final`` — output is a rearrangement of input.
2. ``result == Seq.index s_final (SZ.v k)`` — result is the element
   at position *k* in the final array.
3. ``∀i < k. s_final[i] ≤ result`` — everything left of *k* is ≤.
4. ``∀i > k. result ≤ s_final[i]`` — everything right of *k* is ≥.
5. ``result == PSSSpec.select_spec s0 (SZ.v k)`` — result equals the
   *k*-th element of the sorted sequence (link to pure spec).
6. ``complexity_bounded_quickselect`` — O(n²) worst-case.

**Strongest guarantee.** Conjunct 5 (``result == select_spec s0 k``) is
the strongest possible functional specification — it uniquely identifies
the answer as the *k*-th element of the sorted sequence. The partition
property (conjuncts 3–4) is a structural bonus.

**Limitations:**

- Only worst-case O(n²) is proven; expected O(n) for randomized pivot
  is not mechanized.
- The implementation uses the last element as pivot (deterministic), so
  Θ(n²) is achievable on sorted inputs.

Partial Selection Sort
======================

This is **not** a CLRS algorithm. It finds the *k*-th smallest
element by performing *k* rounds of selection sort: in each round it
finds the minimum of the unsorted suffix and swaps it to the front.
After *k* rounds, ``a[0..k−1]`` holds the *k* smallest elements in
sorted order, and ``a[k−1]`` is the answer.

Specification
~~~~~~~~~~~~~

The pure functional reference answer:

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.PartialSelectionSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: select_spec
   :end-before: //SNIPPET_END: select_spec

``select_spec`` sorts the sequence with a pure insertion sort and
returns the element at index *k*. The module also proves that
``count_lt`` and ``count_le`` are permutation-invariant, establishing
a partition-property characterization of the *k*-th order statistic.

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.PartialSelectionSort.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: select
   :end-before: //SNIPPET_END: select

The postcondition guarantees:

1. ``permutation s0 s_final`` — a rearrangement of the input.
2. ``sorted_prefix s_final k`` — the first *k* positions are sorted.
3. ``prefix_leq_suffix s_final k`` — every element in the sorted
   prefix is ≤ every element in the remaining suffix.
4. ``result == s_final[k-1]`` — the returned value is the *k*-th smallest.
5. ``complexity_bounded_select`` — O(nk) worst-case.

Sorted Permutations are Equal
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A key auxiliary result in the ``Lemmas`` module:

.. literalinclude:: ../autoclrs/ch09-order-statistics/CLRS.Ch09.PartialSelectionSort.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: sorted_permutation_equal
   :end-before: //SNIPPET_END: sorted_permutation_equal

This lemma is used to show that the result of quickselect matches
``select_spec``: since two sorted permutations of the same sequence
are equal element-wise, the pivot at position *k* must equal the
*k*-th element of the reference sorted sequence.

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

3. **Ghost comparison counters**: All four algorithm families thread a
   ``GhostReference.ref nat`` through their loops, proving exact or
   bounded comparison counts:

   - ``find_minimum`` / ``find_maximum``: exact n−1.
   - ``find_minmax``: exact 2(n−1).
   - ``find_minmax_pairs``: ≤ ⌊3n/2⌋.
   - ``partition_in_range``: exact hi−lo−1.
   - ``quickselect``: O(n²) worst-case.
   - ``select``: O(nk).

4. **Count-based permutation invariance**: The ``Spec`` module proves
   ``count_lt_permutation_invariant`` and ``count_le_permutation_invariant``
   by induction using a find-and-remove technique. This enables the
   partition-property characterization of order statistics without
   relying on bag/multiset libraries.
