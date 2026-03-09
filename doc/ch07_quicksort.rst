.. _Ch07_Quicksort:

#############################
Quicksort
#############################

This chapter covers the quicksort algorithm from CLRS Chapter 7, including
the Lomuto partition scheme (§7.1) and the recursive quicksort algorithm.
The implementation is split across Lemmas/Complexity/Impl modules
following the canonical rubric structure. All modules are fully verified with
**zero admits, assumes, or assume\_ calls**. For each component we prove:

1. The output is a permutation of the input.
2. The partition predicate holds (elements ≤ pivot before split, > pivot after).
3. The final array is sorted.
4. Worst-case complexity is O(n²).

Partition
=========

CLRS §7.1 presents partition as the key subroutine of quicksort. The
implementation uses the Lomuto scheme with the last element as pivot.

Specification
~~~~~~~~~~~~~

The shared Lemmas module defines the key predicates:

.. code-block:: fstar

   let between_bounds (s: Seq.seq int) (lb rb: int) =
     larger_than s lb /\ smaller_than s rb

   let complexity_exact_linear (cf c0 n: nat) : prop =
     cf >= c0 /\ cf - c0 == n

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The partition wrapper splits array ownership into three regions
(left, pivot, right) for use by recursive quicksort. The result
is a permutation with the pivot in its final position, all left
elements ≤ pivot, and all right elements > pivot.

The cost is **exactly** ``hi - lo - 1`` comparisons — every
non-pivot element is compared against the pivot exactly once.
This is linked to the ghost counter via
``complexity_exact_linear cf c0 (hi - lo - 1)``.

Strongest Guarantee
~~~~~~~~~~~~~~~~~~~

The partition performs **exactly** n−1 comparisons (not just ≤ n−1).
This is the tightest possible bound: every non-pivot element is
compared against the pivot exactly once.

Limitations
~~~~~~~~~~~

The Lomuto scheme always picks the **last element** as pivot. This
leads to worst-case O(n²) on sorted/reverse-sorted input. CLRS §7.3
discusses randomized pivot selection, which is NOT implemented here.

Quicksort
=========

The ``CLRS.Ch07.Quicksort.Impl`` module implements the recursive algorithm
using ``pts_to_range`` to split array ownership at the pivot position for
the two recursive calls.

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The recursive quicksort with ghost tick counter:

.. literalinclude:: ../autoclrs/ch07-quicksort/CLRS.Ch07.Quicksort.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: clrs_quicksort_with_ticks_sig
   :end-before: //SNIPPET_END: clrs_quicksort_with_ticks_sig

After partition splits the array at pivot position ``p``, the left half
``A[lo..p)`` and right half ``A[p+1..hi)`` are sorted recursively. The
ghost proof function ``quicksort_proof`` combines three facts — both halves
are sorted, they are permutations of the originals, and the pivot separates
their value ranges — to re-join them into a single sorted range.

Top-Level API
~~~~~~~~~~~~~

The user-facing ``quicksort`` function converts ``pts_to`` to
``pts_to_range``, computes ghost bounds via ``seq_min``/``seq_max``, calls
the recursive sort, and converts back:

.. literalinclude:: ../autoclrs/ch07-quicksort/CLRS.Ch07.Quicksort.Impl.fsti
   :language: pulse
   :start-after: //SNIPPET_START: quicksort_sig
   :end-before: //SNIPPET_END: quicksort_sig

Three variants are exported:

1. **quicksort**: sorted + permutation (no complexity tracking).
2. **quicksort_with_complexity**: adds ``complexity_bounded_quadratic``
   via a ghost counter, proving the worst-case O(n²) bound.
3. **quicksort_bounded**: sub-range sorting with caller-provided
   ``lb``/``rb`` bounds, using ``pts_to_range``.

Strongest Guarantee
~~~~~~~~~~~~~~~~~~~

The postcondition proves both sorted order and permutation — the
standard correctness specification for comparison-based sorting.
The O(n²) bound is the tightest *worst-case* bound for deterministic
quicksort with any fixed pivot rule.

Limitations
~~~~~~~~~~~

- **Only worst-case bound proven.** The average-case O(n log n) bound
  from CLRS §7.4 is NOT proven. Proving it would require a
  randomization analysis (expected value over random pivot choices),
  which is outside the scope of this deterministic formalization.
- **Worst case is tight.** For already-sorted or reverse-sorted input
  with last-element pivot, partition always produces a maximally
  unbalanced split (0 and n−1), giving exactly n(n−1)/2 comparisons.

Complexity
==========

Worst-Case Analysis
~~~~~~~~~~~~~~~~~~~

The pure F\* module ``Quicksort.Complexity`` defines the worst-case
recurrence ``T(n) = T(n-1) + (n-1)`` and proves its closed form:

.. literalinclude:: ../autoclrs/ch07-quicksort/CLRS.Ch07.Quicksort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: worst_case_comparisons
   :end-before: //SNIPPET_END: worst_case_comparisons

.. literalinclude:: ../autoclrs/ch07-quicksort/CLRS.Ch07.Quicksort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: worst_case_bound
   :end-before: //SNIPPET_END: worst_case_bound

The ``worst_case_bound`` lemma establishes
``2 * worst_case_comparisons(n) == n * (n-1)``, giving the exact
closed form T(n) = n(n−1)/2.

Convexity
~~~~~~~~~

The maximality theorem shows that any partition split is bounded by the
worst case:

.. literalinclude:: ../autoclrs/ch07-quicksort/CLRS.Ch07.Quicksort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: partition_split_bounded
   :end-before: //SNIPPET_END: partition_split_bounded

This is the key insight: for any split point ``k``,
``(n-1) + T(k) + T(n-1-k) ≤ T(n)``. The proof relies on
``sum_of_parts_bound``: ``T(a) + T(b) ≤ T(a+b)`` by induction,
establishing that the worst-case partition is always the most
unbalanced split.

Quadratic Bound
~~~~~~~~~~~~~~~

The ``Quicksort.Lemmas`` module defines the quadratic complexity bound
predicate used in the postcondition:

.. literalinclude:: ../autoclrs/ch07-quicksort/CLRS.Ch07.Quicksort.Lemmas.fsti
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bounded_quadratic
   :end-before: //SNIPPET_END: complexity_bounded_quadratic

The postcondition says: the final counter minus the initial is at most
``n*(n-1)/2`` where ``n = hi - lo``. This is the standard worst-case
bound for quicksort (CLRS §7.4).

Proof Techniques Summary
=========================

1. **Bound tracking with ``between_bounds``**: The recursive quicksort
   threads ghost lower and upper bounds through calls. The partition
   ensures ``lb ≤ pivot ≤ rb`` and the sub-arrays inherit tightened
   bounds, allowing ``lemma_sorted_append`` to combine sorted halves.

2. **``pts_to_range`` splitting**: Pulse's ``pts_to_range_split`` and
   ``pts_to_range_join`` are used to hand sub-array ownership to
   recursive calls and reassemble the result.

3. **Ghost proof functions**: The ``quicksort_proof`` ghost function
   performs the combine step (joining sorted sub-arrays) purely at the
   proof level, with no runtime cost.

4. **Convexity of the recurrence**: The ``sum_of_parts_bound`` lemma
   proves that ``T(a) + T(b) ≤ T(a+b)`` by induction, establishing
   that the worst-case partition is always the most unbalanced split.

5. **Exact partition cost**: The Lomuto partition is proven to perform
   **exactly** n−1 comparisons via ``complexity_exact_linear``,
   not just bounded by n−1. This tight count feeds into the recursive
   complexity analysis.

All proofs in this chapter are fully verified with **zero admits**.
