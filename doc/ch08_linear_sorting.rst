.. _Ch08_LinearSorting:

########################################
Linear-Time Sorting
########################################

This chapter covers the three linear-time sorting algorithms from CLRS
Chapter 8: counting sort (§8.2), radix sort (§8.3), and bucket sort (§8.4).
These algorithms bypass the Ω(n log n) comparison-based lower bound by
exploiting structure in the keys.

**Verification status.** The in-place counting sort
(``CLRS.Ch08.CountingSort``) and the single-digit radix sort wrapper
(``CLRS.Ch08.RadixSort``) are fully verified with zero admits.
The stable CLRS-faithful counting sort (``CountingSort.Stable``) has
**3 assume\_** calls in Phase 4 (placement bounds and final
postcondition). The multi-digit radix sort modules have **10 admits**
total across ``RadixSort.FullSort`` (4), ``RadixSort.MultiDigit`` (2),
``RadixSort.Spec`` (2), and ``RadixSort.Stability`` (2), all related
to the stability property and its propagation through digit-by-digit
sorting. Bucket sort (``CLRS.Ch08.BucketSort``) has **1 admit** for
the main concatenation step.

Counting Sort
=============

CLRS §8.2 presents counting sort for non-negative integers bounded by a
known maximum value *k*. The algorithm runs in Θ(n + k) time.

Specification
~~~~~~~~~~~~~

The shared lemma module defines the core predicates used by both
counting sort variants:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.CountingSort.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: counting_sort_lemma_defs
   :end-before: //SNIPPET_END: counting_sort_lemma_defs

The ``in_range`` predicate constrains all elements to ``[0, k]``,
enabling the algorithm to use value-indexed count arrays. The
``permutation`` definition is made ``opaque_to_smt`` to prevent the
solver from unfolding the combinatorial structure; element counting
lemmas establish permutation where needed.

In-Place Counting Sort
~~~~~~~~~~~~~~~~~~~~~~

The fully verified in-place variant counts occurrences in Phase 1, then
writes sorted values back in Phase 2. Its signature:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.CountingSort.fst
   :language: pulse
   :start-after: //SNIPPET_START: counting_sort_sig
   :end-before: //SNIPPET_END: counting_sort_sig

The Phase 1 loop maintains ``counts_match_prefix`` — the count array
matches element frequencies for the prefix processed so far. Phase 2
iterates over values 0 through *k*, writing the correct number of copies
of each value. The ``phase2_inv`` predicate tracks a sorted prefix whose
element counts match the input. At loop exit, the ``final_perm`` lemma
shows all counts agree, establishing the permutation postcondition.

Stable Counting Sort
~~~~~~~~~~~~~~~~~~~~

The CLRS-faithful version uses a separate output array ``b`` and the
backwards-traversal placement loop that preserves stability:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.CountingSort.Stable.fst
   :language: pulse
   :start-after: //SNIPPET_START: counting_sort_stable_sig
   :end-before: //SNIPPET_END: counting_sort_stable_sig

This implementation follows the four CLRS phases exactly: initialize
counts, build histogram, compute prefix sums, and place elements in
reverse order. The input array is taken at half permission (``#0.5R``)
so it remains available as a read-only reference.

.. note::

   This module uses **3 assume\_** calls: one for placement-index bounds
   in Phase 4 (``pos >= 1 /\ pos <= len``), and two for the final
   postcondition (``sorted sb_final`` and ``permutation sb_final sa``).
   The structural implementation is faithful to CLRS; fully closing
   these gaps requires strengthening the Phase 3 prefix-sum invariant to
   track cumulative counts.

Complexity
~~~~~~~~~~

The complexity module proves the Θ(n + k) bound:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.CountingSort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: counting_sort_iterations
   :end-before: //SNIPPET_END: counting_sort_iterations

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.CountingSort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: counting_sort_linear
   :end-before: //SNIPPET_END: counting_sort_linear

Radix Sort
==========

CLRS §8.3 defines radix sort as *d* passes of a stable sort, one per
digit position from least significant to most significant. The
formalization has three layers: a single-digit Pulse wrapper, a
multi-digit pure specification, and supporting correctness and
complexity modules.

Single-Digit (Pulse)
~~~~~~~~~~~~~~~~~~~~

For integers bounded by *k*, radix sort with base *k+1* reduces to a
single pass of counting sort. The Pulse wrapper delegates directly:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.RadixSort.fst
   :language: pulse
   :start-after: //SNIPPET_START: radix_sort_sig
   :end-before: //SNIPPET_END: radix_sort_sig

This module has zero admits — it inherits full correctness from the
verified counting sort.

Multi-Digit Specification
~~~~~~~~~~~~~~~~~~~~~~~~~

The ``RadixSort.MultiDigit`` module provides a pure functional
multi-digit radix sort using insertion sort as the stable subroutine.
Digit extraction is standard positional notation:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.RadixSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: digit_extraction
   :end-before: //SNIPPET_END: digit_extraction

The multi-pass structure matches CLRS exactly — sort by digit 0, then
digit 1, up to digit *d−1*:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.RadixSort.MultiDigit.fst
   :language: fstar
   :start-after: //SNIPPET_START: radix_sort_multi
   :end-before: //SNIPPET_END: radix_sort_multi

The main correctness theorem:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.RadixSort.MultiDigit.fst
   :language: fstar
   :start-after: //SNIPPET_START: radix_sort_correct_multi
   :end-before: //SNIPPET_END: radix_sort_correct_multi

The proof proceeds in three steps: (1) radix sort is a permutation (by
composing per-pass permutations), (2) after *d* passes the result is
sorted on every individual digit, and (3) digit-wise sorting implies
value sorting via the digit decomposition theorem
``digit_decomposition_multi``.

.. note::

   The radix sort stability proofs have **10 admits** spread across
   four modules: ``RadixSort.Stability`` (2 — core stability
   reasoning), ``RadixSort.Spec`` (2 — CLRS Lemma 8.3 and main
   correctness theorem), ``RadixSort.MultiDigit`` (2 — stable sort
   preserves order between digits), and ``RadixSort.FullSort`` (4 —
   threading stability through the full sort chain). These all
   involve proving that insertion-sort-by-digit maintains relative
   order for equal-key elements — a detailed but standard argument
   about the leftmost-insertion strategy that produces ∃∀ quantifier
   patterns challenging for the SMT solver.

Stability Theory
~~~~~~~~~~~~~~~~

The ``RadixSort.Spec`` module defines the abstract stable-sort
specification used in the radix sort correctness argument:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.RadixSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_stable_sort_by
   :end-before: //SNIPPET_END: is_stable_sort_by

The ``RadixSort.Stability`` module proves the main inductive invariant
(``radix_sort_invariant``): after *d* passes, the sequence is sorted on
digits 0 through *d−1* in MSD-primary lexicographic order. The
``RadixSort.FullSort`` module bridges from digit-wise sorting to full
value sorting via the digit decomposition theorem.

Complexity
~~~~~~~~~~

The complexity analysis proves the Θ(d(n+k)) bound:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.RadixSort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: radix_sort_ops
   :end-before: //SNIPPET_END: radix_sort_ops

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.RadixSort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: radix_sort_theta_bound
   :end-before: //SNIPPET_END: radix_sort_theta_bound

For fixed *d* and *k*, the bound is linear in *n*. The module also
proves a concrete example: sorting 32-bit integers with *d = 4* digits
in base 256 costs exactly ``8n + 1024`` operations.

Bucket Sort
===========

CLRS §8.4 presents bucket sort for values distributed over a known
range. Elements are distributed into *k* buckets, each bucket is sorted
with insertion sort, and the sorted buckets are concatenated.

The implementation is in pure F\* (not Pulse) and operates on lists.
The sorted predicate:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.BucketSort.fst
   :language: fstar
   :start-after: //SNIPPET_START: bucket_sort_sorted
   :end-before: //SNIPPET_END: bucket_sort_sorted

The key correctness insight — appending two sorted lists with disjoint
value ranges produces a sorted list — is fully proven:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.BucketSort.fst
   :language: fstar
   :start-after: //SNIPPET_START: append_sorted_disjoint
   :end-before: //SNIPPET_END: append_sorted_disjoint

The top-level ``bucket_sort`` function guarantees sortedness and length
preservation:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.BucketSort.fst
   :language: fstar
   :start-after: //SNIPPET_START: bucket_sort_sig
   :end-before: //SNIPPET_END: bucket_sort_sig

When *k = n*, the average-case cost is linear:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.BucketSort.fst
   :language: fstar
   :start-after: //SNIPPET_START: bucket_sort_linear_cost
   :end-before: //SNIPPET_END: bucket_sort_linear_cost

.. note::

   Bucket sort contains **1 admit** in the main function for the
   concatenation step. The component lemmas (insertion sort correctness,
   disjoint-range append, length preservation) are all proven; what
   remains is showing that ``filter_bucket`` produces non-overlapping
   ranges that cover all input elements — a combinatorial argument about
   the bucket distribution function.

Proof Techniques Summary
=========================

1. **Element counting for permutation**: Instead of proving permutation
   via swaps, counting sort uses ``Seq.Properties.count`` to show that
   input and output have identical element frequencies. The
   ``equal_counts_perm`` lemma converts matching counts into a
   permutation proof.

2. **Digit decomposition**: Radix sort correctness hinges on the theorem
   that ``k == digit_sum k d base`` for ``k < base^d``. This is proved
   by induction on *d*, using the division theorem and modular
   arithmetic to relate higher and lower digits.

3. **Stability as an abstract property**: The radix sort modules treat
   stability as a specification predicate (``is_stable_sort_by``)
   rather than proving it for a specific implementation. This separates
   the radix sort correctness argument from the details of counting sort.

4. **Pure specification modules**: Complex mathematical arguments
   (digit arithmetic, recurrence analysis, combinatorial counting) are
   placed in pure F\* modules separate from the Pulse implementations,
   keeping the imperative code focused on loop invariants.
