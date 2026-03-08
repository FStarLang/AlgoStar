.. _Ch08_LinearSorting:

########################################
Linear-Time Sorting
########################################

This chapter covers the three linear-time sorting algorithms from CLRS
Chapter 8: counting sort (§8.2), radix sort (§8.3), and bucket sort (§8.4).
These algorithms bypass the Ω(n log n) comparison-based lower bound by
exploiting structure in the keys.

**All proofs are complete with zero admits.**

Counting Sort
=============

CLRS §8.2 presents counting sort for non-negative integers bounded by a
known maximum value *k*. The algorithm runs in Θ(n + k) time.

Specification
~~~~~~~~~~~~~

The core predicates used by all counting sort variants:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.CountingSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: counting_sort_spec_defs
   :end-before: //SNIPPET_END: counting_sort_spec_defs

``sorted`` requires every pair of indices *i ≤ j* to satisfy
*s[i] ≤ s[j]*. ``permutation`` wraps ``Seq.Properties.permutation``
but is ``opaque_to_smt`` — the solver never sees the combinatorial
definition; element-counting lemmas establish permutation where needed.
``in_range`` constrains all elements to ``[0, k]``, enabling the
algorithm to use value-indexed count arrays.

CLRS-Faithful Stable Sort
~~~~~~~~~~~~~~~~~~~~~~~~~

The CLRS-faithful version uses a separate output array ``b`` and the
backwards-traversal placement loop that preserves stability:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.CountingSort.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: counting_sort_impl_sig
   :end-before: //SNIPPET_END: counting_sort_impl_sig

This implementation follows the four CLRS phases exactly: initialize
counts, build histogram, compute prefix sums, and place elements in
reverse order. The input array is taken at half permission (``#0.5R``)
so it remains available as a read-only reference.

**Postcondition conjuncts:**

1. ``Seq.length sb' == Seq.length sa`` — output has the same length as input.
2. ``S.sorted sb'`` — output is sorted (∀ i ≤ j, sb'[i] ≤ sb'[j]).
3. ``S.permutation sb' sa`` — output is a permutation of the input.

**Strongest guarantee.** ``sorted ∧ permutation`` fully characterizes a
correct sort: the output contains exactly the same multiset of elements in
non-decreasing order. No stronger functional property exists.

In-Place Counting Sort
~~~~~~~~~~~~~~~~~~~~~~

The fully verified in-place variant counts occurrences in Phase 1, then
writes sorted values back in Phase 2. Its signature is identical to the
CLRS version except that it takes full ownership of a single array ``a``
and modifies it in-place. Postcondition: ``sorted ∧ permutation``.

Digit-Keyed Counting Sort
~~~~~~~~~~~~~~~~~~~~~~~~~~

The ``counting_sort_by_digit`` variant is used as the stable subroutine
for radix sort. Instead of ``sorted``, its postcondition guarantees the
stronger ``is_stable_sort_on_digit`` predicate from the stability module:

- Permutation of the input.
- Elements are sorted by their digit at position *d* in the given base.
- Stability: elements with the same digit value preserve their input order.

Complexity
~~~~~~~~~~

No explicit ghost comparison counter is threaded through the counting sort
implementations. The Θ(n + k) time bound is implicit from the algorithm
structure: one pass over the input to count, one pass over the count array
to place. The precondition ``SZ.fits (len + k_val + 2)`` limits *k* to
machine-representable sizes.

Radix Sort
==========

CLRS §8.3 defines radix sort as *d* passes of a stable sort, one per
digit position from least significant to most significant. The
formalization has three layers: a single-digit Pulse wrapper, a
multi-digit Pulse implementation, and a pure multi-digit specification.

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

Multi-Digit Pulse Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The full CLRS ``RADIX-SORT`` loops *d* times, calling
``counting_sort_by_digit`` at each digit position:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.RadixSort.fst
   :language: pulse
   :start-after: //SNIPPET_START: radix_sort_multidigit_sig
   :end-before: //SNIPPET_END: radix_sort_multidigit_sig

The loop invariant tracks ``B.permutation s0 s_curr`` (overall
permutation across passes) and ``sorted_up_to_digit s_curr (vd−1) base``
(sorted on digits 0 through *vd−1*). After all *d* passes,
``lemma_sorted_up_to_all_digits_implies_sorted`` bridges digit-wise
ordering to full value ordering. The key precondition is that all elements
must be less than ``base^bigD``.

Multi-Digit Pure Specification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The ``RadixSort.MultiDigit`` module provides a pure functional
multi-digit radix sort using insertion sort as the stable subroutine:

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

Stability Theory
~~~~~~~~~~~~~~~~

The ``RadixSort.Spec`` module defines the abstract stable-sort
specification used in the radix sort correctness argument:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.RadixSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_stable_sort_by
   :end-before: //SNIPPET_END: is_stable_sort_by

The three conjuncts are: (1) the output is a permutation; (2) the
output is sorted by the given key function; (3) elements with equal
keys preserve their input order (stability).

The correctness lemmas in the ``Lemmas`` aggregation module:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.RadixSort.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: radix_sort_correct_lemmas
   :end-before: //SNIPPET_END: radix_sort_correct_lemmas

The ``Stability`` module proves CLRS Lemma 8.3
(``lemma_stable_pass_preserves_ordering``): a stable sort on digit *d*
preserves ordering on digits 0 through *d−1*. The ``FullSort`` module
bridges from digit-wise sorting to full value sorting via the digit
decomposition theorem.

Limitations
~~~~~~~~~~~

- The pure ``radix_sort_correct`` requires a ``distinct s`` precondition
  for the stability argument. The Pulse implementation does **not** require
  distinctness.
- No standalone complexity ghost counter for Θ(d(n+b)).

Bucket Sort
===========

CLRS §8.4 presents bucket sort for values distributed over a known
range. Elements are distributed into *k* buckets, each bucket is sorted
with insertion sort, and the sorted buckets are concatenated.

The implementation is in pure F\* (not Pulse) and operates on lists.
The sorted predicate:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.BucketSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: bucket_sort_sorted
   :end-before: //SNIPPET_END: bucket_sort_sorted

The key correctness insight — appending two sorted lists where every
element of the left list is ≤ every element of the right list produces
a sorted list — is fully proven:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.BucketSort.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: append_sorted_disjoint
   :end-before: //SNIPPET_END: append_sorted_disjoint

The top-level ``bucket_sort`` function guarantees sortedness, length
preservation, and permutation:

.. literalinclude:: ../ch08-linear-sorting/CLRS.Ch08.BucketSort.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: bucket_sort_sig
   :end-before: //SNIPPET_END: bucket_sort_sig

**Postcondition conjuncts:**

1. ``sorted ys`` — output list is sorted (recursive: each adjacent pair x ≤ y).
2. ``List.length ys == List.length xs`` — length preserved.
3. ``is_permutation xs ys`` — count-based permutation (∀ x. count x xs == count x ys).

**Proof structure.** The permutation proof uses a count-based approach:
``filter_bucket_count`` shows each element appears in exactly one bucket
with the same multiplicity; ``sort_all_buckets_count`` shows insertion
sort preserves counts; ``create_all_buckets_perm`` composes these to
show the concatenated sorted buckets have the same element counts as the
input.

Limitations
~~~~~~~~~~~

- **List-based only**: No array/Pulse implementation. This limits practical
  applicability but provides a clean mathematical formalization.
- **Precondition**: Input must be non-empty (``Cons? xs``).
- **No complexity proof**: Expected O(n) with uniform distribution is not
  mechanized.

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

5. **Opaque predicates**: ``permutation`` is ``opaque_to_smt`` with
   explicit ``reveal_opaque`` calls. Similarly ``is_stable_sort_by_digit``
   and ``sorted_up_to_digit`` use opacity to prevent Z3 matching loops.
