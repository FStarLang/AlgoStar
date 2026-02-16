.. _Ch02_Sorting:

########################################
Sorting I: Insertion Sort & Merge Sort
########################################

This chapter covers the two sorting algorithms from CLRS Chapter 2:
insertion sort (§2.1) and merge sort (§2.3). Both are fully verified
with **zero admits, assumes, or assume_ calls**. For each algorithm
we prove:

1. The output is sorted.
2. The output is a permutation of the input.
3. The number of key operations is bounded by the claimed complexity.

These algorithms introduce the fundamental proof-oriented programming
workflow used throughout this project: define a pure functional
specification, implement in Pulse with a loop invariant, and thread a
ghost cost counter for complexity.

Insertion Sort
==============

CLRS §2.1 presents insertion sort as the first example of a sorting
algorithm with a loop invariant argument. Our formalization makes this
argument precise.

Specification
~~~~~~~~~~~~~

The correctness specification is expressed as two pure predicates:

.. literalinclude:: ../common/CLRS.Common.SortSpec.fst
   :language: fstar
   :start-after: //SNIPPET_START: definitions
   :end-before: //SNIPPET_END: definitions

``sorted`` requires that all pairs of indices in order have their
elements in order — the standard definition. ``permutation`` wraps
F*'s standard library ``Seq.Properties.permutation``, made
``opaque_to_smt`` so that the SMT solver does not unfold it
automatically. This is a key technique: by controlling when the
permutation definition is revealed (via ``reveal_opaque``), we prevent
the solver from being overwhelmed by the combinatorial structure of
permutation counting.

``prefix_sorted s k`` is a strengthened version of ``sorted`` that
only requires sortedness up to index ``k``. This is essential for the
loop invariant: after processing the first ``j`` elements, only
positions ``0`` through ``j-1`` are sorted.

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The main theorem is the type signature of ``insertion_sort``:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.InsertionSort.fst
   :language: fstar
   :start-after: //SNIPPET_START: insertion_sort_sig
   :end-before: //SNIPPET_END: insertion_sort_sig

Reading this signature:

- **Input**: an array ``a`` containing a ghost sequence ``s0`` and a
  length ``len``.
- **Precondition** (``requires``): the length matches and is positive.
- **Postcondition** (``ensures``): there exists a new sequence ``s``
  in the array such that ``s`` has the same length as ``s0``, is
  ``sorted``, and is a ``permutation`` of ``s0``.

The ``#s0: Ghost.erased (Seq.seq int)`` parameter is a *ghost*
(erased) value — it exists only for specification purposes and is
erased at runtime. This is the Pulse idiom for tracking the logical
contents of a mutable array.

Loop Invariant
~~~~~~~~~~~~~~

The outer loop maintains that the first ``j`` elements are sorted and
the array is a permutation of the original:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.InsertionSort.fst
   :language: fstar
   :start-after: //SNIPPET_START: outer_loop
   :end-before: //SNIPPET_END: outer_loop

The invariant binds existential variables ``vj`` (the loop counter
value) and ``s`` (the current array contents). The key conjuncts are:

- ``permutation s0 s``: the array is always a permutation of the input.
- ``prefix_sorted s (SZ.v vj)``: the first ``vj`` elements are sorted.

When the loop exits (``vj == len``), ``prefix_sorted s len`` implies
``sorted s``. Combined with ``permutation s0 s``, this gives the
postcondition.

**Inner loop**: The inner loop slides the key value backward until it
finds its correct position. Its invariant tracks three regions:

- ``[0 .. vi)``: unchanged prefix, still sorted
- ``[vi]``: the key value
- ``(vi .. vj]``: shifted elements, all greater than the key, sorted

The inner invariant also maintains *cross-region ordering*: all prefix
elements are ≤ all shifted elements. This is needed to reassemble the
three regions into a single sorted prefix after the inner loop exits.

Proof Walkthrough
~~~~~~~~~~~~~~~~~

The proof relies on three helper lemmas:

1. ``swap_is_permutation``: Swapping two elements in a sequence
   produces a permutation. This uses F*'s ``Seq.Properties.lemma_swap_permutes``
   internally, with careful handling of the ``opaque_to_smt``
   ``permutation`` wrapper.

2. ``lemma_prefix_le_key``: After the inner loop, all prefix elements
   are ≤ the key. This follows from the exit condition (either ``vi = 0``
   or ``s[vi-1] ≤ key``) combined with ``prefix_sorted``.

3. ``lemma_combine_sorted_regions``: When the three regions
   (prefix ≤ key < shifted, all sorted) are combined, the result is
   sorted up to ``vj + 1``.

The inner loop body (the swap) generates a new sequence ``s_post``.
Most of the invariant maintenance is handled automatically by SMT —
the solver can verify that positions outside the swap are unchanged,
and that the shifted region grows by one element. The main manual
work is calling ``swap_is_permutation`` to maintain the permutation
invariant.

.. note::

   See `PoP-in-FStar, Part 5: Pulse
   <https://fstar-lang.org/tutorial/pulse>`_ for background on
   Pulse loop invariants and separation logic assertions.

Complexity
~~~~~~~~~~

The complexity-instrumented version threads a ghost counter through
the implementation:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.InsertionSort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: ghost_tick
   :end-before: //SNIPPET_END: ghost_tick

The ``tick`` function increments a ``GhostReference.ref nat`` — a
reference that exists only for specification purposes and is
completely erased at runtime. Each comparison in the algorithm
calls ``tick`` once.

The complexity bound and theorem signature:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.InsertionSort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bound
   :end-before: //SNIPPET_END: complexity_bound

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.InsertionSort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: insertion_sort_complexity_sig
   :end-before: //SNIPPET_END: insertion_sort_complexity_sig

The postcondition says: the final counter value ``cf`` minus the
initial value ``c0`` is at most ``n*(n-1)/2``, where ``n`` is the
array length. This is the standard worst-case bound for insertion sort:
at most 1 + 2 + ... + (n-1) = n(n-1)/2 comparisons.

The proof uses a *sum invariant*: after the outer loop iteration for
index ``j``, the number of comparisons is at most ``j*(j-1)/2``.
The inner loop contributes at most ``j`` comparisons (one per swap
plus the initial comparison). The arithmetic step
``j*(j-1)/2 + j = (j+1)*j/2`` is proved by the helper
``lemma_triangle_step``.

Merge Sort
==========

CLRS §2.3 introduces merge sort as a divide-and-conquer algorithm.
Our formalization follows the same structure: a pure functional merge
on sequences, an imperative merge implementation, and a recursive
sort.

Pure Specification
~~~~~~~~~~~~~~~~~~

The merge function is first defined as a pure, total function on
sequences:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.MergeSort.fst
   :language: fstar
   :start-after: //SNIPPET_START: seq_merge
   :end-before: //SNIPPET_END: seq_merge

This is a standard functional merge: at each step, take the smaller
head and recurse. The ``(decreases ...)`` clause proves termination.
This pure function serves as the *specification* — the imperative
merge loop must produce the same sequence as ``seq_merge``.

Three key properties are proved about ``seq_merge``:

- ``seq_merge_length``: the length is the sum of input lengths.
- ``seq_merge_sorted``: if both inputs are sorted, the output is sorted.
- ``seq_merge_permutation``: the output is a permutation of the
  concatenation of the inputs.

The sortedness proof uses an auxiliary predicate ``all_ge v s``
(all elements of ``s`` are ≥ ``v``) and proceeds by induction: the
head of the merge is the overall minimum, and the tail is a sorted
merge of the remaining elements.

The permutation proof goes through element counting:
``seq_merge_count`` proves that for every element ``x``, the count
of ``x`` in ``seq_merge s1 s2`` equals the count in ``s1`` plus
the count in ``s2``. Since ``Seq.append`` has the same count
property, the two sequences are permutations.

Imperative Merge
~~~~~~~~~~~~~~~~

The Pulse implementation merges two sorted sub-arrays in-place (using
temporary buffers):

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.MergeSort.fst
   :language: fstar
   :start-after: //SNIPPET_START: merge_impl_sig
   :end-before: //SNIPPET_END: merge_impl_sig

The implementation copies the two halves into heap-allocated temporary
vectors, then merges back into the original array. The loop invariant
tracks how many elements from each side have been consumed and asserts
that the elements written so far match the corresponding prefix of
``seq_merge s1 s2``.

This is a key proof pattern: rather than proving sortedness and
permutation directly in the loop, we prove that the output matches
the *pure specification* ``seq_merge`` element-by-element. Since
``seq_merge`` is already proven sorted and permutation-preserving,
the postcondition follows immediately.

The helper lemmas ``suffix_step_left`` and ``suffix_step_right``
characterize the next element to write: if the left head is ≤ the
right head, the next element is the left head, and the remaining
suffix is ``seq_merge (tail left) right``.

Recursive Sort
~~~~~~~~~~~~~~

The top-level merge sort signature:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.MergeSort.fst
   :language: fstar
   :start-after: //SNIPPET_START: merge_sort_sig
   :end-before: //SNIPPET_END: merge_sort_sig

The recursive implementation uses ``pts_to_range`` to split the
array permission into two halves, sorts each half recursively, and
merges. The key proof step is ``append_permutations``: if each half
is a permutation of its original, then the concatenation of the sorted
halves is a permutation of the concatenation of the originals.

Complexity
~~~~~~~~~~

The complexity analysis is done in a separate pure F* module (not
Pulse), proving the standard recurrence:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.MergeSort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: merge_sort_ops
   :end-before: //SNIPPET_END: merge_sort_ops

The main theorem:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.MergeSort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: merge_sort_bound
   :end-before: //SNIPPET_END: merge_sort_bound

The bound ``4n⌈log₂ n⌉ + 4n`` is deliberately loose (the constant
4 simplifies the inductive step) but is still O(n log n), matching
CLRS Theorem 2.3. The proof proceeds by strong induction on ``n``:

1. Apply the inductive hypothesis to ``T(⌈n/2⌉) ≤ 4⌈n/2⌉·log₂⌈n/2⌉ + 4⌈n/2⌉``.
2. Substitute into the recurrence ``T(n) = 2·T(⌈n/2⌉) + n``.
3. Use the arithmetic lemma ``arithmetic_step`` to show that
   ``8m·log m + 8m + n ≤ 4n·log n + 4n`` where ``m = ⌈n/2⌉``.

The arithmetic lemma uses ``FStar.Math.Lemmas.lemma_mult_le_right``
to multiply the inequality ``8m ≤ 4n + 4`` by ``(log m + 1)``, then
bounds the remainder using ``log_linear_bound``: for ``n ≥ 2``,
``4·log₂⌈n/2⌉ + 4 ≤ 3n``.

Proof Techniques Summary
=========================

This chapter demonstrates several techniques used throughout the project:

1. **Opaque definitions with selective reveal**: Making ``permutation``
   opaque prevents SMT from unfolding it everywhere. We reveal it only
   in the specific lemmas that need it (``swap_is_permutation``,
   ``compose_permutations``).

2. **Specification-first loop invariants**: Rather than proving
   properties directly in the loop, we prove the loop output matches
   a pure specification (``seq_merge``) and separately prove the
   specification has the desired properties.

3. **Ghost cost counters**: The ``GhostReference.ref nat`` pattern
   threads a cost counter through Pulse code. The counter is erased
   at runtime but its value is constrained by the loop invariant.

4. **Prefix sortedness**: Using ``prefix_sorted s k`` instead of
   ``sorted s`` allows the invariant to express partial progress.

5. **Cross-region ordering**: When the array has multiple sorted
   regions, maintaining that all elements of earlier regions are ≤
   all elements of later regions allows them to be combined into a
   single sorted region.

6. **Permutation transitivity via SMT patterns**: The
   ``compose_permutations`` lemma has SMT patterns
   ``[SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]``,
   allowing the solver to automatically chain permutation arguments
   without explicit lemma calls at each step.
