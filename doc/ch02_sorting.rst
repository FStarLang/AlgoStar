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
3. The number of comparisons is bounded by the claimed complexity.

These algorithms introduce the fundamental proof-oriented programming
workflow used throughout this project: define a pure functional
specification, implement in Pulse with a loop invariant, and thread a
ghost cost counter for complexity.

Common Sorting Specification
============================

Both algorithms share the core definitions from
``CLRS.Common.SortSpec``:

.. literalinclude:: ../common/CLRS.Common.SortSpec.fst
   :language: fstar
   :start-after: //SNIPPET_START: definitions
   :end-before: //SNIPPET_END: definitions

- ``sorted`` requires that all pairs of indices in order have their
  elements in order — the standard definition.
- ``prefix_sorted s k`` only requires sortedness of the first ``k``
  elements. This is essential for insertion sort's loop invariant:
  after processing the first ``j`` elements, only positions ``0``
  through ``j-1`` are sorted.
- ``permutation`` wraps F*'s standard library
  ``Seq.Properties.permutation``, made ``opaque_to_smt`` so that
  the SMT solver does not unfold it automatically. By controlling
  when the definition is revealed (via ``reveal_opaque``), we prevent
  the solver from being overwhelmed by the combinatorial structure of
  permutation counting.

The ghost tick counter used for complexity (``tick``, ``incr_nat``)
is imported from ``CLRS.Common.Complexity``. It increments a
``GhostReference.ref nat`` — a reference that exists only for
specification purposes and is completely erased at runtime.

Insertion Sort
==============

CLRS §2.1 presents insertion sort as the first example of a sorting
algorithm with a loop invariant argument. Our formalization makes this
argument precise.

Specification
~~~~~~~~~~~~~

The complexity bound predicate lives in ``CLRS.Ch02.InsertionSort.Spec``:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.InsertionSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bounded
   :end-before: //SNIPPET_END: complexity_bounded

This says: given a final counter ``cf`` and an initial counter ``c0``,
the number of comparisons ``cf - c0`` is at most ``n*(n-1)/2``. This
is the standard worst-case bound: 1 + 2 + … + (n−1) = n(n−1)/2
comparisons.

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The main theorem is the type signature of ``insertion_sort`` from
``CLRS.Ch02.InsertionSort.Impl``:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.InsertionSort.Impl.fst
   :language: fstar
   :start-after: //SNIPPET_START: insertion_sort_sig
   :end-before: //SNIPPET_END: insertion_sort_sig

Reading this signature:

- **Input**: an array ``a`` containing a ghost sequence ``s0``, a
  length ``len``, and a ghost cost counter ``ctr`` starting at ``c0``.
- **Precondition** (``requires``): the length matches, fits the array,
  and is positive (``SZ.v len > 0``).
- **Postcondition** (``ensures``): there exists a final sequence ``s``
  and counter ``cf`` such that:

  1. ``Seq.length s == Seq.length s0`` — length is preserved.
  2. ``sorted s`` — the output is fully sorted.
  3. ``permutation s0 s`` — the output is a permutation of the input.
  4. ``complexity_bounded cf (reveal c0) (SZ.v len)`` — at most
     n(n−1)/2 comparisons were performed.

The ``#s0: Ghost.erased (Seq.seq int)`` parameter is a *ghost*
(erased) value — it exists only for specification purposes and is
erased at runtime. This is the Pulse idiom for tracking the logical
contents of a mutable array.

Strongest Guarantee
~~~~~~~~~~~~~~~~~~~

The combination ``sorted s ∧ permutation s0 s`` is the strongest
possible functional correctness specification for an in-place
comparison sort. It says:

- The output is ordered (``sorted``), and
- The output contains exactly the same multiset of elements as the
  input (``permutation``).

Together these rule out any incorrect behavior: no element can be
duplicated, dropped, or fabricated. Any sequence that is both sorted
and a permutation of the input is *the* unique sorted arrangement of
those elements.

Limitations
~~~~~~~~~~~

- **Positive length required**: The precondition requires
  ``SZ.v len > 0``. An empty array is trivially sorted, but the
  implementation's outer loop starts at index 1, which requires at
  least one element. This is a minor restriction — callers must
  guard against empty inputs.

- **Swap vs. shift**: CLRS shifts elements rightward and inserts the
  key once; our implementation swaps adjacent elements to bubble the
  key leftward. The *comparison count* is identical, but the *write
  count* is 2× that of the textbook's shift variant. This deviation
  does not affect the proven complexity bound (which counts
  comparisons only) but does mean the constant factor for memory
  writes differs from CLRS.

Complexity
~~~~~~~~~~

The complexity proof is *linked*: the same ``insertion_sort``
function that proves correctness also proves the comparison bound.
The ghost counter ``ctr`` is incremented by ``tick`` (from
``CLRS.Common.Complexity``) at each comparison. The postcondition's
``complexity_bounded`` predicate directly constrains the counter.

The proof uses a *triangular sum invariant*: after the outer loop
iteration for index ``j``, the counter satisfies
``cf - c0 ≤ j*(j−1)/2``. The inner loop contributes at most ``j``
comparisons (one per swap plus the initial comparison). The
arithmetic step ``j*(j−1)/2 + j = (j+1)*j/2`` is proved by the
helper ``lemma_triangle_step``.

The bound n(n−1)/2 is **tight**: it is achieved when the input is
in reverse-sorted order.

Proof Techniques
~~~~~~~~~~~~~~~~

The proof relies on three helper lemmas in
``CLRS.Ch02.InsertionSort.Lemmas``:

1. ``swap_is_permutation`` (from ``SortSpec``): Swapping two elements
   in a sequence produces a permutation. Uses
   ``Seq.Properties.lemma_swap_permutes`` internally, with careful
   handling of the ``opaque_to_smt`` wrapper.

2. ``lemma_prefix_le_key``: After the inner loop, all prefix elements
   are ≤ the key. Follows from the exit condition (either ``vi = 0``
   or ``s[vi−1] ≤ key``) combined with ``prefix_sorted``.

3. ``lemma_combine_sorted_regions``: When three regions (sorted prefix
   ≤ key < sorted shifted suffix) are combined, the result is
   ``prefix_sorted s (vj + 1)``.

The inner loop invariant tracks three array regions:

- ``[0 .. vi)``: unchanged prefix, still sorted
- ``[vi]``: the key value
- ``(vi .. vj]``: shifted elements, all > key, sorted

Cross-region ordering (all prefix elements ≤ all shifted elements) is
maintained to allow reassembly into a single sorted prefix.

.. note::

   See `PoP-in-FStar, Part 5: Pulse
   <https://fstar-lang.org/tutorial/pulse>`_ for background on
   Pulse loop invariants and separation logic assertions.

Merge Sort
==========

CLRS §2.3 introduces merge sort as a divide-and-conquer algorithm.
Our formalization follows the same structure: a pure functional merge
on sequences, an imperative merge implementation, and a recursive
sort.

Pure Specification
~~~~~~~~~~~~~~~~~~

The merge function is defined as a pure, total function on sequences
in ``CLRS.Ch02.MergeSort.Spec``:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.MergeSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: seq_merge
   :end-before: //SNIPPET_END: seq_merge

This is a standard functional merge: at each step, take the smaller
head and recurse. The ``(decreases ...)`` clause proves termination.
This pure function serves as the *specification* — the imperative
merge loop must produce the same sequence as ``seq_merge``.

The same module also defines complexity-bridging predicates:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.MergeSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: merge_sort_complexity_defs
   :end-before: //SNIPPET_END: merge_sort_complexity_defs

- ``merge_complexity_bounded cf c0 lo hi``: the merge step uses at
  most ``hi - lo`` comparisons.
- ``sort_complexity_bounded cf c0 lo hi``: the full sort uses at most
  ``ms_cost (hi - lo)`` comparisons, where ``ms_cost`` wraps the
  pure recurrence ``merge_sort_ops``.

Three key properties are proved about ``seq_merge`` in
``CLRS.Ch02.MergeSort.Lemmas``:

- ``seq_merge_length``: the output length is the sum of input lengths.
- ``seq_merge_sorted``: if both inputs are sorted, the output is sorted.
- ``seq_merge_permutation``: the output is a permutation of the
  concatenation of the inputs.

The sortedness proof uses an auxiliary predicate ``all_ge v s``
(all elements of ``s`` are ≥ ``v``) and proceeds by induction.
The permutation proof goes through element counting:
``seq_merge_count`` shows that for every ``x``, the count in
``seq_merge s1 s2`` equals the count in ``s1`` plus the count in
``s2``.

Correctness Theorem — Merge
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The imperative merge signature from ``CLRS.Ch02.MergeSort.Impl``:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.MergeSort.Impl.fst
   :language: fstar
   :start-after: //SNIPPET_START: merge_sig
   :end-before: //SNIPPET_END: merge_sig

The implementation copies the two halves (``s1``, ``s2``) into
heap-allocated temporary vectors, then merges back into the original
array. The loop invariant tracks how many elements from each side have
been consumed and asserts that the elements written so far match the
corresponding prefix of ``seq_merge s1 s2``.

This is a key proof pattern: rather than proving sortedness and
permutation directly in the loop, we prove that the output matches
the *pure specification* ``seq_merge`` element-by-element. Since
``seq_merge`` is already proven sorted and permutation-preserving,
the postcondition follows immediately.

The helper lemmas ``suffix_step_left`` and ``suffix_step_right``
characterize the next element to write: if the left head is ≤ the
right head, the next element is the left head, and the remaining
suffix is ``seq_merge (tail left) right``.

Correctness Theorem — Merge Sort
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The top-level merge sort signature:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.MergeSort.Impl.fst
   :language: fstar
   :start-after: //SNIPPET_START: merge_sort_sig
   :end-before: //SNIPPET_END: merge_sort_sig

Reading this signature:

- **Input**: array ``a`` with ghost contents ``s0``, length ``len``,
  and ghost counter ``ctr`` at ``c0``.
- **Precondition**: ``len == Seq.length s0 ∧ len == A.length a``.
  Unlike insertion sort, **no positive-length restriction** —
  empty and singleton arrays are handled by the base case.
- **Postcondition**: the output is sorted, a permutation of the
  input, same length, and the counter satisfies
  ``sort_complexity_bounded``.

Strongest Guarantee
~~~~~~~~~~~~~~~~~~~

As with insertion sort, ``sorted s ∧ permutation s0 s`` is the
strongest functional correctness guarantee for a comparison sort.
Merge sort additionally proves the tighter O(n log n) complexity
bound.

Limitations
~~~~~~~~~~~

- **Temporary allocation**: The merge step heap-allocates two
  temporary vectors per call. These are freed after each merge, but
  the allocation pattern differs from CLRS's single-auxiliary-array
  approach. This does not affect the proven comparison count but
  increases memory traffic.

- **Loose complexity constant**: The proven bound is
  ``4n⌈log₂ n⌉ + 4n``, roughly 4× the practical comparison count
  of ≈ n⌈log₂ n⌉. The constant 4 was chosen to simplify the
  inductive proof; tightening it is possible but would complicate
  the arithmetic lemmas significantly.

Complexity
~~~~~~~~~~

The complexity analysis lives in ``CLRS.Ch02.MergeSort.Complexity``,
a pure F* module (no Pulse). It defines the recurrence and proves the
closed-form bound.

The recurrence:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.MergeSort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: merge_sort_ops
   :end-before: //SNIPPET_END: merge_sort_ops

``merge_sort_ops`` encodes T(1) = 0, T(n) = 2·T(⌈n/2⌉) + n for
n > 1. Each merge of two halves costs at most n comparisons (the
``tick`` in the merge loop), and the two recursive calls contribute
T(⌈n/2⌉) each.

The closed-form bound and final theorem:

.. literalinclude:: ../ch02-getting-started/CLRS.Ch02.MergeSort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: merge_sort_bound
   :end-before: //SNIPPET_END: merge_sort_bound

``merge_sort_is_n_log_n`` proves ``merge_sort_ops n ≤ 4n⌈log₂ n⌉ + 4n``,
which is O(n log n) matching CLRS Theorem 2.3.

**The bound is deliberately loose.** The constant 4 simplifies the
inductive step. For practical interpretation:

- n=100: bound ≤ 3,200 comparisons (actual ≈ 700)
- n=1000: bound ≤ 44,000 comparisons (actual ≈ 10,000)
- n=1,000,000: bound ≤ 84,000,000 comparisons (actual ≈ 20,000,000)

The proof proceeds by strong induction on ``n``:

1. Apply the inductive hypothesis to
   T(⌈n/2⌉) ≤ 4⌈n/2⌉·log₂⌈n/2⌉ + 4⌈n/2⌉.
2. Substitute into the recurrence T(n) = 2·T(⌈n/2⌉) + n.
3. Use ``arithmetic_step`` to show
   8m·log m + 8m + n ≤ 4n·log n + 4n where m = ⌈n/2⌉.

The arithmetic lemma uses ``FStar.Math.Lemmas.lemma_mult_le_right``
to multiply the inequality 8m ≤ 4n + 4 by (log m + 1), then bounds
the remainder using ``log_linear_bound``: for n ≥ 2,
4·log₂⌈n/2⌉ + 4 ≤ 3n.

The complexity proof is **linked to the implementation**: the Pulse
``merge_sort`` function threads the ghost counter, and its
postcondition references ``sort_complexity_bounded`` which is defined
in terms of ``merge_sort_ops``. The pure bound
``merge_sort_is_n_log_n`` then gives the O(n log n) conclusion.
The bridge lemma ``ms_cost_split`` establishes that
T(⌊n/2⌋) + T(⌈n/2⌉) + n ≤ T(n), connecting the implementation's
floor-division split to the recurrence's ceiling-division.

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
   The ``tick`` and ``incr_nat`` helpers are imported from
   ``CLRS.Common.Complexity``.

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

File Organization
=================

The code is split into rubric-compliant modules:

**Insertion Sort**:

- ``CLRS.Ch02.InsertionSort.Spec.fst`` — pure specification
  (``complexity_bounded`` predicate).
- ``CLRS.Ch02.InsertionSort.Lemmas.fst/.fsti`` — helper lemma proofs
  (``lemma_prefix_le_key``, ``lemma_combine_sorted_regions``,
  ``lemma_triangle_step``).
- ``CLRS.Ch02.InsertionSort.Impl.fst/.fsti`` — Pulse implementation
  with full correctness + complexity proof.

**Merge Sort**:

- ``CLRS.Ch02.MergeSort.Spec.fst`` — pure specification (``seq_merge``,
  ``all_ge``, ``ms_cost``, complexity predicates).
- ``CLRS.Ch02.MergeSort.Lemmas.fst/.fsti`` — lemma proofs for
  ``seq_merge`` properties and suffix-stepping.
- ``CLRS.Ch02.MergeSort.Complexity.fst/.fsti`` — pure O(n log n)
  bound proof (``merge_sort_ops``, ``merge_sort_bound``,
  ``merge_sort_is_n_log_n``).
- ``CLRS.Ch02.MergeSort.Impl.fst/.fsti`` — Pulse implementation
  with full correctness + complexity proof.

**Common**:

- ``CLRS.Common.SortSpec.fst`` — shared sorting definitions
  (``sorted``, ``prefix_sorted``, ``permutation``, swap/append lemmas).
- ``CLRS.Common.Complexity`` — ghost tick counter (``tick``,
  ``incr_nat``).
