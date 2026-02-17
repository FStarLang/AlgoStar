.. _Ch16_Greedy:

############################
Greedy Algorithms
############################

This chapter covers two greedy algorithms from CLRS Chapter 16:
activity selection (§16.1) and Huffman coding (§16.3). The Pulse
implementations are verified for memory safety and functional
correctness, and the pure specifications formalize the greedy-choice
property and optimal substructure arguments from the textbook.

**Verification status.** The Pulse implementations (``ActivitySelection.fst``,
``Huffman.fst``, ``ActivitySelection.Complexity.fst``,
``Huffman.Complexity.fst``) contain **zero admits and zero assumes**.
The pure specification layer has gaps: ``ActivitySelection.Spec`` uses
4 ``admit()`` calls in the full optimality chain (exchange argument
for ``lemma_compat_order``, inductive optimality helper, greedy
property for tails, and the no-larger-selection corollary);
``Huffman.Spec`` uses 3 ``assume`` calls for the swap-reduces-WPL
lemma, greedy-choice theorem, and optimal-substructure theorem;
``Huffman.Complete`` uses 2 ``admit()`` calls in key optimality
theorems. The Lemmas module (exchange-argument proof for greedy
choice on sequences) is fully verified.

Activity Selection
==================

CLRS §16.1 presents the activity selection problem: given *n*
activities with start and finish times (sorted by finish time), select
a maximum-size subset of mutually compatible (non-overlapping)
activities. The greedy strategy selects the earliest-finishing
compatible activity at each step.

Specification
~~~~~~~~~~~~~

Activities are modelled as two sequences of integers (start times and
finish times). The core predicates define compatibility and mutual
compatibility:

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.ActivitySelection.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: activity_defs
   :end-before: //SNIPPET_END: activity_defs

``finish_sorted`` encodes the precondition that activities are sorted
by finish time. ``compatible`` checks that two activities do not
overlap. ``mutually_compatible`` lifts this to a list, requiring every
pair to be compatible.

An optimal selection is one whose cardinality equals the maximum
over all mutually compatible subsets:

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.ActivitySelection.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_optimal_selection
   :end-before: //SNIPPET_END: is_optimal_selection

Greedy Choice Property
~~~~~~~~~~~~~~~~~~~~~~

CLRS Theorem 16.1 states that the earliest-finishing activity belongs
to some optimal solution. The proof uses an exchange argument:
given any optimal solution, replace its first activity with activity 0
(the earliest-finishing). Because ``finish_sorted`` guarantees
``finish[0] ≤ finish[k]``, activity 0 is compatible with everything
activity *k* was compatible with.

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.ActivitySelection.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: lemma_greedy_choice
   :end-before: //SNIPPET_END: lemma_greedy_choice

The Lemmas module contains a fully verified variant of this exchange
argument operating on sequences rather than lists:

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.ActivitySelection.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: lemma_greedy_choice_seq
   :end-before: //SNIPPET_END: lemma_greedy_choice_seq

Main Optimality Theorem
~~~~~~~~~~~~~~~~~~~~~~~

The chain culminates in ``theorem_implementation_optimal``, which
connects the Pulse implementation's invariant (pairwise-compatible,
strictly-increasing sequence starting at 0) to the list-level
optimality definition:

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.ActivitySelection.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: theorem_implementation_optimal
   :end-before: //SNIPPET_END: theorem_implementation_optimal

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.ActivitySelection.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: lemma_greedy_is_optimal
   :end-before: //SNIPPET_END: lemma_greedy_is_optimal

.. note::

   ``lemma_greedy_is_optimal_helper`` (called by
   ``lemma_greedy_is_optimal``) uses ``admit()``. The inductive
   step combining greedy choice with optimal substructure is
   structurally clear but not yet mechanized.

Pulse Implementation
~~~~~~~~~~~~~~~~~~~~

The Pulse implementation scans the sorted activities in a single pass,
maintaining a ghost sequence of selected indices:

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.ActivitySelection.fst
   :language: pulse
   :start-after: //SNIPPET_START: activity_selection_sig
   :end-before: //SNIPPET_END: activity_selection_sig

The postcondition witnesses the existence of a selection sequence
``sel`` that is pairwise compatible, strictly increasing, starts with
activity 0, and has length equal to the returned count. The loop
invariant is captured by ``greedy_selection_inv``:

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.ActivitySelection.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: greedy_selection_inv
   :end-before: //SNIPPET_END: greedy_selection_inv

This invariant tracks that all selected indices are valid, strictly
increasing, pairwise compatible, and that ``last_finish`` equals the
finish time of the most recently selected activity.

Complexity
~~~~~~~~~~

A separate complexity-instrumented version proves that the algorithm
performs exactly *n* − 1 comparisons (one per candidate activity after
the first):

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.ActivitySelection.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bounded_linear
   :end-before: //SNIPPET_END: complexity_bounded_linear

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.ActivitySelection.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: activity_selection_complexity_sig
   :end-before: //SNIPPET_END: activity_selection_complexity_sig

The ghost counter ``ctr`` is a ``GhostReference.ref nat`` — fully
erased at runtime. Each comparison in the loop body calls ``tick``
once, and the postcondition ``complexity_bounded_linear cf c0 n``
asserts ``cf − c0 = n − 1``.

Huffman Coding
==============

CLRS §16.3 presents Huffman's algorithm for constructing an optimal
prefix-free code. The formalization defines Huffman trees, proves that
weighted path length equals internal-node cost (CLRS equation 16.4),
and provides both a pure functional construction and a Pulse
implementation.

Tree Definition
~~~~~~~~~~~~~~~

Huffman trees are an inductive type where every internal node has
exactly two children (a full binary tree by construction):

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.Huffman.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: htree_def
   :end-before: //SNIPPET_END: htree_def

Weighted Path Length and Cost
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The weighted path length (WPL) sums ``freq × depth`` over all leaves.
The cost sums all internal-node frequencies. CLRS equation 16.4
states these are equal; this is proved by induction:

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.Huffman.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: weighted_path_length
   :end-before: //SNIPPET_END: weighted_path_length

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.Huffman.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: wpl_equals_cost
   :end-before: //SNIPPET_END: wpl_equals_cost

Pure Construction
~~~~~~~~~~~~~~~~~

The pure functional Huffman construction repeatedly merges the two
lowest-frequency trees, inserting the result back into a sorted list:

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.Huffman.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: huffman_from_sorted
   :end-before: //SNIPPET_END: huffman_from_sorted

Termination is proved via the ``decreases (length l)`` clause:
``insert_sorted_length`` shows that merging two trees and reinserting
reduces the list length by one.

Optimality
~~~~~~~~~~

The optimality definition requires minimal WPL among all trees with
the same leaf frequencies:

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.Huffman.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_optimal
   :end-before: //SNIPPET_END: is_optimal

The greedy-choice property (CLRS Lemma 16.2) and optimal-substructure
property (CLRS Lemma 16.3) are stated and their proof outlines are
given, but the bodies use ``assume``. The key supporting lemma
``wpl_after_merge`` — relating the WPL before and after merging two
sibling leaves — is fully verified.

Pulse Implementation
~~~~~~~~~~~~~~~~~~~~

The Pulse implementation computes the total Huffman cost using an
array-based simulation: it repeatedly finds and merges the two minimum
elements, accumulating the merge cost:

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.Huffman.fst
   :language: pulse
   :start-after: //SNIPPET_START: huffman_cost_sig
   :end-before: //SNIPPET_END: huffman_cost_sig

The postcondition proves the cost is non-negative, strictly positive
when *n* > 1, and zero for a single element. This implementation
has **zero admits and zero assumes**.

Complexity
~~~~~~~~~~

The complexity analysis is done in pure F* by instrumenting
``huffman_from_sorted`` with a tick counter that tracks comparisons
during sorted insertion:

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.Huffman.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: huffman_ticks_bounded
   :end-before: //SNIPPET_END: huffman_ticks_bounded

.. literalinclude:: ../ch16-greedy/CLRS.Ch16.Huffman.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: huffman_complexity
   :end-before: //SNIPPET_END: huffman_complexity

The bound ``ticks ≤ n²`` reflects the sorted-list implementation
(linear insertion × *n* − 1 iterations). With a min-heap the bound
would be O(*n* log *n*), but the sorted-list variant is simpler to
verify. The proof proceeds by induction on list length.
``huffman_with_ticks_correct`` additionally proves that the
instrumented version produces the same tree as the uninstrumented one.
