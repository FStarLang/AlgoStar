.. _Ch15_DynamicProg:

#####################
Dynamic Programming
#####################

This chapter covers three dynamic programming algorithms from CLRS
Chapter 15: rod cutting (§15.1), longest common subsequence (§15.4),
and matrix chain multiplication (§15.2). All three algorithms are fully
verified with **zero admits**.

Dynamic programming algorithms share a common proof structure:

1. Define a recursive specification capturing optimal substructure.
2. Prove that the bottom-up table-filling computation matches the
   recursive specification at every entry.
3. Implement the table-filling loop in Pulse and prove it produces
   the same table.
4. Thread a ghost cost counter for complexity.

Rod Cutting
===========

CLRS §15.1 introduces dynamic programming through the rod cutting
problem: given a rod of length *n* and a price table, find the
maximum revenue obtainable by cutting the rod into pieces.

Problem Specification
~~~~~~~~~~~~~~~~~~~~~

The problem is formalized with two predicates:

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.RodCutting.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: cutting_defs
   :end-before: //SNIPPET_END: cutting_defs

``valid_cutting n cuts`` asserts that ``cuts`` is a list of positive
integers summing to ``n``. ``cutting_revenue`` computes the total
revenue by looking up each piece length in the price table. The
optimal revenue is the maximum of ``cutting_revenue`` over all valid
cuttings.

Optimal Substructure
~~~~~~~~~~~~~~~~~~~~

The key mathematical result (CLRS Eq. 15.2) states that
the optimal revenue satisfies the recurrence:

    r(n) = max{1 ≤ i ≤ n} (p[i] + r(n − i))

This is proved as a theorem:

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.RodCutting.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: optimal_substructure
   :end-before: //SNIPPET_END: optimal_substructure

The proof works by showing that ``accum_max`` over the DP table
entries equals ``max_over_range`` over the recursive definition.
This requires:

1. ``build_opt_prefix``: The DP table is prefix-consistent — entry
   ``k`` in ``build_opt prices len`` equals entry ``k`` in
   ``build_opt prices k`` for all ``k ≤ len``.

2. ``accum_max_ext``: ``accum_max`` depends only on the values at
   indices less than ``j``. If two tables agree on those positions,
   ``accum_max`` gives the same result.

Imperative Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~

The Pulse implementation fills the DP table bottom-up using a nested
loop:

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.RodCutting.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: rod_cutting_sig
   :end-before: //SNIPPET_END: rod_cutting_sig

The postcondition is ``result == optimal_revenue s_prices (SZ.v n)``
— the returned value equals the optimal revenue defined by the pure
specification. The implementation uses a heap-allocated vector ``r``
for the DP table.

**Loop invariant**: The outer loop maintains ``dp_correct s_prices sr
(vj - 1)``: for all ``k ≤ vj - 1``, the table entry ``sr[k]``
equals ``optimal_revenue s_prices k``. The inner loop maintains
``vq == accum_max s_prices sr vj (vi - 1)``: the running maximum
``q`` matches the ``accum_max`` specification for the candidates
considered so far.

After the inner loop, we call ``accum_max_dp_correct`` to establish
that the computed maximum equals ``optimal_revenue s_prices vj``,
then store it in the table. This is the key proof step: it bridges
the gap between the imperative computation (inner loop computing a
running max) and the recursive specification (``optimal_revenue``
defined via ``build_opt``).

Complexity
~~~~~~~~~~

The complexity proof shows that the nested loops perform exactly
``n(n+1)/2`` candidate evaluations — the triangle number. The ghost
counter tracks ``triangle(vj - 1) + (vi - 1)`` during the inner loop,
where ``triangle(k) = k(k+1)/2``. After the inner loop completes
``vj`` iterations, the identity
``triangle(vj - 1) + vj = triangle(vj)`` advances the outer invariant.
This gives a tight O(n²) bound, matching CLRS's analysis. The
complexity is **linked**: proven inside the Pulse implementation via
a ghost counter, not just in a separate pure module.

Extended Rod Cutting
~~~~~~~~~~~~~~~~~~~~

CLRS also presents EXTENDED-BOTTOM-UP-CUT-ROD, which augments the
basic algorithm to record not just the optimal revenue but also the
optimal first cut size for each rod length. The procedure returns a
pair ``(r, s)`` where ``r[j]`` is the optimal revenue and ``s[j]`` is
the optimal size of the first piece to cut when solving a subproblem
of size ``j``.

The pure specification adds ``accum_argmax``, a companion to
``accum_max`` that tracks which index ``i`` achieves the maximum:

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.RodCutting.Extended.fst
   :language: fstar
   :start-after: //SNIPPET_START: extended_spec
   :end-before: //SNIPPET_END: extended_spec

The Pulse implementation extends the basic rod cutting loop to
maintain a second vector ``s_cuts`` alongside the revenue table
``r``. The inner loop tracks both a running maximum ``q`` and the
argmax ``best_i`` — the index that achieves that maximum. After
each inner loop completes, both ``r[j]`` and ``s_cuts[j]`` are
written.

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.RodCutting.Extended.fst
   :language: fstar
   :start-after: //SNIPPET_START: extended_sig
   :end-before: //SNIPPET_END: extended_sig

The postcondition uses ``cuts_are_optimal``, a clean predicate
that packages all correctness properties: (1) each ``s[j]`` is a
valid first piece size (between 1 and ``j``), and (2) each cut
achieves the optimal decomposition:
``prices[s[j]-1] + optimal_revenue(j - s[j]) == optimal_revenue(j)``.

These predicates are defined before ``open Pulse.Lib.BoundedIntegers``
(so they use standard integer operators) and marked
``[@@"opaque_to_smt"]`` to prevent Z3 context pollution during the
Pulse proof:

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.RodCutting.Extended.fst
   :language: fstar
   :start-after: //SNIPPET_START: cuts_are_optimal_def
   :end-before: //SNIPPET_END: cuts_are_optimal_def

A ``reconstruct_cutting`` function follows the ``s`` array to produce
the list of piece sizes for any rod length ``j``.
``reconstruct_cutting_sums`` proves that the pieces sum to ``j``
— validating that the cuts define a genuine partition of the rod.

The bridge lemma ``cuts_are_optimal_intro`` is called inside the
Pulse function body after the main loop, using ``reveal_opaque``
to connect the internal loop invariants (``dp_correct`` and
``cuts_achieve_optimal``) to the clean ``cuts_are_optimal`` predicate
in the postcondition.

**Proof notes.** The proof required two techniques beyond the basic
rod cutting proof. First, the ``s_cuts`` validity invariant —
a universal quantifier over all previously computed entries — had to
be carried through the inner loop invariant, even though the inner
loop does not write to ``s_cuts``. Pulse re-existentializes ghost
sequences at each loop iteration, so outer invariant properties are
lost unless explicitly restated. Second, re-establishing the
universal after writing to ``s_cuts[j]`` required a helper lemma
``sc_upd_valid`` that case-splits on ``k = j`` vs ``k ≠ j`` and
calls ``Seq.lemma_index_upd1`` / ``Seq.lemma_index_upd2``
explicitly, using ``Classical.forall_intro`` to close the quantifier.


Longest Common Subsequence
==========================

CLRS §15.4 presents the LCS problem: given two sequences, find the
length of their longest common subsequence.

Specification
~~~~~~~~~~~~~

The pure specification defines LCS length recursively:

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.LCS.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: lcs_spec
   :end-before: //SNIPPET_END: lcs_spec

This follows CLRS Eq. 15.9 directly: if the last characters match,
the LCS length is 1 plus the LCS of the prefixes; otherwise, take
the maximum of dropping one character from either sequence.

The specification module also defines ``is_subsequence``,
``is_common_subsequence`` and ``lcs_table_correct`` predicates.
``lcs_length_nonneg`` proves the result is always non-negative.

Implementation
~~~~~~~~~~~~~~

The Pulse implementation fills a 2D table stored as a flattened 1D
vector. The outer loop iterates over rows (index ``i`` into sequence
``x``), the inner loop over columns (index ``j`` into sequence ``y``).
Each cell ``tbl[i * (n+1) + j]`` stores ``lcs_length x y i j``.

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.LCS.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: lcs_sig
   :end-before: //SNIPPET_END: lcs_sig

The loop invariant asserts that all cells in completed rows and
the completed portion of the current row match the pure specification.
The inner loop body reads at most three previously computed cells
(left, above, diagonal) to fill the current cell, mirroring the
recursive definition.

The correctness proof is structurally identical to rod cutting:
after filling each cell, we show its value matches
``lcs_length x y i j``. The complexity is O(mn), proved by counting
exactly ``(m+1) × (n+1)`` cell evaluations via a ghost counter.
The complexity is **linked** to the Pulse implementation.

**Limitation.** The specification defines ``is_subsequence`` and
``is_common_subsequence`` predicates but does not formally prove
that ``lcs_length x y m n`` equals the length of any actual longest
common subsequence. The CLRS recurrence is standard, but the bridge
from the recurrence to the existential characterization ("there
exists a common subsequence of this length, and no longer one exists")
is not mechanized.


Matrix Chain Multiplication
============================

CLRS §15.2 covers the matrix chain multiplication problem: given a
sequence of matrix dimensions, find the parenthesization that minimizes
the number of scalar multiplications.

Recursive Specification
~~~~~~~~~~~~~~~~~~~~~~~

The recursive optimal substructure (CLRS Eq. 15.7) is defined as a
pure, total function ``mc_cost``.  Given dimensions ``p[0..n]`` where
matrix ``A_i`` has dimensions ``p[i] × p[i+1]``:

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.MatrixChain.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: mc_cost
   :end-before: //SNIPPET_END: mc_cost

``mc_cost p i j`` returns the minimum number of scalar multiplications
needed to compute the product ``A_i · A_{i+1} · ... · A_j``.  The
base case is a single matrix (``i = j``), which costs 0.  The
recursive case tries every split point ``k ∈ [i, j)`` and takes the
minimum of ``mc_cost(i,k) + mc_cost(k+1,j) + p[i]·p[k+1]·p[j+1]``.

Imperative Mirror Specification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The bottom-up DP algorithm is captured by an imperative mirror — pure
functions that exactly trace the three nested loops:

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.MatrixChain.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: mc_spec
   :end-before: //SNIPPET_END: mc_spec

``mc_inner_k`` iterates over split points for a chain from ``i`` to
``j``, accumulating the minimum cost.  ``mc_inner_i`` processes all
starting positions for a given chain length ``l``.  ``mc_outer``
iterates over increasing chain lengths from 2 to ``n``.

DP Correctness
~~~~~~~~~~~~~~

The main equivalence theorem states that the bottom-up DP result
equals the recursive optimum:

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.MatrixChain.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: mc_spec_equiv
   :end-before: //SNIPPET_END: mc_spec_equiv

The proof proceeds by induction on chain length: the initial table is
correct for single matrices (length 1), and processing chain length
``l`` advances ``dp_correct_upto`` from ``l-1`` to ``l``.  The bridge
lemma ``lemma_mc_inner_k_eq_min_splits`` shows that the table-reading
inner loop computes the same result as the recursive ``min_splits``.

.. note::

   The equivalence proof is fully verified (zero admits). Key helper
   lemmas: ``min_splits_acc_irrelevant`` shows that the sentinel value
   ``1000000000`` is irrelevant when the optimal cost is bounded, and
   ``lemma_mc_inner_i_fills_correctly`` proves by induction that each
   table entry is correctly filled.  The main theorem requires an
   ``all_costs_bounded`` precondition ensuring the optimal cost fits
   within the sentinel.

Implementation
~~~~~~~~~~~~~~

The Pulse implementation fills a 2D table using the standard
"increasing chain length" order: first all chains of length 1 (cost 0),
then length 2, length 3, and so on. This gives an O(n³) algorithm with
three nested loops.

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.MatrixChain.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: mc_sig
   :end-before: //SNIPPET_END: mc_sig

The loop invariant asserts that all cells for chains shorter than
the current length are correctly filled. Each cell computation reads
O(n) previously computed cells to find the optimal split point.

The ``Extended`` module provides ``extended_matrix_chain_order``,
which additionally returns the split-point array ``s`` and proves
``cuts_are_optimal``:

.. literalinclude:: ../autoclrs/ch15-dynamic-programming/CLRS.Ch15.MatrixChain.Extended.fst
   :language: pulse
   :start-after: //SNIPPET_START: extended_mc_sig
   :end-before: //SNIPPET_END: extended_mc_sig

Complexity
~~~~~~~~~~

The complexity analysis is done in a separate pure module
(``MatrixChain.Complexity``). It proves ``mc_iterations n ≤ n³``.
Unlike rod cutting and LCS, the complexity is **not linked** to the
Pulse implementation via a ghost counter — the Pulse function does
not carry a complexity ghost reference. The bound is an upper bound
(not tight): the exact count is ``Σ_{l=2..n} (n−l+1)(l−1)``, which
is ``n(n−1)(2n−1)/6``.


DP Proof Pattern Summary
=========================

All three algorithms follow the same proof architecture:

1. **Define the recursive specification** as a pure, total function
   with a ``decreases`` clause.

2. **Prove prefix consistency**: The DP table built for size ``n``
   agrees with the table built for size ``k < n`` at index ``k``.
   This is the ``build_opt_prefix`` pattern.

3. **Prove extensionality**: The recursive step depends only on
   previously computed entries. If two tables agree on those entries,
   they compute the same value. This is the ``accum_max_ext`` pattern.

4. **Prove the Pulse loop matches the spec**: The inner loop computes
   the same value as the recursive specification by maintaining
   ``vq == spec_function(current_args)``.

5. **Bridge the gap**: After the inner loop, call the key lemma
   (``accum_max_dp_correct`` or equivalent) to establish that the
   computed value equals the specification value. This lemma combines
   prefix consistency, extensionality, and the inductive hypothesis.

6. **Thread the ghost counter**: Count one tick per inner-loop
   iteration. The outer invariant tracks the total via a closed-form
   sum (triangle number, product, etc.).

**Pulse-specific patterns for DP:**

- Use ``Pulse.Lib.Vec`` for heap-allocated tables (freed after use).
- Use fractional permissions (``#p: perm``) to borrow the input
  array read-only while the DP table is mutated.
- For 2D tables, flatten to 1D: ``tbl[i * cols + j]``.
- Keep the pure specification before ``open Pulse.Lib.BoundedIntegers``
  to avoid interference with ``decreases`` clauses.

.. note::

   For background on separation logic, fractional permissions, and
   ghost state in Pulse, see `PoP-in-FStar, Part 5: Pulse
   <https://fstar-lang.org/tutorial/pulse>`_.
