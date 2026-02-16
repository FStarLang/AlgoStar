.. _Ch15_DynamicProg:

#####################
Dynamic Programming
#####################

This chapter covers three dynamic programming algorithms from CLRS
Chapter 15: rod cutting (§15.1), longest common subsequence (§15.4),
and matrix chain multiplication (§15.2). All three are fully verified
with **zero admits, assumes, or assume_ calls**.

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

.. literalinclude:: ../ch15-dynamic-programming/CLRS.Ch15.RodCutting.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: cutting_defs
   :end-before: //SNIPPET_END: cutting_defs

``valid_cutting n cuts`` asserts that ``cuts`` is a list of positive
integers summing to ``n``. ``cutting_revenue`` computes the total
revenue by looking up each piece length in the price table. The
optimal revenue is the maximum of ``cutting_revenue`` over all valid
cuttings.

Recursive Specification
~~~~~~~~~~~~~~~~~~~~~~~

Rather than working with the existential "max over all valid cuttings"
directly (which would require reasoning about an unbounded set), we
use the standard DP approach: define the optimal value recursively.

.. literalinclude:: ../ch15-dynamic-programming/CLRS.Ch15.RodCutting.fst
   :language: fstar
   :start-after: //SNIPPET_START: rod_cutting_spec
   :end-before: //SNIPPET_END: rod_cutting_spec

``accum_max prices r j limit`` computes the maximum of
``prices[i-1] + r[j-i]`` for ``i`` from 1 to ``limit``. This is the
inner loop of the DP: for a rod of length ``j``, try every possible
first cut at position ``i``, adding the price of piece ``i`` to the
optimal revenue for the remaining rod of length ``j-i`` (looked up
in the table ``r``).

``build_opt prices len`` constructs the DP table bottom-up:
``build_opt prices len`` returns a sequence of length ``len+1``
where entry ``k`` is the optimal revenue for a rod of length ``k``.

``optimal_revenue prices j`` is simply ``build_opt prices j`` at
index ``j``.

Optimal Substructure
~~~~~~~~~~~~~~~~~~~~

The key mathematical result (CLRS Eq. 15.2) states that
the optimal revenue satisfies the recurrence:

    r(n) = max{1 ≤ i ≤ n} (p[i] + r(n − i))

This is proved as a theorem:

.. literalinclude:: ../ch15-dynamic-programming/CLRS.Ch15.RodCutting.Spec.fst
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

.. literalinclude:: ../ch15-dynamic-programming/CLRS.Ch15.RodCutting.fst
   :language: fstar
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
This gives a tight O(n²) bound, matching CLRS's analysis.

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

.. literalinclude:: ../ch15-dynamic-programming/CLRS.Ch15.RodCutting.Extended.fst
   :language: fstar
   :start-after: //SNIPPET_START: extended_spec
   :end-before: //SNIPPET_END: extended_spec

The Pulse implementation extends the basic rod cutting loop to
maintain a second vector ``s_cuts`` alongside the revenue table
``r``. The inner loop tracks both a running maximum ``q`` and the
argmax ``best_i`` — the index that achieves that maximum. After
each inner loop completes, both ``r[j]`` and ``s_cuts[j]`` are
written.

.. literalinclude:: ../ch15-dynamic-programming/CLRS.Ch15.RodCutting.Extended.fst
   :language: fstar
   :start-after: //SNIPPET_START: extended_sig
   :end-before: //SNIPPET_END: extended_sig

The postcondition guarantees two properties: (1) the returned
revenue equals ``optimal_revenue``, and (2) for every ``j`` in
``1..n``, ``s_cuts[j]`` is a valid first piece size between 1 and
``j``.

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

.. code-block:: fstar

   let rec lcs_length (x y: Seq.seq int) (i j: nat)
     : Tot int (decreases i + j) =
     if i = 0 || j = 0 then 0
     else if Seq.index x (i-1) = Seq.index y (j-1) then
       1 + lcs_length x y (i-1) (j-1)
     else
       let l1 = lcs_length x y (i-1) j in
       let l2 = lcs_length x y i (j-1) in
       if l1 >= l2 then l1 else l2

This follows CLRS Eq. 15.9 directly: if the last characters match,
the LCS length is 1 plus the LCS of the prefixes; otherwise, take
the maximum of dropping one character from either sequence.

Implementation
~~~~~~~~~~~~~~

The Pulse implementation fills a 2D table stored as a flattened 1D
vector. The outer loop iterates over rows (index ``i`` into sequence
``x``), the inner loop over columns (index ``j`` into sequence ``y``).
Each cell ``tbl[i * (n+1) + j]`` stores ``lcs_length x y i j``.

The loop invariant asserts that all cells in completed rows and
the completed portion of the current row match the pure specification.
The inner loop body reads at most three previously computed cells
(left, above, diagonal) to fill the current cell, mirroring the
recursive definition.

The correctness proof is structurally identical to rod cutting:
after filling each cell, we show its value matches
``lcs_length x y i j``. The complexity is O(mn), proved by counting
exactly ``m × n`` cell evaluations via a ghost counter.


Matrix Chain Multiplication
============================

CLRS §15.2 covers the matrix chain multiplication problem: given a
sequence of matrix dimensions, find the parenthesization that minimizes
the number of scalar multiplications.

Specification
~~~~~~~~~~~~~

The pure specification defines the optimal cost recursively:

.. code-block:: fstar

   let rec mc_opt (p: Seq.seq int) (i j: nat)
     : Tot int (decreases (j - i)) =
     if j <= i then 0
     else min_over_k (fun k ->
       mc_opt p i k + mc_opt p (k+1) j +
       Seq.index p i * Seq.index p (k+1) * Seq.index p (j+1)) i j

This follows CLRS Eq. 15.7: try all possible split points ``k``
between ``i`` and ``j``, compute the cost of the left and right
sub-chains plus the cost of the final multiplication, and take the
minimum.

Implementation
~~~~~~~~~~~~~~

The Pulse implementation fills a 2D table using the standard
"increasing chain length" order: first all chains of length 1 (cost 0),
then length 2, length 3, and so on. This gives an O(n³) algorithm with
three nested loops.

The loop invariant asserts that all cells for chains shorter than
the current length are correctly filled. Each cell computation reads
O(n) previously computed cells to find the optimal split point.

The complexity proof counts exactly ``n(n-1)(2n-1)/6`` operations
(the sum of ``k(k-1)`` for ``k`` from 2 to ``n``), giving O(n³).


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
