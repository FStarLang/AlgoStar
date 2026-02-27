.. _Ch04_DivideConquer:

###########################################################
Divide & Conquer: Search, Subarray, Matrix Multiply
###########################################################

This chapter covers divide-and-conquer algorithms from CLRS
Chapter 4: binary search, the maximum subarray problem (§4.1),
and matrix multiplication including Strassen's algorithm (§4.2).
Binary search is fully verified with **zero admits** in both its
correctness and O(log n) complexity proofs. The maximum subarray
problem is treated with two algorithms — Kadane's linear-time scan
(zero admits) and the classic divide-and-conquer approach — both
**fully verified with zero admits**, including a proven equivalence
between the two.

Binary Search
=============

CLRS presents binary search as the prototypical divide-and-conquer
search algorithm. Our Pulse implementation follows the standard
pattern: maintain a search interval ``[lo, hi)`` that shrinks by half
at every step.

Specification
~~~~~~~~~~~~~

The sortedness predicate is the standard definition:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_sorted
   :end-before: //SNIPPET_END: is_sorted

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The main theorem is the type signature of ``binary_search``:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.fst
   :language: pulse
   :start-after: //SNIPPET_START: binary_search_sig
   :end-before: //SNIPPET_END: binary_search_sig

Reading this signature:

- **Input**: a sorted array ``a`` with ghost contents ``s0``, length
  ``len``, and search ``key``.
- **Postcondition**: the result is either a valid index where
  ``s0[result] == key``, or ``len`` if the key is absent from the
  entire array.

The implementation uses a *found flag* pattern to simulate early
exit from a Pulse ``while`` loop. This is a key Pulse idiom: the
loop condition is ``!lo <^ !hi && not !found``, and the invariant
tracks two cases depending on the flag.

Loop Invariant
~~~~~~~~~~~~~~

The loop invariant maintains that the key, if present, must lie in
the interval ``[lo, hi)``:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.fst
   :language: pulse
   :start-after: //SNIPPET_START: binary_search_loop
   :end-before: //SNIPPET_END: binary_search_loop

The invariant splits into two cases:

1. **Found** (``vfound = true``): ``result`` is a valid index with
   ``s0[result] == key``.
2. **Not found** (``vfound = false``): the key is not in
   ``[0, lo)`` or ``[hi, len)``, and any occurrence must lie in
   ``[lo, hi)``.

When the loop exits with ``not found`` and ``lo >= hi``, the
interval is empty, so the key is absent from the entire array.

Note the sorted property is restated in the invariant with an
explicit SMT pattern ``{:pattern Seq.index s0 i; Seq.index s0 j}``
to help the solver efficiently reason about element ordering.

Complexity
~~~~~~~~~~

The complexity-instrumented version proves an O(log n) bound — at
most ⌊log₂ n⌋ + 1 comparisons:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: log2f
   :end-before: //SNIPPET_END: log2f

The complexity bound predicate:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bounded_log
   :end-before: //SNIPPET_END: complexity_bounded_log

The full signature threads a ghost counter:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.BinarySearch.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: binary_search_complexity_sig
   :end-before: //SNIPPET_END: binary_search_complexity_sig

The proof relies on ``lemma_log2f_step``: when the search range
shrinks from ``old_range`` to at most ``old_range / 2``, one
comparison is consumed and ``log2f`` decreases by at least 1. The
loop invariant tracks a *remaining budget*: the comparisons used
so far plus ``log2f`` of the remaining range never exceeds
``log2f`` of the original length.

Maximum Subarray — Kadane's Algorithm
=====================================

CLRS §4.1 introduces the maximum subarray problem and solves it
with a divide-and-conquer algorithm in O(n lg n). Kadane's
algorithm is the well-known O(n) improvement. We verify Kadane's
algorithm in Pulse with full correctness and complexity proofs.

Pure Specification
~~~~~~~~~~~~~~~~~~

The specification models Kadane's recurrence as a pure recursive
function:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.Kadane.fst
   :language: fstar
   :start-after: //SNIPPET_START: kadane_spec
   :end-before: //SNIPPET_END: kadane_spec

At each position ``i``, ``current_sum`` tracks the maximum subarray
sum ending at ``i`` (either extend the previous subarray or start
fresh), and ``best_sum`` tracks the global maximum seen so far.

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The Pulse implementation signature:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.Kadane.fst
   :language: pulse
   :start-after: //SNIPPET_START: max_subarray_sig
   :end-before: //SNIPPET_END: max_subarray_sig

The postcondition states that the returned value equals
``max_subarray_spec s0`` — the pure specification applied to the
input sequence. The proof strategy is *specification matching*:
the loop invariant asserts that ``kadane_spec`` applied from the
current position with the current accumulators equals ``kadane_spec``
applied from position 0 with initial values. When the loop
completes, this collapses to the desired postcondition.

Complexity
~~~~~~~~~~

The complexity-instrumented version proves the Θ(n) bound:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.Kadane.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bounded_linear
   :end-before: //SNIPPET_END: complexity_bounded_linear

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.Kadane.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: max_subarray_complexity_sig
   :end-before: //SNIPPET_END: max_subarray_complexity_sig

The bound is tight: exactly ``n`` operations (one ghost tick per
element). The loop invariant tracks ``vc == c0 + i``, which at
exit gives ``cf - c0 == n``.

Maximum Subarray — Divide and Conquer
=====================================

The divide-and-conquer algorithm from CLRS §4.1 is implemented as
a pure F* function (not Pulse). It splits the array at the
midpoint, recursively finds the maximum subarray in each half, and
also finds the maximum crossing subarray.

Algorithm Structure
~~~~~~~~~~~~~~~~~~~

The ``sum_range`` helper computes the sum of a contiguous range:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: sum_range
   :end-before: //SNIPPET_END: sum_range

The main recursive function follows CLRS exactly — split, recurse
on left and right, find the crossing subarray, and return the
maximum of the three:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: find_maximum_subarray_dc
   :end-before: //SNIPPET_END: find_maximum_subarray_dc

Correctness
~~~~~~~~~~~

The correctness theorem proves that the returned range has the
claimed sum:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_sum_correct
   :end-before: //SNIPPET_END: dc_sum_correct

The proof proceeds by structural induction on the recursion,
using ``lemma_crossing_sum_correct`` to handle the crossing case
and ``lemma_sum_range_append`` for compositional reasoning about
sums.

Complexity
~~~~~~~~~~

The recurrence ``T(n) = 2T(n/2) + n`` with ``T(1) = 1`` gives
O(n log n):

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_ops_count
   :end-before: //SNIPPET_END: dc_ops_count

The bound ``T(n) ≤ 4n(⌈log₂ n⌉ + 1)`` is proved by induction:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_complexity_bound
   :end-before: //SNIPPET_END: dc_complexity_bound

Equivalence (Proven)
~~~~~~~~~~~~~~~~~~~~~~~~~

The equivalence between the divide-and-conquer result and Kadane's
specification is fully proven — both algorithms compute the unique
maximum over all contiguous subarrays:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_kadane_equivalence
   :end-before: //SNIPPET_END: dc_kadane_equivalence

All proofs in this chapter — binary search correctness and complexity,
Kadane's correctness and complexity, D&C structural correctness and
complexity, and the equivalence theorem — are fully verified with
**zero admits**.

Proof Techniques Summary
------------------------

1. **Found-flag early exit**: Pulse ``while`` loops cannot return
   values directly. The pattern uses mutable ``found`` and
   ``result`` variables with the loop condition
   ``!lo <^ !hi && not !found``.

2. **Logarithmic budget tracking**: The binary search complexity
   proof maintains ``comparisons_used + log2f(remaining_range)``
   as a non-increasing quantity, consuming one unit per iteration.

3. **Specification matching**: Rather than proving properties of
   the loop state directly, the Kadane invariant asserts that the
   pure specification evaluated from the current state equals the
   specification from the initial state.

4. **Pure vs. Pulse complexity**: Binary search and Kadane use
   ghost counters in Pulse. The D&C algorithm is pure F*, so its
   complexity is proved by defining ``dc_ops_count`` as a separate
   pure function and bounding it algebraically.

.. _Ch04_MatrixOps:

Matrix Multiplication
======================

This section covers matrix multiplication from CLRS §4.2: the
standard triple-loop algorithm (Pulse) and Strassen's
divide-and-conquer algorithm (pure F*). The standard algorithm is verified in Pulse with
**zero admits** — both functional correctness and O(n³) complexity are
fully proven. Strassen's algorithm is verified as a pure F*
specification with **zero admits** ✅ — all algebraic
identities, the quadrant structural property, and the correctness
theorem equating Strassen to standard multiplication are fully proven
using ``smt_sync'`` for quadrant proofs.

Standard Matrix Multiply
-------------------------

CLRS §4.2 presents the textbook triple-loop algorithm for multiplying
two n×n matrices. Our formalization stores matrices as flat arrays in
row-major order and proves that each output element equals the
corresponding dot product.

Specification
~~~~~~~~~~~~~

The pure specification defines a row-major flat index, a recursive dot
product, and three correctness predicates — full correctness, partial
correctness at a single position ``(i,j)`` up to inner index ``k``,
and partial correctness over all positions before ``(ri, cj)`` in
row-major order:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MatrixMultiply.fst
   :language: fstar
   :start-after: //SNIPPET_START: spec
   :end-before: //SNIPPET_END: spec

``flat_index n i j`` computes ``i * n + j``, mapping 2-D indices to a
flat array. ``dot_product_spec sa sb n i j limit`` computes
∑\ :sub:`k=0`\ :sup:`limit−1` ``sa[i,k] * sb[k,j]``. The three
predicates — ``mat_mul_correct``, ``mat_mul_partial_k``, and
``mat_mul_partial_ij`` — decompose the full postcondition into pieces
that the loop invariants can track incrementally.

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The main theorem is the Pulse signature of ``matrix_multiply``:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MatrixMultiply.fst
   :language: pulse
   :start-after: //SNIPPET_START: matrix_multiply_sig
   :end-before: //SNIPPET_END: matrix_multiply_sig

Reading this signature:

- **Inputs**: arrays ``a``, ``b``, ``c`` of length ``n * n``, with
  ghost sequences ``sa``, ``sb``, ``sc`` tracking their logical
  contents. Arrays ``a`` and ``b`` are read with fractional permission
  ``#pa``, ``#pb``; array ``c`` is written with full permission.
- **Precondition**: ``n > 0``, index arithmetic fits in ``SZ.t``,
  and all arrays have length ``n * n``.
- **Postcondition**: there exists a new sequence ``sc'`` in ``c``
  satisfying ``mat_mul_correct sa sb sc' (SZ.v n)`` — i.e., every
  element ``sc'[i*n+j]`` equals ``dot_product_spec sa sb n i j n``.

Loop Invariants
~~~~~~~~~~~~~~~

The outer loop iterates over rows. Its invariant states that all
positions in rows ``0`` through ``vi - 1`` are fully computed:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MatrixMultiply.fst
   :language: pulse
   :start-after: //SNIPPET_START: outer_loop
   :end-before: //SNIPPET_END: outer_loop

The innermost loop accumulates the dot product for position ``(vi, vj)``.
Its invariant tracks both the partial sum at ``(vi, vj)`` via
``mat_mul_partial_k`` and the preservation of all previously computed
positions via ``mat_mul_partial_ij``:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MatrixMultiply.fst
   :language: pulse
   :start-after: //SNIPPET_START: inner_loop
   :end-before: //SNIPPET_END: inner_loop

When the inner loop exits (``vk == n``), ``mat_mul_partial_k`` at
``k = n`` coincides with the full dot product, so position ``(vi, vj)``
joins the set of completed positions tracked by ``mat_mul_partial_ij``.

Complexity
~~~~~~~~~~

The complexity-instrumented version threads a ghost counter through
the implementation. Each multiply-add (``C[i][j] += A[i][k]*B[k][j]``)
calls ``tick`` once:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MatrixMultiply.fst
   :language: pulse
   :start-after: //SNIPPET_START: ghost_tick
   :end-before: //SNIPPET_END: ghost_tick

The complexity bound predicate and theorem signature:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.MatrixMultiply.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bound
   :end-before: //SNIPPET_END: complexity_bound

The postcondition proves ``cf - c0 == n * n * n``: exactly n³
multiply-add operations, matching the standard analysis. The proof
uses a three-level sum invariant: after processing row ``vi``, column
``vj``, inner index ``vk``, the counter satisfies
``vc - c0 == vi * n * n + vj * n + vk``. When all three loops
complete (``vi = vj = n``, ``vk`` resets each inner iteration), this
yields ``n * n * n``.

Strassen's Algorithm
---------------------

CLRS §4.2 (pp. 79–82) presents Strassen's algorithm, which reduces the number
of recursive multiplications from 8 to 7 by computing auxiliary
products P1–P7 from sums and differences of quadrants.

Matrix Representation
~~~~~~~~~~~~~~~~~~~~~

Unlike the flat-array representation used in the Pulse implementation,
the Strassen formalization uses a sequence-of-sequences representation
that makes quadrant extraction natural:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: matrix_type
   :end-before: //SNIPPET_END: matrix_type

The ``matrix`` refinement type enforces that all rows have the same
length and that both dimensions are positive.

Standard Multiply (Specification)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The reference specification against which Strassen is verified:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: standard_multiply
   :end-before: //SNIPPET_END: standard_multiply

``standard_multiply`` builds the result matrix by computing each
element as ``dot_product a b i j p`` — the standard row-by-column
inner product.

Algorithm
~~~~~~~~~

The recursive Strassen function requires square, power-of-2 matrices:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_multiply
   :end-before: //SNIPPET_END: strassen_multiply

For n > 1 the matrices are split into quadrants A\ :sub:`11`,
A\ :sub:`12`, A\ :sub:`21`, A\ :sub:`22` (and likewise for B), and
seven half-size products are computed:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_products
   :end-before: //SNIPPET_END: strassen_products

The result quadrants are assembled from these products:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_combine
   :end-before: //SNIPPET_END: strassen_combine

Complexity
~~~~~~~~~~

The number of scalar multiplications satisfies the recurrence
T(n) = 7 T(n/2), T(1) = 1. The formalization defines a multiplication
count function, proves it is strictly less than n³ for n > 1, and
establishes the closed form T(n) = 7\ :sup:`log₂ n`:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_complexity
   :end-before: //SNIPPET_END: strassen_complexity

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_closed_form
   :end-before: //SNIPPET_END: strassen_closed_form

The closed-form proof proceeds by induction: unfolding
``strassen_mult_count n = 7 * strassen_mult_count (n/2)`` and
applying the inductive hypothesis gives
``7 * pow7 (log₂(n/2)) = pow7 (log₂ n)``.

.. note::

   The complexity analysis counts **scalar multiplications only**, not
   additions. This matches the CLRS analysis which focuses on the
   multiplication recurrence. The Θ(n²) additions at each recursion
   level are not counted, but the asymptotic class O(n\ :sup:`lg 7`)
   ≈ O(n\ :sup:`2.807`) is correctly characterized since
   n\ :sup:`lg 7` dominates n².

Correctness Proof
~~~~~~~~~~~~~~~~~

The main correctness theorem states that Strassen and standard
multiplication agree element-wise:

.. literalinclude:: ../ch04-divide-conquer/CLRS.Ch04.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_correct
   :end-before: //SNIPPET_END: strassen_correct

The proof works by structural induction on the matrix dimension via
the helper ``lemma_strassen_elem_correct``. For each element ``(i,j)``,
the proof determines which quadrant it falls into (upper-left,
upper-right, lower-left, lower-right) and then expands the Strassen
formula algebraically. For example, in the upper-left quadrant:

- P5 = (A₁₁+A₂₂)(B₁₁+B₂₂) expands to A₁₁B₁₁ + A₁₁B₂₂ + A₂₂B₁₁ + A₂₂B₂₂
- P4 = A₂₂(B₂₁−B₁₁) expands to A₂₂B₂₁ − A₂₂B₁₁
- P2 = (A₁₁+A₁₂)B₂₂ expands to A₁₁B₂₂ + A₁₂B₂₂
- P6 = (A₁₂−A₂₂)(B₂₁+B₂₂) expands to A₁₂B₂₁ + A₁₂B₂₂ − A₂₂B₂₁ − A₂₂B₂₂

Summing C₁₁ = P5 + P4 − P2 + P6 and cancelling yields A₁₁B₁₁ + A₁₂B₂₁,
which is exactly the standard multiply result. The four distributivity
lemmas (``lemma_matrix_product_{add,sub}_{left,right}``) mechanize this
expansion, and the dot product split lemma
(``lemma_dot_product_quadrant_split``) bridges the quadrant-level result
back to the full-matrix dot product.

The quadrant structural property in ``lemma_strassen_elem_correct``
(that submatrix quadrants of a square, power-of-2 matrix are themselves
square and power-of-2) is **fully proven** ✅ using ``smt_sync'`` to
discharge the arithmetic facts without solver timeout.

Proof Techniques Summary
------------------------

This chapter demonstrates several techniques:

1. **Row-major flat indexing**: The Pulse implementation stores n×n
   matrices as flat arrays of length n², using ``flat_index n i j``
   to compute offsets. The ``index_bounds_lemma`` helper gives SMT
   the arithmetic facts needed for bounds checking.

2. **Three-level loop decomposition**: The correctness proof
   decomposes into ``mat_mul_partial_ij`` (all positions before
   ``(i,j)`` are correct) and ``mat_mul_partial_k`` (the current
   position has a partial dot product up to ``k``). This two-predicate
   approach lets each loop level maintain a simple invariant.

3. **Ghost cost counters**: The ``tick`` function increments a
   ``GhostReference.ref nat`` at each multiply-add. The three-level
   counter invariant ``vi * n² + vj * n + vk`` mirrors the loop
   structure and yields the exact n³ bound.

4. **Algebraic expansion via distributivity lemmas**: The Strassen
   correctness proof chains left/right distributivity of matrix
   multiplication over addition and subtraction. Each P\ :sub:`k`
   is expanded symbolically, and cancellation is verified by SMT.

5. **Quadrant-level induction**: Strassen's proof recurses on
   ``rows a``, applying the inductive hypothesis to each of the
   seven half-size products and using ``assemble_quadrants`` to
   reconstruct the full result.
