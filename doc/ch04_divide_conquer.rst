.. _Ch04_DivideConquer:

###########################################################
Divide & Conquer: Search, Subarray, Matrix Multiply
###########################################################

This chapter covers divide-and-conquer algorithms from CLRS
Chapter 4: binary search, the maximum subarray problem (§4.1),
and matrix multiplication including Strassen's algorithm (§4.2).
All implementations are **fully verified with zero admits**.

Binary Search
=============

CLRS presents binary search as the prototypical divide-and-conquer
search algorithm. Our Pulse implementation follows the standard
pattern: maintain a search interval ``[lo, hi)`` that shrinks by half
at every step.

Specification
~~~~~~~~~~~~~

The sortedness predicate and the logarithmic complexity bound are
defined in the pure Spec module:

.. code-block:: fstar

   let is_sorted (s: Seq.seq int) : prop =
     forall (i j: nat). i < j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

   let complexity_bounded_log (cf c0 n: nat) : prop =
     cf >= c0 /\ cf - c0 <= log2f n + 1

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The main theorem is the type signature of ``binary_search``:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.BinarySearch.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: binary_search_sig
   :end-before: //SNIPPET_END: binary_search_sig

Reading this signature:

- **Input**: a sorted array ``a`` with ghost contents ``s0``, length
  ``len``, and search ``key``. A ghost counter ``ctr`` at initial
  value ``c0`` tracks comparisons.
- **Found** (``result < len``): ``s0[result] == key`` — the element
  at the returned index equals the key.
- **Not found** (``result == len``): ``∀ i. s0[i] ≠ key`` — the key
  is absent from the entire array.
- **Complexity**: ``complexity_bounded_log cf c0 len`` — at most
  ⌊log₂ n⌋ + 1 comparisons, linked to the ghost counter.

Strongest Guarantee
~~~~~~~~~~~~~~~~~~~

The postcondition is the strongest functional guarantee: an exact
index when found and a universal absence proof when not found. The
bound of ⌊log₂ n⌋ + 1 comparisons is tight — it is the worst case
for binary search on an array of length n.

Limitations
~~~~~~~~~~~

- The array **must be sorted** (precondition).
- Only the worst-case bound is proven; best case (key at midpoint,
  1 comparison) is not tracked.
- The implementation uses a **found-flag pattern** because Pulse
  ``while`` loops cannot return values directly.

Complexity
~~~~~~~~~~

O(lg n) proven via a ghost counter linked to the imperative
implementation. The loop invariant tracks a *budget*:
``comparisons_used + log2f(remaining_range) <= log2f(n)``. Each
iteration consumes one comparison and halves the range, using
``lemma_log2f_step`` to show ``log2f`` decreases by at least 1.

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

.. code-block:: fstar

   let rec kadane_spec (s: Seq.seq int) (i: nat)
     (current_sum: int) (best_sum: int) : Pure int
     (requires i <= Seq.length s)
     (ensures fun _ -> True)
     = if i >= Seq.length s then best_sum
       else let elem = Seq.index s i in
            let new_current = max_int elem (current_sum + elem) in
            let new_best = max_int best_sum new_current in
            kadane_spec s (i + 1) new_current new_best

   let max_subarray_spec (s: Seq.seq int) : Tot int =
     if Seq.length s = 0 then 0
     else kadane_spec s 0 0 initial_min

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The Pulse implementation signature:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.MaxSubarray.Kadane.fst
   :language: pulse
   :start-after: //SNIPPET_START: max_subarray_sig
   :end-before: //SNIPPET_END: max_subarray_sig

The postcondition states:

- ``result == max_subarray_spec s0`` — the returned value equals
  the pure specification applied to the input sequence.
- ``complexity_bounded_linear cf c0 len`` — exactly n operations,
  linked to the ghost counter.

The Lemmas module proves optimality: ``theorem_kadane_optimal``
shows ``max_subarray_spec s >= sum_range s i j`` for all subarrays
``[i, j)``, and ``theorem_kadane_witness`` shows the maximum is
achieved by some subarray.

Limitations
~~~~~~~~~~~

The Kadane specification uses ``initial_min = -10^9`` as a sentinel.
The ``elements_bounded`` precondition (all elements ≥ -10^9) is
required for the optimality/equivalence proofs but not for the Pulse
implementation itself. CLRS uses -∞; our sentinel is a pragmatic
finite approximation.

Complexity
~~~~~~~~~~

Exactly n operations (Θ(n)), linked to the ghost counter. The loop
invariant tracks ``vc == c0 + i``; at exit ``cf - c0 == n``.

Maximum Subarray — Divide and Conquer
=====================================

The divide-and-conquer algorithm from CLRS §4.1 is implemented as
a **pure F\* function** (not Pulse). It splits the array at the
midpoint, recursively finds the maximum subarray in each half, and
also finds the maximum crossing subarray.

Algorithm Structure
~~~~~~~~~~~~~~~~~~~

The main recursive function follows CLRS exactly — split, recurse
on left and right, find the crossing subarray, and return the
maximum of the three:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst
   :language: fstar
   :start-after: //SNIPPET_START: find_maximum_subarray_dc
   :end-before: //SNIPPET_END: find_maximum_subarray_dc

Correctness
~~~~~~~~~~~

Two key theorems are proven:

1. **Sum correctness** — ``lemma_dc_sum_correct``: the returned range
   ``[left, right)`` has the claimed sum:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_sum_correct
   :end-before: //SNIPPET_END: dc_sum_correct

2. **Optimality** — ``lemma_dc_optimal``: for any subarray ``[qi, qj)``,
   the D&C result is ≥ ``sum_range s qi qj``.

Complexity
~~~~~~~~~~

The recurrence ``T(n) = 2T(n/2) + n`` with ``T(1) = 1`` gives
O(n log n):

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_ops_count
   :end-before: //SNIPPET_END: dc_ops_count

The bound ``T(n) ≤ 4n(⌈log₂ n⌉ + 1)`` is proved by induction:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_complexity_bound
   :end-before: //SNIPPET_END: dc_complexity_bound

.. note::

   The D&C complexity is a **pure recurrence analysis**, NOT linked
   to an imperative ghost counter. There is no Pulse implementation
   of the D&C variant.

Equivalence (Proven)
~~~~~~~~~~~~~~~~~~~~

The equivalence between the divide-and-conquer result and Kadane's
specification is fully proven — both algorithms compute the unique
maximum over all contiguous subarrays:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: dc_kadane_equivalence
   :end-before: //SNIPPET_END: dc_kadane_equivalence

The proof connects D&C and Kadane through the intermediate
``max_sub_sum`` definition: Kadane equals ``max_sub_sum`` (via
``lemma_kadane_correct``), D&C is ≤ ``max_sub_sum`` (via
``lemma_max_sub_ge``) and ≥ ``max_sub_sum`` (via ``lemma_dc_optimal``).

.. _Ch04_MatrixOps:

Matrix Multiplication
======================

This section covers matrix multiplication from CLRS §4.2: the
standard triple-loop algorithm (Pulse) and Strassen's
divide-and-conquer algorithm (pure F\*).

Standard Matrix Multiply
-------------------------

CLRS §4.2 presents the textbook triple-loop algorithm for multiplying
two n×n matrices. Our formalization stores matrices as flat arrays in
row-major order and proves that each output element equals the
corresponding dot product.

Specification
~~~~~~~~~~~~~

The pure specification defines a row-major flat index, a recursive dot
product, and correctness/complexity predicates:

.. code-block:: fstar

   let flat_index (n i j: nat) : nat = i * n + j

   let mat_mul_correct (sa sb sc: Seq.seq int) (n: nat) : prop =
     Seq.length sc == n * n /\
     (forall (i j: nat). i < n /\ j < n ==>
       Seq.index sc (flat_index n i j) == dot_product_spec sa sb n i j n)

   let complexity_bounded_cubic (cf c0 n: nat) : prop =
     cf >= c0 /\ cf - c0 == n * n * n

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The Pulse signature of ``matrix_multiply``:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.MatrixMultiply.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: matrix_multiply_sig
   :end-before: //SNIPPET_END: matrix_multiply_sig

Reading this signature:

- **Inputs**: arrays ``a``, ``b``, ``c`` of length ``n * n``, with
  fractional permissions on ``a`` and ``b`` (read-only) and full
  permission on ``c`` (written).
- **Postcondition**: ``mat_mul_correct sa sb sc' n`` — every element
  ``sc'[i*n+j]`` equals ``dot_product_spec sa sb n i j n``, and
  ``complexity_bounded_cubic cf c0 n`` — exactly n³ operations.

The proof uses a three-level loop decomposition with invariants
``mat_mul_partial_ij`` (all positions before ``(i,j)`` correct) and
``mat_mul_partial_k`` (current position has partial dot product up
to ``k``).

Complexity
~~~~~~~~~~

Exactly n³ multiply-add operations, linked to the ghost counter.
The three-level counter invariant tracks
``vc - c0 == vi * n² + vj * n + vk``.

Strassen's Algorithm
---------------------

CLRS §4.2 (pp. 79–82) presents Strassen's algorithm, which reduces
the number of recursive multiplications from 8 to 7. **This is a
pure F\* implementation (not Pulse).**

Matrix Representation
~~~~~~~~~~~~~~~~~~~~~

The Strassen formalization uses a sequence-of-sequences representation:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.Strassen.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: matrix_type
   :end-before: //SNIPPET_END: matrix_type

Standard Multiply (Specification)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The reference specification against which Strassen is verified:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.Strassen.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: standard_multiply
   :end-before: //SNIPPET_END: standard_multiply

Algorithm
~~~~~~~~~

The recursive Strassen function requires square, power-of-2 matrices:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.Strassen.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_multiply
   :end-before: //SNIPPET_END: strassen_multiply

For n > 1, seven half-size products are computed:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.Strassen.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_products
   :end-before: //SNIPPET_END: strassen_products

The result quadrants are assembled from these products:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.Strassen.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_combine
   :end-before: //SNIPPET_END: strassen_combine

Correctness Proof
~~~~~~~~~~~~~~~~~

The main correctness theorem states that Strassen and standard
multiplication agree element-wise:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.Strassen.Lemmas.fsti
   :language: fstar
   :start-after: //SNIPPET_START: strassen_correct
   :end-before: //SNIPPET_END: strassen_correct

The proof works by structural induction on the matrix dimension via
``lemma_strassen_elem_correct``. For each element ``(i,j)``, the
proof determines which quadrant it falls into and then expands the
Strassen formula algebraically. For example, in the upper-left
quadrant: C₁₁ = P5+P4−P2+P6, which after expansion and
cancellation yields A₁₁B₁₁ + A₁₂B₂₁. Four distributivity lemmas
(``lemma_matrix_product_{add,sub}_{left,right}``) mechanize this
expansion, and ``smt_sync'`` discharges the arithmetic.

Complexity
~~~~~~~~~~

The number of scalar multiplications satisfies the recurrence
T(n) = 7 T(n/2), T(1) = 1:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.Strassen.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_complexity
   :end-before: //SNIPPET_END: strassen_complexity

The closed form T(n) = 7\ :sup:`log₂ n` is proven:

.. literalinclude:: ../autoclrs/ch04-divide-conquer/CLRS.Ch04.Strassen.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_closed_form
   :end-before: //SNIPPET_END: strassen_closed_form

Limitations
~~~~~~~~~~~

- **Power-of-2 only**: the ``pow2_size`` precondition restricts input
  to 2\ :sup:`k` × 2\ :sup:`k` matrices. CLRS handles arbitrary
  sizes by padding; we do not.
- **No imperative version**: Strassen is pure F\* only. There is no
  Pulse implementation and no ghost-counter-linked complexity.
- **Counts multiplications only**: the Θ(n²) additions per recursion
  level are not counted. This matches the CLRS analysis.

Proof Techniques Summary
=========================

1. **Found-flag early exit**: Pulse ``while`` loops cannot return
   values directly. Binary search uses mutable ``found`` and
   ``result`` variables with loop condition
   ``!lo <^ !hi && not !found``.

2. **Logarithmic budget tracking**: The binary search complexity
   proof maintains ``comparisons_used + log2f(remaining_range)``
   as a non-increasing quantity, consuming one unit per iteration.

3. **Specification matching**: Rather than proving properties of
   the loop state directly, the Kadane invariant asserts that the
   pure specification evaluated from the current state equals the
   specification from the initial state.

4. **Pure vs. Pulse complexity**: Binary search, Kadane, and matrix
   multiply use ghost counters in Pulse. The D&C max-subarray and
   Strassen are pure F\*, so their complexity is proved by defining
   pure cost functions and bounding them algebraically.

5. **Algebraic expansion**: The Strassen correctness proof chains
   left/right distributivity of matrix multiplication over addition
   and subtraction, then verifies cancellation by SMT.

6. **Quadrant-level induction**: Strassen's proof recurses on
   ``rows a``, applying the inductive hypothesis to each of the
   seven half-size products.

All proofs in this chapter — binary search, Kadane, D&C max-subarray,
matrix multiply, and Strassen — are fully verified with **zero admits**.
