.. _Ch28_MatrixOps:

########################################
Matrix Operations
########################################

This chapter covers matrix multiplication from CLRS Chapter 28: the
standard triple-loop algorithm (§28.1) and Strassen's divide-and-conquer
algorithm (§28.2). The standard algorithm is verified in Pulse with
**zero admits** — both functional correctness and O(n³) complexity are
fully proven. Strassen's algorithm is verified as a pure F*
specification with **one admit** (a structural property that quadrant
extraction preserves square/power-of-2 constraints); all algebraic
identities and the correctness theorem equating Strassen to standard
multiplication are fully proven.

Standard Matrix Multiply
=========================

CLRS §28.1 presents the textbook triple-loop algorithm for multiplying
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

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.MatrixMultiply.fst
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

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.MatrixMultiply.fst
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

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.MatrixMultiply.fst
   :language: pulse
   :start-after: //SNIPPET_START: outer_loop
   :end-before: //SNIPPET_END: outer_loop

The innermost loop accumulates the dot product for position ``(vi, vj)``.
Its invariant tracks both the partial sum at ``(vi, vj)`` via
``mat_mul_partial_k`` and the preservation of all previously computed
positions via ``mat_mul_partial_ij``:

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.MatrixMultiply.fst
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

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.MatrixMultiply.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: ghost_tick
   :end-before: //SNIPPET_END: ghost_tick

The complexity bound predicate and theorem signature:

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.MatrixMultiply.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bound
   :end-before: //SNIPPET_END: complexity_bound

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.MatrixMultiply.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: matrix_multiply_complexity_sig
   :end-before: //SNIPPET_END: matrix_multiply_complexity_sig

The postcondition proves ``cf - c0 == n * n * n``: exactly n³
multiply-add operations, matching the standard analysis. The proof
uses a three-level sum invariant: after processing row ``vi``, column
``vj``, inner index ``vk``, the counter satisfies
``vc - c0 == vi * n * n + vj * n + vk``. When all three loops
complete (``vi = vj = n``, ``vk`` resets each inner iteration), this
yields ``n * n * n``.

Strassen's Algorithm
=====================

CLRS §28.2 presents Strassen's algorithm, which reduces the number
of recursive multiplications from 8 to 7 by computing auxiliary
products P1–P7 from sums and differences of quadrants.

Matrix Representation
~~~~~~~~~~~~~~~~~~~~~

Unlike the flat-array representation used in the Pulse implementation,
the Strassen formalization uses a sequence-of-sequences representation
that makes quadrant extraction natural:

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: matrix_type
   :end-before: //SNIPPET_END: matrix_type

The ``matrix`` refinement type enforces that all rows have the same
length and that both dimensions are positive.

Standard Multiply (Specification)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The reference specification against which Strassen is verified:

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: standard_multiply
   :end-before: //SNIPPET_END: standard_multiply

``standard_multiply`` builds the result matrix by computing each
element as ``dot_product a b i j p`` — the standard row-by-column
inner product.

Algorithm
~~~~~~~~~

The recursive Strassen function requires square, power-of-2 matrices:

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_multiply
   :end-before: //SNIPPET_END: strassen_multiply

For n > 1 the matrices are split into quadrants A\ :sub:`11`,
A\ :sub:`12`, A\ :sub:`21`, A\ :sub:`22` (and likewise for B), and
seven half-size products are computed:

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_products
   :end-before: //SNIPPET_END: strassen_products

The result quadrants are assembled from these products:

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_combine
   :end-before: //SNIPPET_END: strassen_combine

Complexity
~~~~~~~~~~

The number of scalar multiplications satisfies the recurrence
T(n) = 7 T(n/2), T(1) = 1. The formalization defines a multiplication
count function, proves it is strictly less than n³ for n > 1, and
establishes the closed form T(n) = 7\ :sup:`log₂ n`:

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_complexity
   :end-before: //SNIPPET_END: strassen_complexity

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.Strassen.fst
   :language: fstar
   :start-after: //SNIPPET_START: strassen_closed_form
   :end-before: //SNIPPET_END: strassen_closed_form

The closed-form proof proceeds by induction: unfolding
``strassen_mult_count n = 7 * strassen_mult_count (n/2)`` and
applying the inductive hypothesis gives
``7 * pow7 (log₂(n/2)) = pow7 (log₂ n)``.

Correctness Proof
~~~~~~~~~~~~~~~~~

The main correctness theorem states that Strassen and standard
multiplication agree element-wise:

.. literalinclude:: ../ch28-matrix-ops/CLRS.Ch28.Strassen.fst
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

The single admit is in ``lemma_strassen_elem_correct``: it discharges
the structural property that submatrix quadrants of a square,
power-of-2 matrix are themselves square and power-of-2. This is an
arithmetic fact (not an algorithmic property) that would otherwise
cause a solver timeout due to the large proof context.

Proof Techniques Summary
=========================

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
