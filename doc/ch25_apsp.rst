.. _Ch25_APSP:

###############################################
All-Pairs Shortest Paths: Floyd-Warshall
###############################################

This chapter covers the Floyd-Warshall algorithm from CLRS §25.2, which
computes shortest-path weights between all pairs of vertices in a weighted
directed graph using dynamic programming. The algorithm is fully verified
with **zero admits, assumes, or assume_ calls**. We prove:

1. Functional correctness: the output equals the pure specification.
2. The pure specification computes the classical DP recurrence ``fw_entry``.
3. ``fw_entry`` equals the minimum walk weight (graph-theoretic shortest path).
4. The number of relaxation operations is exactly n³.

The graph is stored as a flat n×n array in row-major layout, with a
sentinel value ``1000000`` representing infinity (no edge). The algorithm
updates the distance matrix in place.

.. list-table:: Chapter 25 Summary
   :header-rows: 1
   :widths: 40 10 50

   * - Property
     - Status
     - Notes
   * - Functional correctness (``contents' == fw_outer``)
     - ✅
     - Impl postcondition
   * - ``fw_outer`` computes ``fw_entry`` at level n
     - ✅
     - ``floyd_warshall_computes_shortest_paths``
   * - ``fw_entry`` = classic DP recurrence
     - ✅
     - Direct encoding in ``Spec.fst``
   * - ``fw_entry`` = min walk weight
     - ✅
     - ``Paths.fst``
   * - Complexity: exactly n³ ops
     - ✅
     - ``fw_complexity_bounded``
   * - Concrete test (3×3)
     - ✅
     - ``SpecTest.fst``
   * - Negative-cycle detection
     - ❌
     - Assumed via precondition
   * - Admits / Assumes
     - **0 / 0**
     -

Specification
=============

The pure specification mirrors the three nested loops of the imperative
algorithm as three recursive functions on sequences:

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_spec
   :end-before: //SNIPPET_END: pure_spec

``fw_inner_j`` processes columns ``j..n-1`` for a fixed row ``i`` and
intermediate vertex ``k``.  The value ``d_ik`` is passed as a parameter
(cached), matching the imperative code's read-once optimization.
``fw_inner_i`` iterates over rows, and ``fw_outer`` iterates over
intermediate vertices.  Each function returns a new sequence, building up
the full Floyd-Warshall computation as ``fw_outer d n 0``.

The specification is *imperative-mirroring*: rather than defining the
algorithm declaratively (e.g., as a minimum over all paths), it directly
encodes the loop structure as recursive sequence transformations.  This
makes the correctness proof between the Pulse implementation and the
spec almost automatic — each loop body simply unfolds the corresponding
recursive call.

FW Recurrence
~~~~~~~~~~~~~

The classic DP recurrence from CLRS Equation 25.5:

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: fw_entry
   :end-before: //SNIPPET_END: fw_entry

Here ``k`` counts how many vertices have been considered as intermediates:
``k=0`` means no intermediates (direct edges), ``k=n`` means all vertices.

Infinity and Safety
~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: inf
   :end-before: //SNIPPET_END: inf

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: safety_predicates
   :end-before: //SNIPPET_END: safety_predicates

``weights_bounded`` ensures path sums cannot reach the infinity sentinel.
``non_negative_diagonal`` (no negative self-loops) is required for the
no-negative-cycles assumption.

Length Preservation
~~~~~~~~~~~~~~~~~~

Three length-preservation lemmas are proved by structural induction
mirroring the specification:

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: length_lemmas
   :end-before: //SNIPPET_END: length_lemmas

These lemmas are essential for the loop invariants: each iteration must
show that array length is preserved so that subsequent index computations
remain in bounds.

Implementation
==============

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The main theorem is the type signature of ``floyd_warshall``:

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Impl.fst
   :language: fstar
   :start-after: //SNIPPET_START: floyd_warshall_sig
   :end-before: //SNIPPET_END: floyd_warshall_sig

Reading this signature:

- **Input**: an array ``dist`` containing a ghost sequence ``contents``
  of length n×n, a size ``n``, and a ghost tick counter ``ctr``.
- **Precondition** (``requires``): the array has n² elements, n > 0,
  and n² fits in ``SZ.t``.
- **Postcondition** (``ensures``): the final array contents equal
  ``fw_outer contents (SZ.v n) 0`` — the pure specification applied
  to the original input — and the tick counter increased by exactly n³.

The ghost parameter ``#contents`` tracks the logical array contents
through separation logic assertions. The ghost tick counter ``ctr``
(``GR.ref nat``) is completely erased at runtime.

**Why this is the strongest functional guarantee:**

- Full equivalence to pure spec, not just "some correct answer".
- Exact complexity (Θ(n³)), not just big-O.
- The Lemmas module further connects ``fw_outer`` to ``fw_entry``.
- The Paths module connects ``fw_entry`` to graph-theoretic shortest paths.

Loop Invariants
~~~~~~~~~~~~~~~

The proof uses a *remaining work* invariant style.  Rather than tracking
what has been computed so far, each invariant asserts that applying the
*remaining* pure computation to the *current* array state yields the
same result as applying the *full* computation to the *original* state.

**Outer loop** (over intermediate vertices ``k``):

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Impl.fst
   :language: fstar
   :start-after: //SNIPPET_START: outer_loop
   :end-before: //SNIPPET_END: outer_loop

The key conjunct is ``fw_outer contents_k n vk == fw_outer contents n 0``:
processing vertices ``vk..n-1`` from the current state equals processing
all vertices from the initial state.  When the loop exits (``vk == n``),
``fw_outer contents_k n n`` reduces to ``contents_k`` (base case of the
recursion), so ``contents_k == fw_outer contents n 0``.

**Middle loop** (over rows ``i``):

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Impl.fst
   :language: fstar
   :start-after: //SNIPPET_START: inner_i_loop
   :end-before: //SNIPPET_END: inner_i_loop

This invariant composes the remaining i-work with the remaining k-work:
processing rows ``vi..n-1`` for vertex ``vk``, then processing vertices
``vk+1..n-1``, equals the full computation.

**Inner loop** (over columns ``j``):

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Impl.fst
   :language: fstar
   :start-after: //SNIPPET_START: inner_j_loop
   :end-before: //SNIPPET_END: inner_j_loop

The innermost invariant composes all three levels: remaining j-work,
remaining i-work, and remaining k-work.  Each loop body performs one
relaxation step — ``d[i][j] = min(d[i][j], d[i][k] + d[k][j])`` —
which exactly matches one unfolding of the ``fw_inner_j`` recursion.

Correctness Lemmas
==================

The main theorem connects the mirroring spec to the declarative
recurrence:

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Lemmas.fsti
   :language: fstar
   :start-after: //SNIPPET_START: floyd_warshall_correct
   :end-before: //SNIPPET_END: floyd_warshall_correct

Supporting lemmas prove that:

- ``fw_inner_j`` correctly computes relaxation for row ``i``.
- ``fw_inner_j`` only modifies row ``i`` (other rows unchanged).
- Row ``k`` is preserved through the full i-loop (critical for the
  cached ``d_ik`` correctness).
- ``fw_inner_i`` correctly computes the full relaxation step.

The inductive ``fw_outer_computes_entry`` proof:

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: fw_outer_computes_entry
   :end-before: //SNIPPET_END: fw_outer_computes_entry

Walk Formalism
==============

The ``Paths`` module connects ``fw_entry`` to graph-theoretic shortest
paths through a complete proof chain:

1. **Walk definitions**: ``is_walk``, ``walk_weight``, ``walk_valid``,
   ``walk_restricted`` (intermediate vertices in ``{0..k-1}``).
2. **Soundness**: ``fw_entry adj n i j k ≤ walk_weight(w)`` for all
   valid restricted walks ``w``.
3. **Achievability**: there exists a walk ``w`` with
   ``walk_weight(w) == fw_entry adj n i j k``.
4. **Final theorem**: ``fw_entry adj n i j n`` equals the minimum walk
   weight over all valid walks — i.e., the true shortest-path distance
   δ(i,j).

This module is **fully proven with zero admits**.

Complexity
==========

The complexity bound is **exact** (Θ(n³)), not merely asymptotic:

.. literalinclude:: ../autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bound
   :end-before: //SNIPPET_END: complexity_bound

Unlike insertion sort's worst-case bound (≤ n(n−1)/2), the
Floyd-Warshall bound is exact — every iteration performs exactly one
relaxation, and every branch of the three nested loops executes.

The proof uses a *linear cost decomposition* across the three loops.
The outer loop invariant tracks that after ``vk`` iterations, exactly
``vk * n * n`` ticks have occurred.  The middle loop adds ``vi * n``
ticks (one row of n relaxations per iteration), and the inner loop adds
one tick per column.  The arithmetic identity
``vk * n * n + n * n = (vk + 1) * n * n`` is discharged automatically
by the SMT solver.

.. list-table:: Complexity Summary
   :header-rows: 1
   :widths: 40 10 50

   * - Aspect
     - Proven
     - Bound
   * - Relaxation operations
     - ✅
     - Exactly n³ (not "O(n³)")
   * - Ghost tick mechanism
     - ✅
     - ``GR.ref nat``, erased at extraction
   * - Runtime overhead
     - None
     - Ghost references compile to nothing

Limitations
===========

1. **Negative-cycle detection not implemented.** The precondition
   ``non_negative_diagonal`` (and the stronger condition that
   ``fw_entry`` diagonal entries remain non-negative at all levels)
   is assumed, not checked at runtime. If the input contains negative
   cycles, the algorithm will silently produce incorrect results.

2. **Fixed infinity sentinel.** The sentinel value ``1000000`` is
   hardcoded. Graphs with edge weights approaching this value may
   produce incorrect results due to integer overflow in path sums.
   The ``weights_bounded`` predicate guards against this but is a
   precondition, not a runtime check.

3. **No predecessor matrix.** CLRS §25.2 also describes maintaining a
   predecessor matrix Π to reconstruct shortest paths. This is not
   implemented — only shortest-path *weights* are computed.

4. **In-place update.** The algorithm overwrites the input distance
   matrix. The original input is available only as a ghost value
   (``#contents``).

Proof Techniques
================

1. **Imperative-mirroring specification**: The pure spec directly
   encodes the loop structure rather than using a declarative
   characterization.  This makes the refinement proof between
   implementation and spec nearly trivial — each loop iteration is
   one unfolding of the corresponding recursive function.

2. **Remaining-work invariants**: Instead of tracking "what I've done
   so far", invariants assert that "applying remaining work to current
   state = applying all work to initial state".  This avoids auxiliary
   definitions for partial results and makes loop-exit reasoning
   immediate (the remaining work is the identity).

3. **Cached reads matching the spec**: The imperative code reads
   ``d[i][k]`` once before the j-loop and reuses it.  The pure spec
   takes ``d_ik`` as a parameter to ``fw_inner_j`` for the same
   reason.  This structural alignment is critical — if the spec
   re-read ``d[i][k]`` inside the j-loop, it could observe intermediate
   updates, breaking the invariant.

4. **Unconditional writes**: The implementation always writes
   ``min(d[i][j], d[i][k] + d[k][j])`` rather than conditionally
   writing only when a shorter path is found.  This avoids branching
   on ghost state in Pulse (conditional writes would require different
   proof obligations for each branch).

5. **Exact complexity via decomposition**: The cost counter decomposes
   as ``vk * n² + vi * n + vj`` across the three loops.  Each loop
   contributes one term, and the SMT solver handles the arithmetic
   identities at loop boundaries.

6. **Ghost erasure**: Both the array contents (``#contents``) and the
   cost counter (``GR.ref nat``) are ghost values, fully erased at
   runtime.  The compiled code is a standard triple-nested loop with
   no proof overhead.
