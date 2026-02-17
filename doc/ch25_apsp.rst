.. _Ch25_APSP:

###############################################
All-Pairs Shortest Paths: Floyd-Warshall
###############################################

This chapter covers the Floyd-Warshall algorithm from CLRS §25.2, which
computes shortest-path weights between all pairs of vertices in a weighted
directed graph using dynamic programming. The algorithm is fully verified
with **zero admits, assumes, or assume_ calls**. We prove:

1. Functional correctness: the output equals the pure specification.
2. The number of relaxation operations is exactly n³.

The graph is stored as a flat n×n array in row-major layout, with a
sentinel value ``1000000`` representing infinity (no edge). The algorithm
updates the distance matrix in place.

Specification
=============

The pure specification mirrors the three nested loops of the imperative
algorithm as three recursive functions on sequences:

.. literalinclude:: ../ch25-apsp/CLRS.Ch25.FloydWarshall.fst
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

Three length-preservation lemmas are proved by structural induction
mirroring the specification:

.. literalinclude:: ../ch25-apsp/CLRS.Ch25.FloydWarshall.fst
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

.. literalinclude:: ../ch25-apsp/CLRS.Ch25.FloydWarshall.fst
   :language: pulse
   :start-after: //SNIPPET_START: floyd_warshall_sig
   :end-before: //SNIPPET_END: floyd_warshall_sig

Reading this signature:

- **Input**: an array ``dist`` containing a ghost sequence ``contents``
  of length n×n, and a size ``n``.
- **Precondition** (``requires``): the array has n² elements, n > 0,
  and n² fits in ``SZ.t``.
- **Postcondition** (``ensures``): the final array contents equal
  ``fw_outer contents (SZ.v n) 0`` — the pure specification applied
  to the original input.

The ghost parameter ``#contents`` tracks the logical array contents
through separation logic assertions.

Loop Invariants
~~~~~~~~~~~~~~~

The proof uses a *remaining work* invariant style.  Rather than tracking
what has been computed so far, each invariant asserts that applying the
*remaining* pure computation to the *current* array state yields the
same result as applying the *full* computation to the *original* state.

**Outer loop** (over intermediate vertices ``k``):

.. literalinclude:: ../ch25-apsp/CLRS.Ch25.FloydWarshall.fst
   :language: pulse
   :start-after: //SNIPPET_START: outer_loop
   :end-before: //SNIPPET_END: outer_loop

The key conjunct is ``fw_outer contents_k n vk == fw_outer contents n 0``:
processing vertices ``vk..n-1`` from the current state equals processing
all vertices from the initial state.  When the loop exits (``vk == n``),
``fw_outer contents_k n n`` reduces to ``contents_k`` (base case of the
recursion), so ``contents_k == fw_outer contents n 0``.

**Middle loop** (over rows ``i``):

.. literalinclude:: ../ch25-apsp/CLRS.Ch25.FloydWarshall.fst
   :language: pulse
   :start-after: //SNIPPET_START: inner_i_loop
   :end-before: //SNIPPET_END: inner_i_loop

This invariant composes the remaining i-work with the remaining k-work:
processing rows ``vi..n-1`` for vertex ``vk``, then processing vertices
``vk+1..n-1``, equals the full computation.

**Inner loop** (over columns ``j``):

.. literalinclude:: ../ch25-apsp/CLRS.Ch25.FloydWarshall.fst
   :language: pulse
   :start-after: //SNIPPET_START: inner_j_loop
   :end-before: //SNIPPET_END: inner_j_loop

The innermost invariant composes all three levels: remaining j-work,
remaining i-work, and remaining k-work.  Each loop body performs one
relaxation step — ``d[i][j] = min(d[i][j], d[i][k] + d[k][j])`` —
which exactly matches one unfolding of the ``fw_inner_j`` recursion.

Complexity
==========

The complexity-instrumented version threads a ghost counter through the
implementation, proving that the total number of relaxation operations
is exactly n³.

The ``tick`` function increments a ``GhostReference.ref nat`` — a
reference that exists only for specification purposes and is completely
erased at runtime:

.. literalinclude:: ../ch25-apsp/CLRS.Ch25.FloydWarshall.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: ghost_tick
   :end-before: //SNIPPET_END: ghost_tick

The complexity bound predicate:

.. literalinclude:: ../ch25-apsp/CLRS.Ch25.FloydWarshall.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bound
   :end-before: //SNIPPET_END: complexity_bound

The complexity theorem signature:

.. literalinclude:: ../ch25-apsp/CLRS.Ch25.FloydWarshall.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: floyd_warshall_complexity_sig
   :end-before: //SNIPPET_END: floyd_warshall_complexity_sig

The postcondition says: the final counter value ``cf`` minus the initial
value ``c0`` is exactly ``n * n * n``, and the output is functionally
correct.  Unlike insertion sort's worst-case bound (≤ n(n−1)/2), the
Floyd-Warshall bound is exact — every iteration performs exactly one
relaxation, and every branch of the three nested loops executes.

The proof uses a *linear cost decomposition* across the three loops.
The outer loop invariant tracks that after ``vk`` iterations, exactly
``vk * n * n`` ticks have occurred:

.. literalinclude:: ../ch25-apsp/CLRS.Ch25.FloydWarshall.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: complexity_k_invariant
   :end-before: //SNIPPET_END: complexity_k_invariant

The middle loop adds ``vi * n`` ticks (one row of n relaxations per
iteration), and the inner loop adds one tick per column.  The arithmetic
identity ``vk * n * n + n * n = (vk + 1) * n * n`` (and similarly for
the inner loops) is discharged automatically by the SMT solver.

Proof Notes
===========

This chapter demonstrates several proof techniques:

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
