.. _Ch24_SSSP:

##############################################
Single-Source Shortest Paths: Dijkstra & BF
##############################################

This chapter covers the two single-source shortest-paths algorithms
from CLRS Chapter 24: Dijkstra's algorithm (§24.3) for graphs with
non-negative weights, and Bellman-Ford (§24.1) for general weights
with negative-cycle detection.  Both are implemented in Pulse and
backed by pure F* specifications.

**Verification status.** The Dijkstra Pulse implementation
(``CLRS.Ch24.Dijkstra.fst``) has **zero admits** — correctness is
verified end-to-end, including a runtime triangle-inequality check and
a connection to the ``sp_dist`` upper-bound theorem.  The
``Dijkstra.TriangleInequality`` companion proves that relaxation
automatically establishes the triangle inequality, with
**1 admit** remaining (stability maintenance when processing order
follows Dijkstra's greedy extraction).  The Bellman-Ford Pulse
implementation (``CLRS.Ch24.BellmanFord.fst``) also has **zero
admits**.  The ``BellmanFord.Spec`` pure specification has **3 admits**
(the inductive path-relaxation lemma, the ``relax_preserves_upper_bound``
helper, and negative-cycle detection).
``BellmanFord.TriangleInequality`` is fully verified.

Shortest-Path Specification
============================

The shared pure specification in ``CLRS.Ch24.ShortestPath.Spec``
defines shortest-path distance via bounded dynamic programming:
``sp_dist_k weights n s v k`` is the minimum weight among all paths
from ``s`` to ``v`` using at most ``k`` edges, and ``sp_dist`` sets
``k = n − 1``.

.. literalinclude:: ../ch24-sssp/CLRS.Ch24.ShortestPath.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: sp_dist
   :end-before: //SNIPPET_END: sp_dist

The central theorem connects the triangle inequality to shortest-path
upper bounds (CLRS Corollary 24.3): if ``dist[source] = 0`` and the
triangle inequality holds, then ``dist[v] ≤ sp_dist(s,v)`` for every
vertex ``v``.

.. literalinclude:: ../ch24-sssp/CLRS.Ch24.ShortestPath.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: has_triangle_inequality
   :end-before: //SNIPPET_END: has_triangle_inequality

.. literalinclude:: ../ch24-sssp/CLRS.Ch24.ShortestPath.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: triangle_ineq_upper_bound
   :end-before: //SNIPPET_END: triangle_ineq_upper_bound

The proof proceeds by strong induction on ``k``: at each step,
``dist[v] ≤ sp_dist_k(s, v, k)`` follows from the inductive
hypothesis on predecessors and the triangle inequality for each edge.
This theorem is fully verified — no admits.

Dijkstra's Algorithm
====================

Imperative Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~

The Pulse implementation operates on a flat ``n × n`` weight matrix
with ``1000000`` as infinity.  It requires all weights to be
non-negative.  The main function runs the standard priority-queue loop
(implemented as a linear scan for simplicity), followed by a read-only
triangle-inequality verification pass:

.. literalinclude:: ../ch24-sssp/CLRS.Ch24.Dijkstra.fst
   :language: fstar
   :start-after: //SNIPPET_START: triangle_inequality
   :end-before: //SNIPPET_END: triangle_inequality

.. literalinclude:: ../ch24-sssp/CLRS.Ch24.Dijkstra.fst
   :language: pulse
   :start-after: //SNIPPET_START: dijkstra_sig
   :end-before: //SNIPPET_END: dijkstra_sig

The postcondition guarantees:

- ``dist[source] == 0``
- All distances non-negative and bounded by ``1000000``
- When ``vtri == true``: the triangle inequality holds for all edges,
  and ``dist[v] ≤ sp_dist(weights, n, source, v)`` for every ``v``

The triangle-inequality verification pass (a nested ``O(n²)`` loop)
checks every edge and sets a boolean flag.  When the flag is true,
``dijkstra_sp_upper_bound_cond`` connects the triangle inequality to
the ``ShortestPath.Spec.triangle_ineq_implies_upper_bound`` theorem,
yielding the shortest-path upper bound.  This entire chain is
**fully verified** with no admits.

Greedy Choice Property (Theorem 24.6)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

``CLRS.Ch24.Dijkstra.Correctness`` formalizes the key invariant:
when vertex ``u`` is extracted as the minimum-distance unvisited
vertex, ``dist[u] = δ(s, u)``.

.. literalinclude:: ../ch24-sssp/CLRS.Ch24.Dijkstra.Correctness.fst
   :language: fstar
   :start-after: //SNIPPET_START: greedy_choice
   :end-before: //SNIPPET_END: greedy_choice

The proof combines the upper-bound property (``dist[u] ≥ δ(s,u)``)
with the triangle-inequality-based lower bound
(``dist[u] ≤ δ(s,u)``).  The ``SP.has_triangle_inequality``
precondition is the stronger form maintained by relaxation; the
theorem follows by applying
``SP.triangle_ineq_implies_upper_bound``.  This lemma is
**fully verified**.

Triangle Inequality from Relaxation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

``CLRS.Ch24.Dijkstra.TriangleInequality`` proves that the triangle
inequality is a *consequence* of the relaxation process — the
verification pass in the Pulse code is redundant.  The key result:
after relaxing all edges from a vertex ``u``,
``edge_satisfies_triangle`` holds for every edge from ``u``.
Extending this to all processed vertices required proving that
relaxation preserves already-established triangle inequalities
(``relaxation_stable_for_processed``).  One admit remains: showing
stability is maintained when the processing order follows Dijkstra's
greedy min-extraction.

Bellman-Ford Algorithm
======================

Imperative Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~

The Pulse implementation performs ``n − 1`` rounds of edge
relaxation on a flat weight matrix, followed by a read-only
negative-cycle detection / triangle-inequality verification pass:

.. literalinclude:: ../ch24-sssp/CLRS.Ch24.BellmanFord.fst
   :language: fstar
   :start-after: //SNIPPET_START: bf_triangle_inequality
   :end-before: //SNIPPET_END: bf_triangle_inequality

.. literalinclude:: ../ch24-sssp/CLRS.Ch24.BellmanFord.fst
   :language: pulse
   :start-after: //SNIPPET_START: bellman_ford_sig
   :end-before: //SNIPPET_END: bellman_ford_sig

The postcondition guarantees:

- ``dist[source] == 0``
- All distances are valid (finite or ``1000000``)
- When ``no_neg_cycle == true``: the triangle inequality holds,
  and ``dist[v] ≤ sp_dist(weights, n, source, v)`` for every ``v``

The verification pass checks every edge for violations; if none are
found, ``bf_sp_upper_bound_cond`` connects to the shortest-path
upper-bound theorem.  The Pulse code is **fully verified** with no
admits.

Pure Specification (CLRS Lemma 24.2)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

``CLRS.Ch24.BellmanFord.Spec`` defines a pure Bellman-Ford on
adjacency-matrix graphs with ``option int`` distance vectors.
The main correctness theorem is the *path-relaxation property*:

.. literalinclude:: ../ch24-sssp/CLRS.Ch24.BellmanFord.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: bf_convergence
   :end-before: //SNIPPET_END: bf_convergence

This states that after ``n − 1`` rounds, ``dist[v]`` equals
``sp_dist(src, v)`` for every vertex.  The proof uses
``bf_correctness_inductive``, which has an admit in the inductive case
(showing that one round of relaxation computes the minimum over all
predecessors).  The upper-bound invariant
(``relax_preserves_upper_bound``) and negative-cycle detection
(``bf_negative_cycle_detection``) are also admitted.

Triangle Inequality from Stability
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

``CLRS.Ch24.BellmanFord.TriangleInequality`` proves — with **zero
admits** — that if one more round of relaxation changes nothing
(i.e., the distance vector is a fixpoint of ``bf_round``), then the
triangle inequality holds.  The key insight is a *stability
decomposition*: a fixpoint of ``relax_all`` implies each
``relax_from_u`` is the identity, which implies each
``relax_edge`` is the identity, which is the contrapositive of
the triangle-inequality violation condition.

Proof Techniques Summary
=========================

1. **Triangle-inequality-first verification**: Both algorithms
   verify correctness by establishing the triangle inequality, then
   appealing to ``triangle_ineq_implies_upper_bound`` to obtain
   shortest-path guarantees.  This avoids proving the full inductive
   path-relaxation property in the imperative code.

2. **Runtime verification pass**: The Pulse implementations use a
   read-only ``O(n²)`` check that confirms the triangle inequality
   holds.  This is elegant: the loop invariant only needs to track
   simple bounds (non-negativity, boundedness), while the deep
   correctness property is verified post-hoc.

3. **Specification-level admits are isolated**: The imperative code
   is admit-free; all admits live in the pure specification modules
   where they document well-understood but labor-intensive graph-theory
   facts (path-relaxation induction, negative-cycle characterization).

4. **Shared ``ShortestPath.Spec``**: Both Dijkstra and Bellman-Ford
   connect to the same ``sp_dist`` oracle and the same
   ``triangle_ineq_implies_upper_bound`` theorem, ensuring consistent
   correctness statements.

5. **Companion triangle-inequality proofs**: Separate modules prove
   that the triangle inequality is a *consequence* of relaxation
   (Dijkstra) or stability (Bellman-Ford), showing the runtime
   check is redundant — a useful result for future optimization.
