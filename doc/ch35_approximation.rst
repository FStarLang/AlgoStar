.. _Ch35_Approximation:

########################################
Approximation Algorithms: Vertex Cover
########################################

This chapter covers the 2-approximation vertex cover algorithm from
CLRS Chapter 35, Section 35.1 (APPROX-VERTEX-COVER). The
formalization proves that the greedy matching-based algorithm always
produces a valid vertex cover and that its size is at most twice the
optimum. The core approximation-ratio proof (CLRS Theorem 35.1) is
fully verified with zero admits. The connection from the Pulse
implementation to the pure theorem is also **fully verified with
zero admits**, including the bridge from the algorithmic execution
trace to the matching structure in ``CLRS.Ch35.VertexCover.Spec``.

Graph and Cover Definitions
============================

Graphs are represented as adjacency matrices over ``n`` vertices.
Covers are modeled as boolean functions on vertex indices:

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: type_defs
   :end-before: //SNIPPET_END: type_defs

An ``edge`` is a pair of vertex indices. ``pairwise_disjoint``
captures the key property of a matching: no two edges share a
vertex. ``is_valid_cover_for_edges`` requires that for every edge
at least one endpoint is in the cover. ``count_cover`` counts
vertices in a cover up to index ``n``.

Minimum Vertex Cover
~~~~~~~~~~~~~~~~~~~~~

The optimization target is formalized as a standard min-cost
predicate:

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: min_vertex_cover
   :end-before: //SNIPPET_END: min_vertex_cover

``is_minimum_vertex_cover`` asserts that ``c_min`` is a valid cover
whose cardinality is at most that of any other valid cover.
``min_vertex_cover_size`` wraps this as an existential proposition
about the optimum value ``opt``.

Approximation-Ratio Proof
===========================

The proof of CLRS Theorem 35.1 proceeds in two steps:

1. **Matching lower bound**: any valid cover must include at least
   one endpoint of each edge in a pairwise-disjoint matching,
   so ``|cover| ≥ |matching|``.

2. **Algorithm cover size**: the cover produced by taking both
   endpoints of every matching edge has size exactly
   ``2 × |matching|``.

Matching Lower Bound
~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: matching_lower_bound
   :end-before: //SNIPPET_END: matching_lower_bound

The proof composes two lemmas: ``sum_ge_length`` (each edge
contributes ≥ 1 to the sum because the cover must include at least
one endpoint) and ``sum_le_count`` (the sum of contributions over a
disjoint matching is at most the total cover count, since disjoint
edges use distinct vertices).

Matching Cover Size
~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: matching_cover_size
   :end-before: //SNIPPET_END: matching_cover_size

This lemma proves that taking all endpoints of a pairwise-disjoint
matching produces a cover of size ``2 × |matching|``. The proof
proceeds by induction on the matching list, using
``matching_cover_add_two`` to account for each edge's two fresh
vertices and ``existsb_false_forall`` to show that disjointness
prevents double-counting.

Theorem 35.1
~~~~~~~~~~~~~

Combining the two lemmas yields the 2-approximation guarantee:

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: theorem_35_1
   :end-before: //SNIPPET_END: theorem_35_1

The postcondition states three facts: the algorithm's cover size
equals ``2 × |M|``, any optimal cover has size ≥ ``|M|``, and
therefore the algorithm's cover is at most ``2 × OPT``.

Pulse Implementation
=====================

The imperative implementation uses an adjacency-matrix representation
and a mutable cover array initialized to zero.

Cover Invariant
~~~~~~~~~~~~~~~~

The loop invariant tracks which edges have been examined so far:

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_cover
   :end-before: //SNIPPET_END: is_cover

``is_cover`` asserts that all edges ``(u, v)`` with ``u < v``
examined before position ``(bound_u, bound_v)`` have at least one
endpoint with a non-zero cover entry.

Algorithm Signature
~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.fst
   :language: pulse
   :start-after: //SNIPPET_START: approx_vertex_cover_sig
   :end-before: //SNIPPET_END: approx_vertex_cover_sig

The postcondition guarantees three properties: the output is a valid
cover (``is_cover``), all entries are binary (0 or 1), and the
2-approximation bound holds for every possible ``opt``.

Outer Loop
~~~~~~~~~~~

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.fst
   :language: pulse
   :start-after: //SNIPPET_START: outer_loop
   :end-before: //SNIPPET_END: outer_loop

The outer loop iterates over rows ``u`` of the adjacency matrix. The
invariant maintains ``is_cover`` up to row ``vu`` and the binary
property on all cover entries. The inner loop iterates over columns
``v > u``, and for each uncovered edge ``(u, v)`` sets both
``cover[u]`` and ``cover[v]`` to 1.

Complexity
==========

The algorithm examines every entry in the upper triangle of the
adjacency matrix:

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: vertex_cover_ops
   :end-before: //SNIPPET_END: vertex_cover_ops

The total work is O(V²) for a graph with V vertices, matching the
cost of a single pass over the adjacency matrix.

Proof Status
=============

This chapter is **fully verified with zero admits**. All proofs are
complete, including ``theorem_35_1``, all supporting lemmas in
``CLRS.Ch35.VertexCover.Spec``, the Pulse loop invariants and
cover-validity proof, the complexity analysis, and the
``approximation_ratio_theorem`` connecting the Pulse algorithm's
output to the matching structure.
