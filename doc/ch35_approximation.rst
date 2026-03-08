.. _Ch35_Approximation:

########################################
Approximation Algorithms: Vertex Cover
########################################

This chapter covers the 2-approximation vertex cover algorithm from
CLRS Chapter 35, Section 35.1 (APPROX-VERTEX-COVER). The
formalization proves that the greedy matching-based algorithm always
produces a valid vertex cover and that its size is at most twice the
optimum. The implementation and all proofs — including CLRS
Theorem 35.1 and the bridge from the Pulse implementation to the
pure theorem — are **fully verified with zero admits**.

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

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Lemmas.fst
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

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Lemmas.fst
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

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: theorem_35_1
   :end-before: //SNIPPET_END: theorem_35_1

The postcondition states three facts: the algorithm's cover size
equals ``2 × |M|``, any optimal cover has size ≥ ``|M|``, and
therefore the algorithm's cover is at most ``2 × OPT``.

Pulse Implementation
=====================

The imperative implementation uses an adjacency-matrix representation
and a mutable cover array initialized to zero. The algorithm scans
the upper triangle of the adjacency matrix (pairs (u, v) with u < v),
which is correct for undirected graphs.

Algorithm Signature
~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: approx_vertex_cover_sig
   :end-before: //SNIPPET_END: approx_vertex_cover_sig

The postcondition guarantees four properties:

1. **Correct length**: ``Seq.length s_cover == SZ.v n``.
2. **Valid cover** (``is_cover``): all edges (u, v) with u < v have
   at least one endpoint with a non-zero cover entry.
3. **Binary output**: every cover entry is 0 or 1.
4. **2-approximation**: for every possible optimal value ``opt``
   satisfying ``min_vertex_cover_size``,
   ``count_cover(cover) ≤ 2 × opt``.

Implementation with Ghost Matching
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The implementation maintains a ghost reference tracking the matching —
the set of edges that triggered vertex additions during execution:

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Impl.fst
   :language: fstar
   :start-after: //SNIPPET_START: approx_vertex_cover
   :end-before: //SNIPPET_END: approx_vertex_cover

The nested loops iterate over all vertex pairs (u, v) with u < v.
For each uncovered edge, both endpoints are added to the cover and
the edge is added to the ghost matching. The loop invariants ensure:

- ``is_cover`` holds up to the current scan position
- The cover is binary (all entries 0 or 1)
- ``matching_inv``: the ghost matching is pairwise disjoint, and the
  cover entries correspond exactly to the matching endpoints

After the loops complete, ``apply_approximation_bound`` bridges from
the Pulse state to the abstract ``theorem_35_1``.

Approximation Ratio Bridge
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The connection from the Pulse implementation to the pure theorem
is established by ``approximation_ratio_theorem``:

.. literalinclude:: ../ch35-approximation/CLRS.Ch35.VertexCover.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: approximation_ratio_theorem
   :end-before: //SNIPPET_END: approximation_ratio_theorem

This lemma shows that the concrete cover array (converted to a
``cover_fn`` via ``seq_to_cover_fn``) has the same counting behavior
as the abstract matching-based cover function, and then applies
``theorem_35_1`` to derive the 2-approximation bound.

Complexity
==========

The algorithm examines every entry in the upper triangle of the
adjacency matrix, giving O(V²) time:

.. code-block:: fstar

   let vertex_cover_iterations (v: nat) : nat = v * (v - 1) / 2

   let vertex_cover_quadratic (v: nat)
     : Lemma (ensures vertex_cover_iterations v <= v * v) = ()

   let vertex_cover_tight_bound (v: nat)
     : Lemma (ensures vertex_cover_iterations v <= v * v / 2) = ()

**Limitation**: CLRS achieves O(V + E) using adjacency lists by
maintaining a set of remaining edges. This implementation uses an
adjacency matrix, requiring O(V²) even for sparse graphs. The
complexity definitions are proven but are **not formally linked** to
the Pulse implementation via ghost operation counters.

Limitations
============

- **Adjacency matrix representation**: O(V²) space and time, even
  for sparse graphs. CLRS uses adjacency lists for O(V + E).
- **Upper-triangle scan** (u < v): correct for undirected graphs;
  directed graphs would need full matrix scan.
- **Graph size limited**: ``n × n`` must fit in ``SizeT``.
- **No edge output**: the matching exists only as a ghost value.
- **Tight ratio not proven**: the 2× bound is proven to be achieved,
  but existence of graphs achieving ratio exactly 2 is not
  formalized.

Proof Techniques Summary
=========================

1. **Ghost matching**: A ghost reference tracks the set of edges
   that triggered vertex additions. This is invisible at runtime
   but enables the verification to reason about the matching
   structure.

2. **Loop invariant composition**: The nested loop invariants
   compose three independent properties — ``is_cover``, binary
   output, and ``matching_inv`` — that are maintained independently
   at each step via separate step lemmas.

3. **Matching-based lower bound**: The proof that any valid cover
   has size ≥ |matching| uses a contribution counting argument:
   each edge in a disjoint matching contributes ≥ 1 to any cover,
   and disjointness prevents overlap. This mirrors the textbook
   proof of CLRS Theorem 35.1.

4. **Bridge from Pulse to pure**: ``seq_to_cover_fn`` converts the
   concrete ``seq int`` to a ``cover_fn``, and ``count_cover_ext``
   shows extensional equality of the counting functions, enabling
   the pure theorem to apply to the imperative output.

Verification Status Summary
=============================

.. list-table::
   :header-rows: 1
   :widths: 40 20 20

   * - Module
     - Type
     - Admits
   * - VertexCover.Spec
     - Pure spec
     - 0
   * - VertexCover.Lemmas
     - Pure proof
     - 0
   * - VertexCover.Complexity
     - Pure proof
     - 0
   * - VertexCover.Impl
     - Pulse impl
     - 0

All modules are fully verified with 0 admits ✅.
