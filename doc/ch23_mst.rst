.. _Ch23_MST:

######################################
Minimum Spanning Trees: Kruskal & Prim
######################################

This chapter covers the two classical MST algorithms from CLRS
Chapter 23: Kruskal's algorithm (§23.2) and Prim's algorithm (§23.2),
unified by the *cut property* (Theorem 23.1).  Both algorithms are
implemented in Pulse and specified in pure F*.

**Verification status.** All 25 source files verify with **zero
admits, zero assumes, zero --admit_smt_queries**.

.. list-table:: Chapter 23 Summary
   :header-rows: 1
   :widths: 40 10 50

   * - Property
     - Status
     - Notes
   * - Cut property (Theorem 23.1)
     - ✅
     - Edge-exchange argument in ``MST.Spec``
   * - Kruskal pure MST correctness
     - ✅
     - ``theorem_kruskal_produces_mst``
   * - Kruskal greedy bridge
     - ✅
     - ``greedy_step_safe`` via cut property
   * - Kruskal Impl: forest + acyclicity
     - ✅
     - ``result_is_forest`` with UF tracking
   * - Kruskal Impl → MST
     - ⚠️
     - Inner scan invariant needs strengthening
   * - Prim pure MST correctness
     - ✅
     - ``prim_spec``
   * - Prim Impl: ``prim_correct``
     - ✅
     - key[source]=0, keys bounded
   * - Prim Impl → MST
     - ⚠️
     - No bridge to ``prim_spec``
   * - Kruskal O(V³)
     - ✅
     - Complexity module disconnected from Impl
   * - Prim O(V²)
     - ✅
     - Complexity module disconnected from Impl
   * - Admits / Assumes
     - **0 / 0**
     -

MST Specification
=================

The shared specification lives in ``CLRS.Ch23.MST.Spec`` and provides
the graph data types, spanning-tree and MST definitions, and the cut
property.

Graph and MST Definitions
~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch23-mst/CLRS.Ch23.MST.Spec.fsti
   :language: fstar
   :start-after: //SNIPPET_START: graph_defs
   :end-before: //SNIPPET_END: graph_defs

A graph is represented as a vertex count ``n`` and an edge list.
Edges are undirected (``edge_eq`` treats ``(u,v)`` and ``(v,u)``
as identical).

.. literalinclude:: ../ch23-mst/CLRS.Ch23.MST.Spec.fsti
   :language: fstar
   :start-after: //SNIPPET_START: spanning_tree_mst
   :end-before: //SNIPPET_END: spanning_tree_mst

``is_spanning_tree`` requires: (1) edges come from the graph, (2)
exactly ``n − 1`` edges, (3) all vertices reachable, and (4)
acyclicity.  ``is_mst`` adds weight minimality over all spanning
trees.

Cut Property (Theorem 23.1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The cut property is the foundation of both Kruskal and Prim.  A *cut*
partitions vertices into two sets; a *light edge* is a minimum-weight
edge crossing the cut; a cut *respects* edge set ``A`` when no edge
in ``A`` crosses it.

.. literalinclude:: ../ch23-mst/CLRS.Ch23.MST.Spec.fsti
   :language: fstar
   :start-after: //SNIPPET_START: cut_defs
   :end-before: //SNIPPET_END: cut_defs

The main theorem:

.. literalinclude:: ../ch23-mst/CLRS.Ch23.MST.Spec.fsti
   :language: fstar
   :start-after: //SNIPPET_START: cut_property
   :end-before: //SNIPPET_END: cut_property

The proof uses edge exchange: if ``e ∉ T``, adding ``e`` creates a
cycle in ``T ∪ {e}`` that must contain another crossing edge ``e'``
with ``w(e) ≤ w(e')``.  Removing ``e'`` yields a new spanning tree
of weight ≤ ``T``, hence also an MST.  This is **fully verified**
with zero admits.

Kruskal's Algorithm
===================

Pure Specification
~~~~~~~~~~~~~~~~~~

``CLRS.Ch23.Kruskal.Spec`` defines a pure, total Kruskal that sorts
edges by weight, then greedily adds edges that do not create a cycle
(checked via a BFS-based ``same_component_dec``).

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Kruskal.Spec.fsti
   :language: fstar
   :start-after: //SNIPPET_START: pure_kruskal
   :end-before: //SNIPPET_END: pure_kruskal

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The top-level correctness theorems state that ``pure_kruskal``
produces a spanning tree and an MST when the graph is connected:

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Kruskal.Spec.fsti
   :language: fstar
   :start-after: //SNIPPET_START: theorem_kruskal_produces_spanning_tree
   :end-before: //SNIPPET_END: theorem_kruskal_produces_spanning_tree

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Kruskal.Spec.fsti
   :language: fstar
   :start-after: //SNIPPET_START: theorem_kruskal_produces_mst
   :end-before: //SNIPPET_END: theorem_kruskal_produces_mst

The proof relies on the cut property: at each step the current forest
defines a cut (vertices reachable from ``e.u`` vs. the rest), and the
lightest crossing edge is safe.

Strongest guarantee
^^^^^^^^^^^^^^^^^^^

``theorem_kruskal_produces_mst`` is the strongest functional guarantee
for Kruskal: given a connected graph with valid edges and an MST, the
pure algorithm produces an MST.  This covers spanning tree structure
(exactly n−1 edges, connected, acyclic, subset of graph edges) and
weight minimality.  The precondition ``∃ mst. is_mst g mst`` is the
one remaining assumption (MST existence is not derived from
connectivity).

Greedy Bridge
~~~~~~~~~~~~~

``CLRS.Ch23.Kruskal.Bridge`` proves two lemmas that bridge *any*
greedy MST algorithm to MST correctness:

1. ``greedy_step_safe``: Adding the minimum-weight cross-component
   edge to a safe forest (⊆ some MST) preserves the safe-edge
   property, using the cut property with the cut defined by the
   adding vertex's component.

2. ``safe_spanning_tree_is_mst``: A spanning tree that is safe
   (⊆ some MST) is itself an MST.

Union-Find for Kruskal
~~~~~~~~~~~~~~~~~~~~~~

``CLRS.Ch23.Kruskal.UF`` provides a union-find model that tracks
component connectivity alongside the edge list:

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Kruskal.UF.fsti
   :language: fstar
   :start-after: //SNIPPET_START: uf_inv_union
   :end-before: //SNIPPET_END: uf_inv_union

Key invariant: ``uf_inv`` relates the parent array to edge-list
reachability — ``find(u) = find(v)`` iff ``reachable(edges, u, v)``.
Soundness (``uf_inv_unreachable``): different roots imply not
reachable.

Imperative Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~

The Pulse implementation in ``CLRS.Ch23.Kruskal.Impl`` uses a flat
``n × n`` adjacency matrix and a union-find ``parent`` array.  Each
round scans all V² entries for the minimum-weight cross-component
edge, then adds it to the forest.

The postcondition ``result_is_forest`` asserts: (1) edge count ≤
``n − 1``, (2) all selected endpoints are valid vertices, and (3)
the result forms an acyclic edge set (via union-find invariant
tracking).

**Impl → MST gap:** The imperative Kruskal proves forest + acyclicity
but does NOT directly prove MST optimality.  The ``Bridge`` module
provides the mathematical machinery (``greedy_step_safe``), but
connecting it to the imperative loop requires strengthening the inner
scan invariant to track minimum cross-component weight per round.

Prim's Algorithm
================

Pure Specification
~~~~~~~~~~~~~~~~~~

``CLRS.Ch23.Prim.Spec`` defines Prim's algorithm on an adjacency
matrix.  At each step, the algorithm finds the minimum-weight edge
from tree vertices to non-tree vertices and adds it.

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Prim.Spec.fsti
   :language: fstar
   :start-after: //SNIPPET_START: pure_prim
   :end-before: //SNIPPET_END: pure_prim

The specification captures the full correctness goal:

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Prim.Spec.fsti
   :language: fstar
   :start-after: //SNIPPET_START: prim_spec
   :end-before: //SNIPPET_END: prim_spec

The proof strategy mirrors CLRS Corollary 23.2: each step selects
a light edge crossing the cut ``(tree, non-tree)``, so by the cut
property the edge is safe.  The inductive safety proof
(``lemma_prim_aux_safety``) and the edge-count lemma
(``lemma_prim_has_n_minus_1_edges``) are **fully verified with
zero admits**.

Strongest guarantee
^^^^^^^^^^^^^^^^^^^

``prim_spec`` is the strongest functional guarantee for Prim at the
pure level: the result has exactly n−1 edges, connects all vertices,
and is a subset of some MST.  Together these imply the result is a
spanning tree contained in an MST.

Imperative Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~

The Pulse implementation processes an ``n × n`` weight matrix
stored as a ``SZ.t`` array, using 64-bit index arithmetic to avoid
overflow:

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Prim.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: prim_sig
   :end-before: //SNIPPET_END: prim_sig

The postcondition ``prim_correct`` establishes:

- ``key[source] == 0``
- All keys bounded by ``infinity`` (65535)
- ``parent[source] == source``
- Array lengths correct

**Limitation: prim_correct is weak.** It does NOT directly prove
the output is an MST.  It only establishes local properties (key
values, parent validity).  To prove MST optimality from the
imperative output would require connecting the loop invariant to the
pure specification's ``prim_spec`` via ``edges_from_parent_key`` and
the MST theory.  This bridging is not yet implemented.

Complexity
==========

.. literalinclude:: ../ch23-mst/CLRS.Ch23.MST.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: kruskal_cubic
   :end-before: //SNIPPET_END: kruskal_cubic

.. literalinclude:: ../ch23-mst/CLRS.Ch23.MST.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: prim_quadratic
   :end-before: //SNIPPET_END: prim_quadratic

.. list-table:: Complexity Summary
   :header-rows: 1
   :widths: 30 20 20 30

   * - Algorithm
     - Proven Bound
     - Module
     - Connected to Impl?
   * - Kruskal (adj-matrix)
     - O(V³)
     - ``Kruskal.Complexity``
     - ❌ Disconnected
   * - Prim (adj-matrix)
     - O(V²)
     - ``Prim.Complexity``
     - ❌ Disconnected

The ghost-tick complexity modules re-implement the algorithms from
scratch with tick counters.  They prove tick bounds internally but
do NOT reference the main ``Impl`` modules.  Kruskal proves
``ticks ≤ 4·V³``; Prim proves ``ticks ≤ 3·V²``.

Limitations
===========

1. **MST existence assumed, not derived.** The precondition
   ``∃ t. is_mst g t`` appears in both ``Kruskal.Spec`` and
   ``Prim.Spec``.  Deriving MST existence from connectivity alone
   is not done.

2. **Kruskal Impl → MST gap.** The imperative Kruskal proves forest +
   acyclicity but not MST optimality.  The ``Bridge`` module provides
   the mathematical machinery, but connecting it to the imperative
   loop requires strengthening the inner scan invariant.

3. **Prim Impl → MST gap.** ``prim_correct`` is a relatively weak
   postcondition (local key/parent properties).  No bridge connects
   the imperative output to ``prim_spec`` or MST theory.

4. **Complexity modules disconnected.** Both ``Kruskal.Complexity``
   and ``Prim.Complexity`` re-implement algorithms from scratch for
   ghost-tick analysis.

5. **Prim uses two infinity values.** The Pulse implementation uses
   ``65535sz`` (SizeT constraint); the pure spec uses ``1000000000``.

Proof Techniques Summary
=========================

1. **Cut property as unifying theorem**: Both algorithms' correctness
   reduces to the same ``cut_property`` lemma in ``MST.Spec``.

2. **Decidable vs. propositional reachability**: The pure spec uses
   ``same_component_dec`` (BFS-based, decidable) alongside the
   propositional ``same_component`` (existential path).  Soundness
   (``same_component_dec_sound``) bridges the two.

3. **Edge sorting as a separate concern**: ``EdgeSorting`` isolates
   the proof that sorting preserves edge sets and is compatible with
   the greedy strategy.

4. **Union-find invariant tracking**: The imperative Kruskal maintains
   ``uf_inv`` throughout the main loop, relating the parent array to
   edge connectivity.  ``uf_inv_union`` proves the invariant is
   maintained when adding an edge.

5. **Greedy bridge**: ``Kruskal.Bridge`` factors out the general
   greedy-MST argument (any safe forest that greedily adds min-weight
   cross-component edges produces an MST), making it reusable.

6. **64-bit index arithmetic**: Prim's implementation uses explicit
   overflow proofs to compute flat-array indices safely.
