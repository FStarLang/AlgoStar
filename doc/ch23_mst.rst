.. _Ch23_MST:

######################################
Minimum Spanning Trees: Kruskal & Prim
######################################

This chapter covers the two classical MST algorithms from CLRS
Chapter 23: Kruskal's algorithm (§23.2) and Prim's algorithm (§23.3),
unified by the *cut property* (Theorem 23.1).  Both algorithms are
implemented in Pulse and specified in pure F*.

**Verification status.** The MST specification module
(``CLRS.Ch23.MST.Spec``) contains **4 admits** — the cut-property
proof and its supporting graph-theory lemmas (cycle detection,
edge-exchange).  Kruskal's specification (``CLRS.Ch23.Kruskal.Spec``)
has **9 admits**; ``EdgeSorting`` has **2 admits** (sort stability);
``SortedEdges`` has 1 ``assume`` (acyclicity preservation);
``Kruskal.Complexity`` has **2 admits** (arithmetic bounds) + 1
``assume_``; the imperative ``Kruskal.fst`` has 1 ``assume val``
(forest axiom). Prim's specification (``CLRS.Ch23.Prim.Spec``) has
**6 admits** for light-edge and spanning-tree properties.

MST Specification
=================

The shared specification lives in ``CLRS.Ch23.MST.Spec`` and provides
the graph data types, spanning-tree and MST definitions, and the cut
property.

Graph and MST Definitions
~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch23-mst/CLRS.Ch23.MST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: graph_defs
   :end-before: //SNIPPET_END: graph_defs

A graph is represented as a vertex count ``n`` and an edge list.
Edges are undirected (``edge_eq`` treats ``(u,v)`` and ``(v,u)``
as identical).

.. literalinclude:: ../ch23-mst/CLRS.Ch23.MST.Spec.fst
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

.. literalinclude:: ../ch23-mst/CLRS.Ch23.MST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: cut_defs
   :end-before: //SNIPPET_END: cut_defs

The main theorem:

.. literalinclude:: ../ch23-mst/CLRS.Ch23.MST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: cut_property
   :end-before: //SNIPPET_END: cut_property

The proof body is currently ``admit()`` — it requires showing that
adding a light edge to a spanning tree and removing a heavier
crossing edge yields another MST (the edge-exchange argument).

Kruskal's Algorithm
===================

Pure Specification
~~~~~~~~~~~~~~~~~~

``CLRS.Ch23.Kruskal.Spec`` defines a pure, total Kruskal that sorts
edges by weight, then greedily adds edges that do not create a cycle
(checked via a BFS-based ``same_component_dec``).

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Kruskal.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: kruskal_step
   :end-before: //SNIPPET_END: kruskal_step

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Kruskal.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_kruskal
   :end-before: //SNIPPET_END: pure_kruskal

The top-level correctness theorem states that ``pure_kruskal``
produces an MST when the graph is connected:

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Kruskal.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: theorem_kruskal_mst
   :end-before: //SNIPPET_END: theorem_kruskal_mst

The proof relies on the cut property: at each step the current forest
defines a cut (vertices reachable from ``e.u`` vs. the rest), and the
lightest crossing edge is safe.  Several sub-lemmas are admitted,
including forest preservation under edge addition, decidable component
correctness, and the final spanning-tree assembly.

Imperative Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~

The Pulse implementation in ``CLRS.Ch23.Kruskal.fst`` uses a
flat ``n × n`` adjacency matrix and a union-find ``parent`` array
with path following.  Selected edges are stored in output arrays
``edge_u`` and ``edge_v``.

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Kruskal.fst
   :language: pulse
   :start-after: //SNIPPET_START: kruskal_sig
   :end-before: //SNIPPET_END: kruskal_sig

The postcondition ``result_is_forest`` asserts: (1) the edge count is
at most ``n − 1``, (2) all selected endpoints are valid vertices, and
(3) the result forms an acyclic edge set (via ``KSpec.is_forest``).
Property (3) depends on ``assume val lemma_kruskal_maintains_forest``
— an axiom asserting that union-find cycle detection preserves
acyclicity.  Completing this axiom would require tracking union-find
component invariants throughout the main loop.

Edge Sorting
~~~~~~~~~~~~

``CLRS.Ch23.Kruskal.EdgeSorting`` proves that insertion-sort on edges
produces a sorted permutation of the input.  Key results:

- ``sort_edges_produces_sorted``: output satisfies
  ``edges_sorted_by_weight``.
- ``sort_edges_is_permutation``: edge membership is preserved.
- ``theorem_sorted_kruskal_produces_mst``: composing sorting with
  ``pure_kruskal`` yields an MST.

Two admits remain: the proof that insertion sort is *stable*
(preserving relative order of equal-weight edges), and the
``lemma_stable_permutation_equal_mst_weight`` theorem.

Prim's Algorithm
================

Pure Specification
~~~~~~~~~~~~~~~~~~

``CLRS.Ch23.Prim.Spec`` defines Prim's algorithm on an adjacency
matrix.  At each step, ``pure_prim_step`` finds the minimum-weight
edge from tree vertices to non-tree vertices and adds it.

The specification captures the full correctness goal:

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Prim.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: prim_spec
   :end-before: //SNIPPET_END: prim_spec

The proof strategy mirrors CLRS Corollary 23.2: each step selects
a light edge crossing the cut ``(tree, non-tree)``, so by the cut
property the edge is safe.  The inductive safety proof
(``lemma_prim_aux_safety``) and the edge-count lemma
(``lemma_prim_has_n_minus_1_edges``) each contain admits.

Imperative Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~

The Pulse implementation processes an ``n × n`` weight matrix
stored as a ``SZ.t`` array, using 64-bit index arithmetic to avoid
overflow:

.. literalinclude:: ../ch23-mst/CLRS.Ch23.Prim.fst
   :language: pulse
   :start-after: //SNIPPET_START: prim_sig
   :end-before: //SNIPPET_END: prim_sig

The postcondition ``prim_correct`` establishes: ``key[source] == 0``,
all keys bounded, and basic functional properties.  Full MST
optimality is *not* stated in the imperative postcondition — it would
require connecting the loop invariant to the pure specification's
``is_mst`` and the admitted graph-theory lemmas in ``Prim.Spec`` and
``MST.Spec``.

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

4. **Union-find axiomatization**: The imperative Kruskal uses
   ``assume val`` for the forest property, cleanly separating the
   union-find invariant (future work) from the rest of the proof.

5. **64-bit index arithmetic**: Prim's implementation uses
   ``U64.mul_mod`` / ``U64.add_mod`` with explicit overflow proofs
   (``lemma_mul_bound``) to compute flat-array indices safely.
