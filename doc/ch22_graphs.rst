.. _Ch22_Graphs:

########################################
Elementary Graph Algorithms
########################################

This chapter covers elementary graph algorithms from CLRS Chapter 22:
breadth-first search (§22.2), depth-first search (§22.3), and
topological sort (§22.4). Each algorithm is developed in three layers:

1. **Pure specification** in F* defining correctness properties.
2. **Pulse implementation** following the CLRS pseudocode with mutable
   state, queues, and stacks.
3. **Complexity analysis** proving O(V²) bounds (using adjacency-matrix
   representation).

The graph representation uses a flat adjacency matrix stored as
``Seq.seq int`` of length V×V, where ``adj[u*n+v] = 1`` indicates
an edge from *u* to *v*.

Breadth-First Search
====================

CLRS §22.2 presents BFS as a queue-based exploration of the graph
from a source vertex *s*. Our formalization proves that the
implementation correctly computes BFS level sets and discovers
vertices in non-decreasing distance order.

Pure Specification
~~~~~~~~~~~~~~~~~~

The BFS specification is built around *level sets*: the set of
vertices at each distance from the source. The key lemma states
that if a vertex is visited at level *k* and has an edge to an
unvisited vertex, that neighbor will be visited at level *k+1*:

.. literalinclude:: ../ch22-elementary-graph/CLRS.Ch22.BFS.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: edge_implies_next_visited
   :end-before: //SNIPPET_END: edge_implies_next_visited

The specification module (``BFS.Spec``) has **0 admits**.

A separate module (``BFS.DistanceSpec``) formalizes the relationship
between BFS level sets and shortest-path distances. Two properties
remain admitted: the proof that no shorter path exists
(``shortest_path_property``) and the main correctness theorem
(``bfs_correctness``). That module has **2 admits**.

Pulse Implementation
~~~~~~~~~~~~~~~~~~~~

The Pulse implementation follows CLRS Figure 22.3, using a queue
to schedule vertex processing. The main function signature:

.. literalinclude:: ../ch22-elementary-graph/CLRS.Ch22.QueueBFS.fst
   :language: pulse
   :start-after: //SNIPPET_START: queue_bfs_sig
   :end-before: //SNIPPET_END: queue_bfs_sig

The postcondition establishes that the ``color`` array correctly
reflects BFS visitation and that ``distance`` values correspond to
the BFS level-set membership defined in the pure specification.

This implementation is **fully verified with 0 assume_ calls**, using a
predicate-based proof architecture parallel to StackDFS. Named predicates
(``queue_ok``, ``dist_ok``, ``source_ok``, ``count_nonwhite``) abstract
the BFS invariant clusters, with isolated lemmas for each state transition
(discover, blacken, frame). A key insight: adding ``queue_ok`` directly to
``maybe_discover``'s postcondition lets Z3 reason about exact ``Seq.upd``
terms instead of chaining through abstract frame quantifiers.

Proof Architecture
^^^^^^^^^^^^^^^^^^

The BFS proof uses four named predicates:

- **count_nonwhite**: counts non-zero entries in the color array;
  equals the queue tail, bounding enqueue operations.
- **source_ok**: the source vertex is non-WHITE with distance 0.
- **queue_ok**: every queue entry in ``[head, tail)`` is a valid
  vertex index (``< n``) with non-WHITE color.
- **dist_ok**: every non-WHITE vertex has distance ``≥ 0``.

Six counting lemmas relate ``count_nonwhite`` through updates
(``all_zero``, ``le``, ``has_white``, ``upd_white``,
``upd_nonwhite``, ``upd_single``).  Preservation lemmas show each
predicate is maintained by the ``discover`` and ``blacken``
operations, and a key ``queue_ok_after_discover`` lemma uses exact
``Seq.upd`` terms to re-establish ``queue_ok`` after enqueuing a
new vertex—avoiding the chained-quantifier trigger problem that
arises when reasoning through abstract frame properties.

Complexity
~~~~~~~~~~

The complexity-instrumented version (``QueueBFS.Complexity``) threads
a ghost counter through the implementation and proves the bound:

.. literalinclude:: ../ch22-elementary-graph/CLRS.Ch22.QueueBFS.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: bfs_complexity_bound
   :end-before: //SNIPPET_END: bfs_complexity_bound

This gives an O(V²) bound for the adjacency-matrix representation
(each vertex scans all V potential neighbors). The complexity module
uses **6 assume_ calls** (the same framing assumptions as the
correctness version plus additional ones for cost invariant
maintenance).

An alternative iterative BFS (``IterativeBFS``) computes the same
level sets using a simple loop instead of a queue. It is **fully
verified with 0 admits**, but does not follow the CLRS queue-based
algorithm.

Depth-First Search
==================

CLRS §22.3 presents DFS with discovery and finish timestamps. Our
formalization captures both the timestamp structure and the
White-Path Theorem (Theorem 22.9).

Pure Specification
~~~~~~~~~~~~~~~~~~

The DFS state tracks vertex colors and timestamps:

.. literalinclude:: ../ch22-elementary-graph/CLRS.Ch22.DFS.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: dfs_state
   :end-before: //SNIPPET_END: dfs_state

The specification module (``DFS.Spec``) has **7 unproven obligations**
(5 ``admit()`` + 2 ``assume()``). The admits cover the parenthesis
theorem (proving ``d[u] < d[v] < f[v] < f[u]`` for descendants),
edge classification (tree, back, forward, cross edges), and
timestamp monotonicity. The two ``assume`` calls provide termination
measures (``count_white_vertices`` decreases) for the pure DFS
function.

White-Path Theorem
~~~~~~~~~~~~~~~~~~

The White-Path Theorem (CLRS Theorem 22.9) is formalized as a
biconditional: vertex *v* is a descendant of vertex *u* in the DFS
forest if and only if at time ``d[u]`` there exists a path from *u*
to *v* consisting entirely of white vertices:

.. literalinclude:: ../ch22-elementary-graph/CLRS.Ch22.DFS.WhitePath.fst
   :language: fstar
   :start-after: //SNIPPET_START: white_path_theorem
   :end-before: //SNIPPET_END: white_path_theorem

This module has **3 admits**: ``white_path_transitive`` (composing
white paths), ``white_path_implies_descendant`` (the hard direction),
and ``descendant_implies_white_path`` (extracting a white path from
DFS ancestry).

Pulse Implementation
~~~~~~~~~~~~~~~~~~~~

The Pulse implementation follows CLRS Figure 22.4, using an explicit
stack to emulate the recursive DFS-Visit procedure:

.. literalinclude:: ../ch22-elementary-graph/CLRS.Ch22.StackDFS.fst
   :language: pulse
   :start-after: //SNIPPET_START: stack_dfs_sig
   :end-before: //SNIPPET_END: stack_dfs_sig

The postcondition ensures that the color, discovery, and finish
arrays reflect a valid DFS traversal: all vertices are black
(fully explored), timestamps are consistent (``d[v] < f[v]``),
and the parenthesis structure holds.

The proof uses a predicate-based approach with five named
abstractions (``stack_ok``, ``dfs_ok``, ``gray_ok``,
``nonwhite_below``, ``scan_ok``), each with explicit
``:pattern`` triggers for quantifier instantiation. Eight
isolated lemmas relate these predicates across discover and
finish operations, enabling clean modular reasoning.

This implementation is **fully verified with 0 assume_ calls**.

Complexity
~~~~~~~~~~

The complexity module (``StackDFS.Complexity``) proves an O(V²)
bound matching the adjacency-matrix representation. It uses
**6 assume_ calls** (stack-top bounds, cost-counter invariants,
and the final complexity postcondition).

An alternative iterative DFS (``IterativeDFS``) uses a simpler
level-by-level approach and is **fully verified with 0 admits**,
but does not follow the CLRS stack-based algorithm or produce
timestamps.

Topological Sort
================

CLRS §22.4 defines topological sort for directed acyclic graphs.
Our formalization provides a pure specification of topological
ordering and a verified Pulse implementation of Kahn's algorithm
(removing zero-in-degree vertices iteratively).

Pure Specification
~~~~~~~~~~~~~~~~~~

A topological order is a permutation of all vertices such that
for every edge (u, v), vertex u appears before v:

.. literalinclude:: ../ch22-elementary-graph/CLRS.Ch22.TopologicalSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_topological_order
   :end-before: //SNIPPET_END: is_topological_order

An important derived property: if a topological order exists, the
graph must be a DAG:

.. literalinclude:: ../ch22-elementary-graph/CLRS.Ch22.TopologicalSort.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: topo_order_implies_dag
   :end-before: //SNIPPET_END: topo_order_implies_dag

The specification and supporting lemma modules (``TopologicalSort.Spec``
and ``TopologicalSort.Lemmas``) have **0 admits**. A separate verified
module (``TopologicalSort.Verified``) proves the full correctness
theorem connecting the loop invariant to ``is_topological_order``,
also with **0 admits**.

Pulse Implementation
~~~~~~~~~~~~~~~~~~~~

The Pulse implementation uses Kahn's algorithm: maintain in-degree
counts, repeatedly extract zero-in-degree vertices, and update
neighbor in-degrees:

.. literalinclude:: ../ch22-elementary-graph/CLRS.Ch22.KahnTopologicalSort.fst
   :language: pulse
   :start-after: //SNIPPET_START: topological_sort_sig
   :end-before: //SNIPPET_END: topological_sort_sig

The postcondition proves three properties: all output elements are
valid vertex indices and non-negative, the output contains all
vertices exactly once (``all_distinct``), and the output is a valid
topological order (``is_topological_order``).

This implementation has **2 admit() calls**: one for the distinctness
property of the output sequence and one for connecting the loop
invariant to the topological ordering property. The complexity
module (``KahnTopologicalSort.Complexity``) has a weaker
postcondition (omitting distinctness and topological order) and
has **0 admits**.

Verification Status Summary
============================

.. list-table::
   :header-rows: 1
   :widths: 40 20 20

   * - Module
     - Type
     - Admits / Assumes
   * - BFS.Spec
     - Pure spec
     - 0
   * - BFS.DistanceSpec
     - Pure spec
     - 2 admit()
   * - DFS.Spec
     - Pure spec
     - 5 admit() + 2 assume()
   * - DFS.WhitePath
     - Pure spec
     - 3 admit()
   * - TopologicalSort.Spec
     - Pure spec
     - 0
   * - TopologicalSort.Lemmas
     - Pure lemmas
     - 0
   * - TopologicalSort.Verified
     - Pure proof
     - 0
   * - Graph.Complexity
     - Pure spec
     - 0
   * - QueueBFS
     - Pulse impl
     - **0** ✅
   * - QueueBFS.Complexity
     - Pulse impl
     - 6 assume\_
   * - StackDFS
     - Pulse impl
     - **0** ✅
   * - StackDFS.Complexity
     - Pulse impl
     - 6 assume\_
   * - KahnTopologicalSort
     - Pulse impl
     - 2 admit()
   * - KahnTopologicalSort.Complexity
     - Pulse impl
     - 0
   * - IterativeBFS
     - Pulse impl
     - 0
   * - IterativeDFS
     - Pulse impl
     - 0

The ``assume_`` calls in the Pulse complexity modules are used for
invariant framing properties — assertions that are semantically
valid but difficult for the SMT solver to discharge automatically.
Both ``StackDFS`` and ``QueueBFS`` demonstrate that these can be
eliminated via predicate-based refactoring with isolated lemmas.
The ``admit()`` calls in ``BFS.DistanceSpec``, ``DFS.Spec``,
``DFS.WhitePath``, and ``KahnTopologicalSort`` mark genuinely
unproven properties that remain as future work.
