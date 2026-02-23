.. _Ch26_MaxFlow:

########################################
Maximum Flow
########################################

This chapter covers maximum flow from CLRS Chapter 26, specifically
the Ford-Fulkerson method (§26.2) and the Edmonds-Karp algorithm
(§26.2, using BFS for augmenting paths). The formalization includes:

1. **Pure specification** defining flow networks, valid flows,
   augmenting paths, and the Ford-Fulkerson framework.
2. **Proof module** with helper lemmas for capacity preservation
   and flow conservation under augmentation.
3. **Complexity analysis** proving the O(VE²) bound for Edmonds-Karp.
4. **Pulse implementation** that initializes a valid zero flow.

.. note::

   This chapter is a **partial formalization**. The Pulse implementation
   currently only initializes the flow to zero (a valid flow). The
   augmenting-path search (BFS on the residual graph) and the full
   Ford-Fulkerson loop are specified in pure F* but not yet implemented
   in Pulse. Eight ``assume()`` calls remain in the proof and complexity
   modules.

Flow Network Specification
==========================

A flow network is defined by a capacity matrix ``cap`` of size V×V.
A valid flow satisfies two properties from CLRS Definition 26.1:

- **Capacity constraint**: ``0 ≤ f(u,v) ≤ cap(u,v)`` for all u, v.
- **Flow conservation**: for every vertex except source and sink,
  the total flow in equals the total flow out.

The specification module (``MaxFlow.Spec``) defines these predicates
along with the residual graph, augmenting paths, bottleneck capacity,
and the ``augment`` operation that pushes flow along a path.

Key definitions include ``flow_value`` (|f| = net flow out of source,
CLRS page 710), ``residual_capacity`` (forward and backward), and
``ford_fulkerson_step`` / ``ford_fulkerson`` (the iterative framework).

This module has **2 assume()** calls: ``augment_preserves_valid``
(augmentation maintains valid flow) and ``augment_increases_value``
(augmentation strictly increases flow value).

Proof Module
============

The proof module (``MaxFlow.Proofs``) contains helper lemmas for the
augmentation operation:

- Sum-flow properties under matrix updates (``lemma_sum_flow_into_update_other``,
  ``lemma_sum_flow_out_increase``, etc.).
- Capacity preservation: ``lemma_augment_edge_capacity`` shows that
  augmenting a single edge maintains capacity constraints.
- Conservation preservation: ``lemma_augment_edge_conservation_intermediate``
  shows flow conservation is maintained for intermediate vertices.
- Zero-flow validity: ``lemma_zero_flow_valid`` proves the zero flow
  satisfies all constraints.

This module has **4 assume()** calls for the most complex graph-theoretic
properties (bottleneck path reasoning, capacity preservation across full
augmentation, and flow value increase).

Complexity Analysis
===================

The complexity module (``MaxFlow.Complexity``) formalizes the Edmonds-Karp
analysis from CLRS §26.2:

- **CLRS Lemma 26.7**: Shortest-path distances in the residual graph
  are monotonically non-decreasing across augmentations.
- **CLRS Lemma 26.8**: Each augmentation creates at least one critical
  (saturated) edge.
- **CLRS Theorem 26.8**: The total number of augmentations is O(VE),
  giving O(VE²) total time (each BFS takes O(E)).
- Corollaries for dense graphs (O(V⁵)) and sparse graphs (O(V³)).

The ghost-tick framework (``edmonds_karp_state`` with tick counter) is
set up but the augmentation step uses ``assume()`` for the key lemmas.
This module has **2 assume()** calls.

Pulse Implementation
====================

The Pulse implementation (``MaxFlow.fst``) currently initializes a
flow matrix to zero and proves it is a valid flow:

- ``lemma_zero_flow_conservation``: zero flow satisfies conservation.
- ``lemma_zero_respects_cap``: zero flow respects all capacity constraints.
- ``max_flow``: Pulse function that allocates and initializes the flow matrix.

The function is **fully verified with 0 admits**. Extending to the full
Ford-Fulkerson loop (finding augmenting paths via BFS, augmenting,
repeating until no path exists) is a stretch goal.

Verification Status Summary
============================

.. list-table::
   :header-rows: 1
   :widths: 40 20 20

   * - Module
     - Type
     - Admits / Assumes
   * - MaxFlow.fst
     - Pulse impl
     - **0** ✅
   * - MaxFlow.Spec
     - Pure spec
     - 2 assume()
   * - MaxFlow.Proofs
     - Pure lemmas
     - 4 assume()
   * - MaxFlow.Complexity
     - Pure spec
     - 2 assume()
   * - MaxFlow.Test
     - Test
     - 0

**Total: 8 assume()** across 4 files (~1,380 lines). All unproven
obligations are ``assume()`` calls marking complex graph-theoretic
properties. Completing these proofs requires formalizing residual-graph
shortest-path properties and the augmentation–conservation interaction.
