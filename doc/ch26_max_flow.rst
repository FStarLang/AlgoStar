.. _Ch26_MaxFlow:

########################################
Maximum Flow
########################################

This chapter covers maximum flow from CLRS Chapter 26, specifically
the Ford-Fulkerson method (§26.2) and the Edmonds-Karp algorithm
(§26.2, using BFS for augmenting paths). The formalization includes:

1. **Pure specification** defining flow networks, valid flows,
   augmenting paths, residual graphs, and cuts.
2. **Augmentation lemmas** proving capacity preservation and flow
   conservation under augmentation (zero admits).
3. **Max-Flow Min-Cut Theorem** (CLRS Theorem 26.6) fully proven
   (zero admits).
4. **O(VE²) complexity analysis** with ghost tick counter (4 axioms
   for BFS shortest-path distance properties).
5. **Pulse implementation** computing maximum flow via BFS-based
   Ford-Fulkerson with proven termination (no fuel).

Flow Network Specification
==========================

A flow network is defined by a capacity matrix ``cap`` of size V×V.
A valid flow satisfies two properties from CLRS Definition 26.1:

- **Capacity constraint**: ``0 ≤ f(u,v) ≤ cap(u,v)`` for all u, v.
- **Flow conservation**: for every vertex except source and sink,
  the total flow in equals the total flow out.

.. literalinclude:: ../ch26-max-flow/CLRS.Ch26.MaxFlow.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: valid_flow
   :end-before: //SNIPPET_END: valid_flow

The termination condition is ``no_augmenting_path``: every path from
source to sink in the residual graph has non-positive bottleneck
capacity. This is the exact precondition of the MFMC theorem.

.. literalinclude:: ../ch26-max-flow/CLRS.Ch26.MaxFlow.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: no_augmenting_path
   :end-before: //SNIPPET_END: no_augmenting_path

Correctness Theorem
===================

The main entry point is ``max_flow`` in ``Impl.fsti``:

.. literalinclude:: ../ch26-max-flow/CLRS.Ch26.MaxFlow.Impl.fsti
   :language: pulse
   :start-after: //SNIPPET_START: max_flow_sig
   :end-before: //SNIPPET_END: max_flow_sig

The postcondition guarantees two properties:

1. **Always**: ``imp_valid_flow`` — the resulting flow satisfies
   capacity constraints and flow conservation in the imperative
   (flat-array) representation.

2. **When completed**: ``no_augmenting_path`` — no augmenting path
   exists in the residual graph, which is the exact precondition
   needed to apply the Max-Flow Min-Cut theorem.

Termination is proven without fuel. Each augmentation increases
``flow_value`` by at least 1 (via ``augment_increases_value``),
and the total flow is bounded by ``cap_sum = Σ cap[source][v]``.
The loop terminates in at most ``cap_sum + 1`` iterations.

Bridge Lemma
~~~~~~~~~~~~

The bridge lemma connects the imperative postcondition to the
pure specification, enabling callers to use the MFMC theorem:

.. literalinclude:: ../ch26-max-flow/CLRS.Ch26.MaxFlow.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: imp_valid_flow_bridge
   :end-before: //SNIPPET_END: imp_valid_flow_bridge

**Usage pattern**: (1) call ``max_flow``, (2) apply the bridge
lemma to obtain ``Spec.valid_flow``, (3) apply the MFMC theorem
to conclude the result is maximum and equals the min-cut capacity.

Max-Flow Min-Cut Theorem
========================

CLRS Theorem 26.6 is fully proven with zero admits in
``Lemmas.MaxFlowMinCut``:

.. literalinclude:: ../ch26-max-flow/CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut.fsti
   :language: fstar
   :start-after: //SNIPPET_START: max_flow_min_cut
   :end-before: //SNIPPET_END: max_flow_min_cut

The proof module also proves:

- **CLRS Lemma 26.4**: ``lemma_flow_value_eq_net_flow`` —
  flow value equals net flow across any s-t cut.
- **CLRS Corollary 26.5**: ``weak_duality`` —
  |f| ≤ c(S,T) for any valid flow and s-t cut.

Both are proven with zero admits.

Strongest Guarantee
~~~~~~~~~~~~~~~~~~~

The postcondition is the strongest functional guarantee achievable:
``imp_valid_flow`` is equivalent to the textbook definition of a
valid flow, and ``no_augmenting_path`` is the exact condition under
which CLRS Theorem 26.6 guarantees the flow is maximum. Together
they certify that any caller can derive max-flow = min-cut via the
proven MFMC theorem, without any additional axioms.

Augmentation Lemmas
===================

The lemma module (``MaxFlow.Lemmas``) proves that augmentation
preserves flow validity and strictly increases flow value. All
lemmas are fully proven with zero admits:

- ``augment_preserves_valid``: augmenting along a simple
  source-to-sink path preserves the capacity constraint and
  flow conservation.
- ``augment_increases_value``: after augmentation, the flow value
  is strictly greater.
- ``zero_flow_valid``: the zero flow satisfies all constraints.

Complexity Analysis
===================

The complexity module (``MaxFlow.Complexity``) formalizes the
Edmonds-Karp analysis from CLRS §26.2:

.. literalinclude:: ../ch26-max-flow/CLRS.Ch26.MaxFlow.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: edmonds_karp_complexity
   :end-before: //SNIPPET_END: edmonds_karp_complexity

The ghost-tick framework threads a ``tick_count`` through the
computation. Each BFS + augmentation adds ``augmentation_cost(E)``
ticks. The total is bounded by
``max_augmentations(V, E) × augmentation_cost(E) ≤ V·E·2E = O(VE²)``.

Proven results:

- ``lemma_augmentation_creates_critical_edge``: each augmentation
  creates at least one critical (saturated) edge.
- ``lemma_max_augmentations_justified``: O(VE) augmentation bound
  derived from the edge criticality bound.
- ``edmonds_karp_complexity``: total cost bounded by ``V·E·2E``.
- ``edmonds_karp_dense_graph_complexity``: O(V⁵) for E = V².
- ``edmonds_karp_sparse_graph_complexity``: O(V³) for E = O(V).

Limitations: Assume Val
=======================

The complexity module contains **4 ``assume val``** declarations —
the **only** assumes in the entire project outside ch22 and ch24:

.. literalinclude:: ../ch26-max-flow/CLRS.Ch26.MaxFlow.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_assume_vals
   :end-before: //SNIPPET_END: complexity_assume_vals

.. list-table::
   :header-rows: 1
   :widths: 35 20 45

   * - Assume Val
     - CLRS Reference
     - Description
   * - ``axiom_spd_source_zero``
     - BFS property
     - δ(s,s) = 0 in the residual graph
   * - ``axiom_spd_bounded``
     - BFS property
     - δ(s,v) ≤ n − 1 for all vertices v
   * - ``lemma_distances_nondecreasing``
     - Lemma 26.7
     - Shortest-path distances non-decreasing after augmentation
   * - ``axiom_edge_critical_bound``
     - Lemma 26.8
     - Each edge becomes critical at most n/2 times

These axioms bridge BFS correctness to the O(VE²) bound. The
functional correctness of the implementation (valid flow + no
augmenting path) is fully proven without any assumes.

One ``assume_`` in ``Test.fst`` asserts ``valid_caps`` for the
test graph; this is justified by the runtime check
``check_valid_caps_fn``.

Verification Status Summary
============================

.. list-table::
   :header-rows: 1
   :widths: 40 20 20

   * - Module
     - Type
     - Admits / Assumes
   * - MaxFlow.Spec
     - Pure spec
     - **0** ✅
   * - MaxFlow.Lemmas
     - Pure lemmas
     - **0** ✅
   * - MaxFlow.Lemmas.MaxFlowMinCut
     - MFMC theorem
     - **0** ✅
   * - MaxFlow.Impl
     - Pulse impl
     - **0** ✅
   * - MaxFlow.Complexity
     - Complexity
     - **4 assume val** ⚠️
   * - MaxFlow.Test
     - Test
     - 1 assume\_ (test)

The Pulse implementation, pure specification, augmentation lemmas,
and Max-Flow Min-Cut theorem are all fully verified with zero
admits. The 4 ``assume val`` in the complexity module pertain to
BFS shortest-path distance properties and do not affect functional
correctness.
