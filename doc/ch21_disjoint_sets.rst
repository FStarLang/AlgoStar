.. _Ch21_DisjointSets:

############################
Disjoint Sets (Union-Find)
############################

This chapter covers the disjoint-set (union-find) data structure from
CLRS Chapter 21, implementing union by rank (§21.3) with full path
compression. The formalization includes a pure F* specification of
the forest model, a Pulse implementation with memory-safe mutable
arrays, termination proofs, compression correctness, and rank-bound
analysis establishing O(log n) worst-case find.

**Verification status.** All four modules (``Spec.fst``,
``Lemmas.fst``, ``Impl.fsti``, ``Impl.fst``) contain **zero admits
and zero assumes**.

.. list-table:: Chapter 21 Summary
   :header-rows: 1
   :widths: 40 10 50

   * - Property
     - Status
     - Notes
   * - Functional correctness (all 3 ops)
     - ✅
     - All postconditions reference ``pure_find``
   * - ``uf_inv`` preservation
     - ✅
     - Across all operations and compression
   * - Merge (``pure_union_same_set``)
     - ✅
     - ``find(x) == find(y)`` after ``union(x,y)``
   * - Stability (``pure_union_other_set``)
     - ✅
     - Unrelated elements unchanged
   * - ``size ≥ 2^rank``
     - ✅
     - ``size_rank_invariant`` in Lemmas
   * - ``rank ≤ ⌊log₂ n⌋``
     - ✅
     - ``rank_logarithmic_bound_sized``
   * - O(log n) worst-case find
     - ✅
     - ``union_by_rank_logarithmic_find``
   * - Amortized O(α(n))
     - ❌
     - Inverse Ackermann analysis not formalized
   * - Admits / Assumes
     - **0 / 0**
     -

Pure Specification
==================

Forest Model
~~~~~~~~~~~~

The union-find forest is modeled as a record of parent and rank
sequences. A valid forest has in-bounds parent pointers, and a root
satisfies ``parent[i] = i``. The rank invariant (CLRS Lemma 21.4)
states that for every non-root node *x*,
``rank[x] < rank[parent[x]]``. The combined invariant ``uf_inv`` is
the conjunction of ``is_valid_uf`` and ``rank_invariant``.

Total Pure Find
~~~~~~~~~~~~~~~

``pure_find`` follows parent pointers to the root. It is **total
without fuel** — termination is proved via a ``count_above`` measure
that counts nodes with rank strictly above the current node's rank.
Since rank strictly increases along parent pointers, this count
decreases at each recursive step.

Key properties:

- ``pure_find_is_root``: result is always a valid root.
- ``pure_find_in_bounds``: result is in ``[0, n)``.
- ``pure_find_idempotent``: ``pure_find(pure_find(x)) == pure_find(x)``.
- ``pure_find_step``: for non-roots, ``pure_find(x) == pure_find(parent[x])``.

Pure Union
~~~~~~~~~~

Union by rank (CLRS §21.3) attaches the shorter tree under the taller
one; on equal rank it increments the new root's rank.

Correctness Theorems
~~~~~~~~~~~~~~~~~~~~

The specification proves both directions of correctness:

- **Merge** (``pure_union_same_set``): After ``union(x,y)``,
  ``pure_find(x) == pure_find(y)``.
- **Stability** (``pure_union_other_set``): For any ``z`` whose
  representative differs from both ``x`` and ``y``,
  ``pure_find(z)`` is unchanged.
- **Invariant preservation** (``pure_union_preserves_inv``):
  ``uf_inv`` is maintained.

Compression lemmas (``compress_preserves_uf_inv``,
``compress_preserves_find_all``) prove that single-node path
compression preserves both ``uf_inv`` and all ``pure_find`` values.

Rank Bound
~~~~~~~~~~

The ``Lemmas`` module introduces ``uf_forest_sized`` (extending the
forest with subtree sizes) and proves:

.. literalinclude:: ../ch21-disjoint-sets/CLRS.Ch21.UnionFind.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: size_rank_invariant
   :end-before: //SNIPPET_END: size_rank_invariant

The equal-rank case is the critical one: when two trees of rank *k*
merge, the new root has rank *k* + 1 and size ≥ 2^k + 2^k = 2^(k+1).
This gives the logarithmic bound ``rank[x] ≤ ⌊log₂ n⌋``
(CLRS Corollary 21.5), since ``2^rank ≤ size ≤ n``.

The final theorem ``union_by_rank_logarithmic_find`` proves
``tree_height(x) ≤ ⌊log₂ n⌋``, establishing O(log n) worst-case
find complexity with union by rank.

Pulse Implementation
====================

The ``Impl`` module provides the three CLRS §21.3 operations as
Pulse functions operating on mutable ``SizeT`` arrays. Bridge
functions (``to_uf``, ``to_nat_seq``) convert between the imperative
representation and the pure ``Spec.uf_forest``.

Make-Set
~~~~~~~~

``make_set`` initializes ``parent[i] = i`` and ``rank[i] = 0`` for
all ``i ∈ [0, n)``. The postcondition establishes ``Spec.uf_inv``
and that every element is a root.

Find-Set
~~~~~~~~

``find_set`` implements the CLRS two-pass FIND-SET with full path
compression:

- **Pass 1** (``find_root_imp``): Read-only traversal to locate
  the root.
- **Pass 2** (``compress_path``): Walks from *x* toward the root,
  setting every intermediate node's parent directly to the root.

The postcondition guarantees:

- ``root == Spec.pure_find(original, x)`` — functional correctness.
- ``∀z < n. Spec.pure_find(compressed, z) == Spec.pure_find(original, z)``
  — compression preserves all representatives.
- ``Spec.uf_inv`` preserved before and after compression.
- ``is_forest`` preserved — acyclicity maintained.

Union
~~~~~

``union`` performs union by rank and returns ``unit`` (matching CLRS).
It uses ``find_root_imp`` (read-only) for both operands, then links
the roots by rank.

The postcondition guarantees:

- **Merge:** ``Spec.pure_find(result, x) == Spec.pure_find(result, y)``
- **Stability:** For any ``z`` disjoint from both ``x`` and ``y``,
  ``Spec.pure_find(result, z) == Spec.pure_find(original, z)``
- ``Spec.uf_inv`` and ``is_forest`` are preserved.

Strongest Guarantee
~~~~~~~~~~~~~~~~~~~

The postconditions fully characterize union-find semantics:

1. Find returns the **exact** pure representative (not just "some root").
2. Compression preserves **all** representatives, not just the queried one.
3. Union's stability clause covers **all** disjoint elements via a
   universal quantifier.
4. The invariant ``uf_inv`` (rank invariant + validity) is maintained
   through every operation, enabling arbitrary composition of operations.

The only missing guarantee is amortized complexity.

Complexity
==========

With union-by-rank, the ``Lemmas`` module proves that tree height
is O(log *n*), giving O(log *n*) worst-case find. The proof proceeds
in three steps:

1. ``size_rank_invariant``: every subtree has at least 2^rank nodes.
2. ``rank_logarithmic_bound_sized``: since 2^rank ≤ size ≤ n, we get
   rank ≤ ⌊log₂ n⌋.
3. ``height_le_root_rank``: tree height ≤ rank[root].

Combining these gives the final theorem:

.. code-block:: fstar

   val union_by_rank_logarithmic_find
     (f: uf_forest_sized{...}) (x: nat{x < f.n})
     : Lemma (ensures tree_height f x <= log2_floor f.n)

.. list-table:: Complexity Summary
   :header-rows: 1
   :widths: 40 10 50

   * - Aspect
     - Proven
     - Bound
   * - Worst-case find (rank only)
     - ✅
     - O(log n) — ``tree_height ≤ ⌊log₂ n⌋``
   * - Amortized find (rank + compression)
     - ❌
     - O(α(n)) — not formalized
   * - Ghost tick counter
     - N/A
     - No complexity instrumentation file

Limitations
===========

1. **Amortized O(α(n)) not proven.** The inverse Ackermann amortized
   analysis (CLRS §21.4) is not formalized. Only the O(log n)
   worst-case bound from union-by-rank alone is proven.

2. **No ghost tick counter.** Unlike other chapters (e.g., Ch 25
   Floyd-Warshall), there is no ``Complexity.fst`` module with
   instrumented ghost ticks. The O(log n) bound is stated as a lemma
   on tree height, not as a runtime counter.

3. **Subtree sizes are specification-only.** The ``uf_forest_sized``
   type in ``Lemmas.fst`` is a proof device — the imperative code does
   not maintain size fields. This means the size-rank invariant cannot
   be directly connected to the imperative state without additional
   bridging.

4. **Linked-list representation (§21.2) not implemented.** The
   formalization uses the array-based forest representation (§21.3)
   only.
