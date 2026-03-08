.. _Ch21_DisjointSets:

############################
Disjoint Sets (Union-Find)
############################

This chapter covers the disjoint-set (union-find) data structure from
CLRS Chapter 21, implementing union by rank (§21.3) with full path
compression. The formalization includes a pure F* specification of
the forest model, a Pulse implementation with memory-safe mutable
arrays, termination proofs, and rank-bound analysis.

**Verification status.** All four modules (``Spec.fst``,
``Lemmas.fst``, ``Impl.fsti``, ``Impl.fst``) contain **zero admits
and zero assumes**.

Pure Specification
==================

Forest Model
~~~~~~~~~~~~

The union-find forest is modeled as a record of parent and rank
sequences. A valid forest has in-bounds parent pointers, and a root
satisfies ``parent[i] = i``. The rank invariant (CLRS Lemma 21.4)
states that for every non-root node *x*,
``rank[x] < rank[parent[x]]``.

Total Pure Find
~~~~~~~~~~~~~~~

``pure_find`` follows parent pointers to the root. It is **total
without fuel** — termination is proved via a ``count_above`` measure
that counts nodes with rank strictly above the current node's rank.
Since rank strictly increases along parent pointers, this count
decreases at each recursive step.

``pure_find_is_root`` and ``pure_find_in_bounds`` prove that the
result is always a valid root. ``rank_mono`` proves that
``rank[x] ≤ rank[root]`` for any node *x* and its root.

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

- ``root == Spec.pure_find(original, x)``
- ``∀z < n. Spec.pure_find(compressed, z) == Spec.pure_find(original, z)``

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

Complexity
==========

With union-by-rank, the ``Lemmas`` module proves that tree height
is O(log *n*), giving O(log *n*) worst-case find. With both
union-by-rank and path compression, the amortized cost is
O(*m* · α(*n*)) where α is the inverse Ackermann function
(CLRS Theorem 21.14). The amortized analysis is not formalized.
