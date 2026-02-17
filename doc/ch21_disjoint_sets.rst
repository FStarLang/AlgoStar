.. _Ch21_DisjointSets:

############################
Disjoint Sets (Union-Find)
############################

This chapter covers the disjoint-set (union-find) data structure from
CLRS Chapter 21, implementing union by rank (§21.3) with path
compression. The formalization includes a pure F* specification of
the forest model, a Pulse implementation with memory-safe mutable
arrays, termination proofs, rank-bound analysis, and a full path
compression variant.

**Verification status.** The Pulse implementations ``find`` and
``union_`` contain **zero admits and zero assumes**. The pure
specification (``Spec.fst``) has 1 ``assume`` call: in
``pure_find_fuel_sufficient``, where ``ranks_bounded`` is assumed
to avoid a circular dependency — the bound ``rank[x] < n`` is
proved in a separate module (``RankBound.fst``) via the
``size_rank_invariant``. The ``FindTermination``,
``RankBound``, and ``FullCompress`` modules have zero admits.

Pure Specification
==================

Forest Model
~~~~~~~~~~~~

The union-find forest is modelled as a record of parent and rank
sequences. A valid forest has in-bounds parent pointers, and a root
satisfies ``parent[i] = i``:

.. literalinclude:: ../ch21-disjoint-sets/CLRS.Ch21.UnionFind.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: uf_forest_def
   :end-before: //SNIPPET_END: uf_forest_def

Rank Invariant
~~~~~~~~~~~~~~

The rank invariant (CLRS Lemma 21.4) states that for every non-root
node *x*, ``rank[x] < rank[parent[x]]``. This guarantees that rank
strictly increases along any path toward a root, which is the key
ingredient for termination of ``find``:

.. literalinclude:: ../ch21-disjoint-sets/CLRS.Ch21.UnionFind.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: rank_invariant
   :end-before: //SNIPPET_END: rank_invariant

The initial forest (every element is its own root with rank 0)
satisfies the rank invariant vacuously — there are no non-root nodes.

Pure Find
~~~~~~~~~

``pure_find`` follows parent pointers to the root. It uses a
fuel-bounded recursive helper and a proof that *n* steps of fuel
always suffice under the rank invariant (since rank strictly
increases at each step and all ranks are bounded by *n*):

.. literalinclude:: ../ch21-disjoint-sets/CLRS.Ch21.UnionFind.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_find
   :end-before: //SNIPPET_END: pure_find

``pure_find_is_root`` and ``pure_find_in_bounds`` prove that the
result is always a valid root. ``rank_monotone_chain`` proves that
``rank[x] ≤ rank[root]`` for any node *x* and its root.

Pure Union
~~~~~~~~~~

Union by rank (CLRS §21.3) attaches the shorter tree under the taller
one; on equal rank it increments the new root's rank:

.. literalinclude:: ../ch21-disjoint-sets/CLRS.Ch21.UnionFind.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_union
   :end-before: //SNIPPET_END: pure_union

Correctness Theorem
~~~~~~~~~~~~~~~~~~~

The main correctness theorem proves that after ``pure_union f x y``,
the resulting forest is valid, maintains the rank invariant, and the
two elements share a common representative:

.. literalinclude:: ../ch21-disjoint-sets/CLRS.Ch21.UnionFind.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_union_correctness
   :end-before: //SNIPPET_END: pure_union_correctness

The proof handles three cases (``rank_x < rank_y``,
``rank_x > rank_y``, equal rank) and uses the helper
``pure_find_fuel_after_update`` to relate ``pure_find`` on the
modified forest to ``pure_find`` on the original.

Rank Bound
~~~~~~~~~~

The ``RankBound`` module proves that ``size[x] ≥ 2^rank[x]``
is preserved by union:

.. literalinclude:: ../ch21-disjoint-sets/CLRS.Ch21.UnionFind.RankBound.fst
   :language: fstar
   :start-after: //SNIPPET_START: size_rank_invariant
   :end-before: //SNIPPET_END: size_rank_invariant

The equal-rank case is the critical one: when two trees of rank *k*
merge, the new root has rank *k* + 1 and size ≥ 2^k + 2^k = 2^(k+1).
This gives the logarithmic bound ``rank[x] ≤ ⌊log₂ n⌋``
(CLRS Theorem 21.5), since ``2^rank ≤ size ≤ n``.

Pulse Implementation
====================

Find
~~~~

The Pulse ``find`` traverses parent pointers in a loop, using a
``fuel`` counter that mirrors the pure specification. It takes a
shared (fractional) permission on the parent array:

.. literalinclude:: ../ch21-disjoint-sets/CLRS.Ch21.UnionFind.fst
   :language: pulse
   :start-after: //SNIPPET_START: find_sig
   :end-before: //SNIPPET_END: find_sig

The postcondition guarantees the result is a root (``is_root s root``)
and equals the pure specification (``find_root s x n == root``). The
loop invariant threads ``has_root_within`` with a decreasing fuel
bound, and ``find_root_monotone`` ensures the result is independent of
the fuel used.

Union
~~~~~

The Pulse ``union_`` calls ``find`` on both operands, then links the
roots by rank:

.. literalinclude:: ../ch21-disjoint-sets/CLRS.Ch21.UnionFind.fst
   :language: pulse
   :start-after: //SNIPPET_START: union_sig
   :end-before: //SNIPPET_END: union_sig

The postcondition returns both roots and guarantees that if they
differ, one's parent now points to the other. When the roots are
already equal, the parent array is unchanged (``Seq.equal sp sparent``).

Full Path Compression
~~~~~~~~~~~~~~~~~~~~~

The ``FullCompress`` module implements CLRS's two-pass FIND-SET:
first walk to the root, then walk again setting every node's parent
to the root. This is the full path compression variant (as opposed
to ``find_compress`` which only compresses the queried node):

.. literalinclude:: ../ch21-disjoint-sets/CLRS.Ch21.UnionFind.FullCompress.fst
   :language: pulse
   :start-after: //SNIPPET_START: find_set_sig
   :end-before: //SNIPPET_END: find_set_sig

After ``find_set``, ``parent[x]`` points directly to the root and the
root remains self-referencing. The implementation uses bounded loops
for both passes to ensure termination.

Complexity
==========

The ``Complexity`` module provides simple worst-case bounds:

- ``find_worst n = n``: without path compression, find is O(*n*).
- ``union_ops = 1``: union is constant time (pointer manipulation).
- ``find_sequence_worst m n = m × n``: a sequence of *m* finds is
  O(*mn*).

With union-by-rank, the ``RankBound`` module shows that tree height
is O(log *n*), improving find to O(log *n*). With both union-by-rank
and path compression, the amortized cost is O(*m* · α(*n*)) where α
is the inverse Ackermann function (CLRS Theorem 21.14). The
amortized analysis is not formalized.
