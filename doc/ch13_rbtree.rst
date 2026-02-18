.. _Ch13_RBTree:

############################
Red-Black Trees
############################

This chapter covers red-black trees from CLRS Chapter 13.  The
formalization has three layers:

- **Pure functional specification** (``RBTree.Spec``): an inductive
  ``rbtree`` type with Okasaki-style ``balance``/``ins``/``insert`` and
  BST ``search``.  All correctness and invariant-preservation lemmas —
  BST ordering, RB properties (no red-red, same black-height, root
  black), membership, and the height bound (Theorem 13.1) — are
  **fully verified with zero admits**.

- **Imperative Pulse wrapper** (``RBTree.fst``): holds the pure
  ``rbtree`` in a mutable reference and exposes ``rb_search`` and
  ``rb_insert``.  Postconditions re-export the full spec guarantees
  (RB invariants, BST ordering, membership, old-key preservation)
  by calling the pure lemmas.  **Zero admits**.

- **Complexity analysis** (``RBTree.Complexity``): pure tick counters
  for search and insert, bounded by height + O(1), combined with the
  height bound to obtain O(lg n) worst-case complexity.  **Zero admits**.

Pure Specification
==================

RB Tree Type
~~~~~~~~~~~~

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Spec.fst
   :language: fstar
   :start-after: (*** Basic Definitions ***)
   :end-before: (*** Tree Metrics ***)

The ``is_rbtree`` predicate conjoins three invariants: the root is
black, no red node has a red child, and all root-to-leaf paths have
the same black-height.

Okasaki-Style Insert (§13.3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Insert uses Okasaki's ``balance`` function that pattern-matches the
four rotation cases (LL, LR, RL, RR) in a single definition.  The
recursive ``ins`` walks the BST structure and calls ``balance`` at
each level; ``insert`` then forces the root black:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Spec.fst
   :language: fstar
   :start-after: (*** Okasaki-style Balance (Insert Fixup) ***)
   :end-before: (*** Theorem 13.1: Height Bound ***)

Theorem 13.1: Height Bound
~~~~~~~~~~~~~~~~~~~~~~~~~~~

The key lemma ``min_nodes_for_bh`` proves that any valid sub-tree
with black-height *bh* contains at least 2\ :sup:`bh` − 1 internal
nodes.  Combined with the red-red exclusion (which forces
height ≤ 2·bh), this gives the CLRS result:

  **height** ≤ 2 · ⌊lg(n + 1)⌋

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Spec.fst
   :language: fstar
   :start-after: // CLRS Theorem 13.1: height <= 2 * log2_floor(n + 1)
   :end-before: (*** Insert Correctness ***)

Insert Correctness
~~~~~~~~~~~~~~~~~~

Three families of lemmas are proved:

1. **Membership**: ``insert_mem`` — after inserting *k*, querying *x*
   returns true iff *x = k* or *x* was already a member.

2. **BST ordering**: ``insert_preserves_bst`` — the BST property is
   maintained through ``balance``.

3. **RB invariants**: ``insert_is_rbtree`` — all three RB properties
   are maintained.  The proof tracks ``same_bh``, ``almost_no_red_red``
   (the root of ``ins`` may be red with a red child, but ``balance``
   restores the invariant at each black ancestor), and
   ``make_black`` re-establishes the root-black property.

Pulse Wrapper
=============

The Pulse implementation stores a ``ref rbtree`` and delegates to the
pure functions:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_search
   :end-before: //SNIPPET_END: rb_search

Search returns exactly ``S.search t key`` — the pure BST search
result.

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_insert
   :end-before: //SNIPPET_END: rb_insert

Insert's postcondition guarantees:

- ``t' == S.insert t key`` — the new tree is the pure-functional insert result
- ``is_rbtree t'`` — all RB invariants are maintained
- ``is_bst t'`` — BST ordering is maintained
- ``mem key t'`` — the new key is a member
- ``∀x. mem x t ⟹ mem x t'`` — all old keys are preserved

Complexity
==========

``RBTree.Complexity`` defines tick counters that shadow the recursive
structure of ``search`` and ``ins``, proves they are bounded by
height + O(1), and combines with Theorem 13.1:

- **Search**: ≤ 2 · ⌊lg(n+1)⌋ + 1 comparisons
- **Insert**: ≤ 2 · ⌊lg(n+1)⌋ + 2 comparisons

Both bounds are proven with **zero admits**.

Remaining Admits
================

**None.** All three modules (``Spec``, ``RBTree``, ``Complexity``)
are fully verified with zero admits and zero assumes.
