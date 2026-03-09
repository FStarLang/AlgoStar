.. _Ch12_BST:

############################
Binary Search Trees
############################

This chapter covers binary search trees from CLRS Chapter 12. The
formalization has two independent implementations sharing a common
pure specification:

- **Pointer-based BST** (``BST.Impl``): heap-allocated nodes with
  parent pointers, connected by a recursive separation-logic predicate
  ``bst_subtree``. Full API: search, insert, delete, minimum,
  maximum, free.

- **Array-based BST** (``BSTArray.Impl``): flat array layout with
  node *i* having left child at ``2i + 1`` and right child at
  ``2i + 2``. Search, insert, delete, inorder, minimum, maximum,
  successor, predecessor.

Both are backed by a shared **pure specification** (``BST.Spec``)
with inductive ``bst`` type and all CLRS operations, plus **key-set
theorems** via ``FStar.FiniteSet``.

All proofs in this chapter are **fully verified with zero admits**.

.. contents::
   :local:
   :depth: 2

Summary
=======

.. list-table::
   :header-rows: 1

   * - Operation
     - CLRS §
     - Pointer-based
     - Array-based
     - Complexity
     - Admits
   * - TREE-SEARCH
     - §12.2
     - ``tree_search``
     - ``tree_search``
     - O(h)
     - 0
   * - TREE-MINIMUM
     - §12.2
     - ``tree_minimum``
     - ``tree_minimum``
     - O(h)
     - 0
   * - TREE-MAXIMUM
     - §12.2
     - ``tree_maximum``
     - —
     - O(h)
     - 0
   * - TREE-INSERT
     - §12.3
     - ``tree_insert``
     - ``tree_insert``
     - O(h)
     - 0
   * - TREE-DELETE
     - §12.3
     - ``tree_delete``
     - ``tree_delete``
     - O(h)
     - 0
   * - INORDER-WALK
     - §12.1
     - —
     - ``inorder_walk``
     - O(n)
     - 0

Pure Specification
==================

BST Data Structure
~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_bst_type
   :end-before: //SNIPPET_END: pure_bst_type

The validity predicate checks, recursively, that all keys in the left
subtree are strictly less than the node key and all keys in the right
subtree are strictly greater:

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_valid
   :end-before: //SNIPPET_END: bst_valid

Search (§12.2)
~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_search
   :end-before: //SNIPPET_END: bst_search

Search correctness: ``bst_search t k`` returns ``true`` if and only
if ``k`` appears in the inorder traversal:

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_search_correct
   :end-before: //SNIPPET_END: bst_search_correct

The proof uses BST validity to rule out keys in the wrong subtree:
if ``k < key``, the ``all_greater key (bst_inorder right)`` property
excludes ``k`` from the right subtree.

Insert (§12.3)
~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_insert
   :end-before: //SNIPPET_END: bst_insert

Insert preserves validity — proved by showing that the inserted key
satisfies the ``all_less`` / ``all_greater`` bounds of every ancestor:

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_insert_valid
   :end-before: //SNIPPET_END: bst_insert_valid

Delete (§12.3)
~~~~~~~~~~~~~~

Delete handles three cases: no children, one child, and two children
(replace with the in-order successor):

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_delete
   :end-before: //SNIPPET_END: bst_delete

Delete preserves validity. The two-children case relies on the
minimum of the right subtree being greater than all left-subtree keys
and less than the remaining right-subtree keys after its removal:

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_delete_valid
   :end-before: //SNIPPET_END: bst_delete_valid

Inorder sortedness ties everything together:

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_inorder_sorted
   :end-before: //SNIPPET_END: bst_inorder_sorted

Key-Set Theorems
~~~~~~~~~~~~~~~~

The ``Insert.Spec`` and ``Delete.Spec`` modules prove the strongest
possible correctness statements using ``FStar.FiniteSet``:

**Insert key-set theorem:**

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Insert.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: insert_key_set_lemma
   :end-before: //SNIPPET_END: insert_key_set_lemma

The full insert correctness combines validity, key-set algebra, and
membership:

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Insert.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: theorem_insert_preserves_bst
   :end-before: //SNIPPET_END: theorem_insert_preserves_bst

**Delete key-set theorem:**

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Delete.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: delete_key_set_lemma
   :end-before: //SNIPPET_END: delete_key_set_lemma

These are the **strongest functional correctness guarantees**: they
exactly characterize the set of keys before and after each operation
using finite set algebra, not just that a specific key is present or
absent.

Pointer-Based Imperative BST
==============================

The Pulse implementation uses heap-allocated nodes with parent
pointers:

.. code-block:: fstar

   noeq type bst_node = {
     key: int; left: bst_ptr; right: bst_ptr; p: bst_ptr }

The recursive separation-logic predicate ``bst_subtree ct ft parent``
links the concrete pointer structure to the pure ``bst`` ghost tree.
A ``Leaf`` requires ``ct == None``; a ``Node l k r`` requires
``ct == Some bp`` where ``bp`` points to a node whose fields
recursively satisfy ``bst_subtree``.

Tree Search
~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_search
   :end-before: //SNIPPET_END: tree_search

The postcondition gives:

- ``result == bst_search 'ft k``: exact equivalence to pure spec.
- ``bst_subtree`` preserved (read-only: ``preserves``).
- Ticks incremented by exactly ``bst_search_ticks 'ft k``.

Tree Insert
~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_insert
   :end-before: //SNIPPET_END: tree_insert

The postcondition guarantees the resulting pointer tree represents
exactly ``bst_insert 'ft k`` — the pure specification applied to
the ghost tree. Parent pointers are correctly maintained.

Tree Minimum & Maximum
~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_minimum
   :end-before: //SNIPPET_END: tree_minimum

``tree_minimum`` walks left children until no valid left child exists.
The postcondition proves ``bst_minimum 'ft == Some result``.

Tree Delete
~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_delete
   :end-before: //SNIPPET_END: tree_delete

Handles all four CLRS cases (leaf, left child only, right child only,
two children with successor replacement). The result tree matches
``bst_delete 'ft k`` exactly. Freed nodes are deallocated.

Free
~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BST.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: free_bst
   :end-before: //SNIPPET_END: free_bst

Array-Based Imperative BST
============================

The array-based BST uses a flat layout: node at index ``i`` has left
child at ``2*i + 1`` and right child at ``2*i + 2``, with separate
``keys`` and ``valid`` arrays.

Tree Search (Array)
~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BSTArray.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_search
   :end-before: //SNIPPET_END: tree_search

Soundness: if ``Some idx`` is returned, ``keys[idx] == key`` and the
node is valid. Completeness: if ``None`` is returned, the key does not
exist in the subtree.

The pure spec provides the connection:

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BSTArray.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_search_sound
   :end-before: //SNIPPET_END: pure_search_sound

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BSTArray.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_search_complete
   :end-before: //SNIPPET_END: pure_search_complete

Tree Insert (Array)
~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BSTArray.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_insert
   :end-before: //SNIPPET_END: tree_insert

Postcondition: ``well_formed_bst`` preserved, and on success the key
exists at some index in the arrays.

Inorder Walk (Array)
~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BSTArray.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: inorder_walk
   :end-before: //SNIPPET_END: inorder_walk

Tree Delete, Minimum, Successor, Predecessor (Array)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BSTArray.Delete.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_minimum
   :end-before: //SNIPPET_END: tree_minimum

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BSTArray.Delete.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_successor
   :end-before: //SNIPPET_END: tree_successor

.. literalinclude:: ../autoclrs/ch12-bst/CLRS.Ch12.BSTArray.Delete.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_delete
   :end-before: //SNIPPET_END: tree_delete

Complexity
==========

Pointer-Based BST
~~~~~~~~~~~~~~~~~

All operations have **exact tick counting** linked to pure tick
functions:

- ``bst_search_ticks t k ≤ bst_height t``
- ``bst_minimum_ticks t ≤ bst_height t``
- ``bst_maximum_ticks t ≤ bst_height t``
- ``bst_insert_ticks t k ≤ bst_height t``
- ``bst_delete_ticks t k ≤ 4 * bst_height t + 1``

Additional structural bounds:

- ``insert_height_bound``: ``height(insert(t,k)) ≤ height(t) + 1``
- ``delete_height_bound``: ``height(delete(t,k)) ≤ height(t)``

Array-Based BST
~~~~~~~~~~~~~~~~

Height is ``⌊log₂(cap)⌋``. All operations bounded by
``tree_height(cap)``:

- ``node_depth_bounded``: ``node_depth(i) ≤ tree_height(cap)``
- ``search_complexity_bound``: at most ``h + 1`` nodes visited
- ``balanced_tree_height``: for balanced trees, ``h = Θ(log n)``

.. note::

   All complexity bounds are O(h) where h is the tree height. Since
   there is no balancing guarantee, h can be O(n) in the worst case.
   For O(lg n) guarantees, see Chapter 13 (red-black trees).

Limitations
===========

- **No balancing guarantee.** Height can be O(n) in the worst case.
  Use Chapter 13 (red-black trees) for O(lg n) bounds.
- **Pointer-based delete tick bound.** Delete is ≤ 4h + 1 ticks (not
  h) due to finding the successor and recursively deleting it.
- **Array-based BST capacity.** Fixed ``cap < 32768``.
- **Array-based delete simplification.** Marks nodes invalid rather
  than performing a full CLRS TRANSPLANT. Children of deleted nodes
  are orphaned rather than reattached.
- **No TREE-SUCCESSOR/TREE-PREDECESSOR in pointer-based BST.** These
  operations are only available in the array-based variant.

Verification Status
===================

All proofs in this chapter are **fully verified with zero admits**,
including the key-set theorems for insert and delete, the pure
specification correctness lemmas, and both imperative implementations.
