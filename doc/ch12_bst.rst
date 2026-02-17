.. _Ch12_BST:

############################
Binary Search Trees
############################

This chapter covers binary search trees from CLRS Chapter 12. The
formalization has two layers:

- **Pure functional specification** (``BST.Spec.Complete``): an
  inductive ``bst`` type with ``search``, ``insert``, ``delete``,
  ``minimum``, ``maximum``, and ``inorder``. All correctness lemmas
  — validity preservation, search correctness, inorder sortedness —
  are **fully verified with zero admits**.

- **Imperative Pulse implementation** (``BST.fst``, ``BST.Delete.fst``):
  an array-based BST where node *i* has left child at 2i + 1 and
  right child at 2i + 2. Search and delete are verified;
  insert has a weaker postcondition.

The ``Insert.Spec`` module (array-based insert preservation) contains
**3 admits** for structural reasoning about disjoint subtree indices
in the array representation. The ``Delete.Spec`` module
(``delete_key_set_lemma``) is **fully verified with zero admits**.

Pure Specification
==================

BST Data Structure
~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Spec.Complete.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_bst_type
   :end-before: //SNIPPET_END: pure_bst_type

The validity predicate checks, recursively, that all keys in the left
subtree are strictly less than the node key and all keys in the right
subtree are strictly greater:

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Spec.Complete.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_valid
   :end-before: //SNIPPET_END: bst_valid

Search (§12.2)
~~~~~~~~~~~~~~

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Spec.Complete.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_search
   :end-before: //SNIPPET_END: bst_search

Search correctness: ``bst_search t k`` returns ``true`` if and only
if ``k`` appears in the inorder traversal:

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Spec.Complete.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_search_correct
   :end-before: //SNIPPET_END: bst_search_correct

The proof uses BST validity to rule out keys in the wrong subtree:
if ``k < key``, the ``all_greater key (bst_inorder right)`` property
excludes ``k`` from the right subtree.

Insert (§12.3)
~~~~~~~~~~~~~~

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Spec.Complete.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_insert
   :end-before: //SNIPPET_END: bst_insert

Insert preserves validity — proved by showing that the inserted key
satisfies the ``all_less`` / ``all_greater`` bounds of every ancestor:

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Spec.Complete.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_insert_valid
   :end-before: //SNIPPET_END: bst_insert_valid

Delete (§12.3)
~~~~~~~~~~~~~~

Delete handles three cases: no children, one child, and two children
(replace with the in-order successor):

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Spec.Complete.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_delete
   :end-before: //SNIPPET_END: bst_delete

Delete preserves validity. The two-children case relies on
``bst_minimum_greater_than_left`` (the successor is larger than all
left-subtree keys) and ``bst_minimum_less_than_rest`` (the successor
is smaller than the remaining right-subtree keys after its removal):

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Spec.Complete.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_delete_valid
   :end-before: //SNIPPET_END: bst_delete_valid

Inorder sortedness ties everything together:

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Spec.Complete.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_inorder_sorted
   :end-before: //SNIPPET_END: bst_inorder_sorted

Delete Key Set Theorem
~~~~~~~~~~~~~~~~~~~~~~

The ``Delete.Spec`` module proves the strongest delete result: after
deleting key *k*, the key set shrinks by exactly {*k*}:

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Delete.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: delete_key_set_lemma
   :end-before: //SNIPPET_END: delete_key_set_lemma

This is proved by structural induction on all four cases (no children,
left only, right only, two children) with explicit ``FiniteSet``
algebra. The proof is **zero admits**.

Array-Based Imperative BST
===========================

The Pulse implementation uses a flat array layout:

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.fst
   :language: fstar
   :start-after: //SNIPPET_START: bst_type
   :end-before: //SNIPPET_END: bst_type

The BST ordering invariant for the array representation uses bounded
ranges:

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.fst
   :language: fstar
   :start-after: //SNIPPET_START: subtree_in_range
   :end-before: //SNIPPET_END: subtree_in_range

Tree Search
~~~~~~~~~~~

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_search
   :end-before: //SNIPPET_END: tree_search

Soundness: if ``Some idx`` is returned, then ``keys[idx] == key``
and the node is valid. Completeness is established in the separate
``BST.Spec`` module via a pure recursive search:

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_search_sound
   :end-before: //SNIPPET_END: pure_search_sound

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_search_complete
   :end-before: //SNIPPET_END: pure_search_complete

Tree Insert
~~~~~~~~~~~

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_insert
   :end-before: //SNIPPET_END: tree_insert

The postcondition guarantees length preservation and that a failed
insert leaves arrays unchanged. The stronger property — that the
BST ordering is preserved — is stated in ``Insert.Spec`` but its
proof has **3 remaining admits**: two for structural reasoning about
disjoint subtrees in the array layout, and one for key-set membership
after insertion.

Tree Minimum & Delete
~~~~~~~~~~~~~~~~~~~~~

``tree_minimum`` walks left children until no valid left child exists:

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Delete.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_minimum
   :end-before: //SNIPPET_END: tree_minimum

``tree_delete`` marks the node invalid, handling all four CLRS cases
(leaf, one child, two children). The Pulse implementation is
simplified for the array representation:

.. literalinclude:: ../ch12-bst/CLRS.Ch12.BST.Delete.fst
   :language: pulse
   :start-after: //SNIPPET_START: tree_delete
   :end-before: //SNIPPET_END: tree_delete

The postcondition guarantees that a successful delete marks the target
node invalid and preserves array lengths. Both ``tree_minimum`` and
``tree_delete`` are **zero admits**.

Remaining Admits
================

The only admits in this chapter are in ``BST.Insert.Spec``, the
array-based insert preservation proof:

1. ``pure_insert_preserves_subtree_range``: BST ordering is maintained
   after insertion. Requires induction over the array-based tree
   structure with disjoint subtree reasoning.

2. ``lemma_subtree_completely_unchanged``: a subtree not containing
   the insertion index is unmodified. Requires proving that array
   indices in one subtree are disjoint from those in a sibling subtree.

3. ``lemma_insert_adds_to_keys_set``: the inserted key appears in
   the key set after insertion. Structurally similar to (1).

All three represent the same fundamental difficulty: reasoning about
disjoint index ranges in an implicit (array-based) tree layout. The
pure functional specification avoids this issue entirely and is fully
verified.
