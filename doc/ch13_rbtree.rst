.. _Ch13_RBTree:

############################
Red-Black Trees (Chapter 13)
############################

CLRS Chapter 13 introduces **red-black trees**, a self-balancing binary
search tree in which every node stores one extra bit — its *color*,
either red or black — and the tree satisfies five properties that
together guarantee that no root-to-leaf path is more than twice as
long as any other.  This ensures that search, insert, and delete all
run in O(lg n) worst-case time.

The formalization provides two independent Pulse implementations —
Okasaki-style (functional balance) and CLRS-style (imperative rotations
with parent pointers) — sharing a common pure specification.  All
proofs are complete with **zero admits**.

.. contents::
   :local:
   :depth: 2

Summary
=======

.. list-table::
   :header-rows: 1

   * - Operation
     - CLRS §
     - Okasaki (``Impl``)
     - CLRS (``CLRSImpl``)
     - Complexity
     - Admits
   * - SEARCH
     - §13.2
     - ``rb_search``
     - ``rb_search``
     - O(lg n)
     - 0
   * - INSERT
     - §13.3
     - ``rb_insert``
     - ``rb_clrs_insert``
     - O(lg n)
     - 0
   * - DELETE
     - §13.4
     - ``rb_delete``
     - ``rb_clrs_delete``
     - O(lg n)
     - 0
   * - MINIMUM
     - §12.2
     - —
     - ``rb_minimum``
     - O(lg n)
     - 0

CLRS Coverage
=============

Chapter 13 covers four topics:

- **§13.1 Properties of red-black trees** — the five RB properties
  (every node is red or black; root is black; leaves (NIL) are black;
  red nodes have black children; all root-to-leaf paths have equal
  black-height) and **Theorem 13.1**: a red-black tree with *n*
  internal nodes has height at most 2·lg(n + 1).

- **§13.2 Rotations** — LEFT-ROTATE and RIGHT-ROTATE as the primitive
  restructuring operations that preserve BST ordering.

- **§13.3 Insertion** — RB-INSERT walks the BST to the insertion point,
  colors the new node red, then calls RB-INSERT-FIXUP, which
  restores the RB properties by walking back up the tree performing
  recolorings and at most two rotations.

- **§13.4 Deletion** — RB-DELETE and RB-DELETE-FIXUP.

Our formalization covers §13.1–13.4 in full.

Formalization Overview
======================

The formalization has four layers, all with **zero admits**:

1. **Pure functional specification** (``CLRS.Ch13.RBTree.Spec``) — an
   inductive ``rbtree`` type, RB invariant predicates, Okasaki-style
   functional ``balance``/``ins``/``insert``, Kahrs-style
   ``del``/``delete``, and minimum/maximum/successor/predecessor.

2. **Correctness lemmas** (``CLRS.Ch13.RBTree.Lemmas``) — Theorem
   13.1 (height bound), membership preservation, BST/RB invariant
   preservation for insert and delete.

3. **Pointer-based Pulse implementation** (``CLRS.Ch13.RBTree.Impl``) —
   Okasaki-style: heap-allocated nodes with mutable fields and
   nullable child pointers, tied to the pure spec via ``is_rbtree``.

4. **CLRS-faithful Pulse implementation**
   (``CLRS.Ch13.RBTree.CLRSImpl``) — parent pointers, explicit
   LEFT-ROTATE/RIGHT-ROTATE, uncle-checking INSERT-FIXUP,
   4-case DELETE-FIXUP, tied to the pure spec via ``rbtree_subtree``.

5. **Complexity analysis** (``CLRS.Ch13.RBTree.Complexity``) — pure
   tick counters proving search and insert are O(lg n) via the height
   bound.


Pure Specification (``RBTree.Spec``)
=====================================

RB Tree Type (§13.1)
~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Spec.fst
   :language: fstar
   :start-after: (*** Basic Definitions ***)
   :end-before: (*** Tree Metrics ***)

The ``is_rbtree`` predicate conjoins the three key properties from
CLRS §13.1: the root is black, no red node has a red child
("Property 4"), and all root-to-leaf paths have the same number of
black nodes ("Property 5", same black-height):

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Spec.fst
   :language: fstar
   :start-after: (*** RB Properties ***)
   :end-before: (*** Membership and BST ***)

The BST ordering predicate uses ``all_lt`` / ``all_gt`` bounds to
ensure that all keys in the left subtree are less than the node key,
and all keys in the right subtree are greater:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Spec.fst
   :language: fstar
   :start-after: (*** Membership and BST ***)
   :end-before: (*** Search ***)


Search (§13.2)
~~~~~~~~~~~~~~~

Search follows the standard BST algorithm, descending left or right
based on key comparison:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Spec.fst
   :language: fstar
   :start-after: (*** Search ***)
   :end-before: (*** Okasaki-style Balance (Insert Fixup) ***)


Okasaki-Style Insert and Balance (§13.3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CLRS §13.3 describes insertion as a two-phase process: (1) BST-walk
to find the insertion point, then (2) fixup via recolorings and
rotations walking back up.  Our formalization uses Okasaki's elegant
functional equivalent: a single ``balance`` function that
pattern-matches all four rotation cases (left-left, left-right,
right-left, right-right) and a recursive ``ins`` that calls
``balance`` at each level on the way up.  The function ``insert``
wraps ``ins`` and forces the root black:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Spec.fst
   :language: fstar
   :start-after: (*** Okasaki-style Balance (Insert Fixup) ***)
   :end-before: (*** Balance Case Classifier ***)

The four cases in ``balance`` correspond exactly to the three cases of
RB-INSERT-FIXUP in CLRS (our four cases arise because CLRS treats the
symmetric left/right sub-cases separately in the text, while Okasaki
unifies them into pattern matches).

Kahrs-Style Delete (§13.4)
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Delete uses Kahrs' formulation:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Spec.fst
   :language: fstar
   :start-after: (*** Delete — Kahrs-style functional deletion ***)

- ``balL``/``balR``: rebalance after a black-height deficit on
  left/right child.
- ``fuse``: merge two subtrees when a node is deleted.
- ``del``: recursive delete with color-aware rebalancing.
- ``delete = make_black ∘ del``.

Theorem 13.1: Height Bound
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CLRS Theorem 13.1 states: *A red-black tree with n internal nodes has
height at most 2·lg(n + 1).*  The proof follows CLRS:

1. **Key lemma** (``min_nodes_for_bh``): any valid subtree with
   black-height *bh* contains at least 2\ :sup:`bh` − 1 internal
   nodes.  Proved by induction on height with an appeal to
   ``pow2_plus``.

2. **Red-red exclusion bound** (``bh_height_bound``): since no two
   consecutive nodes are red, at least half the nodes on any
   root-to-leaf path are black: height ≤ 2·bh.

3. **Combining** (``height_bound_theorem``): from (1),
   n + 1 ≥ 2\ :sup:`bh`, so bh ≤ lg(n + 1), and from (2),
   height ≤ 2·bh ≤ 2·lg(n + 1).


Insert Correctness
~~~~~~~~~~~~~~~~~~~

Three families of lemmas are proved, all with zero admits:

1. **Membership** (``insert_mem``): after inserting *k*, querying *x*
   returns true iff *x = k* or *x* was already a member.  Proved by
   induction through ``ins_mem`` and ``balance_mem``.

2. **BST ordering** (``insert_preserves_bst``): ``balance`` preserves
   the BST property.  The proof requires explicit bound-weakening
   lemmas (``all_lt_weaken``, ``all_gt_weaken``) for the rotation
   cases where keys move between subtrees.

3. **RB invariants** (``insert_is_rbtree``): all three RB properties
   are maintained through insertion.  The key idea is the notion of
   ``almost_no_red_red`` — ``ins`` may introduce a red-red violation
   at the root, but ``balance`` restores the invariant at each black
   ancestor, and ``make_black`` re-establishes root-blackness:

   - ``balance_restores_no_red_red_left/right``: when ``balance`` is
     called on a Black parent with a child that is ``almost_no_red_red``,
     the result is fully ``no_red_red``.
   - ``balance_same_bh`` / ``balance_bh``: balance preserves the
     black-height invariant.
   - ``ins_properties``: the combined inductive lemma showing that
     ``ins`` preserves ``same_bh``, preserves ``bh``, and has
     ``almost_no_red_red``.

Delete Correctness
~~~~~~~~~~~~~~~~~~~

Delete correctness is proved analogously:

- ``delete_mem``: ``mem x (delete t k) ⟺ (mem x t ∧ x ≠ k)``.
- ``delete_preserves_bst``: BST ordering preserved.
- ``delete_is_rbtree``: all RB + BST properties preserved.

The proof requires lemmas for ``balL``, ``balR``, and ``fuse``
showing they preserve both BST ordering and RB invariants.


Okasaki-Style Pulse Implementation (``RBTree.Impl``)
=====================================================

The Pulse implementation uses heap-allocated nodes connected by
mutable pointers, rather than a functional tree in a mutable
reference.  This is a true imperative red-black tree — each node is a
separate heap object that can be individually allocated, mutated, and
freed.

Node Type and Recursive Predicate
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_node_type
   :end-before: //SNIPPET_END: rb_node_type

The ``is_rbtree ct ft`` separation-logic predicate links the concrete
pointer structure to the pure functional spec tree ``ft``.  It is
defined by recursion on the ghost spec tree: a ``Leaf`` requires
``ct == None`` (null pointer); a ``Node c l v r`` requires
``ct == Some p`` where ``p`` points to a heap-allocated node whose
key, color, and child pointers recursively satisfy ``is_rbtree``:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: is_rbtree
   :end-before: //SNIPPET_END: is_rbtree

``valid_rbtree`` bundles the separation-logic predicate with the pure
invariants:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: valid_rbtree
   :end-before: //SNIPPET_END: valid_rbtree

Balance (§13.3 — Pointer Rotations)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The four Okasaki rotation cases must be implemented as pointer
restructuring: reading node fields, mutating child pointers, and
writing back updated nodes.  This is challenging in separation logic
because each case requires opening the tree predicate to a specific
depth, performing the restructuring, and closing it back with the
correct ghost tree.

The implementation factors balance into three stages:

1. **Runtime classifier** (``classify_runtime``): a read-only traversal
   that opens node fields up to two levels deep, reads their colors,
   and returns one of five cases (LL, LR, RL, RR, None).  Crucially,
   this function *preserves* ``is_rbtree`` — it opens and closes each
   node, leaving ownership unchanged.

2. **Per-case rotation handlers** (``balance_ll``, ``balance_lr``,
   ``balance_rl``, ``balance_rr``): each handler opens exactly the
   nodes needed for its case, restructures pointers (reusing existing
   heap-allocated boxes where possible), and closes with a
   postcondition linking to ``S.balance``.  A ``classify_balance_lemma``
   in the Spec module proves that the classifier result matches the
   pure ``balance`` function, enabling a ``rewrite`` to connect the
   concrete result to the spec.

3. **Dispatcher** (``rb_balance``): calls the classifier, then
   dispatches to the correct handler.

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_balance
   :end-before: //SNIPPET_END: rb_balance


Search
~~~~~~~

Search preserves ``is_rbtree`` (read-only) and returns exactly the
pure spec's ``S.search`` result:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_search
   :end-before: //SNIPPET_END: rb_search


Insert
~~~~~~~

``rb_ins`` descends recursively, inserting at a leaf and calling
``rb_balance`` at each level on the way up.  When the key already
exists, the existing node is returned unchanged.  Nodes that are no
longer part of the tree (because ``rb_balance`` restructured pointers
around them) are freed with ``Box.free``:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_ins
   :end-before: //SNIPPET_END: rb_ins

``rb_insert`` wraps ``rb_ins`` and forces the root black, matching
``S.insert = make_black ∘ ins``:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_insert
   :end-before: //SNIPPET_END: rb_insert

The postcondition ``is_rbtree y (S.insert 'ft k)`` guarantees that
the resulting pointer tree represents exactly the pure-functional
insert result — which, by the Spec lemmas, is a valid RB tree, a
valid BST, and contains the new key plus all old keys.

Free
~~~~~

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: free_rbtree
   :end-before: //SNIPPET_END: free_rbtree


Validated and Complexity-Aware APIs
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The validated API (``rb_search_v``, ``rb_insert_v``, ``rb_delete_v``)
bundles the RB + BST invariants:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_insert_v
   :end-before: //SNIPPET_END: rb_insert_v

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_delete_v
   :end-before: //SNIPPET_END: rb_delete_v

CLRS-Style Pulse Implementation (``CLRSImpl``)
================================================

The CLRS-faithful implementation uses parent pointers and explicit
LEFT-ROTATE/RIGHT-ROTATE, matching the pseudocode in §13.2–13.4.

The pure specification (``CLRSSpec``) defines:

- ``left_rotate``, ``right_rotate``: tree restructuring primitives.
- ``clrs_fixup_left``, ``clrs_fixup_right``: uncle-checking fixup
  (Case 1: uncle Red → recolor; Cases 2/3: uncle Black → rotate).
- ``clrs_ins``, ``clrs_insert``: BST insert + fixup.
- ``clrs_del_cases234_left/right``, ``clrs_resolve_left/right``:
  4-case DELETE-FIXUP with symmetric handling.
- ``clrs_del``, ``clrs_delete``: full delete with successor
  replacement and fixup.

The Pulse implementation (``CLRSImpl.fst``) uses a ``rbtree_subtree``
predicate with parent-pointer tracking:

.. code-block:: fstar

   let rec rbtree_subtree (ct: rb_ptr) (ft: S.rbtree) (parent: rb_ptr)
     : Tot slprop (decreases ft)
     = match ft with
       | S.Leaf -> pure (ct == None)
       | S.Node c l v r ->
         exists* (bp: rb_node_ptr) (node: rb_node).
           pure (ct == Some bp) **
           (bp |-> node) **
           pure (node.key == v /\ node.color == c /\ node.p == parent) **
           rbtree_subtree node.left l (Some bp) **
           rbtree_subtree node.right r (Some bp)


Complexity (``RBTree.Complexity``)
===================================

The complexity module defines tick counters that shadow the recursive
structure of ``search``, ``ins``, and ``del``, proves they are bounded
by the tree height plus a constant, and combines with Theorem 13.1 to
obtain logarithmic bounds:

- **Search**: ``search_ticks t k ≤ height t + 1 ≤ 2·lg(n + 1) + 1``
- **Insert**: ``insert_ticks t k ≤ height t + 2 ≤ 2·lg(n + 1) + 2``
- **Delete**: ``delete_ticks t k ≤ 2·height t + 2 ≤ 4·lg(n + 1) + 2``

The balance operation contributes only O(1) to the cost since it
examines a constant number of nodes and performs at most two pointer
restructurings — this is reflected by not adding ticks inside
``balance``.

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: search_complexity
   :end-before: //SNIPPET_END: search_complexity

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: insert_complexity
   :end-before: //SNIPPET_END: insert_complexity

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Complexity.fsti
   :language: fstar
   :start-after: //SNIPPET_START: delete_complexity
   :end-before: //SNIPPET_END: delete_complexity

All bounds are proven with **zero admits**.


Proof Techniques
=================

Several Pulse-specific techniques were developed for these implementations:

- **Option-match rewrite pattern**: After ``match x { None -> }``,
  Pulse rewrites slprops from ``is_rbtree x ft`` to
  ``is_rbtree None ft``.  Ghost helpers must be called with the
  concrete value (e.g., ``is_rbtree_case_none rn.left``), and
  ``with t. rewrite (is_rbtree x t) as (is_rbtree x target)`` is
  used after ``intro_is_rbtree_node`` to connect to the postcondition.

- **Pure classifier for deep pattern matching**: The Okasaki balance
  requires matching 3 levels deep (node, child, grandchild), which
  in Pulse would require deeply nested pointer matches with slprop
  rewrites at each level.  The ``classify_runtime`` + per-case handler
  pattern avoids this: the classifier does the deep reads (read-only,
  preserving slprops), and each handler opens only what it needs.

- **Ghost ``is_rbtree_not_leaf``**: A ghost function that proves
  ``Some? x`` from ``S.Node? ft`` and ``is_rbtree x ft``, enabling
  safe use of ``Some?.v x`` in the rotation handlers.


Limitations
===========

- **Delete tick bound is 4·lg(n+1) + 2, not 2·lg(n+1).** The
  Kahrs-style ``fuse`` traverses both inner spines, doubling the
  constant factor.
- **No amortized analysis.** All bounds are worst-case per operation.
- **Integer keys only.** No generic key type or comparator.
- **Destructive operations.** Insert/delete consume the input tree.
- **CLRS-style lacks complexity bounds.** O(lg n) is proven only for
  the Okasaki-style operations.

Remaining Admits
================

**None.** All modules (``Spec``, ``Lemmas``, ``Complexity``,
``Impl``, ``CLRSSpec``, ``CLRSImpl``) are fully verified with zero
``admit()``, ``assume()``, or ``assume_`` calls.

Deletion (CLRS §13.4) is fully implemented in both the Okasaki-style
(Kahrs formulation) and CLRS-style (rotation-based fixup)
implementations.
