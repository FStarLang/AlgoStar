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

.. contents::
   :local:
   :depth: 2

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

- **§13.4 Deletion** — RB-DELETE and RB-DELETE-FIXUP (not implemented
  in this formalization).

Our formalization covers §13.1–13.3 in full.  Deletion (§13.4) is not
yet implemented.

Formalization Overview
======================

The formalization has three layers, all with **zero admits**:

1. **Pure functional specification** (``CLRS.Ch13.RBTree.Spec``) — an
   inductive ``rbtree`` type, RB invariant predicates, Okasaki-style
   functional ``balance``/``ins``/``insert``, and correctness lemmas for
   membership, BST ordering, RB invariant preservation, and the height
   bound (Theorem 13.1).

2. **Pointer-based Pulse implementation** (``CLRS.Ch13.RBTree``) —
   heap-allocated nodes with mutable fields and nullable child pointers,
   tied to the pure spec via a recursive separation-logic predicate
   ``is_rbtree``.  Operations (search, insert, balance) each have a
   postcondition proving equivalence to the pure spec.

3. **Complexity analysis** (``CLRS.Ch13.RBTree.Complexity``) — pure
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
   :end-before: // ========== Balance case classifier ==========

The four cases in ``balance`` correspond exactly to the three cases of
RB-INSERT-FIXUP in CLRS (our four cases arise because CLRS treats the
symmetric left/right sub-cases separately in the text, while Okasaki
unifies them into pattern matches).

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

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.Spec.fst
   :language: fstar
   :start-after: // CLRS Theorem 13.1: height <= 2 * log2_floor(n + 1)
   :end-before: (*** Insert Correctness ***)


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


Pointer-Based Pulse Implementation (``RBTree``)
=================================================

The Pulse implementation uses heap-allocated nodes connected by
mutable pointers, rather than a functional tree in a mutable
reference.  This is a true imperative red-black tree — each node is a
separate heap object that can be individually allocated, mutated, and
freed.

Node Type and Recursive Predicate
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_node_type
   :end-before: //SNIPPET_END: rb_node_type

The ``is_rbtree ct ft`` separation-logic predicate links the concrete
pointer structure to the pure functional spec tree ``ft``.  It is
defined by recursion on the ghost spec tree: a ``Leaf`` requires
``ct == None`` (null pointer); a ``Node c l v r`` requires
``ct == Some p`` where ``p`` points to a heap-allocated node whose
key, color, and child pointers recursively satisfy ``is_rbtree``:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.fst
   :language: pulse
   :start-after: //SNIPPET_START: is_rbtree
   :end-before: //SNIPPET_END: is_rbtree

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
   dispatches to the correct handler.  Each handler returns
   ``is_rbtree y (S.balance S.Black lt v rt)``; the dispatcher
   rewrites ``S.Black`` to the actual color ``c`` (which the
   classifier already proved equals ``Black`` for rotation cases).

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_balance
   :end-before: //SNIPPET_END: rb_balance


Search
~~~~~~~

Search preserves ``is_rbtree`` (read-only) and returns exactly the
pure spec's ``S.search`` result:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.fst
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

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_ins
   :end-before: //SNIPPET_END: rb_ins

``rb_insert`` wraps ``rb_ins`` and forces the root black, matching
``S.insert = make_black ∘ ins``:

.. literalinclude:: ../ch13-rbtree/CLRS.Ch13.RBTree.fst
   :language: pulse
   :start-after: //SNIPPET_START: rb_insert
   :end-before: //SNIPPET_END: rb_insert

The postcondition ``is_rbtree y (S.insert 'ft k)`` guarantees that
the resulting pointer tree represents exactly the pure-functional
insert result — which, by the Spec lemmas, is a valid RB tree, a
valid BST, and contains the new key plus all old keys.

Proof Techniques
~~~~~~~~~~~~~~~~~

Several Pulse-specific techniques were developed for this implementation:

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


Complexity (``RBTree.Complexity``)
===================================

The complexity module defines tick counters that shadow the recursive
structure of ``search`` and ``ins``, proves they are bounded by the
tree height plus a constant, and combines with Theorem 13.1 to obtain
logarithmic bounds:

- **Search**: ``search_ticks t k ≤ height t + 1 ≤ 2·lg(n + 1) + 1``
- **Insert**: ``insert_ticks t k ≤ height t + 2 ≤ 2·lg(n + 1) + 2``

The balance operation contributes only O(1) to the cost since it
examines a constant number of nodes and performs at most two pointer
restructurings — this is reflected by not adding ticks inside
``balance``.

Both bounds are proven with **zero admits**.


Remaining Admits
================

**None.** All three modules (``Spec``, ``RBTree``, ``Complexity``)
are fully verified with zero ``admit()``, ``assume()``, or
``assume_`` calls.

Deletion (CLRS §13.4) is not yet implemented.
