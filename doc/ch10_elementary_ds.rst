.. _Ch10_DataStructures:

########################################
Elementary Data Structures
########################################

This chapter covers the fundamental data structures from CLRS Chapter 10:
stacks (§10.1), queues (§10.1), and linked lists (§10.2). We provide
three complementary layers of formalization:

1. **Pure functional specifications** in F* that define the abstract
   behaviour of each data structure (LIFO, FIFO, membership).
2. **Imperative Pulse implementations** — array-based stack and queue,
   and pointer-based singly- and doubly-linked lists — each verified
   against the pure specification via a separation-logic invariant.
3. **Complexity bounds** proved via ghost tick counters: stack and queue
   operations are O(1); linked-list search and delete are O(n).

All proofs are complete with **zero admits**.

Pure Specifications
====================

The module ``CLRS.Ch10.DS.Spec`` defines abstract models of each data
structure as plain F* lists and proves their algebraic properties.

Stack (LIFO)
~~~~~~~~~~~~

A stack is modelled as a list where the head is the top:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.DS.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: stack_spec
   :end-before: //SNIPPET_END: stack_spec

The key LIFO property is that popping a freshly pushed element returns
that element and restores the original stack:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.DS.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: stack_lifo
   :end-before: //SNIPPET_END: stack_lifo

Both lemmas hold by computation — the proof body is simply ``()``.

Queue (FIFO)
~~~~~~~~~~~~

The queue specification uses a two-list representation (front and back)
with a well-formedness invariant: if the front is empty, the back must
also be empty. The abstract view is ``front @ rev back``:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.DS.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: queue_spec
   :end-before: //SNIPPET_END: queue_spec

The FIFO property is expressed as: dequeuing from a non-empty queue
returns the head of the abstract list view, and the remaining queue
corresponds to the tail:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.DS.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: queue_fifo
   :end-before: //SNIPPET_END: queue_fifo

Linked List
~~~~~~~~~~~

The list specification defines insert-at-head, linear search, and
delete-first-occurrence on plain F* lists:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.DS.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: list_spec
   :end-before: //SNIPPET_END: list_spec

A separate module ``CLRS.Ch10.LinkedList.Spec`` proves additional
properties including: insert makes the element searchable, delete of a
unique element removes it, and insert-then-delete is the identity.

Array-Based Stack
==================

CLRS §10.1 presents a stack implemented with an array and a ``top``
index. Our Pulse implementation follows this design exactly.

Data Structure and Invariant
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.Stack.fsti
   :language: fstar
   :start-after: //SNIPPET_START: stack_type
   :end-before: //SNIPPET_END: stack_type

The separation-logic invariant ``stack_inv`` ties the array contents
to a ghost list of elements. It asserts ownership of both the
underlying vector and the top-pointer box, and requires that the
first ``top`` elements of the array match the logical list
element-by-element:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.Stack.fsti
   :language: fstar
   :start-after: //SNIPPET_START: stack_inv
   :end-before: //SNIPPET_END: stack_inv

Operations
~~~~~~~~~~

All operations are specified in terms of the ghost ``contents`` list.
``push`` appends to the end (the top of the stack), ``pop`` removes the
last element and returns it, and ``peek`` reads without removing:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.Stack.fsti
   :language: pulse
   :start-after: //SNIPPET_START: stack_ops
   :end-before: //SNIPPET_END: stack_ops

The ``push`` implementation writes the element at position ``top`` and
increments the index. The proof calls
``lemma_array_update_preserves_prefix`` to show that updating the array
at position ``n`` (where ``n`` equals the list length) extends the
element-by-element correspondence by one.

The ``pop`` implementation reads from ``top - 1`` and decrements. The
proof uses ``lemma_init_last_append`` to show that the popped element
equals ``L.last contents`` and the remaining list is ``L.init contents``.

Circular-Buffer Queue
======================

CLRS §10.1 describes a queue backed by a circular buffer. The
implementation tracks ``head``, ``tail``, and ``size`` indices that
wrap around modulo the capacity.

Data Structure and Invariant
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.Queue.fsti
   :language: fstar
   :start-after: //SNIPPET_START: queue_type
   :end-before: //SNIPPET_END: queue_type

The invariant maps circular indices to the logical list: element ``i``
of the list lives at array position ``(head + i) % capacity``:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.Queue.fsti
   :language: fstar
   :start-after: //SNIPPET_START: queue_inv
   :end-before: //SNIPPET_END: queue_inv

The key invariant conjunct ``tail == (head + size) % capacity`` ties
the three indices together. This is maintained through modular
arithmetic lemmas (``lemma_tail_update``, ``lemma_tail_dequeue``,
``lemma_wraparound_eq_mod``).

Operations
~~~~~~~~~~

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.Queue.fsti
   :language: pulse
   :start-after: //SNIPPET_START: queue_ops
   :end-before: //SNIPPET_END: queue_ops

``enqueue`` writes at the tail position, then advances tail with
wraparound (``if tail + 1 >= capacity then 0 else tail + 1``).
The proof calls ``lemma_enqueue_invariant`` to show that the
element-by-element correspondence extends by one index without
disturbing existing entries — the crucial step is proving that the
new tail index differs from all existing indices via
``lemma_mod_index_ne``.

``dequeue`` reads at the head position and advances head. The proof
calls ``lemma_dequeue_invariant`` and ``lemma_mod_index_shift`` to
show that the remaining elements at positions
``(new_head + i) % capacity`` correspond to ``L.tl contents``.

Linked Lists
=============

The project provides two linked-list implementations: a singly-linked
list (``CLRS.Ch10.SinglyLinkedList``) and a true doubly-linked list
with prev pointers (``CLRS.Ch10.DLL``). Both implement the CLRS §10.2
operations: LIST-INSERT, LIST-SEARCH, and LIST-DELETE.

Singly-Linked List
~~~~~~~~~~~~~~~~~~~

The singly-linked list uses heap-allocated boxes for nodes, with a
recursive separation-logic predicate ``is_dlist`` that matches on the
logical list (decreasing) to ensure termination:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.SinglyLinkedList.fst
   :language: fstar
   :start-after: //SNIPPET_START: sll_node
   :end-before: //SNIPPET_END: sll_node

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.SinglyLinkedList.fst
   :language: fstar
   :start-after: //SNIPPET_START: sll_is_dlist
   :end-before: //SNIPPET_END: sll_is_dlist

The predicate unfolds inductively: the empty list is ``pure (x == None)``;
a cons cell requires ownership of the head box and the recursive
predicate on the tail. Ghost helper functions (``intro_is_dlist_cons``,
``is_dlist_case_some``, etc.) handle fold/unfold of the recursive
predicate.

LIST-INSERT inserts at the head in O(1):

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.SinglyLinkedList.fst
   :language: pulse
   :start-after: //SNIPPET_START: sll_list_insert
   :end-before: //SNIPPET_END: sll_list_insert

LIST-SEARCH traverses from head, returning a boolean indicating
membership:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.SinglyLinkedList.fst
   :language: pulse
   :start-after: //SNIPPET_START: sll_list_search
   :end-before: //SNIPPET_END: sll_list_search

LIST-DELETE removes the first occurrence of a key, using ``remove_first``
as the pure specification:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.SinglyLinkedList.fst
   :language: pulse
   :start-after: //SNIPPET_START: sll_list_delete
   :end-before: //SNIPPET_END: sll_list_delete

The delete implementation is recursive: if the head matches, it frees
the node and returns the tail; otherwise it recurses, then updates the
current node's ``next`` pointer to the new tail.

Doubly-Linked List
~~~~~~~~~~~~~~~~~~~

The DLL module (``CLRS.Ch10.DLL``) uses a *doubly-linked segment*
predicate (``dls``) that tracks both forward and backward pointers.
Nodes carry ``key``, ``prev``, and ``next`` fields:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.DLL.fst
   :language: fstar
   :start-after: //SNIPPET_START: dll_node
   :end-before: //SNIPPET_END: dll_node

The ``dls`` predicate is parameterized by the head box, the logical
list, the predecessor pointer, the tail box, and the successor
pointer. The full ``dll`` wraps ``dls`` with ``None`` as both boundary
pointers:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.DLL.fst
   :language: fstar
   :start-after: //SNIPPET_START: dll_dls
   :end-before: //SNIPPET_END: dll_dls

The DLL operations take mutable references to head and tail pointers,
following the CLRS interface where the list object holds pointers to
both ends:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.DLL.fst
   :language: pulse
   :start-after: //SNIPPET_START: dll_list_insert
   :end-before: //SNIPPET_END: dll_list_insert

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.DLL.fst
   :language: pulse
   :start-after: //SNIPPET_START: dll_list_search
   :end-before: //SNIPPET_END: dll_list_search

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.DLL.fst
   :language: pulse
   :start-after: //SNIPPET_START: dll_list_delete
   :end-before: //SNIPPET_END: dll_list_delete

The DLL also provides ``list_delete_node`` for O(n) indexed deletion
(given an erased index ``i < length l``, remove the element at
position ``i``).

A key proof challenge in the DLL is *factoring*: the ``dls`` predicate
must be temporarily decomposed to read or modify the head node. The
helper predicates ``dls_factored`` and ``dls_factored_next`` split the
ownership of the head node from the tail segment, and ghost functions
``factor_dls``/``unfactor_dls`` perform the conversion. The
``dls_append`` ghost function reassembles two adjacent segments.

Complexity
==========

Complexity tracking is fused into the Pulse implementation modules
where it provides meaningful bounds. For stack and queue the operations
are O(1) by construction (single array access / pointer update), so
no separate complexity tracking is needed.

For the singly-linked list, ``CLRS.Ch10.SinglyLinkedList.Impl``
includes ghost-tick instrumented variants (``list_insert_tick``,
``list_search_tick``, ``list_delete_tick``) that use a
``GhostReference.ref nat`` counter. Each node visit calls ``tick``
once, and the postcondition bounds the counter increment:

.. literalinclude:: ../ch10-elementary-ds/CLRS.Ch10.SinglyLinkedList.Impl.fsti
   :language: pulse
   :start-after: //SNIPPET_START: sll_tick_ops
   :end-before: //SNIPPET_END: sll_tick_ops

The complexity invariant in each loop or recursive call tracks
``cf - c0 == number_of_iterations``. For insert this is exactly 1;
for search and delete it is at most ``L.length 'l``, matching the
CLRS worst-case bounds.

Proof Techniques Summary
=========================

1. **Recursive separation-logic predicates**: The ``is_dlist`` and
   ``dls`` predicates match on the logical list (using ``decreases l``)
   to ensure well-foundedness. Ghost fold/unfold helpers manage the
   predicate structure without affecting runtime code.

2. **Factoring for node access**: The DLL's ``dls`` predicate owns
   all nodes collectively. To read or modify the head, we *factor*
   it into head ownership plus a tail segment, operate, then
   *unfactor*. This avoids the need for random-access into the
   predicate.

3. **Modular arithmetic for circular buffers**: The queue invariant
   uses ``(head + i) % capacity`` indexing. Maintaining this through
   enqueue and dequeue requires lemmas about modular arithmetic
   associativity (``(a + b) % n == ((a % n) + b) % n``) and
   injectivity (distinct offsets map to distinct indices when the
   count is below capacity).

4. **Ghost tick counters**: The ``GhostReference.ref nat`` pattern
   from Chapter 2 is reused here. The counter is erased at runtime
   but its value is constrained by the recursive structure or loop
   invariant.
