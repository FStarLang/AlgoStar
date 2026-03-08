.. _Ch11_HashTables:

########################################
Hash Tables
########################################

This chapter covers hash tables from CLRS Chapter 11, focusing on
open addressing with linear probing (§11.4). The formalization
provides:

1. **Pure specification** as an association-list model with algebraic
   properties (insert/search/delete frame lemmas).
2. **Imperative Pulse implementation** of open-addressed hash table
   using sentinel values for empty and deleted slots.
3. **Refinement bridge** proving equivalence between the array
   representation and the abstract model.
4. **Worst-case complexity** O(n) proved via ghost tick counters for
   insert, search, and delete.

All proofs are complete with **zero admits**.

.. contents::
   :local:
   :depth: 2

Summary
=======

.. list-table::
   :header-rows: 1

   * - Operation
     - CLRS §
     - Complexity (proven)
     - Admits
   * - ``hash_insert``
     - §11.4
     - O(n) worst case
     - 0
   * - ``hash_search``
     - §11.4
     - O(n) worst case
     - 0
   * - ``hash_delete``
     - §11.4
     - O(n) worst case
     - 0

Pure Specification
===================

The module ``CLRS.Ch11.HashTable.Spec`` models a hash table as an
association list ``list (nat & int)``. Operations are defined
functionally and their frame properties are proved by induction:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: ht_model
   :end-before: //SNIPPET_END: ht_model

The model is simple: ``ht_insert`` prepends a binding (shadowing any
existing one), ``ht_search`` returns the first matching value, and
``ht_delete`` removes *all* bindings for a key. This last choice
means delete is idempotent and commutative, which simplifies
reasoning.

The key algebraic properties:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: ht_spec_lemmas
   :end-before: //SNIPPET_END: ht_spec_lemmas

These four lemmas constitute the *frame conditions* for a hash table:

- ``lemma_insert_search_same``: inserting key ``k`` then searching
  for ``k`` returns the inserted value. Holds by computation.
- ``lemma_insert_search_other``: inserting key ``k1`` does not affect
  searches for a different key ``k2``. Proved by induction.
- ``lemma_delete_search_same``: deleting key ``k`` makes subsequent
  searches return ``None``. Proved by induction — the recursive
  ``ht_delete`` removes all occurrences.
- ``lemma_delete_search_other``: deleting ``k1`` preserves bindings
  for ``k2``. Proved by induction.

Additional properties include ``lemma_insert_delete_same`` (insert
then delete is equivalent to delete alone),
``lemma_delete_commutes`` (deletes on different keys commute), and
``lemma_delete_idempotent`` (double delete is a no-op).

Open Addressing with Linear Probing
=====================================

CLRS §11.4 presents open addressing as an alternative to chaining.
Our implementation stores keys directly in a flat array, using
sentinel values ``-1`` (empty) and ``-2`` (deleted) to mark slots.
Valid keys are non-negative integers.

Hash Function
~~~~~~~~~~~~~

The hash function is division-method hashing with linear probing:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: ht_hash
   :end-before: //SNIPPET_END: ht_hash

The pure ``hash_probe_nat`` variant is used in specifications and
proofs; the ``hash_probe`` variant in ``Impl.fst`` operates on
``SZ.t`` for the imperative code.

Table Invariant
~~~~~~~~~~~~~~~

The correctness of search depends on the CLRS argument that no
operation ever turns a slot back to NIL (``-1``) after a key was
placed past it. The ``valid_ht`` predicate captures this:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: ht_valid_ht
   :end-before: //SNIPPET_END: ht_valid_ht

For every key at probe position ``probe``, no earlier probe position
contains NIL. This is the invariant that all three operations preserve
and that search relies on for completeness.

Correctness Predicates
~~~~~~~~~~~~~~~~~~~~~~

The correctness of insertion is expressed via ``key_in_table``: the
key exists at some position in the probe sequence:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: ht_key_in_table
   :end-before: //SNIPPET_END: ht_key_in_table

The stronger ``key_findable`` predicate guarantees that search will
reach the key — no empty slot blocks the probe path:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: ht_key_findable
   :end-before: //SNIPPET_END: ht_key_findable

Hash Insert (§11.4)
~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: ht_hash_insert
   :end-before: //SNIPPET_END: ht_hash_insert

The postcondition combines four guarantees on success:

1. ``key_in_table``: the key exists somewhere in the probe sequence.
2. ``key_findable``: no empty slot precedes it (so search finds it).
3. ``seq_modified_at s s' idx``: exactly one slot changed, from
   empty/deleted to the key.
4. ``valid_ht s'``: the table invariant is preserved.

On failure (table full), ``s' == s`` — the table is unchanged.

The implementation:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Impl.fst
   :language: pulse
   :start-after: //SNIPPET_START: ht_hash_insert_impl
   :end-before: //SNIPPET_END: ht_hash_insert_impl

Hash Search (§11.4)
~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: ht_hash_search
   :end-before: //SNIPPET_END: ht_hash_search

Search probes linearly, stopping when it finds the key (returning
its index), hits an empty slot (key not present), or exhausts all
probes. The return value is the found index or ``size`` (sentinel for
not-found). The array is not modified — the ``ensures`` clause
returns the original ghost sequence ``s``.

The **not-found guarantee** is the strongest possible: when ``result
== size``, the postcondition proves ``~(key_in_table s size key)`` —
the key does not exist *anywhere* in the table, not just that it
wasn't found in the probe sequence.

Hash Delete (§11.4)
~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: ht_hash_delete
   :end-before: //SNIPPET_END: ht_hash_delete

Delete finds the key by linear probing, then replaces it with ``-2``
(deleted sentinel). This is CLRS's lazy deletion: deleted slots are
skipped by search but reusable by insert. The ``valid_ht`` invariant
is preserved because the slot changes from a valid key to ``-2``, not
to ``-1`` (NIL) — so no probe chain is broken.

Helper Operations
~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: ht_helpers
   :end-before: //SNIPPET_END: ht_helpers

``hash_table_create`` allocates a vector of ``-1`` sentinels (all
empty) and proves the resulting sequence satisfies ``valid_ht``.
``hash_table_free`` releases the vector.

Complexity
==========

The worst-case complexity of all three operations is O(n) where n is
the table capacity: in the worst case, every slot must be probed.
All three operation signatures in the ``.fsti`` include the complexity
bound ``cf - reveal c0 <= SZ.v size`` as part of the postcondition.

The ghost tick counter ``ctr: GR.ref nat`` is threaded through each
loop. The loop invariant maintains ``vc - c0 == vi`` (exactly one
tick per probe), and the loop exits when ``vi == size``, giving
``cf - c0 ≤ size``.

Internal hash functions used in the implementation:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Impl.fst
   :language: fstar
   :start-after: //SNIPPET_START: ht_hash_internal
   :end-before: //SNIPPET_END: ht_hash_internal

.. note::

   The worst-case O(n) bound proved here covers degenerate inputs.
   Under the uniform hashing assumption (CLRS §11.4), the expected
   number of probes is O(1/(1 − α)) where α is the load factor.
   Proving the average-case bound would require a probabilistic model,
   which is outside the scope of this formalization.

Refinement Bridge (``HashTable.Lemmas``)
=========================================

The ``Lemmas`` module connects the flat-array implementation to the
pure association-list specification:

- ``lemma_linear_probe_surjective``: for any target position *j*,
  there exists a probe *p* such that ``hash_probe_nat key p size == j``.
  This ensures the linear probe sequence covers all slots.

- ``lemma_key_in_table_iff_array_has_key``: the existential
  ``key_in_table`` is equivalent to simple array membership
  ``array_has_key``.

- ``lemma_probes_not_key_full_iff``: exhausting all probes without
  finding the key is equivalent to the key not being in the array.

- ``lemma_array_to_model_mem_full``: the ``Spec.mem`` predicate on
  the abstract model agrees with ``array_has_key`` on the concrete
  representation.

Proof Techniques Summary
=========================

1. **Sentinel-based slot discrimination**: Using ``-1`` (empty) and
   ``-2`` (deleted) as sentinels allows the loop to branch on simple
   integer comparisons. The proof exploits the fact that valid keys
   are non-negative to show that sentinels never collide with keys.

2. **Existential correctness predicate**: ``key_in_table`` is an
   existential (``exists probe. ...``). The insert proof witnesses
   this existential by providing the probe number ``vi`` at which the
   key was placed. SMT handles the existential introduction
   automatically once the witness is in scope.

3. **Read-only search invariant**: The search function does not modify
   the array, so its postcondition returns the original ghost sequence.
   This simplifies the loop invariant — only the ghost counter and
   index variables change.

4. **Exact tick counting**: The complexity invariant
   ``vc - c0 == vi`` is an *equality*, not a bound. The O(n) bound
   follows from ``vi <= size`` at loop exit. This is stronger than
   needed but simplifies the invariant.

5. **Table invariant preservation**: Each operation's proof shows that
   ``valid_ht`` holds before and after. Insert fills an empty/deleted
   slot (never breaks a probe chain). Delete replaces a key with
   ``-2`` (never introduces ``-1``). Search is read-only.

Limitations
===========

- **Only linear probing.** No chaining, quadratic probing, or double
  hashing.
- **O(n) worst case only.** No load-factor analysis or average-case
  bounds.
- **Integer keys only.** Keys must be non-negative integers (sentinel
  encoding). No generic key type or user-supplied hash function.
- **Fixed-size table.** No dynamic resizing or rehashing.
- **Key-only storage.** The imperative implementation stores only keys,
  not key-value pairs (the pure spec models key-value pairs for
  generality).
