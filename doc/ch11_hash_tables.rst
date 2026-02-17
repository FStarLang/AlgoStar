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
3. **Worst-case complexity** O(n) proved via ghost tick counters for
   both insert and search.

All proofs are complete with **zero admits**.

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

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.fst
   :language: fstar
   :start-after: //SNIPPET_START: ht_hash
   :end-before: //SNIPPET_END: ht_hash

The pure ``hash_probe_nat`` variant is used in specifications and
proofs; the ``hash_probe`` variant operates on ``SZ.t`` for the
imperative code. ``lemma_hash_probe_consistent`` bridges the two.

Correctness Predicate
~~~~~~~~~~~~~~~~~~~~~

The correctness of insertion is expressed via ``key_in_table``: the
key exists at some position in the probe sequence:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.fst
   :language: fstar
   :start-after: //SNIPPET_START: ht_key_in_table
   :end-before: //SNIPPET_END: ht_key_in_table

This is an existential: there exists a probe number ``probe < size``
such that the array at position ``hash_probe_nat key probe size``
contains ``key``. The search operation's correctness is expressed
dually: if the result index is in bounds, the array at that index
contains the key.

Hash Insert
~~~~~~~~~~~

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.fst
   :language: pulse
   :start-after: //SNIPPET_START: ht_hash_insert
   :end-before: //SNIPPET_END: ht_hash_insert

The implementation probes linearly from ``h(key)`` until it finds an
empty (``-1``) or deleted (``-2``) slot, then writes the key. If no
slot is found after ``size`` probes, the table is full and the
function returns ``false`` without modifying the array.

The loop invariant tracks two cases:

- If ``inserted == true``: ``key_in_table`` holds for the current
  array state.
- If ``inserted == false``: the array is unchanged (``Seq.equal st s``).

This clean split avoids reasoning about partial modifications.

Hash Search
~~~~~~~~~~~

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.fst
   :language: pulse
   :start-after: //SNIPPET_START: ht_hash_search
   :end-before: //SNIPPET_END: ht_hash_search

Search probes linearly, stopping when it finds the key (returning
its index), hits an empty slot (key not present), or exhausts all
probes. The return value is the found index or ``size`` (sentinel for
not-found). The array is not modified — the ``ensures`` clause
returns the original ghost sequence ``s``.

The loop invariant additionally tracks ``probes_not_key s size key vi``,
asserting that all probes ``0 .. vi - 1`` did not contain the key.
This provides a basis for clients to reason about the not-found case.

Complexity
==========

The worst-case complexity of both operations is O(n) where n is the
table capacity: in the worst case, every slot must be probed. The
complexity bounds are defined as:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: ht_complexity_bounds
   :end-before: //SNIPPET_END: ht_complexity_bounds

The instrumented insert function threads a ghost tick counter,
calling ``tick`` once per probe:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: ht_insert_complexity
   :end-before: //SNIPPET_END: ht_insert_complexity

The loop invariant maintains ``vc - c0 == vi`` (exactly one tick per
probe), and the loop exits when ``vi == size``, giving
``cf - c0 <= size``.

The instrumented search function has the same structure:

.. literalinclude:: ../ch11-hash-tables/CLRS.Ch11.HashTable.Complexity.fst
   :language: pulse
   :start-after: //SNIPPET_START: ht_search_complexity
   :end-before: //SNIPPET_END: ht_search_complexity

The postcondition combines functional correctness (found index
contains the key) with the complexity bound (at most ``size`` probes).

.. note::

   The worst-case O(n) bound proved here covers degenerate inputs.
   Under the uniform hashing assumption (CLRS §11.4), the expected
   number of probes is O(1/(1 − α)) where α is the load factor.
   Proving the average-case bound would require a probabilistic model,
   which is outside the scope of this formalization.

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
