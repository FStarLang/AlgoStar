/*
 * Hash Table with Open Addressing — C implementation with c2pulse verification.
 *
 * CLRS §11.4: Open addressing hash table with linear probing.
 * Division-method hash: h(k) = k % m
 * Probe sequence: h(k, i) = (h(k) + i) % m
 *
 * Sentinel values: -1 = empty, -2 = deleted, >= 0 = valid key
 *
 * Uses c2pulse's _rec for natural recursive probing, replacing
 * explicit while-loops with done/count/idx mutable variables.
 *
 * Specifications at parity with CLRS.Ch11.HashTable.Impl.fsti:
 *   - c_valid_ht: hash table invariant preserved by all operations
 *   - hash_search: found index contains key; not found => key absent
 *   - hash_insert: c_valid_ht preserved, key present on success
 *   - hash_delete: c_valid_ht preserved, key removed on success
 *   - hash_insert_no_dup: search then insert, no duplicate keys
 *
 * Complexity bounds (ghost counter) are omitted since c2pulse does not
 * support ghost references; the Impl.fsti proofs cover those.
 *
 * c_valid_ht is defined in BridgeLemmas using the total seq_val function,
 * avoiding the Some?/array_read well-typedness issues in quantifiers.
 * The bridge lemma lemma_c_valid_ht_iff_valid_ht connects it to Impl.valid_ht.
 *
 * array_value_of extracts the ghost sequence from the c2pulse array model.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

_include_pulse(open CLRS.Ch11.HashTable.Impl)
_include_pulse(open CLRS.Ch11.HashTable.C.BridgeLemmas)

/*
 * Recursive probe helper for hash_search.
 *
 * Scans probe positions starting at idx (the count-th probe),
 * stopping when: key is found, an empty slot (-1) is hit,
 * or all positions have been checked.
 *
 * Returns the index if found, or size if not found.
 */
_rec size_t hash_search_probe(_array int *table, size_t size, int key,
                              size_t idx, size_t count)
  _requires(table._length == size)
  _requires(size > 0)
  _requires(key >= 0)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(key))))
  _requires(count <= size)
  _requires((bool) _inline_pulse(SizeT.v $(idx) == hash_probe_nat (Int32.v $(key)) (SizeT.v $(count)) (SizeT.v $(size))))
  _requires((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
  _requires((bool) _inline_pulse(forall (p: nat). p < SizeT.v $(count) ==> seq_val (array_value_of $(table)) (hash_probe_nat (Int32.v $(key)) p (SizeT.v $(size))) =!= Int32.v $(key)))
  _preserves_value(table._length)
  _ensures(return <= size)
  _ensures(return < size ==> table[return] == key)
  _ensures((bool) _inline_pulse((return_1 = $(size)) ==> (forall (p: nat). p < SizeT.v $(size) ==> seq_val (array_value_of $(table)) (hash_probe_nat (Int32.v $(key)) p (SizeT.v $(size))) =!= Int32.v $(key))))
  _ensures(_forall(size_t k, k < size ==> table[k] == _old(table[k])))
  _ensures((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
  _decreases(size - count)
{
  if (count >= size) {
    return size;
  }

  int slot = table[idx];

  if (slot == key) {
    return idx;
  }

  if (slot == -1) {
    return size;
  }

  size_t next_idx;
  if (idx + 1 == size) {
    next_idx = 0;
  } else {
    next_idx = idx + 1;
  }
  return hash_search_probe(table, size, key, next_idx, count + 1);
}

/*
 * Search for a key in the hash table using linear probing.
 * Returns the array index if found, or size if not found.
 */
size_t hash_search(_array int *table, size_t size, int key)
  _requires(table._length == size)
  _requires(size > 0)
  _requires(key >= 0)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(key))))
  _requires((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
  _ensures(table._length == size)
  _ensures(return <= size)
  _ensures(return < size ==> table[return] == key)
  _ensures((bool) _inline_pulse((return_1 = $(size)) ==> (forall (p: nat). p < SizeT.v $(size) ==> seq_val (array_value_of $(table)) (hash_probe_nat (Int32.v $(key)) p (SizeT.v $(size))) =!= Int32.v $(key))))
  _ensures(_forall(size_t k, k < size ==> table[k] == _old(table[k])))
  _ensures((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
{
  size_t start = (size_t)key % size;
  return hash_search_probe(table, size, key, start, 0);
}

/*
 * Recursive probe helper for hash_insert.
 *
 * Scans probe positions starting at idx (the count-th probe),
 * inserting the key at the first empty (-1) or deleted (-2) slot.
 *
 * Returns true if inserted, false if all positions occupied.
 */
_rec bool hash_insert_probe(_array int *table, size_t size, int key,
                            size_t idx, size_t count)
  _requires(table._length == size)
  _requires(size > 0)
  _requires(key >= 0)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(key))))
  _requires(count <= size)
  _requires((bool) _inline_pulse(SizeT.v $(idx) == hash_probe_nat (Int32.v $(key)) (SizeT.v $(count)) (SizeT.v $(size))))
  _requires((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
  _requires((bool) _inline_pulse(forall (q: nat). q < SizeT.v $(count) ==> seq_val (array_value_of $(table)) (hash_probe_nat (Int32.v $(key)) q (SizeT.v $(size))) =!= -1 /\ seq_val (array_value_of $(table)) (hash_probe_nat (Int32.v $(key)) q (SizeT.v $(size))) =!= -2))
  _preserves_value(table._length)
  _ensures(return ==> _exists(size_t k, k < size && table[k] == key))
  _ensures(return == false ==> _forall(size_t k, k < size ==> table[k] == _old(table[k])))
  _ensures((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
  _decreases(size - count)
{
  if (count >= size) {
    return false;
  }

  int slot = table[idx];

  if (slot == -1 || slot == -2) {
    table[idx] = key;
    return true;
  }

  size_t next_idx;
  if (idx + 1 == size) {
    next_idx = 0;
  } else {
    next_idx = idx + 1;
  }
  return hash_insert_probe(table, size, key, next_idx, count + 1);
}

/*
 * Insert a key into the hash table using linear probing.
 * Returns true if successful, false if the table is full.
 */
bool hash_insert(_array int *table, size_t size, int key)
  _requires(table._length == size)
  _requires(size > 0)
  _requires(key >= 0)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(key))))
  _requires((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
  _ensures(table._length == size)
  _ensures(return ==> _exists(size_t k, k < size && table[k] == key))
  _ensures(return == false ==> _forall(size_t k, k < size ==> table[k] == _old(table[k])))
  _ensures((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
{
  size_t start = (size_t)key % size;
  return hash_insert_probe(table, size, key, start, 0);
}

/*
 * Delete a key from the hash table.
 * Returns true if the key was found and deleted (marked -2),
 * false if the key was not found.
 */
bool hash_delete(_array int *table, size_t size, int key)
  _requires(table._length == size)
  _requires(size > 0)
  _requires(key >= 0)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(key))))
  _requires((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
  _ensures(table._length == size)
  _ensures(return ==> _exists(size_t j, j < size && _old(table[j]) == key && table[j] == -2))
  _ensures(return == false ==> _forall(size_t k, k < size ==> table[k] == _old(table[k])))
  _ensures((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
{
  size_t idx = hash_search(table, size, key);
  if (idx < size) {
    table[idx] = -2;
    return true;
  }
  return false;
}

/*
 * Insert a key only if not already present (prevents duplicates).
 * Returns true if the key is in the table after the call
 * (either already present or freshly inserted),
 * false if the table is full and the key was not present.
 */
bool hash_insert_no_dup(_array int *table, size_t size, int key)
  _requires(table._length == size)
  _requires(size > 0)
  _requires(key >= 0)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(key))))
  _requires((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
  _ensures(table._length == size)
  _ensures(return ==> _exists(size_t k, k < size && table[k] == key))
  _ensures(return == false ==> _forall(size_t k, k < size ==> table[k] == _old(table[k])))
  _ensures((bool) _inline_pulse(c_valid_ht (array_value_of $(table)) (SizeT.v $(size))))
{
  size_t search_result = hash_search(table, size, key);
  if (search_result < size) {
    return true;
  }
  return hash_insert(table, size, key);
}
