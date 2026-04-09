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
 * Specifications aim for parity with CLRS.Ch11.HashTable.Impl.fsti:
 *   - hash_search: found index contains key; not found means key absent
 *   - hash_insert: key present in table on success; table full on failure
 *   - hash_delete: specific slot changed from key to -2 on success
 *   - hash_insert_no_dup: search then insert, no duplicate keys
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

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
  _requires(idx < size)
  _preserves_value(table._length)
  _ensures(return <= size)
  _ensures(return < size ==> table[return] == key)
  _ensures(_forall(size_t k, k < size ==> table[k] == _old(table[k])))
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
  _ensures(table._length == size)
  _ensures(return <= size)
  _ensures(return < size ==> table[return] == key)
  _ensures(_forall(size_t k, k < size ==> table[k] == _old(table[k])))
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
  _requires(idx < size)
  _preserves_value(table._length)
  _ensures(return ==> _exists(size_t k, k < size && table[k] == key))
  _ensures(return == false ==> _forall(size_t k, k < size ==> table[k] == _old(table[k])))
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
  _ensures(table._length == size)
  _ensures(return ==> _exists(size_t k, k < size && table[k] == key))
  _ensures(return == false ==> _forall(size_t k, k < size ==> table[k] == _old(table[k])))
{
  size_t start = (size_t)key % size;
  return hash_insert_probe(table, size, key, start, 0);
}

/*
 * Delete a key from the hash table.
 * Returns true if the key was found and deleted (marked -2),
 * false if the key was not found.
 *
 * On success: exactly one slot changed from key to -2, all others unchanged.
 * On failure: table completely unchanged.
 */
bool hash_delete(_array int *table, size_t size, int key)
  _requires(table._length == size)
  _requires(size > 0)
  _requires(key >= 0)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(key))))
  _ensures(table._length == size)
  _ensures(return ==> _exists(size_t j, j < size && _old(table[j]) == key && table[j] == -2))
  _ensures(return == false ==> _forall(size_t k, k < size ==> table[k] == _old(table[k])))
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
  _ensures(table._length == size)
  _ensures(return ==> _exists(size_t k, k < size && table[k] == key))
  _ensures(return == false ==> _forall(size_t k, k < size ==> table[k] == _old(table[k])))
{
  size_t search_result = hash_search(table, size, key);
  if (search_result < size) {
    return true;
  }
  return hash_insert(table, size, key);
}
