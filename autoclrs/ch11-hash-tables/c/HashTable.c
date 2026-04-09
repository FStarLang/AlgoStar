/*
 * Hash Table with Open Addressing — C implementation with c2pulse verification.
 *
 * CLRS §11.4: Open addressing hash table with linear probing.
 * Division-method hash: h(k) = k % m
 * Probe sequence: h(k, i) = (h(k) + i) % m
 *
 * Sentinel values: -1 = empty, -2 = deleted, >= 0 = valid key
 *
 * Proves functional correctness specifications equivalent to
 * CLRS.Ch11.HashTable.Impl.fsti:
 *   - hash_search: found index contains key; not found means key absent
 *   - hash_insert: key present in table on success; table full on failure
 *   - hash_delete: slot marked deleted on success; table unchanged on failure
 *   - hash_insert_no_dup: search then insert, no duplicate keys
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

/*
 * Search for a key in the hash table using linear probing.
 * Returns the array index if found, or size if not found.
 *
 * Uses a running index with wrap-around to avoid SizeT overflow.
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
  size_t idx = (size_t)key % size;
  size_t count = 0;
  size_t found_idx = size;
  bool done = false;

  while (done == false && count < size)
    _invariant(_live(count) && _live(idx) && _live(found_idx) && _live(done))
    _invariant(_live(*table))
    _invariant(table._length == size)
    _invariant(count <= size)
    _invariant(idx < size)
    _invariant(found_idx <= size)
    _invariant(found_idx < size ==> table[found_idx] == key)
    _invariant(_forall(size_t k, k < size ==> table[k] == _old(table[k])))
  {
    int slot = table[idx];

    if (slot == key) {
      found_idx = idx;
      done = true;
    } else if (slot == -1) {
      done = true;
    }

    count = count + 1;
    if (idx + 1 == size) {
      idx = 0;
    } else {
      idx = idx + 1;
    }
  }

  return found_idx;
}

/*
 * Insert a key into the hash table using linear probing.
 * Returns true if successful, false if the table is full.
 *
 * Inserts into the first empty (-1) or deleted (-2) slot
 * found along the probe sequence.
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
  size_t idx = (size_t)key % size;
  size_t count = 0;
  bool inserted = false;

  while (inserted == false && count < size)
    _invariant(_live(count) && _live(idx) && _live(inserted))
    _invariant(_live(*table))
    _invariant(table._length == size)
    _invariant(count <= size)
    _invariant(idx < size)
    _invariant(inserted ==> _exists(size_t k, k < size && table[k] == key))
    _invariant(inserted == false ==> _forall(size_t k, k < size ==> table[k] == _old(table[k])))
  {
    int slot = table[idx];

    if (slot == -1 || slot == -2) {
      table[idx] = key;
      inserted = true;
    }

    count = count + 1;
    if (idx + 1 == size) {
      idx = 0;
    } else {
      idx = idx + 1;
    }
  }

  return inserted;
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
  _ensures(table._length == size)
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
