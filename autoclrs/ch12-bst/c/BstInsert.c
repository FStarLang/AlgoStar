/*
 * BST Insert — Recursive C implementation with c2pulse verification.
 *
 * Array-based BST: node i has left child at 2*i+1, right child at 2*i+2.
 * Keys stored in keys[], occupancy in valid[] (0 = empty, 1 = occupied).
 *
 * Proves: if insert returns an index < cap, then keys[result] == key
 *         and valid[result] != 0 (key was placed correctly).
 *
 * CLRS Reference: §12.3 TREE-INSERT (recursive)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Recursive BST insert.
 *
 * Starting at node i, if the slot is empty we insert; if the key
 * matches we return; otherwise we recurse into the appropriate child.
 *
 * Returns the index where the key was placed (or already existed),
 * or cap if the tree is full (no empty slot on the search path).
 */
_rec size_t bst_insert(_array int *keys, _array int *valid, size_t cap, int key, size_t i)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(i <= cap)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  _ensures(return <= cap)
  _ensures(return < cap ==> keys[return] == key && valid[return] != 0)
  /* Frame: only position return may have changed */
  _ensures(_forall(size_t j, j < cap && j != return ==> keys[j] == _old(keys[j])))
  _ensures(_forall(size_t j, j < cap && j != return ==> valid[j] == _old(valid[j])))
  _decreases(cap - i)
{
  if (i >= cap) {
    return cap;
  }
  if (valid[i] == 0) {
    keys[i] = key;
    valid[i] = 1;
    return i;
  }
  if (keys[i] == key) {
    return i;
  }
  if (key < keys[i]) {
    size_t left = 2 * i + 1;
    if (left >= cap) {
      return cap;
    }
    return bst_insert(keys, valid, cap, key, left);
  } else {
    size_t right = 2 * i + 2;
    if (right >= cap) {
      return cap;
    }
    return bst_insert(keys, valid, cap, key, right);
  }
}
