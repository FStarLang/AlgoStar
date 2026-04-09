/*
 * BST Insert — C implementation with c2pulse verification.
 *
 * Array-based BST: node i has left child at 2*i+1, right child at 2*i+2.
 * Keys stored in keys[], occupancy in valid[] (0 = empty, 1 = occupied).
 *
 * Proves: if insert returns an index < cap, then keys[result] == key
 *         and valid[result] != 0 (key was placed correctly).
 *
 * CLRS Reference: §12.3 TREE-INSERT (iterative variant)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Iterative BST insert.
 *
 * Walks down from the root (index 0).  At each node, if the slot is
 * empty we insert; if the key matches we return; otherwise we descend
 * left or right.
 *
 * Returns the index where the key was placed (or already existed),
 * or cap if the tree is full (no empty slot on the search path).
 */
size_t bst_insert(_array int *keys, _array int *valid, size_t cap, int key)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  _ensures(return <= cap)
  _ensures(return < cap ==> keys[return] == key && valid[return] != 0)
{
  size_t i = 0;
  size_t result = cap;

  while (i < cap && result == cap)
    _invariant(_live(i) && _live(result))
    _invariant(_live(*keys) && _live(*valid))
    _invariant(keys._length == cap && valid._length == cap)
    _invariant(i <= cap && result <= cap)
    _invariant(cap > 0 && cap < 32768)
    _invariant(result < cap ==> keys[result] == key && valid[result] != 0)
  {
    if (valid[i] == 0) {
      keys[i] = key;
      valid[i] = 1;
      result = i;
    } else if (keys[i] == key) {
      result = i;
    } else if (key < keys[i]) {
      size_t left = 2 * i + 1;
      if (left >= cap) {
        i = cap;
      } else {
        i = left;
      }
    } else {
      size_t right = 2 * i + 2;
      if (right >= cap) {
        i = cap;
      } else {
        i = right;
      }
    }
  }

  return result;
}
