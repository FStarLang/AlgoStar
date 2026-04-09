/*
 * BST Search — C implementation with c2pulse verification.
 *
 * Array-based BST: node i has left child at 2*i+1, right child at 2*i+2.
 * Keys stored in keys[], occupancy in valid[] (0 = empty, nonzero = occupied).
 *
 * Proves:
 *   1. If search returns an index < cap, then keys[result] == key
 *      and valid[result] is nonzero (search soundness).
 *   2. The arrays are unmodified (read-only operation).
 *
 * CLRS Reference: §12.2 TREE-SEARCH (iterative variant)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Iterative BST search.
 *
 * Walks down from the root (index 0), comparing keys and following
 * left (2*i+1) or right (2*i+2) children.
 *
 * Returns the index of the node containing key, or cap if not found.
 */
size_t bst_search(_array int *keys, _array int *valid, size_t cap, int key)
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
      i = cap;
    } else if (keys[i] == key) {
      result = i;
    } else if (key < keys[i]) {
      size_t next = 2 * i + 1;
      if (next >= cap) {
        i = cap;
      } else {
        i = next;
      }
    } else {
      size_t next = 2 * i + 2;
      if (next >= cap) {
        i = cap;
      } else {
        i = next;
      }
    }
  }

  return result;
}
