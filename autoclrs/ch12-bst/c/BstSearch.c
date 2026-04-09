/*
 * BST Search — Recursive C implementation with c2pulse verification.
 *
 * Array-based BST: node i has left child at 2*i+1, right child at 2*i+2.
 * Keys stored in keys[], occupancy in valid[] (0 = empty, nonzero = occupied).
 *
 * Proves:
 *   1. If search returns an index < cap, then keys[result] == key
 *      and valid[result] is nonzero (search soundness).
 *   2. The arrays are unmodified (read-only operation).
 *
 * CLRS Reference: §12.2 TREE-SEARCH (recursive)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Recursive BST search.
 *
 * Starting at node i, compares keys and recurses into
 * left (2*i+1) or right (2*i+2) children.
 *
 * Returns the index of the node containing key, or cap if not found.
 */
_rec size_t bst_search(_array int *keys, _array int *valid, size_t cap, int key, size_t i)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(i <= cap)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  _ensures(return <= cap)
  _ensures(return < cap ==> keys[return] == key && valid[return] != 0)
  /* Frame: arrays are unmodified (read-only operation) */
  _ensures(_forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(_forall(size_t j, j < cap ==> valid[j] == _old(valid[j])))
  _decreases(cap - i)
{
  if (i >= cap) {
    return cap;
  }
  if (valid[i] == 0) {
    return cap;
  }
  if (keys[i] == key) {
    return i;
  }
  if (key < keys[i]) {
    size_t left = 2 * i + 1;
    if (left >= cap) {
      return cap;
    }
    return bst_search(keys, valid, cap, key, left);
  } else {
    size_t right = 2 * i + 2;
    if (right >= cap) {
      return cap;
    }
    return bst_search(keys, valid, cap, key, right);
  }
}
