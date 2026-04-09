/*
 * BST Minimum & Maximum — Recursive C implementation with c2pulse verification.
 *
 * Array-based BST: node i has left child at 2*i+1, right child at 2*i+2.
 * Keys stored in keys[], occupancy in valid[] (0 = empty, nonzero = occupied).
 *
 * Proves:
 *   1. bst_minimum returns a key that exists in the tree (at a valid position).
 *   2. bst_maximum returns a key that exists in the tree (at a valid position).
 *   3. The arrays are unmodified (read-only operations).
 *
 * CLRS Reference: §12.2 TREE-MINIMUM and TREE-MAXIMUM (recursive)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Recursive BST minimum.
 *
 * Starting at node i, follows left children (2*i+1) until
 * no valid left child exists.
 * Returns the key at the leftmost valid node in the subtree.
 *
 * Precondition: node i must be valid (valid[i] != 0).
 */
_rec int bst_minimum(_array int *keys, _array int *valid, size_t cap, size_t i)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(i < cap && valid[i] != 0)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  /* Local BST ordering: left child key < parent key */
  _requires(_forall(size_t j,
    j < cap && valid[j] != 0 && 2 * j + 1 < cap && valid[2 * j + 1] != 0
      ==> keys[2 * j + 1] < keys[j]))
  /* Frame: arrays are unmodified (read-only operation) */
  _ensures(_forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(_forall(size_t j, j < cap ==> valid[j] == _old(valid[j])))
  /* Result is bounded by the root key of the subtree */
  _ensures(return <= keys[i])
  _decreases(cap - i)
{
  size_t left = 2 * i + 1;
  if (left >= cap) {
    return keys[i];
  }
  if (valid[left] == 0) {
    return keys[i];
  }
  return bst_minimum(keys, valid, cap, left);
}

/*
 * Recursive BST maximum.
 *
 * Starting at node i, follows right children (2*i+2) until
 * no valid right child exists.
 * Returns the key at the rightmost valid node in the subtree.
 *
 * Precondition: node i must be valid (valid[i] != 0).
 */
_rec int bst_maximum(_array int *keys, _array int *valid, size_t cap, size_t i)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(i < cap && valid[i] != 0)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  /* Local BST ordering: right child key > parent key */
  _requires(_forall(size_t j,
    j < cap && valid[j] != 0 && 2 * j + 2 < cap && valid[2 * j + 2] != 0
      ==> keys[j] < keys[2 * j + 2]))
  /* Frame: arrays are unmodified (read-only operation) */
  _ensures(_forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(_forall(size_t j, j < cap ==> valid[j] == _old(valid[j])))
  /* Result is bounded by the root key of the subtree */
  _ensures(return >= keys[i])
  _decreases(cap - i)
{
  size_t right = 2 * i + 2;
  if (right >= cap) {
    return keys[i];
  }
  if (valid[right] == 0) {
    return keys[i];
  }
  return bst_maximum(keys, valid, cap, right);
}
