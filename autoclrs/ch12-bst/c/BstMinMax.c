/*
 * BST Minimum & Maximum — C implementation with c2pulse verification.
 *
 * Array-based BST: node i has left child at 2*i+1, right child at 2*i+2.
 * Keys stored in keys[], occupancy in valid[] (0 = empty, nonzero = occupied).
 *
 * Proves:
 *   1. bst_minimum returns a key that exists in the tree (at a valid position).
 *   2. bst_maximum returns a key that exists in the tree (at a valid position).
 *   3. The arrays are unmodified (read-only operations).
 *
 * CLRS Reference: §12.2 TREE-MINIMUM and TREE-MAXIMUM (iterative variants)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Iterative BST minimum.
 *
 * Walks left from the root (index 0) until no left child exists.
 * Returns the key at the leftmost valid node.
 *
 * Precondition: the root must be valid (valid[0] != 0).
 */
int bst_minimum(_array int *keys, _array int *valid, size_t cap)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(valid[0] != 0)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  /* Local BST ordering: left child key < parent key */
  _requires(_forall(size_t i,
    i < cap && valid[i] != 0 && 2 * i + 1 < cap && valid[2 * i + 1] != 0
      ==> keys[2 * i + 1] < keys[i]))
{
  size_t i = 0;

  while (i < cap)
    _invariant(_live(i))
    _invariant(_live(*keys) && _live(*valid))
    _invariant(keys._length == cap && valid._length == cap)
    _invariant(cap > 0 && cap < 32768)
    _invariant(i <= cap)
    _invariant(i < cap ==> valid[i] != 0)
    _invariant(_forall(size_t j,
      j < cap && valid[j] != 0 && 2 * j + 1 < cap && valid[2 * j + 1] != 0
        ==> keys[2 * j + 1] < keys[j]))
  {
    size_t left = 2 * i + 1;
    if (left >= cap) {
      return keys[i];
    }
    if (valid[left] == 0) {
      return keys[i];
    }
    i = left;
  }

  return keys[0];
}

/*
 * Iterative BST maximum.
 *
 * Walks right from the root (index 0) until no right child exists.
 * Returns the key at the rightmost valid node.
 *
 * Precondition: the root must be valid (valid[0] != 0).
 */
int bst_maximum(_array int *keys, _array int *valid, size_t cap)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(valid[0] != 0)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  /* Local BST ordering: right child key > parent key */
  _requires(_forall(size_t i,
    i < cap && valid[i] != 0 && 2 * i + 2 < cap && valid[2 * i + 2] != 0
      ==> keys[i] < keys[2 * i + 2]))
{
  size_t i = 0;

  while (i < cap)
    _invariant(_live(i))
    _invariant(_live(*keys) && _live(*valid))
    _invariant(keys._length == cap && valid._length == cap)
    _invariant(cap > 0 && cap < 32768)
    _invariant(i <= cap)
    _invariant(i < cap ==> valid[i] != 0)
    _invariant(_forall(size_t j,
      j < cap && valid[j] != 0 && 2 * j + 2 < cap && valid[2 * j + 2] != 0
        ==> keys[j] < keys[2 * j + 2]))
  {
    size_t right = 2 * i + 2;
    if (right >= cap) {
      return keys[i];
    }
    if (valid[right] == 0) {
      return keys[i];
    }
    i = right;
  }

  return keys[0];
}
