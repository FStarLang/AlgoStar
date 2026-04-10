/*
 * BST Successor — Recursive C implementation with c2pulse verification.
 *
 * Array-based BST: node i has left child at 2*i+1, right child at 2*i+2.
 * Parent of i (for i > 0) is (i-1)/2.
 * i is a right child iff i > 0 and i % 2 == 0.
 * i is a left child  iff i > 0 and i % 2 == 1.
 *
 * Algorithm (CLRS §12.2 TREE-SUCCESSOR):
 *   Case 1: If right child exists and is valid, return TREE-MINIMUM(right child).
 *   Case 2: Walk up while current is a right child. If we find a left child,
 *           its parent is the successor. If we reach root, no successor.
 *
 * Returns the index of the successor, or cap if no successor exists.
 *
 * Proves:
 *   1. If result < cap, then valid[result] != 0 (result is a valid node).
 *   2. The arrays are unmodified (read-only).
 *
 * CLRS Reference: §12.2 TREE-SUCCESSOR
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Find the index of the minimum-key node in the subtree rooted at i.
 * (Helper for successor — returns the index, not the key.)
 *
 * Walks left children until no valid left child exists.
 */
_rec size_t bst_minimum_idx(_array int *keys, _array int *valid, size_t cap, size_t i)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(i < cap && valid[i] != 0)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  /* Frame: arrays unmodified */
  _ensures(_forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(_forall(size_t j, j < cap ==> valid[j] == _old(valid[j])))
  /* Result is a valid node within bounds */
  _ensures(return < cap && valid[return] != 0)
  _decreases(cap - i)
{
  size_t left = 2 * i + 1;
  if (left >= cap) {
    return i;
  }
  if (valid[left] == 0) {
    return i;
  }
  return bst_minimum_idx(keys, valid, cap, left);
}

/*
 * Walk up the tree from node i while i is a right child (even index > 0).
 * Returns the first ancestor that is a left child, or 0 if we reach the root.
 */
_rec size_t walk_up_right(_array int *keys, _array int *valid, size_t cap, size_t i)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(i < cap)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  _ensures(_forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(_forall(size_t j, j < cap ==> valid[j] == _old(valid[j])))
  _ensures(return <= cap)
  _ensures(return < cap ==> valid[return] != 0)
  _decreases(i)
{
  /* If at root or if i is a left child (odd), stop */
  if (i == 0) {
    /* Reached root while going up through right children — no successor */
    return cap;
  }
  /* Compute parent here, before branching */
  size_t parent = (i - 1) / 2;
  if (i % 2 == 1) {
    /* i is a left child — its parent is the successor */
    if (parent < cap) {
      if (valid[parent] != 0) {
        return parent;
      }
    }
    return cap;
  }
  /* i is a right child (even, > 0) — move to parent and continue */
  return walk_up_right(keys, valid, cap, parent);
}

/*
 * Tree successor.
 *
 * Returns the index of the in-order successor of node idx,
 * or cap if there is no successor.
 */
size_t bst_successor(_array int *keys, _array int *valid, size_t cap, size_t idx)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(idx < cap && valid[idx] != 0)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  /* Frame: arrays unmodified */
  _ensures(_forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(_forall(size_t j, j < cap ==> valid[j] == _old(valid[j])))
  /* Result bounds */
  _ensures(return <= cap)
  _ensures(return < cap ==> valid[return] != 0)
{
  /* Case 1: If right child exists and is valid, return minimum of right subtree */
  size_t right = 2 * idx + 2;
  if (right < cap) {
    if (valid[right] != 0) {
      return bst_minimum_idx(keys, valid, cap, right);
    }
  }

  /* Case 2: Walk up to find successor */
  return walk_up_right(keys, valid, cap, idx);
}
