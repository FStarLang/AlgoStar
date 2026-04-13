/*
 * BST Predecessor — Recursive C implementation with c2pulse verification.
 *
 * Array-based BST: node i has left child at 2*i+1, right child at 2*i+2.
 * Parent of i (for i > 0) is (i-1)/2.
 * i is a left child  iff i > 0 and i % 2 == 1.
 * i is a right child iff i > 0 and i % 2 == 0.
 *
 * Algorithm (CLRS §12.2 TREE-PREDECESSOR, symmetric to TREE-SUCCESSOR):
 *   Case 1: If left child exists and is valid, return TREE-MAXIMUM(left child).
 *   Case 2: Walk up while current is a left child. If we find a right child,
 *           its parent is the predecessor. If we reach root, no predecessor.
 *
 * Returns the index of the predecessor, or cap if no predecessor exists.
 *
 * Proves:
 *   1. If result < cap, then valid[result] != 0 (result is a valid node).
 *   2. The arrays are unmodified (read-only).
 *
 * CLRS Reference: §12.2 TREE-PREDECESSOR
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open CLRS.Ch12.BST.C.BridgeLemmas)

/*
 * Find the index of the maximum-key node in the subtree rooted at i.
 * Walks right children until no valid right child exists.
 */
_rec size_t bst_maximum_idx(_array int *keys, _array int *valid, size_t cap, size_t i)
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
  size_t right = 2 * i + 2;
  if (right >= cap) {
    return i;
  }
  if (valid[right] == 0) {
    return i;
  }
  return bst_maximum_idx(keys, valid, cap, right);
}

/*
 * Walk up the tree from node i while i is a left child (odd index > 0).
 * Returns the parent of the first right-child ancestor, or cap if none.
 */
_rec size_t walk_up_left(_array int *keys, _array int *valid, size_t cap, size_t i)
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
  /* If at root or if i is a right child (even > 0), stop */
  if (i == 0) {
    /* Reached root while going up through left children — no predecessor */
    return cap;
  }
  /* Compute parent here, before branching */
  size_t parent = (i - 1) / 2;
  if (i % 2 == 0) {
    /* i is a right child — its parent is the predecessor */
    if (parent < cap) {
      if (valid[parent] != 0) {
        return parent;
      }
    }
    return cap;
  }
  /* i is a left child (odd) — move to parent and continue */
  return walk_up_left(keys, valid, cap, parent);
}

/*
 * Tree predecessor.
 *
 * Returns the index of the in-order predecessor of node idx,
 * or cap if there is no predecessor.
 */
size_t bst_predecessor(_array int *keys, _array int *valid, size_t cap, size_t idx)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(idx < cap && valid[idx] != 0)
  _requires((bool) _inline_pulse(c_valid_bst (array_value_of $(keys)) (array_value_of $(valid)) (SizeT.v $(cap))))
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  /* Frame: arrays unmodified */
  _ensures(_forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(_forall(size_t j, j < cap ==> valid[j] == _old(valid[j])))
  /* Result bounds */
  _ensures(return <= cap)
  _ensures(return < cap ==> valid[return] != 0)
{
  /* Case 1: If left child exists and is valid, return maximum of left subtree */
  size_t left = 2 * idx + 1;
  if (left < cap) {
    if (valid[left] != 0) {
      return bst_maximum_idx(keys, valid, cap, left);
    }
  }

  /* Case 2: Walk up to find predecessor */
  return walk_up_left(keys, valid, cap, idx);
}
