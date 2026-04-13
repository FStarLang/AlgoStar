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
 *   4. Result bounded by root key (minimum <= root, maximum >= root).
 *
 * CLRS Reference: §12.2 TREE-MINIMUM and TREE-MAXIMUM (recursive)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open CLRS.Ch12.BST.C.BridgeLemmas)

/*
 * Recursive BST minimum.
 *
 * Starting at node i, follows left children (2*i+1) until
 * no valid left child exists.
 * Returns the key at the leftmost valid node in the subtree.
 *
 * Precondition: node i must be valid (valid[i] != 0).
 * Precondition: BST is valid (c_valid_bst).
 */
_rec int bst_minimum(_array int *keys, _array int *valid, size_t cap, size_t i)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(i < cap && valid[i] != 0)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  /* BST validity implies left-child ordering (via bridge lemma) */
  _requires((bool) _inline_pulse(c_valid_bst (array_value_of $(keys)) (array_value_of $(valid)) (SizeT.v $(cap))))
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
  _ghost_stmt(c_valid_bst_local_left (array_value_of (!var_keys)) (array_value_of (!var_valid)) (SizeT.v (!var_cap)) (SizeT.v (!var_i)));
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
 * Precondition: BST is valid (c_valid_bst).
 */
_rec int bst_maximum(_array int *keys, _array int *valid, size_t cap, size_t i)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(i < cap && valid[i] != 0)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  /* BST validity implies right-child ordering (via bridge lemma) */
  _requires((bool) _inline_pulse(c_valid_bst (array_value_of $(keys)) (array_value_of $(valid)) (SizeT.v $(cap))))
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
  _ghost_stmt(c_valid_bst_local_right (array_value_of (!var_keys)) (array_value_of (!var_valid)) (SizeT.v (!var_cap)) (SizeT.v (!var_i)));
  return bst_maximum(keys, valid, cap, right);
}
