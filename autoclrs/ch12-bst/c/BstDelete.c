/*
 * BST Delete — C implementation with c2pulse verification.
 *
 * Array-based BST: node i has left child at 2*i+1, right child at 2*i+2.
 * Keys stored in keys[], occupancy in valid[] (0 = empty, nonzero = occupied).
 *
 * Algorithm (CLRS §12.3 TREE-DELETE, adapted for array representation):
 *   Case 1: Leaf node (no valid children) — mark invalid.
 *   Case 2: Node has right child — find successor (min of right subtree),
 *           swap keys, mark successor invalid (since successor is a leaf
 *           or has only a right child; we handle the leaf case).
 *   Case 3: Node has only left child — return 0 (unsupported, same as Pulse).
 *
 * Proves:
 *   1. Array lengths are preserved.
 *   2. If returns 0, arrays are unchanged.
 *   3. BST validity is a precondition (c_valid_bst from BridgeLemmas).
 *
 * CLRS Reference: §12.3 TREE-DELETE
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open CLRS.Ch12.BST.C.BridgeLemmas)

/* bst_minimum_idx: find index of minimum node in subtree (from BstSuccessor.c) */
_rec size_t bst_minimum_idx(_array int *keys, _array int *valid, size_t cap, size_t i)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(i < cap && valid[i] != 0)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  _ensures(_forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(_forall(size_t j, j < cap ==> valid[j] == _old(valid[j])))
  _ensures(return < cap && valid[return] != 0)
  _decreases(cap - i);

/*
 * Tree delete.
 *
 * Deletes the node at index del_idx from the BST.
 * Returns 1 on success, 0 if the deletion cannot be performed
 * (e.g., node has only a left child, or successor has a right child).
 */
int bst_delete(_array int *keys, _array int *valid, size_t cap, size_t del_idx)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(del_idx < cap && valid[del_idx] != 0)
  /* BST validity precondition */
  _requires((bool) _inline_pulse(c_valid_bst (array_value_of $(keys)) (array_value_of $(valid)) (SizeT.v $(cap))))
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  /* If failure (return == 0), arrays are unchanged */
  _ensures(return == 0 ==> _forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(return == 0 ==> _forall(size_t j, j < cap ==> valid[j] == _old(valid[j])))
{
  size_t left = 2 * del_idx + 1;
  size_t right = 2 * del_idx + 2;

  /* Check if children exist and are valid */
  int has_left = 0;
  if (left < cap) {
    if (valid[left] != 0) {
      has_left = 1;
    }
  }

  int has_right = 0;
  if (right < cap) {
    if (valid[right] != 0) {
      has_right = 1;
    }
  }

  /* Case 1: Leaf node — just mark invalid */
  if (has_left == 0) {
    if (has_right == 0) {
      valid[del_idx] = 0;
      return 1;
    }
  }

  /* Case 3: Only left child — unsupported (same as Pulse impl) */
  if (has_right == 0) {
    return 0;
  }

  /* Case 2: Has right child — use successor key-swap approach */
  size_t succ_idx = bst_minimum_idx(keys, valid, cap, right);

  /* Check if successor is a leaf (no valid right child) */
  size_t succ_right = 2 * succ_idx + 2;
  int succ_has_right = 0;
  if (succ_right < cap) {
    if (valid[succ_right] != 0) {
      succ_has_right = 1;
    }
  }

  if (succ_has_right != 0) {
    /* Successor has a right child: cannot handle without full transplant */
    return 0;
  }

  /* Successor is a leaf: swap key and delete successor */
  int succ_key = keys[succ_idx];
  keys[del_idx] = succ_key;
  valid[succ_idx] = 0;
  return 1;
}
