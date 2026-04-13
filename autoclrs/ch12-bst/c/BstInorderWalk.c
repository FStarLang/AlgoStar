/*
 * BST Inorder Walk — Recursive C implementation with c2pulse verification.
 *
 * Array-based BST: node i has left child at 2*i+1, right child at 2*i+2.
 * Keys stored in keys[], occupancy in valid[] (0 = empty, nonzero = occupied).
 *
 * Writes the keys of the subtree rooted at index i, in sorted (inorder) order,
 * into the output[] array starting at position *write_pos.
 *
 * Proves:
 *   1. The BST arrays (keys, valid) are unmodified (read-only).
 *   2. write_pos stays within [0, out_len].
 *
 * CLRS Reference: §12.1 INORDER-TREE-WALK (recursive)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open CLRS.Ch12.BST.C.BridgeLemmas)

/*
 * Recursive inorder walk helper.
 *
 * Starting at node i:
 *   1. Recurse on left child (2*i+1)
 *   2. Write keys[i] to output[*write_pos], increment *write_pos
 *   3. Recurse on right child (2*i+2)
 *
 * If i >= cap or valid[i] == 0, the node is absent — do nothing.
 * If *write_pos >= out_len, skip the write (output full) but still recurse.
 */
_rec void bst_inorder_walk(_array int *keys, _array int *valid,
                           size_t cap, size_t i,
                           _array int *output, size_t *write_pos, size_t out_len)
  _requires(keys._length == cap && valid._length == cap)
  _requires(output._length == out_len)
  _requires(cap > 0 && cap < 32768)
  _requires(i <= 2 * cap)
  _requires(*write_pos <= out_len)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  _preserves_value(output._length)
  /* BST arrays are unmodified (read-only) */
  _ensures(_forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(_forall(size_t j, j < cap ==> valid[j] == _old(valid[j])))
  /* write_pos stays in bounds */
  _ensures(*write_pos <= out_len)
  _decreases(2 * cap - i)
{
  if (i >= cap) {
    return;
  }
  if (valid[i] == 0) {
    return;
  }

  /* Recurse on left subtree: left = 2*i+1 <= 2*(cap-1)+1 = 2*cap-1 <= 2*cap */
  size_t left = 2 * i + 1;
  bst_inorder_walk(keys, valid, cap, left, output, write_pos, out_len);

  /* Write current key */
  size_t wp = *write_pos;
  if (wp < out_len) {
    output[wp] = keys[i];
    *write_pos = wp + 1;
  }

  /* Recurse on right subtree: right = 2*i+2 <= 2*(cap-1)+2 = 2*cap */
  size_t right = 2 * i + 2;
  bst_inorder_walk(keys, valid, cap, right, output, write_pos, out_len);
}
