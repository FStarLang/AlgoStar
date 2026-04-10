/*
 * BST Delete by Key — C implementation with c2pulse verification.
 *
 * Combines BST search with BST delete:
 *   1. Search for the key in the array-based BST.
 *   2. If found, delete the node at that index using bst_delete.
 *   3. Return 1 on success, 0 if not found or deletion failed.
 *
 * CLRS Reference: §12.2 TREE-SEARCH + §12.3 TREE-DELETE
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/* Forward declaration: bst_search from BstSearch.c */
_rec size_t bst_search(_array int *keys, _array int *valid, size_t cap, int key, size_t i)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(i <= cap)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  _ensures(return <= cap)
  _ensures(return < cap ==> keys[return] == key && valid[return] != 0)
  _ensures(_forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(_forall(size_t j, j < cap ==> valid[j] == _old(valid[j])))
  _decreases(cap - i);

/* Forward declaration: bst_delete from BstDelete.c */
int bst_delete(_array int *keys, _array int *valid, size_t cap, size_t del_idx)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _requires(del_idx < cap && valid[del_idx] != 0)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
  _ensures(return == 0 ==> _forall(size_t j, j < cap ==> keys[j] == _old(keys[j])))
  _ensures(return == 0 ==> _forall(size_t j, j < cap ==> valid[j] == _old(valid[j])));

/*
 * Delete a key from the BST.
 *
 * Searches for the key starting at root (index 0), then deletes it
 * if found. Returns 1 on successful deletion, 0 otherwise.
 */
int bst_delete_key(_array int *keys, _array int *valid, size_t cap, int key)
  _requires(keys._length == cap && valid._length == cap)
  _requires(cap > 0 && cap < 32768)
  _preserves_value(keys._length)
  _preserves_value(valid._length)
{
  size_t idx = bst_search(keys, valid, cap, key, 0);
  if (idx >= cap) {
    /* Key not found */
    return 0;
  }
  /* Key found at idx — delete it */
  return bst_delete(keys, valid, cap, idx);
}
