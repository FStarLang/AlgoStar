/*
 * Red-Black Tree Insert — C implementation with c2pulse verification.
 *
 * Uses an array-based tree representation where nodes are stored in
 * a flat array and children are referenced by index.
 * A child index >= cap means nil/leaf (no child).
 *
 * Proves:
 *   1. Memory safety (all array accesses in bounds).
 *   2. Well-formedness: all child indices remain <= new cap.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

typedef struct {
  int32_t key;
  int32_t color;
  size_t left;
  size_t right;
} rb_node;

/*
 * BST insert: adds key k to the tree if not already present.
 * Modifies cap and root through pointers.
 *
 * - cap is incremented by 1 on successful insert (new node at old cap).
 * - root is updated if the tree was empty.
 * - On duplicate key or full array, cap and root are unchanged.
 * - New node is colored red (color = 0).
 * - The well-formedness invariant is preserved.
 */
void rb_insert(_array rb_node *nodes, size_t max_cap, size_t *p_cap, size_t *p_root, int32_t k)
  _preserves(nodes._length == max_cap)
  _preserves(max_cap > 0)
  _requires(*p_cap <= max_cap)
  _requires(*p_root <= *p_cap)
  _requires(_forall(size_t i, i < *p_cap ==>
    nodes[i].left  <= *p_cap &&
    nodes[i].right <= *p_cap))
  _ensures(*p_cap <= max_cap)
  _ensures(*p_root <= *p_cap)
  _ensures(_forall(size_t i, i < *p_cap ==>
    nodes[i].left  <= *p_cap &&
    nodes[i].right <= *p_cap))
  /* Capacity grows by at most 1 */
  _ensures((_specint) *p_cap >= (_specint) _old(*p_cap))
  _ensures((_specint) *p_cap <= (_specint) _old(*p_cap) + 1)
{
  size_t cap = *p_cap;
  size_t root = *p_root;

  /* Phase 1: BST traversal to find insertion point */
  size_t parent = cap;
  size_t curr = root;
  bool go_left = false;

  while (curr < cap)
    _invariant(_live(curr))
    _invariant(_live(parent))
    _invariant(_live(go_left))
    _invariant(_live(*nodes))
    _invariant(_live(*p_cap))
    _invariant(_live(*p_root))
    _invariant(nodes._length == max_cap)
    _invariant(max_cap > 0)
    _invariant(cap <= max_cap)
    _invariant(root <= cap)
    _invariant(curr <= cap)
    _invariant(parent <= cap)
    _invariant(*p_cap == cap)
    _invariant(*p_root == root)
    _invariant(_forall(size_t i, i < cap ==>
      nodes[i].left  <= cap &&
      nodes[i].right <= cap))
  {
    parent = curr;
    int32_t node_key = nodes[curr].key;
    if (k < node_key) {
      go_left = true;
      curr = nodes[curr].left;
    } else if (k > node_key) {
      go_left = false;
      curr = nodes[curr].right;
    } else {
      return;
    }
  }

  /* Check capacity */
  if (cap >= max_cap) return;

  /* Phase 2: Insert new node at index cap */
  size_t new_cap = cap + 1;
  nodes[cap] = (rb_node) {.key = k, .color = 0, .left = new_cap, .right = new_cap};

  /* Phase 3: Link parent to new node */
  if (parent < cap) {
    /* Update parent's child pointer */
    rb_node p_nd = nodes[parent];
    if (go_left) {
      nodes[parent] = (rb_node) {.key = p_nd.key, .color = p_nd.color,
                                  .left = cap, .right = p_nd.right};
    } else {
      nodes[parent] = (rb_node) {.key = p_nd.key, .color = p_nd.color,
                                  .left = p_nd.left, .right = cap};
    }
    *p_cap = new_cap;
    *p_root = root;
  } else {
    /* Tree was empty — new node becomes root */
    *p_cap = new_cap;
    *p_root = cap;
  }
}
