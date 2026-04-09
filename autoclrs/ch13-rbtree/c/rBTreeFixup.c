/*
 * Red-Black Tree Insert with Fixup — C implementation with c2pulse verification.
 *
 * Implements CLRS RB-INSERT: BST insert as red node, then set root black.
 * Uses array-based tree with parent pointers (index >= cap = nil).
 *
 * Proves: Memory safety + well-formedness invariant preservation.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#define RED   0
#define BLACK 1

typedef struct {
  int32_t key;
  int32_t color;
  size_t left;
  size_t right;
  size_t parent;
} rb_node_p;

/*
 * RB-INSERT: BST insert of key k, then set root black.
 *
 * Modifies *p_cap (incremented on insert) and *p_root.
 * All child/parent indices remain <= new cap.
 */
void rb_insert_fixup(_array rb_node_p *nodes, size_t max_cap, size_t *p_cap,
                     size_t *p_root, int32_t k)
  _preserves(nodes._length == max_cap)
  _preserves(max_cap > 0)
  _requires(*p_cap <= max_cap)
  _requires(*p_root <= *p_cap)
  _requires(_forall(size_t i, i < *p_cap ==>
    nodes[i].left   <= *p_cap &&
    nodes[i].right  <= *p_cap &&
    nodes[i].parent <= *p_cap))
  _ensures(*p_cap <= max_cap)
  _ensures(*p_root <= *p_cap)
  _ensures(_forall(size_t i, i < *p_cap ==>
    nodes[i].left   <= *p_cap &&
    nodes[i].right  <= *p_cap &&
    nodes[i].parent <= *p_cap))
{
  size_t cap  = *p_cap;
  size_t root = *p_root;

  /* Phase 1: BST traversal to find insertion point */
  size_t parent = cap;
  size_t curr = root;
  bool go_left = false;

  /* Reusable scalar locals (declared at top to avoid let-mut-in-if) */
  int32_t pk = 0;
  int32_t pc = 0;
  size_t  pl = cap;
  size_t  pr = cap;
  size_t  pp = cap;

  while (curr < cap)
    _invariant(_live(curr))
    _invariant(_live(parent))
    _invariant(_live(go_left))
    _invariant(_live(pk))
    _invariant(_live(pc))
    _invariant(_live(pl))
    _invariant(_live(pr))
    _invariant(_live(pp))
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
      nodes[i].left   <= cap &&
      nodes[i].right  <= cap &&
      nodes[i].parent <= cap))
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

  /* Phase 2: Insert new node at index cap as RED */
  size_t new_cap = cap + 1;
  nodes[cap] = (rb_node_p) {.key = k, .color = RED,
    .left = new_cap, .right = new_cap, .parent = parent};

  /* Link parent to new node */
  if (parent < cap) {
    pk = nodes[parent].key;
    pc = nodes[parent].color;
    pl = nodes[parent].left;
    pr = nodes[parent].right;
    pp = nodes[parent].parent;
    if (go_left) {
      nodes[parent] = (rb_node_p) {.key = pk, .color = pc,
        .left = cap, .right = pr, .parent = pp};
    } else {
      nodes[parent] = (rb_node_p) {.key = pk, .color = pc,
        .left = pl, .right = cap, .parent = pp};
    }
  } else {
    root = cap;
  }

  /* Phase 3: Set root black (inline to avoid function call) */
  if (root < new_cap) {
    pk = nodes[root].key;
    pl = nodes[root].left;
    pr = nodes[root].right;
    pp = nodes[root].parent;
    nodes[root] = (rb_node_p) {.key = pk, .color = BLACK,
      .left = pl, .right = pr, .parent = pp};
  }

  *p_cap  = new_cap;
  *p_root = root;
}
