/*
 * Red-Black Tree Delete — C implementation with c2pulse verification.
 *
 * Implements CLRS RB-DELETE: find node, transplant, replace with successor.
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
 * RB-TRANSPLANT: replace subtree rooted at u with subtree rooted at v.
 */
void rb_transplant(_array rb_node_p *nodes, size_t cap, size_t *p_root,
                   size_t u, size_t v)
  _preserves(nodes._length == cap)
  _preserves(cap > 0)
  _requires(u < cap)
  _requires(v <= cap)
  _requires(*p_root <= cap)
  _preserves(_forall(size_t i, i < cap ==>
    nodes[i].left   <= cap &&
    nodes[i].right  <= cap &&
    nodes[i].parent <= cap))
  _ensures(*p_root <= cap)
{
  size_t up = nodes[u].parent;
  int32_t nk = 0;
  int32_t nc = 0;
  size_t  nl = cap;
  size_t  nr = cap;
  size_t  np = cap;

  if (up >= cap) {
    *p_root = v;
  } else {
    nk = nodes[up].key;
    nc = nodes[up].color;
    nl = nodes[up].left;
    nr = nodes[up].right;
    np = nodes[up].parent;
    if (nl == u) {
      nodes[up] = (rb_node_p) {.key = nk, .color = nc,
        .left = v, .right = nr, .parent = np};
    } else {
      nodes[up] = (rb_node_p) {.key = nk, .color = nc,
        .left = nl, .right = v, .parent = np};
    }
  }

  if (v < cap) {
    nk = nodes[v].key;
    nc = nodes[v].color;
    nl = nodes[v].left;
    nr = nodes[v].right;
    nodes[v] = (rb_node_p) {.key = nk, .color = nc,
      .left = nl, .right = nr, .parent = up};
  }
}

/*
 * Find minimum in subtree: recursive version returning index.
 * fuel bounds recursion depth (pass cap for initial call).
 */
_rec size_t tree_minimum(_array rb_node_p *nodes, size_t cap, size_t idx, size_t fuel)
  _preserves(nodes._length == cap)
  _preserves(cap > 0)
  _requires(idx < cap)
  _preserves(_forall(size_t i, i < cap ==>
    nodes[i].left   <= cap &&
    nodes[i].right  <= cap &&
    nodes[i].parent <= cap))
  _ensures(return < cap)
  /* Frame: arrays are unmodified */
  _ensures(_forall(size_t i, i < cap ==>
    nodes[i].key    == _old(nodes[i].key) &&
    nodes[i].color  == _old(nodes[i].color) &&
    nodes[i].left   == _old(nodes[i].left) &&
    nodes[i].right  == _old(nodes[i].right) &&
    nodes[i].parent == _old(nodes[i].parent)))
  _decreases((_specint) fuel)
{
  size_t left = nodes[idx].left;
  if (fuel == 0 || left >= cap) {
    return idx;
  }
  return tree_minimum(nodes, cap, left, fuel - 1);
}

/*
 * Delete when z has no left child: transplant z with right child.
 */
void delete_no_left(_array rb_node_p *nodes, size_t cap, size_t *p_root, size_t z)
  _preserves(nodes._length == cap)
  _preserves(cap > 0)
  _requires(z < cap)
  _requires(*p_root <= cap)
  _preserves(_forall(size_t i, i < cap ==>
    nodes[i].left   <= cap &&
    nodes[i].right  <= cap &&
    nodes[i].parent <= cap))
  _ensures(*p_root <= cap)
{
  size_t zr = nodes[z].right;
  rb_transplant(nodes, cap, p_root, z, zr);
}

/*
 * Delete when z has no right child: transplant z with left child.
 */
void delete_no_right(_array rb_node_p *nodes, size_t cap, size_t *p_root, size_t z)
  _preserves(nodes._length == cap)
  _preserves(cap > 0)
  _requires(z < cap)
  _requires(*p_root <= cap)
  _preserves(_forall(size_t i, i < cap ==>
    nodes[i].left   <= cap &&
    nodes[i].right  <= cap &&
    nodes[i].parent <= cap))
  _ensures(*p_root <= cap)
{
  size_t zl = nodes[z].left;
  rb_transplant(nodes, cap, p_root, z, zl);
}

/*
 * Delete when z has two children: find successor, transplant, copy key.
 * zr = right child of z, must be < cap.
 */
void delete_two_children(_array rb_node_p *nodes, size_t cap, size_t *p_root,
                         size_t z, size_t zr)
  _preserves(nodes._length == cap)
  _preserves(cap > 0)
  _requires(z < cap)
  _requires(zr < cap)
  _requires(*p_root <= cap)
  _preserves(_forall(size_t i, i < cap ==>
    nodes[i].left   <= cap &&
    nodes[i].right  <= cap &&
    nodes[i].parent <= cap))
  _ensures(*p_root <= cap)
{
  size_t y = tree_minimum(nodes, cap, zr, cap);

  int32_t yk = nodes[y].key;
  int32_t zc = nodes[z].color;
  size_t yr = nodes[y].right;

  rb_transplant(nodes, cap, p_root, y, yr);

  /* Overwrite z's key with successor's key */
  size_t zl = nodes[z].left;
  size_t zr2 = nodes[z].right;
  size_t zp = nodes[z].parent;
  nodes[z] = (rb_node_p) {.key = yk, .color = zc,
    .left = zl, .right = zr2, .parent = zp};
}

/*
 * RB-DELETE: find and remove the node with key k.
 * Uses separate helper functions for the three cases, inlines root-coloring.
 */
void rb_delete(_array rb_node_p *nodes, size_t cap, size_t *p_root, int32_t k)
  _preserves(nodes._length == cap)
  _preserves(cap > 0)
  _requires(*p_root <= cap)
  _preserves(_forall(size_t i, i < cap ==>
    nodes[i].left   <= cap &&
    nodes[i].right  <= cap &&
    nodes[i].parent <= cap))
  _ensures(*p_root <= cap)
{
  size_t root = *p_root;
  int32_t nk = 0;
  size_t  nl = cap;
  size_t  nr = cap;
  size_t  np = cap;

  /* Phase 1: Find node z with key k */
  size_t z = root;
  bool found = false;
  size_t found_idx = cap;

  while (z < cap)
    _invariant(_live(z))
    _invariant(_live(found))
    _invariant(_live(found_idx))
    _invariant(_live(root))
    _invariant(_live(nk))
    _invariant(_live(nl))
    _invariant(_live(nr))
    _invariant(_live(np))
    _invariant(_live(*nodes))
    _invariant(_live(*p_root))
    _invariant(nodes._length == cap)
    _invariant(cap > 0)
    _invariant(z <= cap)
    _invariant(root <= cap)
    _invariant(found_idx <= cap)
    _invariant(!found || found_idx < cap)
    _invariant(*p_root == root)
    _invariant(_forall(size_t i, i < cap ==>
      nodes[i].left   <= cap &&
      nodes[i].right  <= cap &&
      nodes[i].parent <= cap))
  {
    int32_t node_key = nodes[z].key;
    if (k < node_key) {
      z = nodes[z].left;
    } else if (k > node_key) {
      z = nodes[z].right;
    } else {
      found = true;
      found_idx = z;
      z = cap;
    }
  }

  if (!found) return;

  z = found_idx;

  /* Phase 2: Delete node z — check children and dispatch */
  size_t zl = nodes[z].left;
  size_t zr = nodes[z].right;

  if (zl >= cap) {
    delete_no_left(nodes, cap, p_root, z);
    root = *p_root;
    if (root < cap) {
      nk = nodes[root].key;
      nl = nodes[root].left;
      nr = nodes[root].right;
      np = nodes[root].parent;
      nodes[root] = (rb_node_p) {.key = nk, .color = BLACK,
        .left = nl, .right = nr, .parent = np};
    }
    return;
  }

  if (zr >= cap) {
    delete_no_right(nodes, cap, p_root, z);
    root = *p_root;
    if (root < cap) {
      nk = nodes[root].key;
      nl = nodes[root].left;
      nr = nodes[root].right;
      np = nodes[root].parent;
      nodes[root] = (rb_node_p) {.key = nk, .color = BLACK,
        .left = nl, .right = nr, .parent = np};
    }
    return;
  }

  /* Both children exist */
  delete_two_children(nodes, cap, p_root, z, zr);

  /* Phase 3: Set root black */
  root = *p_root;
  if (root < cap) {
    nk = nodes[root].key;
    nl = nodes[root].left;
    nr = nodes[root].right;
    np = nodes[root].parent;
    nodes[root] = (rb_node_p) {.key = nk, .color = BLACK,
      .left = nl, .right = nr, .parent = np};
  }
}
