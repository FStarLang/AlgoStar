/*
 * Red-Black Tree Rotations — C implementation with c2pulse verification.
 *
 * Left and right rotations for CLRS Ch13 red-black tree maintenance.
 * Uses array-based tree with parent pointers.
 *
 * Proves: Memory safety + well-formedness invariant preservation.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

typedef struct {
  int32_t key;
  int32_t color;
  size_t left;
  size_t right;
  size_t parent;
} rb_node_p;

/*
 * Left rotation at node x (CLRS Figure 13.2):
 *
 *       x                y
 *      / \              / \
 *     a   y    ==>     x   c
 *        / \          / \
 *       b   c        a   b
 */
void left_rotate(_array rb_node_p *nodes, size_t cap, size_t *p_root, size_t x)
  _preserves(nodes._length == cap)
  _preserves(cap > 0)
  _requires(x < cap)
  _requires(nodes[x].right < cap)
  _requires(*p_root < cap)
  _preserves(_forall(size_t i, i < cap ==>
    nodes[i].left  <= cap &&
    nodes[i].right <= cap &&
    nodes[i].parent <= cap))
  _ensures(*p_root < cap)
{
  /* Read all values before any mutation — only scalars, no struct vars */
  size_t y  = nodes[x].right;
  size_t b  = nodes[y].left;
  size_t xp = nodes[x].parent;

  int32_t x_key   = nodes[x].key;
  int32_t x_color = nodes[x].color;
  size_t  x_left  = nodes[x].left;

  int32_t y_key   = nodes[y].key;
  int32_t y_color = nodes[y].color;
  size_t  y_right = nodes[y].right;

  /* Conditionally read b's fields */
  int32_t b_key    = 0;
  int32_t b_color  = 0;
  size_t  b_left   = cap;
  size_t  b_right  = cap;
  if (b < cap) {
    b_key   = nodes[b].key;
    b_color = nodes[b].color;
    b_left  = nodes[b].left;
    b_right = nodes[b].right;
  }

  /* Conditionally read xp's fields */
  int32_t xp_key    = 0;
  int32_t xp_color  = 0;
  size_t  xp_left   = cap;
  size_t  xp_right  = cap;
  size_t  xp_parent = cap;
  if (xp < cap) {
    xp_key    = nodes[xp].key;
    xp_color  = nodes[xp].color;
    xp_left   = nodes[xp].left;
    xp_right  = nodes[xp].right;
    xp_parent = nodes[xp].parent;
  }

  /* Now perform ALL writes */

  /* x: right = b, parent = y */
  nodes[x] = (rb_node_p) {.key = x_key, .color = x_color,
    .left = x_left, .right = b, .parent = y};

  /* y: left = x, parent = xp */
  nodes[y] = (rb_node_p) {.key = y_key, .color = y_color,
    .left = x, .right = y_right, .parent = xp};

  /* b: parent = x (if exists) */
  if (b < cap) {
    nodes[b] = (rb_node_p) {.key = b_key, .color = b_color,
      .left = b_left, .right = b_right, .parent = x};
  }

  /* xp: replace child x with y */
  if (xp >= cap) {
    *p_root = y;
  } else if (xp_left == x) {
    nodes[xp] = (rb_node_p) {.key = xp_key, .color = xp_color,
      .left = y, .right = xp_right, .parent = xp_parent};
  } else {
    nodes[xp] = (rb_node_p) {.key = xp_key, .color = xp_color,
      .left = xp_left, .right = y, .parent = xp_parent};
  }
}

/*
 * Right rotation at node y (mirror of left rotation):
 *
 *       y                x
 *      / \              / \
 *     x   c    ==>     a   y
 *    / \                  / \
 *   a   b                b   c
 */
void right_rotate(_array rb_node_p *nodes, size_t cap, size_t *p_root, size_t y_idx)
  _preserves(nodes._length == cap)
  _preserves(cap > 0)
  _requires(y_idx < cap)
  _requires(nodes[y_idx].left < cap)
  _requires(*p_root < cap)
  _preserves(_forall(size_t i, i < cap ==>
    nodes[i].left  <= cap &&
    nodes[i].right <= cap &&
    nodes[i].parent <= cap))
  _ensures(*p_root < cap)
{
  /* Read all values before any mutation */
  size_t x  = nodes[y_idx].left;
  size_t b  = nodes[x].right;
  size_t yp = nodes[y_idx].parent;

  int32_t y_key   = nodes[y_idx].key;
  int32_t y_color = nodes[y_idx].color;
  size_t  y_right = nodes[y_idx].right;

  int32_t x_key   = nodes[x].key;
  int32_t x_color = nodes[x].color;
  size_t  x_left  = nodes[x].left;

  /* Conditionally read b's fields */
  int32_t b_key    = 0;
  int32_t b_color  = 0;
  size_t  b_left   = cap;
  size_t  b_right  = cap;
  if (b < cap) {
    b_key   = nodes[b].key;
    b_color = nodes[b].color;
    b_left  = nodes[b].left;
    b_right = nodes[b].right;
  }

  /* Conditionally read yp's fields */
  int32_t yp_key    = 0;
  int32_t yp_color  = 0;
  size_t  yp_left   = cap;
  size_t  yp_right  = cap;
  size_t  yp_parent = cap;
  if (yp < cap) {
    yp_key    = nodes[yp].key;
    yp_color  = nodes[yp].color;
    yp_left   = nodes[yp].left;
    yp_right  = nodes[yp].right;
    yp_parent = nodes[yp].parent;
  }

  /* Now perform ALL writes */

  /* y: left = b, parent = x */
  nodes[y_idx] = (rb_node_p) {.key = y_key, .color = y_color,
    .left = b, .right = y_right, .parent = x};

  /* x: right = y, parent = yp */
  nodes[x] = (rb_node_p) {.key = x_key, .color = x_color,
    .left = x_left, .right = y_idx, .parent = yp};

  /* b: parent = y (if exists) */
  if (b < cap) {
    nodes[b] = (rb_node_p) {.key = b_key, .color = b_color,
      .left = b_left, .right = b_right, .parent = y_idx};
  }

  /* yp: replace child y with x */
  if (yp >= cap) {
    *p_root = x;
  } else if (yp_left == y_idx) {
    nodes[yp] = (rb_node_p) {.key = yp_key, .color = yp_color,
      .left = x, .right = yp_right, .parent = yp_parent};
  } else {
    nodes[yp] = (rb_node_p) {.key = yp_key, .color = yp_color,
      .left = yp_left, .right = x, .parent = yp_parent};
  }
}
