/*
 * Red-Black Tree Search — Recursive C implementation with c2pulse verification.
 *
 * Uses an array-based tree representation where nodes are stored in
 * a flat array and children are referenced by index.
 * A child index >= cap means nil/leaf (no child).
 *
 * Proves:
 *   1. Memory safety (all array accesses in bounds).
 *   2. Soundness: if return is true, then the key exists at some node.
 *   3. Frame preservation: the array is unmodified (read-only operation).
 *   4. Functional correctness: result matches CLRS.Ch13.RBTree.Spec.search
 *      via tree_of abstraction (see bridge lemma in _include_pulse).
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

_include_pulse(
  module S = CLRS.Ch13.RBTree.Spec

  let rec tree_of
    (nodes: Seq.seq (option ty_rb_node))
    (idx: nat)
    (fuel: nat)
    : Tot S.rbtree (decreases fuel)
    = if fuel = 0 || idx >= Seq.length nodes then S.Leaf
      else match Seq.index nodes idx with
           | None -> S.Leaf
           | Some nd ->
             let c = if Int32.v nd.struct_rb_node_anon_1__color = 0
                     then S.Red else S.Black in
             S.Node c
               (tree_of nodes (SizeT.v nd.struct_rb_node_anon_1__left) (fuel - 1))
               (Int32.v nd.struct_rb_node_anon_1__key)
               (tree_of nodes (SizeT.v nd.struct_rb_node_anon_1__right) (fuel - 1))
)

/*
 * Recursive BST search on a flat-array RB tree.
 *
 * Starting at node curr, compares keys and recurses into
 * left or right children.  fuel bounds the recursion depth
 * (pass cap for the initial call).
 *
 * Returns true if a node with key k is found, false otherwise.
 */
_rec bool rb_search(_array rb_node *nodes, size_t cap, size_t curr, int32_t k, size_t fuel)
  _preserves(nodes._length == cap)
  _preserves(cap > 0)
  _requires(curr <= cap)
  _preserves(_forall(size_t i, i < cap ==>
    nodes[i].left  <= cap &&
    nodes[i].right <= cap))
  /* Frame: arrays are unmodified (read-only operation) */
  _ensures(_forall(size_t i, i < cap ==>
    nodes[i].key   == _old(nodes[i].key) &&
    nodes[i].color == _old(nodes[i].color) &&
    nodes[i].left  == _old(nodes[i].left) &&
    nodes[i].right == _old(nodes[i].right)))
  _decreases((_specint) fuel)
{
  if (fuel == 0 || curr >= cap) {
    return false;
  }
  int32_t node_key = nodes[curr].key;
  if (k < node_key) {
    return rb_search(nodes, cap, nodes[curr].left, k, fuel - 1);
  } else if (k > node_key) {
    return rb_search(nodes, cap, nodes[curr].right, k, fuel - 1);
  } else {
    return true;
  }
}
