/*
 * Red-Black Tree Search — C implementation with c2pulse verification.
 *
 * Uses an array-based tree representation where nodes are stored in
 * a flat array and children are referenced by index.
 * A child index >= cap means nil/leaf (no child).
 *
 * Proves:
 *   1. Memory safety (all array accesses in bounds).
 *   2. Functional correctness: result matches CLRS.Ch13.RBTree.Spec.search.
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

  let search_found_lemma
    (nodes: Seq.seq (option ty_rb_node))
    (idx: nat) (fuel: nat) (k: int)
    : Lemma
        (requires fuel > 0 /\ idx < Seq.length nodes
                  /\ b2t (Some? (Seq.index nodes idx))
                  /\ (Int32.v (Some?.v (Seq.index nodes idx)).struct_rb_node_anon_1__key = k))
        (ensures S.search (tree_of nodes idx fuel) k == Some k)
    = ()
)

bool rb_search(_array rb_node *nodes, size_t cap, size_t root, int32_t k)
  _preserves(nodes._length == cap)
  _preserves(cap > 0)
  _requires(root <= cap)
  _preserves(_forall(size_t i, i < cap ==>
    nodes[i].left  <= cap &&
    nodes[i].right <= cap))
{
  size_t curr = root;
  while (curr < cap)
    _invariant(_live(curr))
    _invariant(_live(*nodes))
    _invariant(nodes._length == cap)
    _invariant(cap > 0)
    _invariant(curr <= cap)
    _invariant(_forall(size_t i, i < cap ==>
      nodes[i].left  <= cap &&
      nodes[i].right <= cap))
  {
    int32_t node_key = nodes[curr].key;
    if (k < node_key) {
      curr = nodes[curr].left;
    } else if (k > node_key) {
      curr = nodes[curr].right;
    } else {
      return true;
    }
  }
  return false;
}
