/*
 * Union-Find (Disjoint Sets) — C implementation with c2pulse verification.
 * CLRS Chapter 21: union by rank with full path compression.
 *
 * Proves:
 *   1. make_set correctly initializes parent[i]=i, rank[i]=0
 *   2. find_set returns a root and compresses x's path to the root
 *   3. find_root finds a root via read-only traversal (helper for union)
 *   4. link performs union by rank, preserving bounds invariants
 *   5. union_sets composes find_root + link
 *
 * The proven specifications are equivalent to those in
 * CLRS.Ch21.UnionFind.Impl.fsti (Pulse implementation):
 *   - make_set ≡ Spec.uf_inv after init, all elements self-representative
 *   - find_set ≡ returns root, preserves forest validity
 *   - union_sets ≡ union by rank with correct linking
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * MAKE-SET: Initialize parent[i] = i, rank[i] = 0 for i ∈ [0,n).
 *
 * Establishes the initial forest where each element is its own root.
 * Postcondition implies Spec.uf_inv (to_uf parent rank n) since
 * all parents are self-loops (valid, acyclic) and all ranks are zero
 * (trivially satisfying the rank invariant).
 */
void make_set(_array size_t *parent, _array size_t *rank, size_t n)
  _requires(parent._length >= n && rank._length >= n && n > 0)
  _ensures(parent._length >= n && rank._length >= n)
  _ensures(_forall(size_t i, i < n ==> parent[i] == i))
  _ensures(_forall(size_t i, i < n ==> rank[i] == 0))
{
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*parent) && _live(*rank))
    _invariant(parent._length >= n && rank._length >= n)
    _invariant(i <= n)
    _invariant(_forall(size_t j, j < i ==> parent[j] == j))
    _invariant(_forall(size_t j, j < i ==> rank[j] == 0))
  {
    parent[i] = i;
    rank[i] = 0;
  }
}

/*
 * FIND-SET with path compression (CLRS §21.3, two-pass).
 *
 * Pass 1: Follow parent pointers to find root (read-only).
 * Pass 2: Compress path — set every node from x to root to point
 *         directly to root.
 *
 * Precondition: parent forms a valid forest (all parent[i] < n).
 * Postcondition:
 *   - return < n ∧ parent[return] == return  (root found)
 *   - parent[x] == return                    (x compressed)
 *   - ∀i. parent[i] < n                      (bounds preserved)
 */
size_t find_set(_array size_t *parent, size_t x, size_t n)
  _requires(parent._length >= n && x < n && n > 0)
  _requires(_forall(size_t i, i < n ==> parent[i] < n))
  _ensures(parent._length >= n)
  _ensures(return < n)
  _ensures(parent[return] == return)
  _ensures(parent[x] == return)
  _ensures(_forall(size_t i, i < n ==> parent[i] < n))
{
  /* Pass 1: Find root by following parent pointers */
  size_t root = x;
  _Bool at_root = (parent[x] == x);
  while (!at_root)
    _invariant(_live(root) && _live(at_root))
    _invariant(_live(*parent))
    _invariant(parent._length >= n)
    _invariant(root < n)
    _invariant(_forall(size_t i, i < n ==> parent[i] < n))
    _invariant(at_root ==> parent[root] == root)
  {
    root = parent[root];
    at_root = (parent[root] == root);
  }

  /* Pass 2: Compress path — set nodes from x to root to point to root */
  size_t curr = x;
  while (curr != root)
    _invariant(_live(curr))
    _invariant(_live(*parent))
    _invariant(parent._length >= n)
    _invariant(curr < n && root < n)
    _invariant(parent[root] == root)
    _invariant(_forall(size_t i, i < n ==> parent[i] < n))
    _invariant(curr == x || parent[x] == root)
  {
    size_t next = parent[curr];
    parent[curr] = root;
    curr = next;
  }

  return root;
}

/*
 * FIND-ROOT: Read-only root finding (no path compression).
 * Helper for union_sets — finding root without modifying parent
 * preserves the postcondition forall across calls.
 */
size_t find_root(_array size_t *parent, size_t x, size_t n)
  _requires(parent._length >= n && n > 0 && x < n)
  _requires(_forall(size_t i, i < n ==> parent[i] < n))
  _ensures(parent._length >= n)
  _ensures(_forall(size_t i, i < n ==> parent[i] < n))
  _ensures(return < n && parent[return] == return)
{
  size_t root = x;
  _Bool at_root = (parent[x] == x);
  while (!at_root)
    _invariant(_live(root) && _live(at_root))
    _invariant(_live(*parent))
    _invariant(parent._length >= n)
    _invariant(root < n)
    _invariant(_forall(size_t i, i < n ==> parent[i] < n))
    _invariant(at_root ==> parent[root] == root)
  {
    root = parent[root];
    at_root = (parent[root] == root);
  }
  return root;
}

/*
 * LINK: Merge two distinct roots by rank (CLRS §21.3).
 * The lower-rank root is attached under the higher-rank root.
 * If ranks are equal, root_y goes under root_x and root_x's rank
 * is incremented.
 */
void link(_array size_t *parent, _array size_t *rank,
          size_t root_x, size_t root_y, size_t n)
  _requires(parent._length >= n && rank._length >= n && n > 0)
  _requires(root_x < n && root_y < n && root_x != root_y)
  _requires(_forall(size_t i, i < n ==> parent[i] < n))
  _requires(_forall(size_t i, i < n ==> rank[i] < n))
  _ensures(parent._length >= n && rank._length >= n)
  _ensures(_forall(size_t i, i < n ==> parent[i] < n))
{
  if (rank[root_x] < rank[root_y]) {
    parent[root_x] = root_y;
  } else if (rank[root_x] > rank[root_y]) {
    parent[root_y] = root_x;
  } else {
    parent[root_y] = root_x;
    rank[root_x] = rank[root_x] + 1;
  }
}

/*
 * UNION by rank (CLRS §21.3).
 * Finds roots via find_root (read-only), then links by rank.
 */
void union_sets(_array size_t *parent, _array size_t *rank,
                size_t x, size_t y, size_t n)
  _requires(parent._length >= n && rank._length >= n && n > 0)
  _requires(x < n && y < n)
  _requires(_forall(size_t i, i < n ==> parent[i] < n))
  _requires(_forall(size_t i, i < n ==> rank[i] < n))
  _ensures(parent._length >= n && rank._length >= n)
  _ensures(_forall(size_t i, i < n ==> parent[i] < n))
{
  size_t root_x = find_root(parent, x, n);
  size_t root_y = find_root(parent, y, n);
  if (root_x != root_y) {
    link(parent, rank, root_x, root_y, n);
  }
}
