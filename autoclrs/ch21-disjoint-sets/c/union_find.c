/*
 * Union-Find (Disjoint Sets) — C implementation with c2pulse verification.
 * CLRS Chapter 21: union by rank with full path compression.
 *
 * Uses c2pulse _rec functions for naturally recursive algorithms:
 *   1. make_set correctly initializes parent[i]=i, rank[i]=0
 *   2. find_root: recursive read-only root finding (uses rank for termination)
 *   3. find_set: recursive one-pass path compression (CLRS §21.3)
 *   4. link performs union by rank, preserving bounds invariants
 *   5. union_sets composes find_root + link
 *
 * Specifications are tightened to require the rank invariant
 * (CLRS Lemma 21.4), which provides a natural decreasing measure
 * for the recursive functions.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * MAKE-SET: Initialize parent[i] = i, rank[i] = 0 for i ∈ [0,n).
 *
 * Establishes the initial forest where each element is its own root.
 * All parents are self-loops (valid, acyclic) and all ranks are zero
 * (trivially satisfying the rank invariant).
 */
void make_set(_array size_t *parent, _array size_t *rank, size_t n)
  _requires(parent._length >= n && rank._length >= n && n > 0)
  _ensures(parent._length >= n && rank._length >= n)
  _ensures(_forall(size_t i, i < n ==> parent[i] == i))
  _ensures(_forall(size_t i, i < n ==> rank[i] == 0))
  _ensures(_forall(size_t i, i < n ==> parent[i] < n))
  _ensures(_forall(size_t i, i < n ==> rank[i] < n))
  /* Rank invariant: trivially satisfied since all parent[i] == i */
  _ensures(_forall(size_t i, i < n && parent[i] != i ==> rank[i] < rank[parent[i]]))
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
 * FIND-ROOT: Recursive read-only root finding (CLRS §21.3).
 *
 * Follows parent pointers to find the root without any modification.
 * Termination: rank strictly increases along parent pointers (CLRS
 * Lemma 21.4), so n − rank[x] is a well-founded decreasing measure.
 *
 * Used by union_sets to find roots before linking.
 */
_rec size_t find_root(_array size_t *parent, _array size_t *rank,
                      size_t x, size_t n)
  _requires(parent._length >= n && rank._length >= n && n > 0 && x < n)
  _requires(_forall(size_t i, i < n ==> parent[i] < n))
  _requires(_forall(size_t i, i < n ==> rank[i] < n))
  /* Rank invariant: rank strictly increases along parent pointers (CLRS Lemma 21.4) */
  _requires(_forall(size_t i, i < n && parent[i] != i ==> rank[i] < rank[parent[i]]))
  _preserves_value(parent._length)
  _preserves_value(rank._length)
  _ensures(_forall(size_t i, i < n ==> parent[i] < n))
  _ensures(_forall(size_t i, i < n ==> parent[i] == _old(parent[i])))
  _ensures(_forall(size_t i, i < n ==> rank[i] == _old(rank[i])))
  _ensures(return < n && parent[return] == return)
  /* Rank invariant preserved (arrays unchanged, so trivially holds) */
  _ensures(_forall(size_t i, i < n && parent[i] != i ==> rank[i] < rank[parent[i]]))
  _decreases((_specint) n - (_specint) rank[x])
{
  if (parent[x] == x) return x;
  return find_root(parent, rank, parent[x], n);
}

/*
 * FIND-SET: Recursive one-pass path compression (CLRS §21.3).
 *
 *   FIND-SET(x):
 *     if x ≠ x.p
 *       x.p ← FIND-SET(x.p)
 *     return x.p
 *
 * Termination: same rank-based measure as find_root.
 * Path compression only modifies parent pointers, not ranks.
 */
_rec size_t find_set(_array size_t *parent, _array size_t *rank,
                     size_t x, size_t n)
  _requires(parent._length >= n && rank._length >= n && x < n && n > 0)
  _requires(_forall(size_t i, i < n ==> parent[i] < n))
  _requires(_forall(size_t i, i < n ==> rank[i] < n))
  /* Rank invariant (CLRS Lemma 21.4) */
  _requires(_forall(size_t i, i < n && parent[i] != i ==> rank[i] < rank[parent[i]]))
  _ensures(parent._length >= n && rank._length >= n)
  _ensures(return < n)
  _ensures(parent[return] == return)
  _ensures(parent[x] == return)
  _ensures(_forall(size_t i, i < n ==> parent[i] < n))
  _ensures(_forall(size_t i, i < n ==> rank[i] == _old(rank[i])))
  /* Rank invariant preserved through path compression */
  _ensures(_forall(size_t i, i < n && parent[i] != i ==> rank[i] < rank[parent[i]]))
  _decreases((_specint) n - (_specint) rank[x])
{
  if (parent[x] == x) return x;
  size_t root = find_set(parent, rank, parent[x], n);
  parent[x] = root;
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
  _requires(parent[root_x] == root_x && parent[root_y] == root_y)
  _requires(_forall(size_t i, i < n ==> parent[i] < n))
  _requires(_forall(size_t i, i < n ==> rank[i] < n))
  _requires(_forall(size_t i, i < n && parent[i] != i ==> rank[i] < rank[parent[i]]))
  _ensures(parent._length >= n && rank._length >= n)
  _ensures(_forall(size_t i, i < n ==> parent[i] < n))
  /* Rank monotonicity: ranks never decrease */
  _ensures(_forall(size_t i, i < n ==> rank[i] >= _old(rank[i])))
  /* Rank invariant preserved through union by rank */
  _ensures(_forall(size_t i, i < n && parent[i] != i ==> rank[i] < rank[parent[i]]))
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
  _requires(_forall(size_t i, i < n && parent[i] != i ==> rank[i] < rank[parent[i]]))
  _ensures(parent._length >= n && rank._length >= n)
  _ensures(_forall(size_t i, i < n ==> parent[i] < n))
  /* Rank invariant preserved through union */
  _ensures(_forall(size_t i, i < n && parent[i] != i ==> rank[i] < rank[parent[i]]))
  /* Rank monotonicity */
  _ensures(_forall(size_t i, i < n ==> rank[i] >= _old(rank[i])))
{
  size_t root_x = find_root(parent, rank, x, n);
  size_t root_y = find_root(parent, rank, y, n);
  if (root_x != root_y) {
    link(parent, rank, root_x, root_y, n);
  }
}
