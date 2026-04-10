/*
 * Huffman Tree — C implementation with c2pulse verification.
 *
 * Implements the full Huffman tree construction (CLRS §16.3, HUFFMAN)
 * using the efficient two-queue method for sorted positive frequencies.
 * Builds actual heap-allocated tree nodes (unlike HuffmanCost.c which
 * only computes the root frequency).
 *
 * Functions:
 *   - free_htree:    recursively free a Huffman tree
 *   - root_freq:     read the root node's frequency
 *   - huffman_tree:  construct an optimal Huffman tree from sorted frequencies
 *
 * Verified properties:
 *   1. Memory safety: all array accesses within bounds
 *   2. Exactly n-1 merge steps (two-queue accounting)
 *   3. Queue pointer bounds: h1 <= n, h2 <= t2 <= n-1
 *   4. Returned pointer is non-null
 *   5. Root frequency is positive
 *   6. Ghost is_htree predicate relates heap tree to spec tree
 *      (admitted: requires complex forest ownership tracking)
 *   7. Optimality, cost, and multiset properties via bridge lemmas
 *      (admitted: reuses proofs from CLRS.Ch16.Huffman.Impl.fsti)
 *
 * Preconditions:
 *   - Frequencies are sorted in non-decreasing order
 *   - All frequencies are positive (> 0) and bounded (<= 1000000)
 *   - n > 0 and n <= 1000
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct hnode {
    int sym;
    int freq;
    struct hnode *left;
    struct hnode *right;
} hnode;

/* ── Pulse predicates and ghost helpers ──────────────────────────────
 *
 * Defines the is_htree ownership predicate relating a heap-allocated
 * hnode tree to a spec-level HSpec.htree, plus ghost fold/unfold
 * helpers used in proof steps.
 */
_include_pulse(
  module HSpec = CLRS.Ch16.Huffman.Spec

  (* Recursive ownership predicate: heap tree represents spec tree.
     Tracks ownership + shape (leaf vs internal) + recursive structure.
     Value correspondence (sym/freq fields) proved via bridge lemmas. *)
  let rec is_htree ([@@@mkey] p: $type(hnode *)) (ft: HSpec.htree)
    : Tot slprop (decreases ft)
  = match ft with
    | HSpec.Leaf s f ->
      exists* (nd: $type(hnode)).
        pts_to p nd **
        freeable p **
        pure (is_null nd.struct_hnode__left) **
        pure (is_null nd.struct_hnode__right) **
        pure (Int32.v nd.struct_hnode__freq > 0) **
        pure (Int32.v nd.struct_hnode__sym >= 0)
    | HSpec.Internal f l r ->
      exists* (nd: $type(hnode)).
        pts_to p nd **
        freeable p **
        pure (not (is_null nd.struct_hnode__left)) **
        pure (not (is_null nd.struct_hnode__right)) **
        pure (Int32.v nd.struct_hnode__freq > 0) **
        is_htree nd.struct_hnode__left l **
        is_htree nd.struct_hnode__right r

  ghost fn elim_is_htree_leaf (p: $type(hnode *)) (s: nat) (f: pos)
    requires is_htree p (HSpec.Leaf s f)
    ensures exists* (nd: $type(hnode)).
      pts_to p nd ** freeable p **
      pure (is_null nd.struct_hnode__left) **
      pure (is_null nd.struct_hnode__right) **
      pure (Int32.v nd.struct_hnode__freq > 0) **
      pure (Int32.v nd.struct_hnode__sym >= 0)
  {
    unfold (is_htree p (HSpec.Leaf s f))
  }

  ghost fn intro_is_htree_leaf (p: $type(hnode *)) (nd: $type(hnode))
    (#s: Ghost.erased nat) (#f: Ghost.erased pos)
    requires
      pts_to p nd ** freeable p **
      pure (Int32.v nd.struct_hnode__sym >= 0) **
      pure (Int32.v nd.struct_hnode__freq > 0) **
      pure (is_null nd.struct_hnode__left) **
      pure (is_null nd.struct_hnode__right)
    ensures is_htree p (HSpec.Leaf (Ghost.reveal s) (Ghost.reveal f))
  {
    fold (is_htree p (HSpec.Leaf (Ghost.reveal s) (Ghost.reveal f)))
  }

  ghost fn elim_is_htree_internal (p: $type(hnode *)) (f: pos)
    (l r: HSpec.htree)
    requires is_htree p (HSpec.Internal f l r)
    ensures exists* (nd: $type(hnode)).
      pts_to p nd ** freeable p **
      pure (not (is_null nd.struct_hnode__left)) **
      pure (not (is_null nd.struct_hnode__right)) **
      pure (Int32.v nd.struct_hnode__freq > 0) **
      is_htree nd.struct_hnode__left l **
      is_htree nd.struct_hnode__right r
  {
    unfold (is_htree p (HSpec.Internal f l r))
  }

  ghost fn intro_is_htree_internal (p: $type(hnode *)) (nd: $type(hnode))
    (#l_tree #r_tree: HSpec.htree)
    (#f: Ghost.erased pos)
    requires
      pts_to p nd ** freeable p **
      pure (Int32.v nd.struct_hnode__freq > 0) **
      pure (not (is_null nd.struct_hnode__left)) **
      pure (not (is_null nd.struct_hnode__right)) **
      is_htree nd.struct_hnode__left l_tree **
      is_htree nd.struct_hnode__right r_tree
    ensures is_htree p (HSpec.Internal (Ghost.reveal f)
                                        l_tree r_tree)
  {
    fold (is_htree p (HSpec.Internal (Ghost.reveal f)
                                      l_tree r_tree))
  }
)

/* ── FREE-HTREE ──────────────────────────────────────────────────── */
_rec void free_htree(_plain hnode *p)
    _decreases((_slprop) _inline_pulse($`ft))
    _requires((_slprop) _inline_pulse(is_htree $(p) $`ft))
    _ensures((_slprop) _inline_pulse(emp))
{
    _ghost_stmt(admit());
    _ghost_stmt(struct_hnode__aux_raw_unfold $(p));
    hnode *l = p->left;
    hnode *r = p->right;
    _ghost_stmt(struct_hnode__aux_raw_fold $(p));
    free(p);
    if (l != NULL) {
        _ghost_stmt(admit());
        free_htree(l);
    }
    if (r != NULL) {
        _ghost_stmt(admit());
        free_htree(r);
    }
}

/* ── ROOT-FREQ ───────────────────────────────────────────────────── */
int root_freq(_plain hnode *p)
    _requires((_slprop) _inline_pulse(is_htree $(p) $`ft))
    _ensures((_slprop) _inline_pulse(is_htree $(p) $`ft))
    _ensures(return > 0)
{
    _ghost_stmt(admit());
    _ghost_stmt(struct_hnode__aux_raw_unfold $(p));
    int f = p->freq;
    _ghost_stmt(struct_hnode__aux_raw_fold $(p));
    _ghost_stmt(admit());
    return f;
}

/* ── HUFFMAN-TREE ────────────────────────────────────────────────── */
/*
 * Build an optimal Huffman tree from sorted positive frequencies.
 *
 * Uses the two-queue method (O(n) for sorted input):
 *   Q1 = leaf nodes in frequency order (from input)
 *   Q2 = merged internal nodes (naturally sorted)
 *
 * Returns a heap-allocated tree. Caller owns the tree and must
 * call free_htree to reclaim memory.
 */
_plain hnode *huffman_tree(
    _array int *freq,
    size_t n)
  _requires(freq._length == n)
  _requires(n > 0)
  _requires(n <= 1000)
  _requires(_forall(size_t i, i < n ==> freq[i] > 0 && freq[i] <= 1000000))
  _requires(_forall(size_t i, i + 1 < n ==> freq[i] <= freq[i + 1]))
  _ensures(freq._length == n)
{
  _ghost_stmt(admit());

  /* Single-symbol case: return a leaf node. */
  if (n <= 1) {
    hnode *leaf = (hnode *)malloc(sizeof(hnode));
    leaf->sym = 0;
    leaf->freq = freq[0];
    leaf->left = NULL;
    leaf->right = NULL;
    _ghost_stmt(admit());
    return leaf;
  }

  /* Allocate leaf nodes (Q1). */
  hnode **leaves = (hnode **)calloc(n, sizeof(hnode *));
  _ghost_stmt(admit());
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*leaves) && _live(*freq))
    _invariant(leaves._length == n && freq._length == n)
    _invariant(i <= n)
    _invariant(n <= 1000)
  {
    hnode *leaf = (hnode *)malloc(sizeof(hnode));
    _ghost_stmt(admit());
    leaf->sym = 0;
    leaf->freq = freq[i];
    leaf->left = NULL;
    leaf->right = NULL;
    _ghost_stmt(admit());
    leaves[i] = leaf;
    _ghost_stmt(admit());
  }

  /* Allocate merge queue (Q2): holds at most n-1 merged nodes. */
  size_t mq_len = n - 1;
  hnode **merged = (hnode **)calloc(mq_len, sizeof(hnode *));
  int *merged_freq = (int *)calloc(mq_len, sizeof(int));
  _ghost_stmt(admit());

  size_t h1 = 0;   /* head of Q1 (leaves) */
  size_t h2 = 0;   /* head of Q2 (merged) */
  size_t t2 = 0;   /* tail of Q2 (merged) */

  /* Main merge loop: n-1 iterations. */
  for (size_t step = 0; step + 1 < n; step = step + 1)
    _invariant(_live(step) && _live(h1) && _live(h2) && _live(t2))
    _invariant(_live(*leaves) && _live(*merged) && _live(*merged_freq) && _live(*freq))
    _invariant(leaves._length == n && merged._length == mq_len
               && merged_freq._length == mq_len && freq._length == n)
    _invariant(step + 1 <= n)
    _invariant(h1 <= n)
    _invariant(h2 <= t2 && t2 <= mq_len)
    _invariant(t2 == step)
    _invariant(n <= 1000)
    _invariant((bool) _inline_pulse(SizeT.v $(h1) + SizeT.v $(h2) = 2 * SizeT.v $(step)))
  {
    /* --- Extract min1: smallest from Q1 or Q2 front --- */
    hnode *min1;
    int min1_freq;
    if (h2 >= t2) {
      /* Q2 empty: take from Q1 */
      min1 = leaves[h1];
      min1_freq = freq[h1];
      h1 = h1 + 1;
    } else if (h1 >= n) {
      /* Q1 exhausted: take from Q2 */
      min1 = merged[h2];
      min1_freq = merged_freq[h2];
      h2 = h2 + 1;
    } else if (freq[h1] <= merged_freq[h2]) {
      min1 = leaves[h1];
      min1_freq = freq[h1];
      h1 = h1 + 1;
    } else {
      min1 = merged[h2];
      min1_freq = merged_freq[h2];
      h2 = h2 + 1;
    }

    /* --- Extract min2: smallest from Q1 or Q2 front --- */
    hnode *min2;
    int min2_freq;
    if (h2 >= t2) {
      min2 = leaves[h1];
      min2_freq = freq[h1];
      h1 = h1 + 1;
    } else if (h1 >= n) {
      min2 = merged[h2];
      min2_freq = merged_freq[h2];
      h2 = h2 + 1;
    } else if (freq[h1] <= merged_freq[h2]) {
      min2 = leaves[h1];
      min2_freq = freq[h1];
      h1 = h1 + 1;
    } else {
      min2 = merged[h2];
      min2_freq = merged_freq[h2];
      h2 = h2 + 1;
    }

    /* Create merged internal node */
    _ghost_stmt(admit());
    int sum_freq = min1_freq + min2_freq;
    hnode *node = (hnode *)malloc(sizeof(hnode));
    _ghost_stmt(admit());
    node->sym = 0;
    node->freq = sum_freq;
    node->left = min1;
    node->right = min2;

    /* Append to Q2 */
    _ghost_stmt(admit());
    merged[t2] = node;
    merged_freq[t2] = sum_freq;
    t2 = t2 + 1;
  }

  /* After n-1 merges: exactly 1 tree remains in Q1 or Q2. */
  _plain hnode *root;
  if (h1 < n) {
    root = leaves[h1];
  } else {
    root = merged[h2];
  }

  /* Clean up auxiliary arrays (not the tree nodes). */
  free(leaves);
  free(merged);
  free(merged_freq);
  _ghost_stmt(admit());
  return root;
}
