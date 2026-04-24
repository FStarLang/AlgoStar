(**
 * CLRS Chapter 13: Red-Black Trees — Complexity Analysis for CLRS-Style Operations
 *
 * Tick counters and complexity bounds for the rotation-based CLRS insert/delete
 * (§13.3–13.4), complementing the shared search complexity from
 * CLRS.Ch13.RBTree.Complexity.
 *
 * Key results:
 *   - CLRS insert: clrs_insert_ticks ≤ h+2 ≤ 2·lg(n+1)+2  (O(log n))
 *   - CLRS delete: clrs_delete_ticks ≤ 2h+2 ≤ 4·lg(n+1)+2  (O(log n))
 *   - minimum:     minimum_ticks ≤ h                        (O(log n))
 *
 * Search complexity is identical for both Okasaki and CLRS implementations
 * and is covered by CLRS.Ch13.RBTree.Complexity.
 *
 * NO admits. NO assumes.
 *)
module CLRS.Ch13.RBTree.CLRSComplexity

open CLRS.Ch13.RBTree.Spec

// ========== CLRS Insert Tick Counters ==========

/// clrs_ins tick count: number of recursive calls (path length)
val clrs_ins_ticks (t: rbtree) (k: int) : nat

/// clrs_insert tick count = clrs_ins_ticks + 1 (for make_black)
val clrs_insert_ticks (t: rbtree) (k: int) : nat

// ========== Minimum Tick Counter ==========

/// minimum tick count: left-spine traversal
val minimum_ticks (t: rbtree{Node? t}) : nat

// ========== CLRS Delete Tick Counters ==========

/// clrs_del tick count: path traversal + successor search at deletion point
val clrs_del_ticks (t: rbtree) (k: int) : nat

/// clrs_delete tick count = clrs_del_ticks + 1 (for make_black)
val clrs_delete_ticks (t: rbtree) (k: int) : nat

// ========== Height-Based Bounds ==========

val clrs_ins_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures clrs_ins_ticks t k <= height t + 1)

val clrs_insert_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures clrs_insert_ticks t k <= height t + 2)

val minimum_ticks_bounded (t: rbtree{Node? t})
  : Lemma (ensures minimum_ticks t <= height t)

val clrs_del_ticks_bounded (t: rbtree) (k: int)
  : Lemma (requires is_bst t)
          (ensures clrs_del_ticks t k <= 2 * height t + 1)

val clrs_delete_ticks_bounded (t: rbtree) (k: int)
  : Lemma (requires is_bst t)
          (ensures clrs_delete_ticks t k <= 2 * height t + 2)

// ========== Logarithmic Bounds ==========

//SNIPPET_START: clrs_insert_complexity
/// CLRS insert is O(log n): ≤ 2·lg(n+1) + 2 steps
val clrs_insert_complexity (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t /\ node_count t >= 1)
          (ensures clrs_insert_ticks t k <= 2 * log2_floor (node_count t + 1) + 2)
//SNIPPET_END: clrs_insert_complexity

//SNIPPET_START: clrs_delete_complexity
/// CLRS delete is O(log n): ≤ 4·lg(n+1) + 2 steps
val clrs_delete_complexity (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t /\ is_bst t /\ node_count t >= 1)
          (ensures clrs_delete_ticks t k <= 4 * log2_floor (node_count t + 1) + 2)
//SNIPPET_END: clrs_delete_complexity

// ========== Combined Big-O Statements ==========

val clrs_insert_big_o (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t)
          (ensures (node_count t >= 1 ==>
                    clrs_insert_ticks t k <= 2 * log2_floor (node_count t + 1) + 2) /\
                   (node_count t = 0 ==> clrs_insert_ticks t k = 2))

val clrs_delete_big_o (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t /\ is_bst t)
          (ensures (node_count t >= 1 ==>
                    clrs_delete_ticks t k <= 4 * log2_floor (node_count t + 1) + 2) /\
                   (node_count t = 0 ==> clrs_delete_ticks t k = 2))
