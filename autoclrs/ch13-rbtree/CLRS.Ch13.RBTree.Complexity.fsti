(**
 * CLRS Chapter 13: Red-Black Trees — Complexity Analysis Interface
 *
 * Signatures for complexity theorems following CLRS §13.1–13.4:
 *   - Search is O(log n): ≤ h+1 steps
 *   - Insert is O(log n): ≤ h+2 steps
 *   - Delete is O(log n): ≤ 2h+2 steps
 *
 * Ghost tick counters count recursive calls; bounds proven via
 * CLRS Theorem 13.1 (height ≤ 2·lg(n+1)).
 *)
module CLRS.Ch13.RBTree.Complexity

open CLRS.Ch13.RBTree.Spec

// ========== Search/Insert Tick Counters and Bounds ==========

/// Search tick count: number of recursive calls
val search_ticks (t: rbtree) (k: int) : nat

/// Insert inner-loop tick count (path traversal)
val ins_ticks (t: rbtree) (k: int) : nat

/// Insert tick count = ins_ticks + 1 (for make_black)
val insert_ticks (t: rbtree) (k: int) : nat

val search_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures search_ticks t k <= height t + 1)

val ins_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures ins_ticks t k <= height t + 1)

val insert_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures insert_ticks t k <= height t + 2)

// ========== Search/Insert Logarithmic Bounds ==========

//SNIPPET_START: search_complexity
/// Search is O(log n): ≤ 2·lg(n+1) + 1 steps
val search_complexity (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t /\ node_count t >= 1)
          (ensures search_ticks t k <= 2 * log2_floor (node_count t + 1) + 1)
//SNIPPET_END: search_complexity

//SNIPPET_START: insert_complexity
/// Insert is O(log n): ≤ 2·lg(n+1) + 2 steps
val insert_complexity (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t /\ node_count t >= 1)
          (ensures insert_ticks t k <= 2 * log2_floor (node_count t + 1) + 2)
//SNIPPET_END: insert_complexity

val search_big_o (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t)
          (ensures (node_count t >= 1 ==>
                    search_ticks t k <= 2 * log2_floor (node_count t + 1) + 1) /\
                   (node_count t = 0 ==> search_ticks t k = 1))

val insert_big_o (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t)
          (ensures (node_count t >= 1 ==>
                    insert_ticks t k <= 2 * log2_floor (node_count t + 1) + 2) /\
                   (node_count t = 0 ==> insert_ticks t k = 2))

// ========== Delete Tick Counters and Bounds ==========

/// Fuse tick count: traverses inner spines during delete
val fuse_ticks (l r: rbtree) : nat

/// Delete inner-loop tick count (path traversal + fuse)
val del_ticks (t: rbtree) (k: int) : nat

/// Delete tick count = del_ticks + 1 (for make_black)
val delete_ticks (t: rbtree) (k: int) : nat

val fuse_ticks_bounded (l r: rbtree)
  : Lemma (ensures fuse_ticks l r <= height l + height r + 1)

val del_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures del_ticks t k <= 2 * height t + 1)

val delete_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures delete_ticks t k <= 2 * height t + 2)

// ========== Delete Logarithmic Bounds ==========

//SNIPPET_START: delete_complexity
/// Delete is O(log n): ≤ 4·lg(n+1) + 2 steps
val delete_complexity (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t /\ node_count t >= 1)
          (ensures delete_ticks t k <= 4 * log2_floor (node_count t + 1) + 2)
//SNIPPET_END: delete_complexity

val delete_big_o (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t)
          (ensures (node_count t >= 1 ==>
                    delete_ticks t k <= 4 * log2_floor (node_count t + 1) + 2) /\
                   (node_count t = 0 ==> delete_ticks t k = 2))
