(**
 * CLRS Chapter 13: Red-Black Trees — Lemma Signatures
 *
 * Interface for correctness lemmas about red-black tree operations.
 * Exposes key theorems for external modules:
 *   - Theorem 13.1: height bound
 *   - Insert/delete: membership, BST, RB invariant preservation
 *   - Minimum/maximum: membership and optimality
 *   - Successor/predecessor: correctness
 *   - Node count preservation
 *)
module CLRS.Ch13.RBTree.Lemmas

open FStar.Mul
open CLRS.Ch13.RBTree.Spec

// ========== Theorem 13.1: Height Bound ==========

val min_nodes_for_bh (t: rbtree)
  : Lemma (requires same_bh t /\ no_red_red t)
          (ensures node_count t >= pow2 (bh t) - 1)

val bh_height_bound (t: rbtree)
  : Lemma (requires no_red_red t /\ same_bh t)
          (ensures height t <= 2 * bh t + color_bonus t)

val rbtree_height_le_2bh (t: rbtree)
  : Lemma (requires is_rbtree t /\ Node? t)
          (ensures height t <= 2 * bh t)

val pow2_log2_le (n: pos)
  : Lemma (ensures pow2 (log2_floor n) <= n)

val log2_floor_ge (n: pos) (k: nat)
  : Lemma (requires n >= pow2 k)
          (ensures log2_floor n >= k)

/// CLRS Theorem 13.1: height ≤ 2·lg(n+1)
val height_bound_theorem (t: rbtree)
  : Lemma (requires is_rbtree t /\ node_count t >= 1)
          (ensures height t <= 2 * log2_floor (node_count t + 1))

// ========== Balance Classifier Lemma ==========

val classify_balance_lemma (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma (
    match classify_balance c l r with
    | BC_LL -> (match l with
               | Node Red (Node Red a x b) y c_ -> balance c l v r == Node Red (Node Black a x b) y (Node Black c_ v r)
               | _ -> False)
    | BC_LR -> (match l with
               | Node Red a x (Node Red b y c_) -> balance c l v r == Node Red (Node Black a x b) y (Node Black c_ v r)
               | _ -> False)
    | BC_RL -> (match r with
               | Node Red (Node Red b y c_) z d -> balance c l v r == Node Red (Node Black l v b) y (Node Black c_ z d)
               | _ -> False)
    | BC_RR -> (match r with
               | Node Red b y (Node Red c_ z d) -> balance c l v r == Node Red (Node Black l v b) y (Node Black c_ z d)
               | _ -> False)
    | BC_None -> balance c l v r == Node c l v r)

// ========== Insert Correctness ==========

val balance_mem (c: color) (l: rbtree) (v: int) (r: rbtree) (k: int)
  : Lemma (ensures mem k (balance c l v r) <==> (k = v || mem k l || mem k r))

val ins_mem (t: rbtree) (k: int) (x: int)
  : Lemma (ensures mem x (ins t k) <==> (x = k || mem x t))

val insert_mem (t: rbtree) (k: int) (x: int)
  : Lemma (ensures mem x (insert t k) <==> (x = k || mem x t))

val balance_all_lt (c: color) (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma (requires all_lt l bound /\ all_lt r bound /\ v < bound)
          (ensures all_lt (balance c l v r) bound)

val balance_all_gt (c: color) (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma (requires all_gt l bound /\ all_gt r bound /\ v > bound)
          (ensures all_gt (balance c l v r) bound)

val all_lt_weaken (t: rbtree) (b1 b2: int)
  : Lemma (requires all_lt t b1 /\ b1 <= b2)
          (ensures all_lt t b2)

val all_gt_weaken (t: rbtree) (b1 b2: int)
  : Lemma (requires all_gt t b1 /\ b2 <= b1)
          (ensures all_gt t b2)

val ins_preserves_bst (t: rbtree) (k: int)
  : Lemma (requires is_bst t)
          (ensures is_bst (ins t k))

val insert_preserves_bst (t: rbtree) (k: int)
  : Lemma (requires is_bst t)
          (ensures is_bst (insert t k))

// ========== Insert Preserves RB Properties ==========

val balance_same_bh (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma (requires same_bh l /\ same_bh r /\ bh l = bh r)
          (ensures same_bh (balance c l v r))

val balance_bh (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma (requires same_bh l /\ same_bh r /\ bh l = bh r)
          (ensures bh (balance c l v r) = bh (Node c l v r))

val balance_restores_no_red_red_left (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma (requires c = Black /\ almost_no_red_red l /\ no_red_red r)
          (ensures no_red_red (balance c l v r))

val balance_restores_no_red_red_right (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma (requires c = Black /\ no_red_red l /\ almost_no_red_red r)
          (ensures no_red_red (balance c l v r))

val ins_properties (t: rbtree) (k: int)
  : Lemma (requires same_bh t /\ no_red_red t)
          (ensures same_bh (ins t k) /\
                   bh (ins t k) = bh t /\
                   almost_no_red_red (ins t k) /\
                   (Node? t /\ Black? (Node?.c t) ==> no_red_red (ins t k)))

/// Insert preserves all RB properties
val insert_is_rbtree (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t)
          (ensures is_rbtree (insert t k))

// ========== Minimum / Maximum Correctness ==========

val minimum_mem (t: rbtree{Node? t})
  : Lemma (ensures mem (minimum t) t)

val maximum_mem (t: rbtree{Node? t})
  : Lemma (ensures mem (maximum t) t)

val all_gt_mem (t: rbtree) (bound: int) (x: int)
  : Lemma (requires all_gt t bound /\ mem x t)
          (ensures x > bound)

val all_lt_mem (t: rbtree) (bound: int) (x: int)
  : Lemma (requires all_lt t bound /\ mem x t)
          (ensures x < bound)

val minimum_is_min (t: rbtree{Node? t}) (x: int)
  : Lemma (requires is_bst t /\ mem x t)
          (ensures minimum t <= x)

val maximum_is_max (t: rbtree{Node? t}) (x: int)
  : Lemma (requires is_bst t /\ mem x t)
          (ensures maximum t >= x)

val bst_lt_not_mem (t: rbtree) (bound: int) (k: int)
  : Lemma (requires all_gt t bound /\ k <= bound)
          (ensures mem k t = false)

val bst_gt_not_mem (t: rbtree) (bound: int) (k: int)
  : Lemma (requires all_lt t bound /\ k >= bound)
          (ensures mem k t = false)

// ========== Successor / Predecessor Correctness ==========

val successor_mem (t: rbtree) (k: int)
  : Lemma (ensures (match successor t k with
                     | Some s -> mem s t = true /\ s > k
                     | None -> true))

val predecessor_mem (t: rbtree) (k: int)
  : Lemma (ensures (match predecessor t k with
                     | Some p -> mem p t = true /\ p < k
                     | None -> true))

val successor_is_next (t: rbtree) (k: int) (x: int)
  : Lemma (requires is_bst t /\ mem x t = true /\ x > k)
          (ensures (match successor t k with
                     | Some s -> s <= x
                     | None -> false))

val predecessor_is_prev (t: rbtree) (k: int) (x: int)
  : Lemma (requires is_bst t /\ mem x t = true /\ x < k)
          (ensures (match predecessor t k with
                     | Some p -> p >= x
                     | None -> false))

// ========== Delete Correctness ==========

val delete_mem (t: rbtree) (k: int) (x: int)
  : Lemma (requires is_bst t)
          (ensures mem x (delete t k) <==> (mem x t && x <> k))

val delete_preserves_bst (t: rbtree) (k: int)
  : Lemma (requires is_bst t)
          (ensures is_bst (delete t k))

/// Delete preserves all RB and BST properties
val delete_is_rbtree (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t /\ is_bst t)
          (ensures is_rbtree (delete t k) /\ is_bst (delete t k))

// ========== Insert Node Count ==========

val insert_node_count (t: rbtree) (k: int)
  : Lemma (requires is_bst t)
          (ensures node_count (insert t k) = (if mem k t then node_count t else node_count t + 1))
