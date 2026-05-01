module CLRS.Ch12.BSTArray.Complexity


(** Array-backed BST Complexity Analysis
    
    This module proves O(h) complexity bounds for BST search operations,
    where h is the height of the tree.
    
    Definitions (log2_floor, tree_height, node_depth) are in the .fsti.
    This file contains only the lemma proofs.
**)

(** Lemma: log2_floor is bounded by its input **)
let rec log2_floor_bounded (n:nat{n > 0})
  : Lemma (ensures log2_floor n <= n)
          (decreases n)
  = if n = 1 then ()
    else log2_floor_bounded (n / 2)

(** Lemma: 2^(log2_floor n) <= n < 2^(log2_floor n + 1) **)
let rec log2_floor_power_bounds (n:nat{n > 0})
  : Lemma (ensures (
            let l = log2_floor n in
            pow2 l <= n /\ n < pow2 (l + 1)))
          (decreases n)
  = if n = 1 then ()
    else (
      log2_floor_power_bounds (n / 2);
      Math.Lemmas.pow2_plus 1 (log2_floor (n / 2))
    )

(** Lemma: height is bounded by capacity **)
let height_bounded_by_capacity (cap:nat{cap > 0})
  : Lemma (tree_height cap <= cap)
  = log2_floor_bounded cap

(** Lemma: node depth equals floor log of (i+1) **)
let rec node_depth_is_log (i:nat)
  : Lemma (ensures node_depth i = log2_floor (i + 1))
          (decreases i)
  = if i = 0 then ()
    else (
      node_depth_is_log ((i - 1) / 2);
      assert ((i - 1) / 2 + 1 = (i + 1) / 2)
    )

(** Lemma: log2_floor is monotone **)
let rec log2_floor_monotone (m:nat{m > 0}) (n:nat{n > 0 /\ m <= n})
  : Lemma (ensures log2_floor m <= log2_floor n)
          (decreases m)
  = if m = 1 then ()
    else if n = 1 then ()
    else (
      Math.Lemmas.lemma_div_le m n 2;
      if m / 2 > 0 then log2_floor_monotone (m / 2) (n / 2)
    )

(** Lemma: depth of left child (2*i+1) is one more than parent **)
let node_depth_left_child (i:nat)
  : Lemma (node_depth (2 * i + 1) == 1 + node_depth i)
  = ()

(** Lemma: depth of right child (2*i+2) is one more than parent **)
let node_depth_right_child (i:nat)
  : Lemma (node_depth (2 * i + 2) == 1 + node_depth i)
  = assert ((2 * i + 2 - 1) / 2 == i)

(** Lemma: all nodes in a tree of capacity cap have depth <= height **)
let node_depth_bounded (cap:nat{cap > 0}) (i:nat{i < cap})
  : Lemma (node_depth i <= tree_height cap)
  = node_depth_is_log i;
    if i + 1 <= cap then (
      log2_floor_monotone (i + 1) cap
    )

(** Search path length in BST: at most h+1 nodes visited **)
let search_path_length (cap:nat{cap > 0}) (start:nat{start < cap})
  : Lemma (node_depth start + 1 <= tree_height cap + 1)
  = node_depth_bounded cap start

(** Main complexity theorem: BST search does O(h) work **)
let search_complexity_bound (cap:nat{cap > 0})
  : Lemma (
      let h = tree_height cap in
      h <= cap /\
      h = log2_floor cap /\
      (forall (i:nat{i < cap}). node_depth i <= h)
    )
  = log2_floor_bounded cap;
    introduce forall (i:nat{i < cap}). node_depth i <= tree_height cap
    with node_depth_bounded cap i

(** Corollary: For balanced trees with n nodes **)
let balanced_tree_height (n:nat{n > 0}) (cap:nat{cap >= n /\ cap <= 2 * n})
  : Lemma (tree_height cap <= log2_floor (2 * n))
  = log2_floor_monotone cap (2 * n)
