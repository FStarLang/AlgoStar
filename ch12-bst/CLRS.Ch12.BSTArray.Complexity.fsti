module CLRS.Ch12.BSTArray.Complexity

(**
 * Interface: Array-Backed BST Complexity Analysis
 *
 * Structural bounds for array-backed BSTs:
 *   - tree_height = ⌊log₂(cap)⌋
 *   - node_depth ≤ tree_height for all valid indices
 *   - Search path length is O(h)
 *
 * CLRS Reference: Theorem 12.2
 *)

open FStar.Mul

(** Floor of log base 2 *)
val log2_floor: n:nat{n > 0} -> nat

(** log2_floor is bounded by its input *)
val log2_floor_bounded: n:nat{n > 0} ->
  Lemma (ensures log2_floor n <= n)

(** 2^(log2_floor n) <= n < 2^(log2_floor n + 1) *)
val log2_floor_power_bounds: n:nat{n > 0} ->
  Lemma (ensures (let l = log2_floor n in
                  pow2 l <= n /\ n < pow2 (l + 1)))

(** Height of array-backed BST with given capacity *)
val tree_height: cap:nat{cap > 0} -> nat

(** Height is bounded by capacity *)
val height_bounded_by_capacity: cap:nat{cap > 0} ->
  Lemma (tree_height cap <= cap)

(** Depth of a node at index i *)
val node_depth: nat -> nat

(** Node depth equals floor log of (i+1) *)
val node_depth_is_log: i:nat ->
  Lemma (ensures node_depth i = log2_floor (i + 1))

(** log2_floor is monotone *)
val log2_floor_monotone: m:nat{m > 0} -> n:nat{n > 0 /\ m <= n} ->
  Lemma (ensures log2_floor m <= log2_floor n)

(** Depth of left child is one more than parent *)
val node_depth_left_child: i:nat ->
  Lemma (node_depth (2 * i + 1) == 1 + node_depth i)

(** Depth of right child is one more than parent *)
val node_depth_right_child: i:nat ->
  Lemma (node_depth (2 * i + 2) == 1 + node_depth i)

(** All nodes have depth ≤ height *)
val node_depth_bounded: cap:nat{cap > 0} -> i:nat{i < cap} ->
  Lemma (node_depth i <= tree_height cap)

(** Main complexity theorem: BST search does O(h) work *)
val search_complexity_bound: cap:nat{cap > 0} ->
  Lemma (let h = tree_height cap in
         h <= cap /\
         h = log2_floor cap /\
         (forall (i:nat{i < cap}). node_depth i <= h))

(** For balanced trees, height is Θ(log n) *)
val balanced_tree_height: n:nat{n > 0} -> cap:nat{cap >= n /\ cap <= 2 * n} ->
  Lemma (tree_height cap <= log2_floor (2 * n))
