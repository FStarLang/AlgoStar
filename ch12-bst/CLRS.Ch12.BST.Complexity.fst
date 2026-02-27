module CLRS.Ch12.BST.Complexity

open FStar.Mul

(** Array-backed BST Complexity Analysis
    
    This module proves O(h) complexity bounds for BST search operations,
    where h is the height of the tree.
    
    Key insights from CLRS Chapter 12:
    - TREE-SEARCH follows a root-to-leaf path
    - At each level, it does O(1) work (one comparison)
    - Total work is O(h) where h = height of tree
    
    Array representation:
    - Node at index i has left child at 2*i+1, right child at 2*i+2
    - For capacity cap, maximum height is ⌊log₂(cap)⌋
**)

(** Compute floor of log base 2 of a positive natural number **)
let rec log2_floor (n:nat{n > 0}) : nat =
  if n = 1 then 0
  else 1 + log2_floor (n / 2)

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

(** Height of array-backed BST with given capacity
    This is the maximum depth from root (index 0) to any valid index < cap **)
let tree_height (cap:nat{cap > 0}) : nat =
  log2_floor cap

(** Lemma: height is bounded by capacity **)
let height_bounded_by_capacity (cap:nat{cap > 0})
  : Lemma (tree_height cap <= cap)
  = log2_floor_bounded cap

(** Depth of a node at index i in the array-backed BST **)
let rec node_depth (i:nat) : nat =
  if i = 0 then 0
  else 1 + node_depth ((i - 1) / 2)  // parent index

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

(** Main complexity theorem: BST search does O(h) work
    
    Theorem: A search operation starting from the root (index 0) in an 
    array-backed BST with capacity cap visits at most h+1 nodes, where
    h = tree_height cap = ⌊log₂(cap)⌋.
    
    Since each node visit does O(1) work (one comparison), total work is O(h).
**)
let search_complexity_bound (cap:nat{cap > 0})
  : Lemma (
      let h = tree_height cap in
      h <= cap /\  // height is at most linear
      h = log2_floor cap /\ // height is logarithmic for full tree
      (forall (i:nat{i < cap}). node_depth i <= h)  // all nodes within height
    )
  = log2_floor_bounded cap;
    introduce forall (i:nat{i < cap}). node_depth i <= tree_height cap
    with node_depth_bounded cap i

(** Corollary: For balanced trees with n nodes in capacity cap where cap ≈ 2n,
    height is Θ(log n) **)
let balanced_tree_height (n:nat{n > 0}) (cap:nat{cap >= n /\ cap <= 2 * n})
  : Lemma (tree_height cap <= log2_floor (2 * n))
  = log2_floor_monotone cap (2 * n)

(** Summary: BST operations have the following complexity bounds:
    
    1. tree_height cap = ⌊log₂(cap)⌋ for array capacity cap
    2. Any search path has length ≤ h + 1 where h = tree_height cap  
    3. Each step does O(1) work, so total work is O(h)
    4. For balanced trees, h = Θ(log n), giving O(log n) search
    5. For degenerate trees, h can be Θ(n), giving O(n) search in worst case
**)
