module CLRS.Ch12.BST.Spec.Complexity

(* ========================================================================
   Pure BST Complexity Analysis
   
   This module proves O(h) complexity bounds for BST operations on the
   pure inductive BST data structure, where h is the height of the tree.
   
   Following CLRS Chapter 12:
   - TREE-SEARCH follows a root-to-leaf path: O(h) comparisons
   - TREE-INSERT follows a root-to-leaf path: O(h) comparisons  
   - TREE-DELETE follows a path and may walk to successor: O(2h) comparisons
   ======================================================================== *)

open CLRS.Ch12.BST.Spec.Complete
open FStar.Mul

(* Helper: max function for natural numbers *)
let max (a: nat) (b: nat) : nat = if a >= b then a else b

(* ========================================================================
   § 1. BST Height Definition
   
   Height of a tree is the maximum distance from root to any leaf.
   - Leaf has height 0
   - Node has height 1 + max(height left, height right)
   ======================================================================== *)

let rec bst_height (t: bst) : nat =
  match t with
  | Leaf -> 0
  | Node left _ right -> 1 + max (bst_height left) (bst_height right)

(* ========================================================================
   § 2. Search Complexity
   
   Count the number of comparisons during search operation.
   ======================================================================== *)

let rec bst_search_ticks (t: bst) (k: int) : nat =
  match t with
  | Leaf -> 0
  | Node left key right ->
      if k = key then 1  // One comparison, found it
      else if k < key then 1 + bst_search_ticks left k  // One comparison, go left
      else 1 + bst_search_ticks right k  // Two comparisons (k=key, k<key), go right

(* Lemma: Search ticks are bounded by tree height *)
let rec search_ticks_bounded (t: bst) (k: int)
  : Lemma 
    (ensures bst_search_ticks t k <= bst_height t)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node left key right ->
        if k = key then ()
        else if k < key then (
          // Going left: ticks = 1 + search_ticks left k
          search_ticks_bounded left k;
          // search_ticks left k <= height left
          // So: 1 + search_ticks left k <= 1 + height left
          // And: 1 + height left <= 1 + max(height left, height right) = height t
          assert (bst_height left <= max (bst_height left) (bst_height right))
        ) else (
          // Going right: ticks = 1 + search_ticks right k
          search_ticks_bounded right k;
          // search_ticks right k <= height right
          // So: 1 + search_ticks right k <= 1 + height right
          // And: 1 + height right <= 1 + max(height left, height right) = height t
          assert (bst_height right <= max (bst_height left) (bst_height right))
        )

(* ========================================================================
   § 3. Minimum/Maximum Complexity
   
   Finding minimum/maximum walks down one side of the tree.
   ======================================================================== *)

let rec bst_minimum_ticks (t: bst) : nat =
  match t with
  | Leaf -> 0
  | Node Leaf _ _ -> 1  // Check that left is Leaf
  | Node left _ _ -> 1 + bst_minimum_ticks left  // Check left, recurse

let rec bst_maximum_ticks (t: bst) : nat =
  match t with
  | Leaf -> 0
  | Node _ _ Leaf -> 1  // Check that right is Leaf
  | Node _ _ right -> 1 + bst_maximum_ticks right  // Check right, recurse

(* Lemma: Minimum ticks are bounded by tree height *)
let rec minimum_ticks_bounded (t: bst)
  : Lemma
    (ensures bst_minimum_ticks t <= bst_height t)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node Leaf _ _ -> ()
    | Node left _ right ->
        minimum_ticks_bounded left;
        assert (bst_height left <= max (bst_height left) (bst_height right))

(* Lemma: Maximum ticks are bounded by tree height *)
let rec maximum_ticks_bounded (t: bst)
  : Lemma
    (ensures bst_maximum_ticks t <= bst_height t)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ _ Leaf -> ()
    | Node left _ right ->
        maximum_ticks_bounded right;
        assert (bst_height right <= max (bst_height left) (bst_height right))

(* ========================================================================
   § 4. Insert Complexity
   
   Insert walks down from root to insertion point.
   ======================================================================== *)

let rec bst_insert_ticks (t: bst) (k: int) : nat =
  match t with
  | Leaf -> 0  // Create new node, no comparisons
  | Node left key right ->
      if k < key then 1 + bst_insert_ticks left k
      else if k > key then 1 + bst_insert_ticks right k
      else 1  // Found existing key, one comparison (k < key is false, then we check k > key and it's false, but we count it as visiting one node)

(* Lemma: Insert height after insertion *)
let rec insert_height_bound (t: bst) (k: int)
  : Lemma
    (ensures bst_height (bst_insert t k) <= bst_height t + 1)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node left key right ->
        if k < key then (
          insert_height_bound left k;
          // height (insert left k) <= height left + 1
          // So: 1 + max(height (insert left k), height right)
          //  <= 1 + max(height left + 1, height right)
          //  <= 1 + max(height left, height right) + 1 = height t + 1
          ()
        ) else if k > key then (
          insert_height_bound right k;
          ()
        ) else ()

(* Lemma: Insert ticks are bounded by tree height *)
let rec insert_ticks_bounded (t: bst) (k: int)
  : Lemma
    (ensures bst_insert_ticks t k <= bst_height t)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node left key right ->
        if k < key then (
          insert_ticks_bounded left k;
          assert (bst_height left <= max (bst_height left) (bst_height right))
        ) else if k > key then (
          insert_ticks_bounded right k;
          assert (bst_height right <= max (bst_height left) (bst_height right))
        ) else ()

(* ========================================================================
   § 5. Delete Complexity
   
   Delete is more complex:
   - Finding the node to delete: O(h)
   - If node has two children, finding successor (minimum of right): O(h)
   - Recursively deleting successor: O(h)
   - Total: O(2h) in worst case
   
   NOTE: Proving tight bounds for delete requires BST validity to establish
   that paths taken are deterministic. Without validity, we can't prove
   that minimum(left) < key, so we can't prove which branch delete takes.
   ======================================================================== *)

let rec bst_delete_ticks (t: bst) (k: int) : nat =
  match t with
  | Leaf -> 0
  | Node left key right ->
      if k < key then
        1 + bst_delete_ticks left k
      else if k > key then
        1 + bst_delete_ticks right k
      else
        // Found the key: count as 1 node visit
        match left, right with
        | Leaf, Leaf -> 1  // No children case
        | Leaf, _ -> 1     // Only right child
        | _, Leaf -> 1     // Only left child  
        | _, _ ->          // Two children case
            // Need to find successor and delete it
            1 + bst_minimum_ticks right + bst_delete_ticks right (match bst_minimum right with Some x -> x | None -> key)

(* Helper lemma: deletion doesn't increase height *)
let rec delete_height_bound (t: bst) (k: int)
  : Lemma
    (ensures bst_height (bst_delete t k) <= bst_height t)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node left key right ->
        if k < key then (
          delete_height_bound left k
        ) else if k > key then (
          delete_height_bound right k
        ) else (
          match left, right with
          | Leaf, Leaf -> ()
          | Leaf, _ -> ()
          | _, Leaf -> ()
          | _, _ ->
              match bst_minimum right with
              | Some successor_key ->
                  delete_height_bound right successor_key
              | None -> ()
        )

(* ========================================================================
   § 5.1. Delete Minimum Complexity
   
   Key insight: When deleting the minimum element, we follow the leftmost path.
   The minimum element has no left child (by definition of minimum), so when
   we reach it, we're in a simple delete case (0 or 1 child), not the expensive
   two-children case.
   
   This means delete_minimum takes at most O(h) operations, not O(2h).
   ======================================================================== *)

(* Helper lemma: For any non-empty tree, bst_minimum returns Some value *)
let rec minimum_exists (t: bst)
  : Lemma
    (requires Node? t)
    (ensures Some? (bst_minimum t))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node Leaf _ _ -> ()
    | Node left _ _ -> minimum_exists left

(* Key Lemma: Deleting the minimum element from a tree takes at most 2h operations.
   
   Note: Without BST validity assumptions, proving this requires detailed case analysis
   of the comparison branches in bst_delete_ticks. The key insight is that the minimum
   element (leftmost node) has no left child, so its deletion is a simple case.
   
   With BST validity, this can be proven by induction showing that:
   - The minimum is always in the left subtree (or is the root if no left child)
   - When deleting the minimum, we follow the left path and hit a simple delete case
   - Total operations: O(h) for finding + O(1) for deleting = O(h)
   
   For the purposes of this complexity analysis, we admit this lemma, noting that:
   - It's provable with BST validity
   - Even without it, a conservative bound of 2h suffices for O(h) complexity
*)
let rec delete_minimum_bounded (t: bst)
  : Lemma
    (requires Node? t /\ bst_valid t)
    (ensures (
      match bst_minimum t with
      | Some min_key -> bst_delete_ticks t min_key <= 2 * bst_height t
      | None -> False  // Cannot happen for non-empty tree
    ))
    (decreases t)
  = match t with
    | Leaf -> ()  // Impossible by precondition
    | Node Leaf key right ->
      ()
    | Node left key right ->
      minimum_exists left;
      (match bst_minimum left with
       | Some min_key ->
         bst_minimum_in_tree left;
         lemma_all_less_implies_mem_less key min_key (bst_inorder left);
         assert (min_key < key);
         delete_minimum_bounded left
       | None -> ())

(* Lemma: Delete ticks are bounded by 4 * tree height + 1
   
   This lemma expresses the O(h) complexity of BST delete operations (with constant factor 4).
   
   Without BST validity assumptions, we use conservative bounds:
   - Finding the node to delete: at most h comparisons (following one path)
   - Finding the successor (minimum of right): at most h steps
   - Deleting the successor: at most 2h steps (conservative bound without validity)
   - Total: h + h + 2h = 4h
   
   With BST validity, tighter bounds are possible (2h + 1) because the minimum
   has no left child, making its deletion simpler.
   
   Proof approach:
   - Leaf: trivial (0 <= 0)
   - Node with k < key or k > key: recurse, use IH
   - Node with k = key:
     * 0 or 1 child: O(1) operation
     * 2 children: use the helper lemmas with conservative bounds
*)
let rec delete_ticks_bounded (t: bst) (k: int)
  : Lemma
    (requires bst_valid t)
    (ensures bst_delete_ticks t k <= 4 * bst_height t + 1)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node left key right ->
        if k < key then (
          delete_ticks_bounded left k;
          assert (bst_height t >= 1 + bst_height left)
        ) else if k > key then (
          delete_ticks_bounded right k;
          assert (bst_height t >= 1 + bst_height right)
        ) else (
          match left, right with
          | Leaf, Leaf -> ()
          | Leaf, _ -> ()
          | _, Leaf -> ()
          | Node _ _ _, Node _ _ _ ->
              minimum_exists right;
              let Some successor_key = bst_minimum right in
              minimum_ticks_bounded right;
              delete_minimum_bounded right;
              assert (bst_height t >= bst_height right);
              assert (4 * bst_height t >= 4 * bst_height right);
              assert (3 * bst_height right <= 4 * bst_height right)
        )

(* ========================================================================
   § 6. Complexity Summary
   
   All basic BST operations run in O(h) time where h is tree height:
   - Search: <= h comparisons
   - Minimum/Maximum: <= h steps
   - Insert: <= h comparisons
   - Delete: <= 4h + 1 operations (with conservative analysis)
   
   For balanced trees: h = O(log n), giving O(log n) operations
   For degenerate trees: h = O(n), giving O(n) operations
   
   Note on delete complexity:
   - The bound of 4h + 1 is conservative, accounting for structural analysis
     without BST validity assumptions
   - With BST validity (all keys left < key < all keys right), the bound
     can be tightened to 2h + 1, as the minimum has no left child
   - In both cases, the asymptotic complexity is O(h)
   ======================================================================== *)
