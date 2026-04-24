module CLRS.Ch12.BST.Complexity

(**
 * Pure BST Complexity Analysis — Lemma Proofs
 *
 * Definitions (max, bst_height, tick functions) are in the .fsti.
 * This file contains only the lemma proofs.
 *
 * CLRS Reference: Theorem 12.2
 *)

open CLRS.Ch12.BST.Spec

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


let rec minimum_exists (t: bst)
  : Lemma
    (requires Node? t)
    (ensures Some? (bst_minimum t))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node Leaf _ _ -> ()
    | Node left _ _ -> minimum_exists left


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


