module CLRS.Ch12.BST.Complexity

(**
 * Interface: Pure BST Complexity Analysis
 *
 * O(h) complexity bounds for BST operations on the pure inductive BST,
 * where h is the height of the tree.
 *
 * Definitions (max, bst_height, tick functions) are transparent.
 * Lemma proofs are in the .fst.
 *
 * CLRS Reference: Theorem 12.2
 *)

open CLRS.Ch12.BST.Spec

(** Max of two natural numbers *)
let max (a: nat) (b: nat) : nat = if a >= b then a else b

(** Height of a BST *)
let rec bst_height (t: bst) : nat =
  match t with
  | Leaf -> 0
  | Node left _ right -> 1 + max (bst_height left) (bst_height right)

(** Search tick count *)
let rec bst_search_ticks (t: bst) (k: int) : nat =
  match t with
  | Leaf -> 0
  | Node left key right ->
      if k = key then 1
      else if k < key then 1 + bst_search_ticks left k
      else 1 + bst_search_ticks right k

(** Search ticks bounded by tree height *)
val search_ticks_bounded: t:bst -> k:int ->
  Lemma (ensures bst_search_ticks t k <= bst_height t)

(** Minimum tick count *)
let rec bst_minimum_ticks (t: bst) : nat =
  match t with
  | Leaf -> 0
  | Node Leaf _ _ -> 1
  | Node left _ _ -> 1 + bst_minimum_ticks left

(** Maximum tick count *)
let rec bst_maximum_ticks (t: bst) : nat =
  match t with
  | Leaf -> 0
  | Node _ _ Leaf -> 1
  | Node _ _ right -> 1 + bst_maximum_ticks right

(** Minimum ticks bounded by tree height *)
val minimum_ticks_bounded: t:bst ->
  Lemma (ensures bst_minimum_ticks t <= bst_height t)

(** Maximum ticks bounded by tree height *)
val maximum_ticks_bounded: t:bst ->
  Lemma (ensures bst_maximum_ticks t <= bst_height t)

(** Insert tick count *)
let rec bst_insert_ticks (t: bst) (k: int) : nat =
  match t with
  | Leaf -> 0
  | Node left key right ->
      if k < key then 1 + bst_insert_ticks left k
      else if k > key then 1 + bst_insert_ticks right k
      else 1

(** Insert does not increase height by more than 1 *)
val insert_height_bound: t:bst -> k:int ->
  Lemma (ensures bst_height (bst_insert t k) <= bst_height t + 1)

(** Insert ticks bounded by tree height *)
val insert_ticks_bounded: t:bst -> k:int ->
  Lemma (ensures bst_insert_ticks t k <= bst_height t)

(** Delete tick count *)
let rec bst_delete_ticks (t: bst) (k: int) : nat =
  match t with
  | Leaf -> 0
  | Node left key right ->
      if k < key then
        1 + bst_delete_ticks left k
      else if k > key then
        1 + bst_delete_ticks right k
      else
        match left, right with
        | Leaf, Leaf -> 1
        | Leaf, _ -> 1
        | _, Leaf -> 1
        | _, _ ->
            1 + bst_minimum_ticks right + bst_delete_ticks right (match bst_minimum right with Some x -> x | None -> key)

(** Delete does not increase height *)
val delete_height_bound: t:bst -> k:int ->
  Lemma (ensures bst_height (bst_delete t k) <= bst_height t)

(** Non-empty tree has a minimum *)
val minimum_exists: t:bst ->
  Lemma (requires Node? t) (ensures Some? (bst_minimum t))

(** Deleting the minimum is bounded by 2 * height *)
val delete_minimum_bounded: t:bst ->
  Lemma (requires Node? t /\ bst_valid t)
        (ensures (match bst_minimum t with
                  | Some min_key -> bst_delete_ticks t min_key <= 2 * bst_height t
                  | None -> False))

(** Delete ticks bounded by 4 * height + 1 (O(h)) *)
val delete_ticks_bounded: t:bst -> k:int ->
  Lemma (requires bst_valid t)
        (ensures bst_delete_ticks t k <= 4 * bst_height t + 1)
