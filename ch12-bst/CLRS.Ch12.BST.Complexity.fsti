module CLRS.Ch12.BST.Complexity

(**
 * Interface: Pure BST Complexity Analysis
 *
 * O(h) complexity bounds for BST operations on the pure inductive BST,
 * where h is the height of the tree.
 *
 * CLRS Reference: Theorem 12.2 — Search, Insert, Delete, Min, Max,
 * Successor, Predecessor all run in O(h) time on a BST of height h.
 *)

open CLRS.Ch12.BST.Spec
open FStar.Mul

(** Max of two natural numbers *)
val max: nat -> nat -> nat

(** Height of a BST *)
val bst_height: bst -> nat

(** Search tick count *)
val bst_search_ticks: bst -> int -> nat

(** Search ticks bounded by tree height *)
val search_ticks_bounded: t:bst -> k:int ->
  Lemma (ensures bst_search_ticks t k <= bst_height t)

(** Minimum tick count *)
val bst_minimum_ticks: bst -> nat

(** Maximum tick count *)
val bst_maximum_ticks: bst -> nat

(** Minimum ticks bounded by tree height *)
val minimum_ticks_bounded: t:bst ->
  Lemma (ensures bst_minimum_ticks t <= bst_height t)

(** Maximum ticks bounded by tree height *)
val maximum_ticks_bounded: t:bst ->
  Lemma (ensures bst_maximum_ticks t <= bst_height t)

(** Insert tick count *)
val bst_insert_ticks: bst -> int -> nat

(** Insert does not increase height by more than 1 *)
val insert_height_bound: t:bst -> k:int ->
  Lemma (ensures bst_height (bst_insert t k) <= bst_height t + 1)

(** Insert ticks bounded by tree height *)
val insert_ticks_bounded: t:bst -> k:int ->
  Lemma (ensures bst_insert_ticks t k <= bst_height t)

(** Delete tick count *)
val bst_delete_ticks: bst -> int -> nat

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
