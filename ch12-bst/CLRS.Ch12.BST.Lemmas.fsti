module CLRS.Ch12.BST.Lemmas

(**
 * Interface: Unified BST Correctness Lemmas
 *
 * Exposes the key correctness theorems for BST operations:
 *   - Insert key-set algebra: key_set(insert(t,k)) = key_set(t) ∪ {k}
 *   - Delete key-set algebra: key_set(delete(t,k)) = key_set(t) \ {k}
 *   - Search correctness:     bst_search ⟺ mem (bst_inorder)
 *   - Insert/Delete preserve BST validity
 *   - Inorder traversal is sorted
 *
 * CLRS Reference: Theorems 12.2, 12.3
 *)

open FStar.List.Tot
module FS = FStar.FiniteSet.Base
open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BST.KeySet

(** Insert key-set theorem: key_set(insert(t,k)) = key_set(t) ∪ {k} *)
val insert_key_set_lemma: t:bst -> k:int ->
  Lemma (requires bst_valid t)
        (ensures FS.equal (key_set (bst_insert t k))
                          (FS.union (key_set t) (FS.singleton k)))

(** Full insert correctness: preserves validity, key-set union, membership *)
val theorem_insert_preserves_bst: t:bst -> k:int ->
  Lemma (requires bst_valid t)
        (ensures (
          let t' = bst_insert t k in
          bst_valid t' /\
          FS.equal (key_set t') (FS.union (key_set t) (FS.singleton k)) /\
          FS.mem k (key_set t')
        ))

(** Delete key-set theorem: key_set(delete(t,k)) = key_set(t) \ {k} *)
val delete_key_set_lemma: t:bst -> k:int ->
  Lemma (requires bst_valid t /\ bst_search t k)
        (ensures FS.equal (key_set (bst_delete t k))
                          (FS.remove k (key_set t)))

(** Search correctness: bst_search ⟺ membership in inorder traversal *)
val search_correct: t:bst -> k:int ->
  Lemma (requires bst_valid t)
        (ensures bst_search t k <==> mem k (bst_inorder t))

(** Insert preserves BST validity *)
val insert_valid: t:bst -> k:int ->
  Lemma (requires bst_valid t)
        (ensures bst_valid (bst_insert t k))

(** Delete preserves BST validity *)
val delete_valid: t:bst -> k:int ->
  Lemma (requires bst_valid t)
        (ensures bst_valid (bst_delete t k))

(** Inorder traversal of a valid BST is sorted *)
val inorder_sorted: t:bst ->
  Lemma (requires bst_valid t)
        (ensures sorted (bst_inorder t))
