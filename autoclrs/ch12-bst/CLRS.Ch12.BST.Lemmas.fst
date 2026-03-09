module CLRS.Ch12.BST.Lemmas

(**
 * Unified BST Correctness Lemmas
 *
 * Re-exports the key correctness theorems from the component modules:
 *   - Insert.Spec: key_set(insert(t,k)) = key_set(t) ∪ {k}
 *   - Delete.Spec: key_set(delete(t,k)) = key_set(t) \ {k}
 *   - Spec:        search correctness, insert/delete validity preservation,
 *                  inorder sorted
 *
 * CLRS Reference: Theorems 12.2, 12.3
 *)

open FStar.List.Tot
module FS = FStar.FiniteSet.Base
open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BST.KeySet

(* ========================================================================
   § 1. Insert Correctness (from Insert.Spec)
   ======================================================================== *)

//SNIPPET_START: insert_key_set_lemma
let insert_key_set_lemma (t: bst) (k: int)
  : Lemma (requires bst_valid t)
          (ensures FS.equal (key_set (bst_insert t k))
                            (FS.union (key_set t) (FS.singleton k)))
  = CLRS.Ch12.BST.Insert.Spec.insert_key_set_lemma t k
//SNIPPET_END: insert_key_set_lemma

let theorem_insert_preserves_bst (t: bst) (k: int)
  : Lemma
    (requires bst_valid t)
    (ensures (
      let t' = bst_insert t k in
      bst_valid t' /\
      FS.equal (key_set t') (FS.union (key_set t) (FS.singleton k)) /\
      FS.mem k (key_set t')
    ))
  = CLRS.Ch12.BST.Insert.Spec.theorem_insert_preserves_bst t k

(* ========================================================================
   § 2. Delete Correctness (from Delete.Spec)
   ======================================================================== *)

//SNIPPET_START: delete_key_set_lemma
let delete_key_set_lemma (t: bst) (k: int)
  : Lemma (requires bst_valid t /\ bst_search t k)
          (ensures FS.equal (key_set (bst_delete t k))
                            (FS.remove k (key_set t)))
  = CLRS.Ch12.BST.Delete.Spec.delete_key_set_lemma t k
//SNIPPET_END: delete_key_set_lemma

(* ========================================================================
   § 3. Core Correctness Lemmas (from Spec)
   ======================================================================== *)

let search_correct (t: bst) (k: int)
  : Lemma (requires bst_valid t)
          (ensures bst_search t k <==> mem k (bst_inorder t))
  = bst_search_correct t k

let insert_valid (t: bst) (k: int)
  : Lemma (requires bst_valid t)
          (ensures bst_valid (bst_insert t k))
  = bst_insert_valid t k

let delete_valid (t: bst) (k: int)
  : Lemma (requires bst_valid t)
          (ensures bst_valid (bst_delete t k))
  = bst_delete_valid t k

let inorder_sorted (t: bst)
  : Lemma (requires bst_valid t)
          (ensures sorted (bst_inorder t))
  = bst_inorder_sorted t
