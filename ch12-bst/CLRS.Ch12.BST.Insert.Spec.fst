module CLRS.Ch12.BST.Insert.Spec

(**
 * BST Insert Key Set Specification
 *
 * Theorem: key_set(insert(t,k)) = key_set(t) ∪ {k} for valid BST t
 *
 * Uses list-based BST from CLRS.Ch12.BST.Spec.Complete
 * Main lemma verified with zero admits (FiniteSet algebra via all_finite_set_facts_lemma)
 *
 * Proof approach: Option B from PROGRESS_PLAN — mirrors CLRS.Ch12.BST.Delete.Spec
 *)

open FStar.List.Tot
module FS = FStar.FiniteSet.Base
open CLRS.Ch12.BST.Spec.Complete
open CLRS.Ch12.BST.KeySet

(* ========================================================================
   Main Theorem: key_set(insert(t,k)) = key_set(t) ∪ {k}
   ======================================================================== *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

//SNIPPET_START: insert_key_set_lemma
val insert_key_set_lemma: t:bst -> k:int ->
  Lemma (requires bst_valid t)
        (ensures FS.equal (key_set (bst_insert t k))
                          (FS.union (key_set t) (FS.singleton k)))
        (decreases t)
//SNIPPET_END: insert_key_set_lemma

let rec insert_key_set_lemma t k =
  FS.all_finite_set_facts_lemma ();
  match t with
  | Leaf ->
      lemma_list_to_set_singleton k

  | Node left key right ->
      lemma_list_to_set_append (bst_inorder left) ([key] @ bst_inorder right);
      lemma_list_to_set_append [key] (bst_inorder right);
      lemma_list_to_set_singleton key;

      if k < key then begin
        insert_key_set_lemma left k;
        lemma_list_to_set_append (bst_inorder (bst_insert left k)) ([key] @ bst_inorder right);
        lemma_list_to_set_append [key] (bst_inorder right)
      end else if k > key then begin
        insert_key_set_lemma right k;
        lemma_list_to_set_append (bst_inorder left) ([key] @ bst_inorder (bst_insert right k));
        lemma_list_to_set_append [key] (bst_inorder (bst_insert right k))
      end else begin
        // k = key, tree unchanged; key_set(t) ∪ {k} = key_set(t) since k ∈ key_set(t)
        lemma_mem_append key [key] (bst_inorder right);
        lemma_mem_append key (bst_inorder left) ([key] @ bst_inorder right);
        lemma_list_to_set_mem key (bst_inorder t)
      end

#pop-options

(* ========================================================================
   Top-level Correctness Theorem
   ======================================================================== *)

//SNIPPET_START: theorem_insert_preserves_bst
let theorem_insert_preserves_bst (t: bst) (k: int)
  : Lemma
    (requires bst_valid t)
    (ensures (
      let t' = bst_insert t k in
      bst_valid t' /\
      FS.equal (key_set t') (FS.union (key_set t) (FS.singleton k)) /\
      FS.mem k (key_set t')
    ))
  = bst_insert_valid t k;
    insert_key_set_lemma t k;
    FS.all_finite_set_facts_lemma ()
//SNIPPET_END: theorem_insert_preserves_bst
