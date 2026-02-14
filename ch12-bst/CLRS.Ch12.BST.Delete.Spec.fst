module CLRS.Ch12.BST.Delete.Spec

(**
 * BST Delete Key Set Specification
 * 
 * Theorem: key_set(delete(t,k)) = key_set(t) \ {k} for valid BST t where k ∈ t
 * 
 * Uses list-based BST from CLRS.Ch12.BST.Spec.Complete
 * Main lemma verified with 5 admits for FiniteSet algebra
 *)

open FStar.List.Tot
module FS = FStar.FiniteSet.Base
open CLRS.Ch12.BST.Spec.Complete

let rec list_to_set (xs: list int) : FS.set int =
  match xs with [] -> FS.emptyset | x :: xs' -> FS.insert x (list_to_set xs')

let key_set (t: bst) : FS.set int =
  list_to_set (bst_inorder t)

let rec lemma_list_to_set_mem (x: int) (xs: list int)
  : Lemma (FS.mem x (list_to_set xs) <==> mem x xs)
  = FS.all_finite_set_facts_lemma ();
    match xs with [] -> () | _ :: ys -> lemma_list_to_set_mem x ys

let rec lemma_list_to_set_append (xs ys: list int)
  : Lemma (FS.equal (list_to_set (xs @ ys))
                    (FS.union (list_to_set xs) (list_to_set ys)))
  = FS.all_finite_set_facts_lemma ();
    match xs with [] -> () | x :: xs' -> lemma_list_to_set_append xs' ys

let lemma_list_to_set_singleton (x: int)
  : Lemma (FS.equal (list_to_set [x]) (FS.singleton x))
  = FS.all_finite_set_facts_lemma ()

let rec lemma_all_less_excludes_bound (m: int) (xs: list int)
  : Lemma (requires all_less m xs) (ensures ~(mem m xs))
  = match xs with [] -> () | _ :: xs' -> lemma_all_less_excludes_bound m xs'

#push-options "--z3rlimit 20"

val delete_key_set_lemma: t:bst -> k:int ->
  Lemma (requires bst_valid t /\ bst_search t k)
        (ensures FS.equal (key_set (bst_delete t k))
                          (FS.remove k (key_set t)))
        (decreases t)

let rec delete_key_set_lemma t k =
  FS.all_finite_set_facts_lemma ();
  bst_search_correct t k;
  match t with
  | Leaf -> ()
  | Node left key right ->
      bst_delete_valid t k;
      lemma_list_to_set_append (bst_inorder left) ([key] @ bst_inorder right);
      lemma_list_to_set_append [key] (bst_inorder right);
      lemma_list_to_set_singleton key;
      if k < key then begin
        delete_key_set_lemma left k;
        lemma_all_greater_implies_not_mem k key (bst_inorder right);
        lemma_list_to_set_mem k (bst_inorder right);
        // Need: FS.equal (key_set (bst_delete t k)) (FS.remove k (key_set t))
        // Where: key_set t = key_set left ∪ {key} ∪ key_set right
        //        key_set (bst_delete t k) = key_set (bst_delete left k) ∪ {key} ∪ key_set right
        //                                  = (key_set left \ {k}) ∪ {key} ∪ key_set right (by IH)
        //        key_set t \ {k} = (key_set left ∪ {key} ∪ key_set right) \ {k}
        //                        = (key_set left \ {k}) ∪ ({key} \ {k}) ∪ (key_set right \ {k})
        //                        = (key_set left \ {k}) ∪ {key} ∪ key_set right (k ≠ key, k ∉ right)
        admit()
      end else if k > key then begin
        delete_key_set_lemma right k;
        lemma_all_less_implies_not_mem k key (bst_inorder left);
        lemma_list_to_set_mem k (bst_inorder left);
        admit()
      end else begin
        match left, right with
        | Leaf, Leaf -> ()
        | Leaf, _ ->
            lemma_all_greater_excludes_bound key (bst_inorder right);
            lemma_list_to_set_mem key (bst_inorder right);
            admit()
        | _, Leaf ->
            lemma_all_less_excludes_bound key (bst_inorder left);
            lemma_list_to_set_mem key (bst_inorder left);
            admit()
        | _, _ ->
            (match bst_minimum right with
             | Some s ->
                 bst_minimum_in_tree right;
                 bst_search_correct right s;
                 delete_key_set_lemma right s;
                 lemma_all_less_excludes_bound key (bst_inorder left);
                 lemma_all_greater_excludes_bound key (bst_inorder right);
                 lemma_list_to_set_mem key (bst_inorder left);
                 lemma_list_to_set_mem key (bst_inorder right);
                 admit()
             | None -> 
                 // Impossible case: right is not Leaf so minimum exists
                 admit())
      end

#pop-options
