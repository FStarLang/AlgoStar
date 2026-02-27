module CLRS.Ch12.BST.KeySet

(**
 * Shared Key Set Definitions for BST Specifications
 *
 * Provides list_to_set, key_set, and associated lemmas used by both
 * Insert.Spec and Delete.Spec.
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
    match xs with [] -> () | _ :: xs' -> lemma_list_to_set_append xs' ys

let lemma_list_to_set_singleton (x: int)
  : Lemma (FS.equal (list_to_set [x]) (FS.singleton x))
  = FS.all_finite_set_facts_lemma ()
