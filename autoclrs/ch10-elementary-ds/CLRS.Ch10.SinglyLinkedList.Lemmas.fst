module CLRS.Ch10.SinglyLinkedList.Lemmas

(**
   Proofs of correctness lemmas about the pure Singly-Linked List specification.
   All lemmas reference CLRS.Ch10.SinglyLinkedList.Spec.
   
   NO admits. NO assumes.
*)

open FStar.List.Tot
open CLRS.Ch10.SinglyLinkedList.Spec

let lemma_insert_search (l: list int) (x: int)
  : Lemma (list_search (list_insert_head l x) x == true)
  = ()

let lemma_insert_search_other (l: list int) (x: int) (y: int)
  : Lemma (requires y <> x)
          (ensures list_search (list_insert_head l x) y == list_search l y)
  = ()

let rec lemma_delete_not_found (l: list int) (x: int)
  : Lemma (requires ~(list_search l x))
          (ensures list_delete l x == l)
  = match l with
    | [] -> ()
    | hd :: tl -> 
        assert (hd <> x);
        lemma_delete_not_found tl x

let lemma_delete_single_occurrence (l: list int) (x: int)
  : Lemma (requires count x l == 1)
          (ensures ~(list_search (list_delete l x) x))
  = CLRS.Ch10.SinglyLinkedList.Spec.lemma_delete_count l x;
    let l' = list_delete l x in
    assert (count x l' == 0);
    CLRS.Ch10.SinglyLinkedList.Spec.lemma_mem_count x l'

let lemma_insert_length (l: list int) (x: int)
  : Lemma (list_length (list_insert_head l x) == list_length l + 1)
  = ()

let lemma_delete_length_decreases (l: list int) (x: int)
  : Lemma (requires list_search l x)
          (ensures list_length (list_delete l x) == list_length l - 1)
  = CLRS.Ch10.SinglyLinkedList.Spec.lemma_delete_length l x

let lemma_insert_delete_head (l: list int) (x: int)
  : Lemma (list_delete (list_insert_head l x) x == l)
  = ()

let lemma_search_empty (x: int)
  : Lemma (list_search [] x == false)
  = ()

let lemma_delete_empty (x: int)
  : Lemma (list_delete [] x == [])
  = ()
