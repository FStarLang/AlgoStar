module CLRS.Ch10.SinglyLinkedList.Lemmas

(**
   Proofs of correctness lemmas about the pure Singly-Linked List specification.
   
   Proves properties about list_insert_head, list_search, list_delete:
   - Insert makes element searchable
   - Delete correctness (single occurrence, not found)
   - Length invariants
   
   Based on the specification in CLRS.Ch10.SinglyLinkedList.Spec.
*)

open FStar.List.Tot
open CLRS.Ch10.SinglyLinkedList.Spec

/// Inserting x makes x searchable
val lemma_insert_search (l: list int) (x: int)
  : Lemma (list_search (list_insert_head l x) x == true)

/// Inserting x doesn't affect search for different element
val lemma_insert_search_other (l: list int) (x: int) (y: int)
  : Lemma (requires y <> x)
          (ensures list_search (list_insert_head l x) y == list_search l y)

/// Deleting non-existent element is identity
val lemma_delete_not_found (l: list int) (x: int)
  : Lemma (requires ~(list_search l x))
          (ensures list_delete l x == l)

/// Deleting single occurrence removes it
val lemma_delete_single_occurrence (l: list int) (x: int)
  : Lemma (requires count x l == 1)
          (ensures ~(list_search (list_delete l x) x))

/// Insert increases length by 1
val lemma_insert_length (l: list int) (x: int)
  : Lemma (list_length (list_insert_head l x) == list_length l + 1)

/// Delete of found element decreases length by exactly 1
val lemma_delete_length_decreases (l: list int) (x: int)
  : Lemma (requires list_search l x)
          (ensures list_length (list_delete l x) == list_length l - 1)

/// Inserting then deleting same element removes it from head
val lemma_insert_delete_head (l: list int) (x: int)
  : Lemma (list_delete (list_insert_head l x) x == l)

/// Search in empty list returns false
val lemma_search_empty (x: int)
  : Lemma (list_search [] x == false)

/// Delete from empty list returns empty
val lemma_delete_empty (x: int)
  : Lemma (list_delete [] x == [])
