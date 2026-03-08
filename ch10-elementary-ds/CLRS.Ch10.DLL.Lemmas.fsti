module CLRS.Ch10.DLL.Lemmas

(**
   Proofs of correctness lemmas about the pure DLL specification.
   
   At the pure specification level, DLL operations are identical to
   linked list operations on list int. These lemmas prove correctness
   of insert, search, delete, and delete-at-index.
*)

open FStar.List.Tot
open CLRS.Ch10.DLL.Spec

/// Inserting x makes x searchable
val lemma_dll_insert_search (l: dll_spec) (x: int)
  : Lemma (dll_search (dll_insert l x) x == true)

/// Inserting x preserves searchability of other elements
val lemma_dll_insert_search_other (l: dll_spec) (x: int) (y: int)
  : Lemma (requires y <> x)
          (ensures dll_search (dll_insert l x) y == dll_search l y)

/// Delete of non-existent element is identity
val lemma_dll_delete_not_found (l: dll_spec) (x: int)
  : Lemma (requires ~(dll_search l x))
          (ensures dll_delete l x == l)

/// Insert increases length by 1
val lemma_dll_insert_length (l: dll_spec) (x: int)
  : Lemma (dll_length (dll_insert l x) == dll_length l + 1)

/// Delete of found element decreases length by 1
val lemma_dll_delete_length (l: dll_spec) (x: int)
  : Lemma (requires dll_search l x)
          (ensures dll_length (dll_delete l x) == dll_length l - 1)

/// Delete at valid index decreases length by 1
val lemma_dll_delete_at_length (i: nat) (l: dll_spec)
  : Lemma (requires i < dll_length l)
          (ensures dll_length (dll_delete_at i l) == dll_length l - 1)

/// Insert then delete same element restores original list
val lemma_dll_insert_delete (l: dll_spec) (x: int)
  : Lemma (dll_delete (dll_insert l x) x == l)

/// Search in empty DLL returns false
val lemma_dll_search_empty (x: int)
  : Lemma (dll_search dll_empty x == false)

/// Insert at tail increases length by 1
val lemma_dll_insert_tail_length (l: dll_spec) (x: int)
  : Lemma (dll_length (dll_insert_tail l x) == dll_length l + 1)

/// Insert at tail makes x searchable
val lemma_dll_insert_tail_search (l: dll_spec) (x: int)
  : Lemma (dll_search (dll_insert_tail l x) x == true)

/// Delete-last of non-existent element is identity
val lemma_dll_delete_last_not_found (l: dll_spec) (x: int)
  : Lemma (requires ~(dll_search l x))
          (ensures dll_delete_last l x == l)

/// Delete-last of found element decreases length by 1
val lemma_dll_delete_last_length (l: dll_spec) (x: int)
  : Lemma (requires dll_search l x)
          (ensures dll_length (dll_delete_last l x) == dll_length l - 1)
