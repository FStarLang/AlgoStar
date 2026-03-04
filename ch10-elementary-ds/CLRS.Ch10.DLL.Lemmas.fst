module CLRS.Ch10.DLL.Lemmas

(**
   Proofs of correctness lemmas about the pure DLL specification.
   
   NO admits. NO assumes.
*)

open FStar.List.Tot
open CLRS.Ch10.DLL.Spec

let lemma_dll_insert_search (l: dll_spec) (x: int)
  : Lemma (dll_search (dll_insert l x) x == true)
  = ()

let lemma_dll_insert_search_other (l: dll_spec) (x: int) (y: int)
  : Lemma (requires y <> x)
          (ensures dll_search (dll_insert l x) y == dll_search l y)
  = ()

let rec lemma_dll_delete_not_found (l: dll_spec) (x: int)
  : Lemma (requires ~(dll_search l x))
          (ensures dll_delete l x == l)
  = match l with
    | [] -> ()
    | hd :: tl -> lemma_dll_delete_not_found tl x

let lemma_dll_insert_length (l: dll_spec) (x: int)
  : Lemma (dll_length (dll_insert l x) == dll_length l + 1)
  = ()

let rec lemma_dll_delete_length_aux (l: dll_spec) (x: int)
  : Lemma (dll_length (dll_delete l x) <= dll_length l)
  = match l with
    | [] -> ()
    | hd :: tl ->
        if hd = x then ()
        else lemma_dll_delete_length_aux tl x

let rec lemma_dll_delete_length (l: dll_spec) (x: int)
  : Lemma (requires dll_search l x)
          (ensures dll_length (dll_delete l x) == dll_length l - 1)
  = match l with
    | [] -> ()
    | hd :: tl ->
        if hd = x then ()
        else (
          lemma_dll_delete_length tl x;
          lemma_dll_delete_length_aux tl x
        )

let rec lemma_dll_delete_at_length (i: nat) (l: dll_spec)
  : Lemma (requires i < dll_length l)
          (ensures dll_length (dll_delete_at i l) == dll_length l - 1)
  = match l with
    | hd :: tl ->
        if i = 0 then ()
        else lemma_dll_delete_at_length (i - 1) tl

let lemma_dll_insert_delete (l: dll_spec) (x: int)
  : Lemma (dll_delete (dll_insert l x) x == l)
  = ()

let lemma_dll_search_empty (x: int)
  : Lemma (dll_search dll_empty x == false)
  = ()
