(*
   Common list helper lemmas shared across Chapter 10 data structures.
   
   These lemmas about list append/indexing are used by Stack, Queue,
   and LinkedList implementations.
*)
module CLRS.Common.ListLemmas

open FStar.List.Tot

// Length of append
let rec lemma_append_length (#a:Type) (l1 l2: list a)
  : Lemma (length (append l1 l2) == length l1 + length l2)
  = match l1 with
    | [] -> ()
    | _ :: xs -> lemma_append_length xs l2

// Indexing into append
let rec lemma_index_append (#a:Type) (l1 l2: list a) (i:nat)
  : Lemma 
    (requires i < length (append l1 l2))
    (ensures 
      (if i < length l1 
       then index (append l1 l2) i == index l1 i
       else (i - length l1 < length l2 /\
             index (append l1 l2) i == index l2 (i - length l1))))
    (decreases l1)
  = match l1 with
    | [] -> ()
    | _ :: xs -> if i = 0 then () else lemma_index_append xs l2 (i - 1)
