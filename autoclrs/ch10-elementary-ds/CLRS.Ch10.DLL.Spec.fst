module CLRS.Ch10.DLL.Spec

(**
   Pure functional specification for Doubly-Linked List from CLRS §10.2.
   
   At the pure specification level, a DLL is modeled as a list int.
   The doubly-linked pointer structure is an implementation concern handled
   in CLRS.Ch10.DLL (the Pulse implementation).
   
   Operations: insert at head (O(1)), search by key (O(n)),
   delete by key (O(n)), delete at index (O(n)).
*)

open FStar.List.Tot

/// Abstract DLL type: a list of integers
type dll_spec = list int

/// Empty DLL
let dll_empty : dll_spec = []

/// Insert element at head (CLRS LIST-INSERT)
let dll_insert (l: dll_spec) (x: int) : dll_spec =
  x :: l

/// Search for element (CLRS LIST-SEARCH)
let dll_search (l: dll_spec) (x: int) : bool =
  mem x l

/// Delete first occurrence of element (CLRS LIST-DELETE by key)
let rec dll_delete (l: dll_spec) (x: int) : dll_spec =
  match l with
  | [] -> []
  | hd :: tl -> if hd = x then tl else hd :: dll_delete tl x

/// Delete element at index (CLRS LIST-DELETE by position)
let rec dll_delete_at (i: nat) (l: dll_spec) : dll_spec =
  match l with
  | [] -> []
  | hd :: tl -> if i = 0 then tl else hd :: dll_delete_at (i - 1) tl

/// Length of DLL
let dll_length (l: dll_spec) : nat =
  length l

/// Insert at tail (CLRS doubly-linked list advantage)
let dll_insert_tail (l: dll_spec) (x: int) : dll_spec =
  l @ [x]

/// Delete last occurrence of element
let rec dll_delete_last (l: dll_spec) (x: int) : dll_spec =
  match l with
  | [] -> []
  | hd :: tl ->
    if mem x tl then hd :: dll_delete_last tl x
    else if hd = x then tl
    else hd :: tl

/// Remove last occurrence (standalone, matches dll_delete_last)
let rec remove_last (k: int) (l: list int) : list int =
  match l with
  | [] -> []
  | hd :: tl ->
    if mem k tl then hd :: remove_last k tl
    else if hd = k then tl
    else hd :: tl
