module CLRS.Ch10.DLL.Impl

(**
   Doubly-Linked List implementation interface — CLRS §10.2.

   Internal representation (node, dls segment predicate) is hidden.
   Clients interact through the abstract `dll` predicate and operations.

   Operations:
   - list_insert: Insert at head, O(1)
   - list_insert_tail: Insert at tail, O(1) runtime
   - list_search: Search by key (front-to-back), O(n)
   - list_search_back: Search by key (back-to-front), O(n)
   - list_search_ptr: Search returning pointer, O(n)
   - list_delete: Delete first occurrence of key, O(n)
   - list_delete_last: Delete last occurrence of key, O(n)
   - list_delete_node: Delete at index, O(n)
*)

#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box }
module L = FStar.List.Tot
open FStar.List.Tot

//SNIPPET_START: dll_node
/// Abstract node type — internal representation hidden
val node : Type0

/// DLL pointer: None for null, Some for a boxed node
let dptr = option (box node)
//SNIPPET_END: dll_node

//SNIPPET_START: dll_predicate
/// Abstract DLL predicate: hd and tl are head/tail pointers, l is the logical list
val dll (hd tl: dptr) (l: list int) : slprop
//SNIPPET_END: dll_predicate

/// Create an empty DLL
ghost
fn dll_nil (hd tl: dptr)
  requires pure (hd == None /\ tl == None)
  ensures dll hd tl []

/// Destroy an empty DLL
ghost
fn dll_nil_elim (hd tl: dptr)
  requires dll hd tl []
  ensures pure (hd == None /\ tl == None)

/// dll with hd==None implies l==[]
ghost
fn dll_none_nil (hd tl: dptr) (#l: erased (list int))
  preserves dll hd tl l
  requires pure (hd == None)
  ensures pure (l == ([] #int))

/// dll with Some? hd implies Cons? l
ghost
fn dll_some_cons (hd tl: dptr) (#l: erased (list int))
  preserves dll hd tl l
  requires pure (Some? hd)
  ensures pure (Cons? l)

/// Remove first occurrence of k from list
let rec remove_first (k: int) (l: list int) : list int =
  match l with
  | [] -> []
  | hd :: tl -> if hd = k then tl else hd :: remove_first k tl

/// Remove element at index i from list
let rec remove_at (i: nat) (l: list int) : list int =
  match l with
  | [] -> []
  | hd :: tl -> if i = 0 then tl else hd :: remove_at (i - 1) tl

/// Remove last occurrence of k from list
let rec remove_last (k: int) (l: list int) : list int =
  match l with
  | [] -> []
  | hd :: tl ->
    if mem k tl then hd :: remove_last k tl
    else if hd = k then tl
    else hd :: tl

//SNIPPET_START: dll_ops
/// LIST-INSERT: Insert x at head of the DLL, O(1)
fn list_insert (hd_ref tl_ref: ref dptr) (x: int) (#l: erased (list int))
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (x :: l)

/// LIST-INSERT-TAIL: Insert x at tail of the DLL, O(1) runtime
fn list_insert_tail (hd_ref tl_ref: ref dptr) (x: int) (#l: erased (list int))
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (l @ [x])

/// LIST-SEARCH: Search for key k (front-to-back), O(n)
fn list_search (hd tl: dptr) (k: int)
  preserves dll hd tl 'l
  returns found: bool
  ensures pure (found <==> L.mem k 'l)

/// LIST-SEARCH-BACK: Search for key k (back-to-front), O(n)
fn list_search_back (hd tl: dptr) (k: int)
  preserves dll hd tl 'l
  returns found: bool
  ensures pure (found <==> L.mem k 'l)

/// LIST-SEARCH returning pointer (Some if found, None if not)
fn list_search_ptr (hd tl: dptr) (k: int)
  preserves dll hd tl 'l
  returns result: dptr
  ensures pure (
    match result with
    | None -> ~(L.mem k 'l)
    | Some _ -> L.mem k 'l
  )

/// LIST-DELETE: Delete first occurrence of key k
fn list_delete (hd_ref tl_ref: ref dptr) (k: int) (#l: erased (list int))
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_first k l)

/// LIST-DELETE-LAST: Delete last occurrence of key k
fn list_delete_last (hd_ref tl_ref: ref dptr) (k: int) (#l: erased (list int))
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_last k l)

/// LIST-DELETE-NODE: Delete element at index i
fn list_delete_node
  (hd_ref tl_ref: ref dptr)
  (#l: erased (list int) {Cons? l})
  (i: nat {i < L.length l})
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_at i l)
//SNIPPET_END: dll_ops
