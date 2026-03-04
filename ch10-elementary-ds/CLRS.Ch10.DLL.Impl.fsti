module CLRS.Ch10.DLL.Impl

(**
   Doubly-Linked List implementation interface — CLRS §10.2.
   
   True DLL with prev and next pointers. Segment predicate `dls` for
   non-empty segments, `dll` for full lists.
   
   Operations:
   - list_insert: Insert at head, O(1)
   - list_search: Search by key, O(n)
   - list_search_ptr: Search returning pointer, O(n)
   - list_delete: Delete by key, O(n)
   - list_delete_node: Delete at index, O(n)
*)

#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module L = FStar.List.Tot
open FStar.List.Tot

//SNIPPET_START: dll_node
noeq
type node = {
  key:  int;
  prev: option (box node);
  next: option (box node);
}

let dptr = option (box node)
//SNIPPET_END: dll_node

//SNIPPET_START: dll_dls
let rec dls
  ([@@@mkey] p: box node)
  (l: list int {Cons? l})
  (prev_ptr: dptr)
  (tail: box node)
  (last_ptr: dptr)
  : Tot slprop (decreases l)
  = match l with
    | [k] ->
      exists* (v: node).
        pts_to p v **
        pure (v.key == k /\ v.prev == prev_ptr /\
              v.next == last_ptr /\ p == tail)
    | k :: rest ->
      exists* (v: node) (np: box node).
        pts_to p v **
        dls np rest (Some p) tail last_ptr **
        pure (v.key == k /\ v.prev == prev_ptr /\
              v.next == Some np)

let dll (hd tl: dptr) (l: list int) : slprop =
  match l with
  | [] -> pure (hd == None /\ tl == None)
  | k :: rest ->
    exists* (hp tp: box node).
      dls hp (k :: rest) None tp None **
      pure (hd == Some hp /\ tl == Some tp)
//SNIPPET_END: dll_dls

/// dll hd==None ↔ l==[]
ghost
fn dll_none_nil (hd tl: dptr) (#l: erased (list int))
  preserves dll hd tl l
  requires pure (hd == None)
  ensures pure (l == ([] #int))

/// dll hd==Some → Cons? l
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

//SNIPPET_START: dll_ops
/// LIST-INSERT: Insert x at head of the DLL
fn list_insert (hd_ref tl_ref: ref dptr) (x: int)
  requires exists* hd tl l.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl' l.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (x :: l)

/// LIST-SEARCH: Search for key k in the DLL
fn list_search (hd tl: dptr) (k: int)
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
fn list_delete (hd_ref tl_ref: ref dptr) (k: int)
  requires exists* hd tl l.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl' l.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_first k l)

/// LIST-DELETE-NODE: Delete element at index i
fn list_delete_node
  (hd_ref tl_ref: ref dptr) (x: box node)
  (#l: erased (list int) {Cons? l})
  (i: nat {i < L.length l})
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_at i l)
//SNIPPET_END: dll_ops
