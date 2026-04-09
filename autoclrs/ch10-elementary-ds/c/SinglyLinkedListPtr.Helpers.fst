(*
   Helper module for pointer-based singly linked list.
   
   Defines the recursive is_list predicate connecting
   a ref struct_node chain to a logical F* list, plus
   list operations (insert) written in Pulse.
   
   Uses the c2pulse-generated struct_node type and operations
   from SinglyLinkedListPtr.
*)
module SinglyLinkedListPtr.Helpers
#lang-pulse
open Pulse
open Pulse.Lib.C
open SinglyLinkedListPtr

module L = FStar.List.Tot

(* Recursive predicate: the ref chain starting at head represents list l.
   We use list Int32.t to avoid coercion issues between int and Int32.int_t.
   Each non-null node is freeable (owns pts_to + freeable). *)
let rec is_list ([@@@mkey] head: ref struct_node) (l: list Int32.t)
  : Tot slprop (decreases l)
= match l with
  | [] -> pure (is_null head)
  | hd :: tl ->
    exists* (nd: struct_node).
      pure (not (is_null head)) **
      pts_to head nd **
      freeable head **
      pure (nd.struct_node__data == hd) **
      is_list nd.struct_node__next tl

(* --- Ghost boilerplate for fold/unfold --- *)

ghost fn elim_is_list_nil (head: ref struct_node)
  requires is_list head 'l ** pure ('l == [])
  ensures pure (is_null head)
{
  rewrite each 'l as ([] #Int32.t);
  unfold (is_list head [])
}

ghost fn intro_is_list_nil (head: ref struct_node)
  requires pure (is_null head)
  ensures is_list head []
{
  fold (is_list head ([] #Int32.t))
}

ghost fn elim_is_list_cons (head: ref struct_node) (hd: Int32.t) (tl: list Int32.t)
  requires is_list head (hd :: tl)
  ensures exists* (nd: struct_node).
    pure (not (is_null head)) **
    pts_to head nd **
    freeable head **
    pure (nd.struct_node__data == hd) **
    is_list nd.struct_node__next tl
{
  unfold (is_list head (hd :: tl))
}

ghost fn intro_is_list_cons
  (head: ref struct_node)
  (nd: struct_node)
  (tl: list Int32.t)
  requires
    pure (not (is_null head)) **
    pts_to head nd **
    freeable head **
    is_list nd.struct_node__next tl
  ensures is_list head (nd.struct_node__data :: tl)
{
  fold (is_list head (nd.struct_node__data :: tl))
}

(* --- List operations --- *)

(*
 * LIST-INSERT: Allocate a new node with key x and prepend it to the list.
 * Returns the new head pointer.
 *
 * Corresponds to CLRS LIST-INSERT(L, x): set x.next = L.head; L.head = x
 *)
fn list_insert (head: ref struct_node) (x: Int32.t) (#l: list Int32.t)
  requires is_list head l
  returns new_head: ref struct_node
  ensures is_list new_head (x :: l)
{
  let n = Pulse.Lib.C.Ref.alloc_ref #struct_node ();
  n := { struct_node__data = x; struct_node__next = head };
  Pulse.Lib.Reference.pts_to_not_null n;
  intro_is_list_cons n { struct_node__data = x; struct_node__next = head } l;
  n
}
