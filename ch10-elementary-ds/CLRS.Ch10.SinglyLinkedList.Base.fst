(*
   Shared definitions for singly-linked list implementations (CLRS §10.2).
   
   Contains: node type, dlist type alias, is_dlist recursive predicate,
   ghost boilerplate (fold/unfold helpers), and remove_first.
   
   Used by: SinglyLinkedList.fst, SinglyLinkedList.Complexity.fst,
            SinglyLinkedList.Complexity.Enhanced.fst
*)

module CLRS.Ch10.SinglyLinkedList.Base
#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module L = FStar.List.Tot

// Node: key + next pointer (singly linked)
//SNIPPET_START: sll_node
noeq
type node = {
  key:  int;
  next: option (box node);
}

// A singly-linked list is a nullable pointer to the head node
let dlist = option (box node)
//SNIPPET_END: sll_node

// Recursive predicate: the list starting at x represents logical list l.
//SNIPPET_START: sll_is_dlist
let rec is_dlist ([@@@mkey] x: dlist) (l: list int) : Tot slprop (decreases l) =
  match l with
  | [] -> pure (x == None)
  | hd :: tl ->
    exists* (p: box node) (tail: dlist).
      pure (x == Some p) **
      pts_to p { key = hd; next = tail } **
      is_dlist tail tl
//SNIPPET_END: sll_is_dlist

// --- Boilerplate ghost functions for fold/unfold ---

ghost
fn elim_is_dlist_nil (x: dlist)
  requires is_dlist x 'l
  requires pure ('l == [])
  ensures pure (x == None)
{
  rewrite each 'l as ([] #int);
  unfold (is_dlist x [])
}

ghost
fn intro_is_dlist_nil (x: dlist)
  requires pure (x == None)
  ensures is_dlist x []
{
  fold (is_dlist x ([] #(int)))
}

ghost
fn intro_is_dlist_cons (x: dlist) (v: box node) (#nd: node) (#tl: list int)
  requires pts_to v nd **
           is_dlist nd.next tl **
           pure (x == Some v)
  ensures is_dlist x (nd.key :: tl)
{
  rewrite (pts_to v nd) as (pts_to v { key = nd.key; next = nd.next });
  fold (is_dlist x (nd.key :: tl))
}

// Match on l to determine if x is None or Some
let is_dlist_cases (x: dlist) (l: list int) : slprop =
  match x with
  | None -> pure (l == [])
  | Some v ->
    exists* (nd: node) (tl: list int).
      pts_to v nd **
      pure (l == nd.key :: tl) **
      is_dlist nd.next tl

ghost
fn cases_of_is_dlist (x: dlist) (l: list int)
  requires is_dlist x l
  ensures is_dlist_cases x l
{
  match l {
    [] -> {
      unfold (is_dlist x []);
      fold (is_dlist_cases None l);
      rewrite each (None #(box node)) as x
    }
    head :: tl -> {
      unfold (is_dlist x (head :: tl));
      with w tail. _;
      let v = Some?.v x;
      rewrite each w as v;
      rewrite each tail as ({ key = head; next = tail }).next in (is_dlist tail tl);
      fold (is_dlist_cases (Some v) l);
      rewrite each (Some #(box node) v) as x
    }
  }
}

ghost
fn is_dlist_case_none (x: dlist) (#l: list int)
  preserves is_dlist x l
  requires pure (x == None)
  ensures pure (l == [])
{
  cases_of_is_dlist x l;
  rewrite each x as (None #(box node));
  unfold (is_dlist_cases None l);
  fold (is_dlist x ([] #int));
  rewrite is_dlist x [] as is_dlist x l
}

ghost
fn is_dlist_case_some (x: dlist) (v: box node) (#l: list int)
  requires is_dlist x l
  requires pure (x == Some v)
  ensures exists* (nd: node) (tl: list int).
    pts_to v nd **
    is_dlist nd.next tl **
    pure (l == nd.key :: tl)
{
  cases_of_is_dlist x l;
  rewrite each x as (Some v);
  unfold (is_dlist_cases (Some v) l)
}

// Remove first occurrence of k from list
let rec remove_first (k: int) (l: list int) : list int =
  match l with
  | [] -> []
  | hd :: tl -> if hd = k then tl else hd :: remove_first k tl
