module CLRS.Ch10.SinglyLinkedList.Impl

(**
   Singly-linked list implementation — CLRS §10.2.
   
   Heap-allocated singly-linked list with operations:
   - list_insert: Insert at head, O(1)
   - list_search: Search by key, O(n)
   - list_delete: Delete by key, O(n)
   
   Also includes ghost-tick instrumented variants with precise complexity bounds:
   - list_insert_tick: exactly 1 tick (O(1))
   - list_search_tick: at most n ticks (O(n))
   - list_delete_tick: at most n+1 ticks (O(n))
   
   Uses the shared definitions from CLRS.Ch10.SinglyLinkedList.Base:
   node type, dlist alias, is_dlist predicate, remove_first.
*)

#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
module L = FStar.List.Tot
module GR = Pulse.Lib.GhostReference
open CLRS.Ch10.SinglyLinkedList.Base

//SNIPPET_START: sll_ops
/// LIST-INSERT(L, x): Insert x at head of the list
fn list_insert (x: int) (head: dlist)
  requires is_dlist head 'l
  returns new_head: dlist
  ensures is_dlist new_head (x :: 'l)

/// LIST-SEARCH(L, k): Search for key k in the list
fn list_search (head: dlist) (k: int)
  preserves is_dlist head 'l
  returns found: bool
  ensures pure (found <==> L.mem k 'l)

/// LIST-DELETE(L, k): Delete first occurrence of key k
fn list_delete (head: dlist) (k: int)
  requires is_dlist head 'l
  returns new_head: dlist
  ensures is_dlist new_head (remove_first k 'l)
//SNIPPET_END: sll_ops

// ========== Complexity-tracked variants ==========

let incr_nat (n: erased nat) : erased nat = hide (reveal n + 1)

/// INSERT cost: exactly 1 operation
let insert_cost : nat = 1

/// SEARCH cost: at most n comparisons
let search_cost (n: nat) : nat = n

/// DELETE cost: at most n comparisons + 1 pointer surgery
let delete_cost (n: nat) : nat = n + 1

//SNIPPET_START: sll_tick_ops
/// LIST-INSERT with complexity tracking: exactly 1 tick (O(1))
fn list_insert_tick (x: int) (head: dlist) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns new_head: dlist
  ensures exists* (cf: erased nat).
    is_dlist new_head (x :: 'l) ** GR.pts_to ctr cf **
    pure (reveal cf == reveal c0 + insert_cost)

/// LIST-SEARCH with complexity tracking: at most n ticks (O(n))
fn list_search_tick (head: dlist) (k: int) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns found: bool
  ensures exists* (cf: erased nat).
    is_dlist head 'l ** GR.pts_to ctr cf **
    pure (
      found <==> L.mem k 'l /\
      reveal cf - reveal c0 <= search_cost (L.length 'l)
    )

/// LIST-DELETE with complexity tracking: at most n+1 ticks (O(n))
fn list_delete_tick (head: dlist) (k: int) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns new_head: dlist
  ensures exists* (cf: erased nat).
    is_dlist new_head (remove_first k 'l) ** GR.pts_to ctr cf **
    pure (
      reveal cf - reveal c0 <= delete_cost (L.length 'l)
    )
//SNIPPET_END: sll_tick_ops
