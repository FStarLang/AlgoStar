(*
   Singly-linked list with Complexity Bounds (CLRS Chapter 10)
   
   Extends CLRS.Ch10.SinglyLinkedList with ghost tick counters to track
   the number of operations performed by each function.
   
   Proves:
   1. list_insert: exactly 1 tick (O(1))
   2. list_search: at most |l| ticks (O(n))
   3. list_delete: at most |l| ticks (O(n))
   
   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   
   NO admits. NO assumes.
*)

module CLRS.Ch10.SinglyLinkedList.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module L = FStar.List.Tot
module GR = Pulse.Lib.GhostReference
open CLRS.Ch10.SinglyLinkedList.Base

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Operations with Complexity ==========

// LIST-INSERT with complexity: Insert x at head, exactly 1 tick (O(1))
//SNIPPET_START: dll_insert_tick
fn list_insert_tick (x: int) (head: dlist) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns new_head: dlist
  ensures exists* (cf: erased nat).
    is_dlist new_head (x :: 'l) ** GR.pts_to ctr cf **
    pure (reveal cf == reveal c0 + 1)
//SNIPPET_END: dll_insert_tick
{
  // Allocate new node: key = x, next = old head
  let nd = Box.alloc #node { key = x; next = head };
  tick ctr;
  rewrite each head as ({ key = x; next = head }).next in (is_dlist head 'l);
  fold (is_dlist (Some nd) (x :: 'l));
  Some nd
}

// LIST-SEARCH with complexity: at most |l| ticks (O(n))
//SNIPPET_START: dll_search_tick
fn rec list_search_tick (head: dlist) (k: int) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns found: bool
  ensures exists* (cf: erased nat).
    is_dlist head 'l ** GR.pts_to ctr cf **
    pure (found <==> L.mem k 'l /\ reveal cf - reveal c0 <= L.length 'l)
//SNIPPET_END: dll_search_tick
{
  match head {
    norewrite None -> {
      is_dlist_case_none head;
      false
    }
    norewrite Some vl -> {
      is_dlist_case_some head vl;
      with _nd _tl. _;
      let nd = !vl;
      tick ctr;
      if (nd.key = k) {
        // Found it — restore the predicate and return true
        intro_is_dlist_cons head vl;
        true
      } else {
        // Recurse on tail
        let r = list_search_tick nd.next k ctr;
        intro_is_dlist_cons head vl;
        r
      }
    }
  }
}

// LIST-DELETE with complexity: at most |l| ticks (O(n))
//SNIPPET_START: dll_delete_tick
fn rec list_delete_tick (head: dlist) (k: int) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns new_head: dlist
  ensures exists* l' (cf: erased nat).
    is_dlist new_head l' ** GR.pts_to ctr cf **
    pure (
      (L.mem k 'l ==> l' == remove_first k 'l) /\
      (~(L.mem k 'l) ==> l' == 'l) /\
      reveal cf - reveal c0 <= L.length 'l
    )
//SNIPPET_END: dll_delete_tick
{
  match head {
    norewrite None -> {
      is_dlist_case_none head;
      // l == [], key k is not in list, return head unchanged
      head
    }
    norewrite Some vl -> {
      is_dlist_case_some head vl;
      with _nd _tl. _;
      let nd = !vl;
      tick ctr;
      if (nd.key = k) {
        // This is the node to delete — splice it out
        // Free the box and return its tail
        let tail = nd.next;
        with tl. rewrite (is_dlist nd.next tl) as (is_dlist tail tl);
        Box.free vl;
        tail
      } else {
        // Recurse on tail, then reconstruct
        let new_tail = list_delete_tick nd.next k ctr;
        with l' cf1. assert (is_dlist new_tail l' ** GR.pts_to ctr cf1);
        // Update the node to point to new_tail
        vl := { key = nd.key; next = new_tail };
        rewrite each new_tail as ({ key = nd.key; next = new_tail }).next
          in (is_dlist new_tail l');
        fold (is_dlist (Some vl) (nd.key :: l'));
        (Some vl)
      }
    }
  }
}
