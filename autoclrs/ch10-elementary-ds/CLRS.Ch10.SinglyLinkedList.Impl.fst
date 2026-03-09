module CLRS.Ch10.SinglyLinkedList.Impl
// Singly-linked list — CLRS §10.2
// See CLRS.Ch10.DLL.Impl.fst for the true doubly-linked list with prev pointers.
//
// Representation: Each node is a heap-allocated box containing {key, next}.
// The list is a nullable pointer (option (box node)).
// The recursive predicate `is_dlist` matches on the logical list, similar to
// Pulse.Lib.LinkedList.is_list.
//
// LIST-INSERT(L, x): Insert at head, O(1)
// LIST-SEARCH(L, k): Traverse from head, O(n)
// LIST-DELETE(L, k): Delete by key, O(n) — combines LIST-SEARCH + LIST-DELETE
//
// Also includes ghost-tick instrumented variants with precise complexity bounds.
// NO admits. NO assumes.

#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module L = FStar.List.Tot
module GR = Pulse.Lib.GhostReference
open CLRS.Ch10.SinglyLinkedList.Base

// --- Operations ---

// CLRS §10.2 LIST-INSERT(L, x): Insert x at head
//   x.next = L.head
//   if L.head != NIL then L.head.prev = x
//   L.head = x
//   x.prev = NIL
//
// Note: We don't model prev in the predicate (see design note above),
// so the CLRS lines updating prev are elided from the proof obligation.
// The key structural change is: new head node → old list.
//SNIPPET_START: sll_list_insert
fn list_insert (x: int) (head: dlist)
  requires is_dlist head 'l
  returns new_head: dlist
  ensures is_dlist new_head (x :: 'l)
//SNIPPET_END: sll_list_insert
{
  // Allocate new node: key = x, next = old head
  let nd = Box.alloc #node { key = x; next = head };
  rewrite each head as ({ key = x; next = head }).next in (is_dlist head 'l);
  fold (is_dlist (Some nd) (x :: 'l));
  Some nd
}

// CLRS §10.2 LIST-SEARCH(L, k): Search by traversing from head
//   x = L.head
//   while x != NIL and x.key != k
//     x = x.next
//   return x
//SNIPPET_START: sll_list_search
fn rec list_search (head: dlist) (k: int)
  preserves is_dlist head 'l
  returns found: bool
  ensures pure (found <==> L.mem k 'l)
//SNIPPET_END: sll_list_search
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
      if (nd.key = k) {
        // Found it — restore the predicate and return true
        intro_is_dlist_cons head vl;
        true
      } else {
        // Recurse on tail
        let r = list_search nd.next k;
        intro_is_dlist_cons head vl;
        r
      }
    }
  }
}

// LIST-DELETE: Remove the first occurrence of key k from the list.
//SNIPPET_START: sll_list_delete
fn rec list_delete (head: dlist) (k: int)
  requires is_dlist head 'l
  returns new_head: dlist
  ensures is_dlist new_head (remove_first k 'l)
//SNIPPET_END: sll_list_delete
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
      if (nd.key = k) {
        // This is the node to delete — splice it out
        // Free the box and return its tail
        let tail = nd.next;
        with tl. rewrite (is_dlist nd.next tl) as (is_dlist tail tl);
        Box.free vl;
        tail
      } else {
        // Recurse on tail, then reconstruct
        let new_tail = list_delete nd.next k;
        with l'. assert (is_dlist new_tail l');
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

// ========== Complexity-tracked variants ==========
// Ghost-tick instrumented operations with exact bounds.
// Uses GhostReference.ref nat for the tick counter — fully erased at runtime.

let incr_nat (n: erased nat) : erased nat = hide (reveal n + 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

let insert_cost : nat = 1
let search_cost (n: nat) : nat = n
let delete_cost (n: nat) : nat = n + 1

// LIST-INSERT with complexity: Insert x at head, exactly 1 tick (O(1))
fn list_insert_tick (x: int) (head: dlist) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns new_head: dlist
  ensures exists* (cf: erased nat).
    is_dlist new_head (x :: 'l) ** GR.pts_to ctr cf **
    pure (reveal cf == reveal c0 + insert_cost)
{
  let nd = Box.alloc #node { key = x; next = head };
  tick ctr;
  rewrite each head as ({ key = x; next = head }).next in (is_dlist head 'l);
  fold (is_dlist (Some nd) (x :: 'l));
  Some nd
}

// LIST-SEARCH with complexity: at most n ticks (O(n))
fn rec list_search_tick (head: dlist) (k: int) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns found: bool
  ensures exists* (cf: erased nat).
    is_dlist head 'l ** GR.pts_to ctr cf **
    pure (
      found <==> L.mem k 'l /\
      reveal cf - reveal c0 <= search_cost (L.length 'l)
    )
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
        intro_is_dlist_cons head vl;
        true
      } else {
        let r = list_search_tick nd.next k ctr;
        intro_is_dlist_cons head vl;
        r
      }
    }
  }
}

// LIST-DELETE with complexity: at most n+1 ticks (O(n))
fn rec list_delete_tick (head: dlist) (k: int) (ctr: GR.ref nat)
  (#c0: erased nat)
  requires is_dlist head 'l ** GR.pts_to ctr c0
  returns new_head: dlist
  ensures exists* l' (cf: erased nat).
    is_dlist new_head l' ** GR.pts_to ctr cf **
    pure (
      (L.mem k 'l ==> l' == remove_first k 'l) /\
      (~(L.mem k 'l) ==> l' == 'l) /\
      reveal cf - reveal c0 <= delete_cost (L.length 'l)
    )
{
  match head {
    norewrite None -> {
      is_dlist_case_none head;
      head
    }
    norewrite Some vl -> {
      is_dlist_case_some head vl;
      with _nd _tl. _;
      let nd = !vl;
      tick ctr;
      if (nd.key = k) {
        let tail = nd.next;
        with tl. rewrite (is_dlist nd.next tl) as (is_dlist tail tl);
        Box.free vl;
        tail
      } else {
        let new_tail = list_delete_tick nd.next k ctr;
        with l' cf1. assert (is_dlist new_tail l' ** GR.pts_to ctr cf1);
        vl := { key = nd.key; next = new_tail };
        rewrite each new_tail as ({ key = nd.key; next = new_tail }).next
          in (is_dlist new_tail l');
        fold (is_dlist (Some vl) (nd.key :: l'));
        (Some vl)
      }
    }
  }
}
