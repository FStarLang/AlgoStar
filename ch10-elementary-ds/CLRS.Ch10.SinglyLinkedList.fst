module CLRS.Ch10.SinglyLinkedList
// Singly-linked list — CLRS §10.2
// See CLRS.Ch10.DLL.fst for the true doubly-linked list with prev pointers.
//
// Representation: Each node is a heap-allocated box containing {key, next}.
// The list is a nullable pointer (option (box node)).
// The recursive predicate `is_dlist` matches on the logical list, similar to
// Pulse.Lib.LinkedList.is_list.
//
// LIST-INSERT(L, x): Insert at head, O(1)
// LIST-SEARCH(L, k): Traverse from head, O(n)
// LIST-DELETE(L, k): Delete by key, O(n) — combines LIST-SEARCH + LIST-DELETE

#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module L = FStar.List.Tot
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
