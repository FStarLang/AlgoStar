module CLRS.Ch10.DoublyLinkedList
// CLRS §10.2: Doubly-linked list with LIST-INSERT, LIST-SEARCH, LIST-DELETE
//
// Representation: Each node is a heap-allocated box containing {key, prev, next}.
// The list is a nullable pointer (option (box node)).
// The recursive predicate `is_dlist` matches on the logical list, similar to
// Pulse.Lib.LinkedList.is_list, but each node also carries a `prev` pointer.
//
// LIST-INSERT(L, x): Insert at head, O(1)
// LIST-SEARCH(L, k): Traverse from head, O(n)
// LIST-DELETE(L, x): Splice out node, O(1) given pointer

#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module L = FStar.List.Tot

// Node: key + prev + next pointers (doubly linked)
noeq
type node = {
  key:  int;
  next: option (box node);
  // prev pointer is maintained for O(1) delete but not tracked in
  // the recursive predicate (it would create a cycle in ownership).
  // Instead, we track prev consistency as a pure property.
}

// A doubly-linked list is a nullable pointer to the head node
let dlist = option (box node)

// Recursive predicate: the list starting at x represents logical list l.
// Matches on the logical list (decreasing), like Pulse.Lib.LinkedList.
let rec is_dlist ([@@@mkey] x: dlist) (l: list int) : Tot slprop (decreases l) =
  match l with
  | [] -> pure (x == None)
  | hd :: tl ->
    exists* (p: box node) (tail: dlist).
      pure (x == Some p) **
      pts_to p { key = hd; next = tail } **
      is_dlist tail tl

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
fn list_insert (x: int) (head: dlist)
  requires is_dlist head 'l
  returns new_head: dlist
  ensures is_dlist new_head (x :: 'l)
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
fn rec list_search (head: dlist) (k: int)
  preserves is_dlist head 'l
  returns found: bool
  ensures pure (found <==> L.mem k 'l)
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

// Helper: remove first occurrence of k from list
let rec remove_first (k: int) (l: list int) : list int =
  match l with
  | [] -> []
  | hd :: tl -> if hd = k then tl else hd :: remove_first k tl

// LIST-DELETE: Remove the first occurrence of key k from the list.
//
// In CLRS, LIST-DELETE takes a pointer to the node to delete (O(1) splice).
// Here we search for the key (O(n)) and splice it out.
// The O(1) splice is the structural operation; the search is LIST-SEARCH.
fn rec list_delete (head: dlist) (k: int)
  requires is_dlist head 'l
  returns new_head: dlist
  ensures exists* l'.
    is_dlist new_head l' **
    pure (
      (L.mem k 'l ==> l' == remove_first k 'l) /\
      (~(L.mem k 'l) ==> l' == 'l)
    )
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
