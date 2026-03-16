module CLRS.Ch10.DLL.Impl
// CLRS §10.2: True Doubly-Linked List
//
// Nodes have {key, prev, next}. Segment predicate `dls` from Pulse.Lib.Deque.
// Operations: LIST-INSERT (O(1)), LIST-INSERT-TAIL (O(1) runtime),
//             LIST-SEARCH (O(n)), LIST-SEARCH-BACK (O(n)),
//             LIST-DELETE (O(n)), LIST-DELETE-LAST (O(n)),
//             LIST-DELETE-NODE (O(n) traversal to index, O(1) pointer surgery)
//
// All operations fully verified with 0 admits.

#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module L = FStar.List.Tot
open FStar.List.Tot

// === Internal types (hidden from .fsti) ===

//SNIPPET_START: dll_node_internal
noeq
type node = {
  key:  int;
  prev: option (box node);
  next: option (box node);
}
//SNIPPET_END: dll_node_internal

// === Internal segment predicate ===

//SNIPPET_START: dll_dls_internal
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
//SNIPPET_END: dll_dls_internal

// === Ghost helpers for empty dll (exposed in .fsti) ===

ghost
fn dll_nil (hd tl: dptr)
  requires pure (hd == None /\ tl == None)
  ensures dll hd tl []
{
  fold (dll hd tl ([] #int))
}

ghost
fn dll_nil_elim (hd tl: dptr)
  requires dll hd tl []
  ensures pure (hd == None /\ tl == None)
{
  unfold (dll hd tl ([] #int))
}

// dll hd==None ↔ l==[]
ghost
fn dll_none_nil (hd tl: dptr) (#l: erased (list int))
  preserves dll hd tl l
  requires pure (hd == None)
  ensures pure (l == ([] #int))
{
  let ll = reveal l;
  match ll {
    [] -> { () }
    k :: rest -> {
      rewrite each l as (k :: rest) in (dll hd tl l);
      unfold (dll hd tl (k :: rest));
      // Pure: hd == Some hp, but hd == None -> contradiction
      unreachable ()
    }
  }
}

// dll hd==Some → Cons? l
ghost
fn dll_some_cons (hd tl: dptr) (#l: erased (list int))
  preserves dll hd tl l
  requires pure (Some? hd)
  ensures pure (Cons? l)
{
  let ll = reveal l;
  match ll {
    [] -> {
      rewrite each l as ([] #int) in (dll hd tl l);
      unfold (dll hd tl []);
      // Pure: hd == None, but Some? hd -> contradiction
      unreachable ()
    }
    k :: rest -> { () }
  }
}

// --- Factor/unfactor ---

let dls_factored_next
  ([@@@mkey] p: box node) (l: list int {Cons? l})
  (tail: box node) (last_ptr: dptr) (v_next: dptr)
  : Tot slprop
  = match l with
    | [_] -> pure (v_next == last_ptr /\ p == tail)
    | _ :: r0 :: rs ->
      exists* (np: box node).
        dls np (r0 :: rs) (Some p) tail last_ptr **
        pure (v_next == Some np)

// When v_next==None and last_ptr==None: singleton
ghost
fn factored_next_none_nil
  (p: box node)
  (#l: erased (list int) {Cons? l})
  (#tail: erased (box node))
  preserves dls_factored_next p l tail None None
  ensures pure (L.tl l == ([] #int))
{
  let hd = L.hd l;
  let tl = L.tl l;
  match tl {
    [] -> { () }
    y :: ys -> {
      rewrite each l as (hd :: y :: ys) in
        (dls_factored_next p l tail None None);
      unfold (dls_factored_next p (hd :: y :: ys) tail None None);
      // pure (None == Some np) → contradiction
      unreachable ()
    }
  }
}

// When v_next==Some np and last_ptr==None: multi-element
ghost
fn factored_next_some_cons
  (p: box node) (np: box node)
  (#l: erased (list int) {Cons? l})
  (#tail: erased (box node))
  preserves dls_factored_next p l tail None (Some np)
  ensures pure (Cons? (L.tl l))
{
  let hd = L.hd l;
  let tl = L.tl l;
  match tl {
    [] -> {
      rewrite each l as [hd] in
        (dls_factored_next p l tail None (Some np));
      unfold (dls_factored_next p [hd] tail None (Some np));
      // pure (Some np == None) → contradiction
      unreachable ()
    }
    y :: ys -> { () }
  }
}

// Extract tail dls from factored_next (multi-element case)
ghost
fn elim_factored_next
  (p: box node) (np: box node)
  (#l: erased (list int) {Cons? l /\ Cons? (L.tl l)})
  (#tail: erased (box node))
  (#last_ptr: erased dptr)
  requires dls_factored_next p l tail last_ptr (Some np)
  ensures dls np (L.tl l) (Some p) tail last_ptr
{
  let hd = L.hd l;
  let r0 = L.hd (L.tl l);
  let rs = L.tl (L.tl l);
  rewrite each l as (hd :: r0 :: rs) in
    (dls_factored_next p l tail last_ptr (Some np));
  unfold (dls_factored_next p (hd :: r0 :: rs) tail last_ptr (Some np));
  with np'. _;
  rewrite each np' as np;
  rewrite each (r0 :: rs) as (L.tl l);
}

// Reinsert tail dls into factored_next
ghost
fn intro_factored_next
  (p: box node) (np: box node)
  (#l: erased (list int) {Cons? l /\ Cons? (L.tl l)})
  (#tail: erased (box node))
  (#last_ptr: erased dptr)
  requires dls np (L.tl l) (Some p) tail last_ptr
  ensures dls_factored_next p l tail last_ptr (Some np)
{
  let hd = L.hd l;
  let r0 = L.hd (L.tl l);
  let rs = L.tl (L.tl l);
  rewrite each (L.tl l) as (r0 :: rs) in
    (dls np (L.tl l) (Some p) tail last_ptr);
  fold (dls_factored_next p (hd :: r0 :: rs) tail last_ptr (Some np));
  rewrite each (hd :: r0 :: rs) as l
}

let dls_factored
  ([@@@mkey] p: box node) (l: list int {Cons? l})
  (prev_ptr: dptr) (tail: box node) (last_ptr: dptr)
  : Tot slprop
  = exists* (v: node).
      pts_to p v **
      pure (v.key == L.hd l /\ v.prev == prev_ptr) **
      dls_factored_next p l tail last_ptr v.next

ghost
fn factor_dls
  (p: box node) (l: list int {Cons? l})
  (prev_ptr: dptr) (tail: box node) (last_ptr: dptr)
  requires dls p l prev_ptr tail last_ptr
  ensures dls_factored p l prev_ptr tail last_ptr
{
  let hd = L.hd l;
  let tl = L.tl l;
  match tl {
    [] -> {
      rewrite each l as [hd] in (dls p l prev_ptr tail last_ptr);
      unfold (dls p [hd] prev_ptr tail last_ptr);
      with v. assert (pts_to p v);
      fold (dls_factored_next p [hd] tail last_ptr v.next);
      fold (dls_factored p [hd] prev_ptr tail last_ptr);
      rewrite each [hd] as l
    }
    y :: ys -> {
      rewrite each l as (hd :: y :: ys) in (dls p l prev_ptr tail last_ptr);
      unfold (dls p (hd :: y :: ys) prev_ptr tail last_ptr);
      with v. assert (pts_to p v);
      fold (dls_factored_next p (hd :: y :: ys) tail last_ptr v.next);
      fold (dls_factored p (hd :: y :: ys) prev_ptr tail last_ptr);
      rewrite each (hd :: y :: ys) as l
    }
  }
}

ghost
fn unfactor_dls
  (p: box node) (l: list int {Cons? l})
  (prev_ptr: dptr) (tail: box node) (last_ptr: dptr)
  requires dls_factored p l prev_ptr tail last_ptr
  ensures dls p l prev_ptr tail last_ptr
{
  unfold (dls_factored p l prev_ptr tail last_ptr);
  with v. assert (pts_to p v);
  unfold (dls_factored_next p l tail last_ptr v.next);
  let hd = L.hd l;
  let tl = L.tl l;
  match tl {
    [] -> {
      rewrite each l as [hd];
      fold (dls p [hd] prev_ptr tail last_ptr);
      rewrite each [hd] as l
    }
    y :: ys -> {
      rewrite each l as (hd :: y :: ys);
      fold (dls p (hd :: y :: ys) prev_ptr tail last_ptr);
      rewrite each (hd :: y :: ys) as l
    }
  }
}

// Wrap dls with prev_ptr=None into dll
ghost
fn dls_to_dll
  (hp tp: box node) (#l: erased (list int) {Cons? l})
  requires dls hp l None tp None
  ensures dll (Some hp) (Some tp) l
{
  let k = L.hd l;
  let rest = L.tl l;
  rewrite each l as (k :: rest);
  fold (dll (Some hp) (Some tp) (k :: rest));
  rewrite each (k :: rest) as l
}

// Unwrap dll to get dls
ghost
fn unfold_dll_cons
  (hd tl: dptr) (#l: erased (list int) {Cons? l})
  requires dll hd tl l
  ensures exists* (hp tp: box node).
    dls hp l None tp None **
    pure (hd == Some hp /\ tl == Some tp)
{
  let k = L.hd l;
  let rest = L.tl l;
  rewrite each l as (k :: rest) in (dll hd tl l);
  unfold (dll hd tl (k :: rest));
  rewrite each (k :: rest) as l
}

// Set the prev pointer of the first node
fn set_prev
  (p: box node) (prev': dptr)
  (#l: erased (list int) {Cons? l})
  (#prev_ptr: erased dptr)
  (#tail: erased (box node))
  (#last_ptr: erased dptr)
  requires dls p l prev_ptr tail last_ptr
  ensures dls p l prev' tail last_ptr
{
  factor_dls p l prev_ptr tail last_ptr;
  unfold (dls_factored p l prev_ptr tail last_ptr);
  with v. assert (pts_to p v);
  let cv = Box.(!p);
  Box.(p := { cv with prev = prev' });
  rewrite (dls_factored_next p l tail last_ptr cv.next)
       as (dls_factored_next p l tail last_ptr ({ cv with prev = prev' }).next);
  fold (dls_factored p l prev' tail last_ptr);
  unfactor_dls p l prev' tail last_ptr
}

// Fold a cons onto a dls
ghost
fn fold_dls_cons
  (p: box node) (k: int) (rest: list int {Cons? rest})
  (prev_ptr: dptr) (tail: box node) (last_ptr: dptr)
  (v: node) (np: box node)
  requires
    pts_to p v **
    dls np rest (Some p) tail last_ptr **
    pure (v.key == k /\ v.prev == prev_ptr /\ v.next == Some np)
  ensures
    dls p (k :: rest) prev_ptr tail last_ptr
{
  let r0 = Cons?.hd rest;
  let r1 = Cons?.tl rest;
  rewrite each rest as (r0 :: r1);
  fold (dls p (k :: r0 :: r1) prev_ptr tail last_ptr);
  rewrite each (k :: r0 :: r1) as (k :: rest)
}

// --- DLS APPEND ---

// Append two adjacent DLS segments: l1 @ l2
// The proof is by induction on l1.
ghost
fn rec dls_append
  (h1: box node) (t1: box node)
  (#l1: erased (list int) {Cons? l1})
  (#prev1: erased dptr)
  (h2: box node) (t2: box node)
  (#l2: erased (list int) {Cons? l2})
  (#last2: erased dptr)
  requires dls h1 l1 prev1 t1 (Some h2) ** dls h2 l2 (Some t1) t2 last2
  ensures dls h1 (l1 @ l2) prev1 t2 last2
  decreases L.length l1
{
  let k1 = L.hd l1;
  let r1 = L.tl l1;
  rewrite each l1 as (k1 :: r1) in (dls h1 l1 prev1 t1 (Some h2));
  match r1 {
    [] -> {
      // l1 = [k1], so h1 == t1
      unfold (dls h1 [k1] prev1 t1 (Some h2));
      with v1. assert (pts_to h1 v1);
      // v1.next == Some h2, so we already have the link
      // Result: dls h1 ([k1] @ l2) prev1 t2 last2
      //       = dls h1 (k1 :: l2) prev1 t2 last2
      // Need to fold this as a multi-node dls
      let k2 = L.hd l2;
      let r2 = L.tl l2;
      rewrite each l2 as (k2 :: r2) in (dls h2 l2 (Some t1) t2 last2);
      rewrite each t1 as h1;
      fold (dls h1 (k1 :: k2 :: r2) prev1 t2 last2);
      rewrite each (k1 :: k2 :: r2) as ([k1] @ (k2 :: r2));
      rewrite each (k2 :: r2) as l2;
      rewrite each ([k1] @ l2) as (l1 @ l2)
    }
    k1' :: r1' -> {
      // l1 = k1 :: k1' :: r1', so it's multi-element
      unfold (dls h1 (k1 :: k1' :: r1') prev1 t1 (Some h2));
      with v1 np1. assert (pts_to h1 v1);
      // np1 is the second node of l1
      // Recursive call: append (np1, l1.tail) with (h2, l2)
      rewrite each (k1' :: r1') as r1;
      dls_append np1 t1 h2 t2;
      // Now we have: dls np1 (r1 @ l2) (Some h1) t2 last2
      // Fold h1 back on
      rewrite each (r1 @ l2) as ((k1' :: r1') @ l2);
      fold_dls_cons h1 k1 ((k1' :: r1') @ l2) prev1 t2 last2 v1 np1;
      // dls h1 (k1 :: (k1' :: r1') @ l2) prev1 t2 last2
    }
  }
}

// --- LIST-INSERT ---

//SNIPPET_START: dll_list_insert
fn list_insert (hd_ref tl_ref: ref dptr) (x: int) (#l: erased (list int))
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (x :: l)
//SNIPPET_END: dll_list_insert
{
  let hd = Pulse.Lib.Reference.(!hd_ref);
  let tl = Pulse.Lib.Reference.(!tl_ref);
  match hd {
    norewrite None -> {
      // Empty list: hd = None => l = []
      dll_none_nil hd tl;
      rewrite each l as ([] #int) in (dll hd tl l);
      unfold (dll hd tl []);
      let nd = Box.alloc #node { key = x; prev = None; next = None };
      fold (dls nd [x] None nd None);
      fold (dll (Some nd) (Some nd) [x]);
      rewrite each [x] as (x :: l) in (dll (Some nd) (Some nd) [x]);
      Pulse.Lib.Reference.(hd_ref := Some nd);
      Pulse.Lib.Reference.(tl_ref := Some nd)
    }
    norewrite Some old_hp -> {
      // Non-empty: hd = Some old_hp => Cons? l
      dll_some_cons hd tl;
      let lk = hide (L.hd l);
      let lr = hide (L.tl l);
      rewrite each l as (reveal lk :: reveal lr) in (dll hd tl l);
      unfold (dll hd tl (reveal lk :: reveal lr));
      with hp tp. _;
      rewrite each hp as old_hp;
      let nd = Box.alloc #node { key = x; prev = None; next = Some old_hp };
      set_prev old_hp (Some nd);
      let nd_v = Box.(!nd);
      fold_dls_cons nd x (reveal lk :: reveal lr) None tp None nd_v old_hp;
      fold (dll (Some nd) (Some tp) (x :: reveal lk :: reveal lr));
      Pulse.Lib.Reference.(hd_ref := Some nd);
      rewrite each (Some tp) as tl;
      rewrite each (reveal lk :: reveal lr) as l
    }
  }
}

// === dls_rev: Reversed DLS predicate (traverses prev pointers from tail to head) ===
// Structurally symmetric to dls but traverses in the opposite direction.
// Used internally by list_insert_tail to access the tail node in O(1) runtime.

let rec dls_rev
  ([@@@mkey] p: box node)
  (l: list int {Cons? l})
  (next_ptr: dptr)
  (head: box node)
  (first_ptr: dptr)
  : Tot slprop (decreases l)
  = match l with
    | [k] ->
      exists* (v: node).
        pts_to p v **
        pure (v.key == k /\ v.next == next_ptr /\
              v.prev == first_ptr /\ p == head)
    | k :: rest ->
      exists* (v: node) (pp: box node).
        pts_to p v **
        dls_rev pp rest (Some p) head first_ptr **
        pure (v.key == k /\ v.next == next_ptr /\
              v.prev == Some pp)

// --- dls_rev factor/unfactor (analogous to dls_factored) ---

let dls_rev_factored_prev
  ([@@@mkey] p: box node) (l: list int {Cons? l})
  (head: box node) (first_ptr: dptr) (v_prev: dptr)
  : Tot slprop
  = match l with
    | [_] -> pure (v_prev == first_ptr /\ p == head)
    | _ :: r0 :: rs ->
      exists* (pp: box node).
        dls_rev pp (r0 :: rs) (Some p) head first_ptr **
        pure (v_prev == Some pp)

let dls_rev_factored
  ([@@@mkey] p: box node) (l: list int {Cons? l})
  (next_ptr: dptr) (head: box node) (first_ptr: dptr)
  : Tot slprop
  = exists* (v: node).
      pts_to p v **
      pure (v.key == L.hd l /\ v.next == next_ptr) **
      dls_rev_factored_prev p l head first_ptr v.prev

ghost
fn factor_dls_rev
  (p: box node) (l: list int {Cons? l})
  (next_ptr: dptr) (head: box node) (first_ptr: dptr)
  requires dls_rev p l next_ptr head first_ptr
  ensures dls_rev_factored p l next_ptr head first_ptr
{
  let hd = L.hd l;
  let tl = L.tl l;
  match tl {
    [] -> {
      rewrite each l as [hd] in (dls_rev p l next_ptr head first_ptr);
      unfold (dls_rev p [hd] next_ptr head first_ptr);
      with v. assert (pts_to p v);
      fold (dls_rev_factored_prev p [hd] head first_ptr v.prev);
      fold (dls_rev_factored p [hd] next_ptr head first_ptr);
      rewrite each [hd] as l
    }
    y :: ys -> {
      rewrite each l as (hd :: y :: ys) in (dls_rev p l next_ptr head first_ptr);
      unfold (dls_rev p (hd :: y :: ys) next_ptr head first_ptr);
      with v. assert (pts_to p v);
      fold (dls_rev_factored_prev p (hd :: y :: ys) head first_ptr v.prev);
      fold (dls_rev_factored p (hd :: y :: ys) next_ptr head first_ptr);
      rewrite each (hd :: y :: ys) as l
    }
  }
}

ghost
fn unfactor_dls_rev
  (p: box node) (l: list int {Cons? l})
  (next_ptr: dptr) (head: box node) (first_ptr: dptr)
  requires dls_rev_factored p l next_ptr head first_ptr
  ensures dls_rev p l next_ptr head first_ptr
{
  unfold (dls_rev_factored p l next_ptr head first_ptr);
  with v. assert (pts_to p v);
  unfold (dls_rev_factored_prev p l head first_ptr v.prev);
  let hd = L.hd l;
  let tl = L.tl l;
  match tl {
    [] -> {
      rewrite each l as [hd];
      fold (dls_rev p [hd] next_ptr head first_ptr);
      rewrite each [hd] as l
    }
    y :: ys -> {
      rewrite each l as (hd :: y :: ys);
      fold (dls_rev p (hd :: y :: ys) next_ptr head first_ptr);
      rewrite each (hd :: y :: ys) as l
    }
  }
}

// --- dls_rev factored_prev helpers (analogous to dls factored_next) ---

// When v_prev==None and first_ptr==None: l is singleton
ghost
fn factored_prev_none_nil
  (p: box node)
  (#l: erased (list int) {Cons? l})
  (#head: erased (box node))
  preserves dls_rev_factored_prev p l head None None
  ensures pure (L.tl l == ([] #int))
{
  let hd = L.hd l;
  let tl = L.tl l;
  match tl {
    [] -> { () }
    y :: ys -> {
      rewrite each l as (hd :: y :: ys) in
        (dls_rev_factored_prev p l head None None);
      unfold (dls_rev_factored_prev p (hd :: y :: ys) head None None);
      unreachable ()
    }
  }
}

// When v_prev==Some pp and first_ptr==None: multi-element
ghost
fn factored_prev_some_cons
  (p: box node) (pp: box node)
  (#l: erased (list int) {Cons? l})
  (#head: erased (box node))
  preserves dls_rev_factored_prev p l head None (Some pp)
  ensures pure (Cons? (L.tl l))
{
  let hd = L.hd l;
  let tl = L.tl l;
  match tl {
    [] -> {
      rewrite each l as [hd] in
        (dls_rev_factored_prev p l head None (Some pp));
      unfold (dls_rev_factored_prev p [hd] head None (Some pp));
      unreachable ()
    }
    y :: ys -> { () }
  }
}

// Extract sub dls_rev from factored_prev (multi-element case)
ghost
fn elim_factored_prev
  (p: box node) (pp: box node)
  (#l: erased (list int) {Cons? l /\ Cons? (L.tl l)})
  (#head: erased (box node))
  (#first_ptr: erased dptr)
  requires dls_rev_factored_prev p l head first_ptr (Some pp)
  ensures dls_rev pp (L.tl l) (Some p) head first_ptr
{
  let hd = L.hd l;
  let r0 = L.hd (L.tl l);
  let rs = L.tl (L.tl l);
  rewrite each l as (hd :: r0 :: rs) in
    (dls_rev_factored_prev p l head first_ptr (Some pp));
  unfold (dls_rev_factored_prev p (hd :: r0 :: rs) head first_ptr (Some pp));
  with pp'. _;
  rewrite each pp' as pp;
  rewrite each (r0 :: rs) as (L.tl l);
}

// Reinsert sub dls_rev into factored_prev
ghost
fn intro_factored_prev
  (p: box node) (pp: box node)
  (#l: erased (list int) {Cons? l /\ Cons? (L.tl l)})
  (#head: erased (box node))
  (#first_ptr: erased dptr)
  requires dls_rev pp (L.tl l) (Some p) head first_ptr
  ensures dls_rev_factored_prev p l head first_ptr (Some pp)
{
  let hd = L.hd l;
  let r0 = L.hd (L.tl l);
  let rs = L.tl (L.tl l);
  rewrite each (L.tl l) as (r0 :: rs) in
    (dls_rev pp (L.tl l) (Some p) head first_ptr);
  fold (dls_rev_factored_prev p (hd :: r0 :: rs) head first_ptr (Some pp));
  rewrite each (hd :: r0 :: rs) as l
}

// --- fold_dls_rev_cons: analogous to fold_dls_cons ---
ghost
fn fold_dls_rev_cons
  (p: box node) (k: int) (rest: list int {Cons? rest})
  (next_ptr: dptr) (head: box node) (first_ptr: dptr)
  (v: node) (pp: box node)
  requires
    pts_to p v **
    dls_rev pp rest (Some p) head first_ptr **
    pure (v.key == k /\ v.next == next_ptr /\ v.prev == Some pp)
  ensures
    dls_rev p (k :: rest) next_ptr head first_ptr
{
  let r0 = Cons?.hd rest;
  let r1 = Cons?.tl rest;
  rewrite each rest as (r0 :: r1);
  fold (dls_rev p (k :: r0 :: r1) next_ptr head first_ptr);
  rewrite each (k :: r0 :: r1) as (k :: rest)
}

// --- dls_rev_snoc: Append a node at the end of a dls_rev segment ---
ghost
fn rec dls_rev_snoc
  (tail: box node)
  (#rl: erased (list int) {Cons? rl})
  (last_ptr: dptr) (np: box node)
  (p: box node) (v: node) (prev_ptr: dptr)
  requires
    dls_rev tail rl last_ptr np (Some p) **
    pts_to p v **
    pure (v.prev == prev_ptr /\ v.next == Some np)
  ensures
    dls_rev tail (rl @ [v.key]) last_ptr p prev_ptr
  decreases L.length rl
{
  let k0 = L.hd rl;
  let rest = L.tl rl;
  rewrite each rl as (k0 :: rest) in (dls_rev tail rl last_ptr np (Some p));
  match rest {
    [] -> {
      unfold (dls_rev tail [k0] last_ptr np (Some p));
      with v0. assert (pts_to tail v0);
      rewrite each np as tail in (pure (v.prev == prev_ptr /\ v.next == Some np));
      fold (dls_rev p [v.key] (Some tail) p prev_ptr);
      fold (dls_rev tail [k0; v.key] last_ptr p prev_ptr);
      rewrite each [k0; v.key] as ([k0] @ [v.key]);
      rewrite each ([k0] @ [v.key]) as (rl @ [v.key])
    }
    k0' :: r0' -> {
      unfold (dls_rev tail (k0 :: k0' :: r0') last_ptr np (Some p));
      with v0 pp0. assert (pts_to tail v0);
      rewrite each (k0' :: r0') as rest;
      dls_rev_snoc pp0 (Some tail) np p v prev_ptr;
      fold_dls_rev_cons tail k0 (rest @ [v.key]) last_ptr p prev_ptr v0 pp0
    }
  }
}

// --- dls_to_dls_rev: Convert dls to dls_rev ---

// SMTPat: L.rev preserves non-emptiness
let rev_preserves_cons (#a:Type) (l:list a {Cons? l})
  : Lemma (Cons? (L.rev l))
  [SMTPat (L.rev l)]
  = FStar.List.Tot.Properties.rev_length l

// One-step unfolding of L.rev for SMT
#push-options "--fuel 2 --ifuel 2"
let rev_cons (#a:Type) (x:a) (rest:list a)
  : Lemma (L.rev (x :: rest) == L.rev rest @ [x])
  [SMTPat (L.rev (x :: rest))]
  = FStar.List.Tot.Properties.rev_append [x] rest
#pop-options

// mem is preserved by rev
#push-options "--fuel 2"
let rec mem_rev (#a:eqtype) (x: a) (l: list a)
  : Lemma (L.mem x (L.rev l) == L.mem x l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      mem_rev x tl;
      FStar.List.Tot.Properties.append_mem (L.rev tl) [hd] x
#pop-options

#push-options "--fuel 2"
ghost
fn rec dls_to_dls_rev
  (p: box node)
  (#l: erased (list int) {Cons? l})
  (prev_ptr: dptr) (tail: box node) (last_ptr: dptr)
  requires dls p l prev_ptr tail last_ptr
  ensures dls_rev tail (L.rev l) last_ptr p prev_ptr
  decreases L.length l
{
  let k = L.hd l;
  let rest = L.tl l;
  match rest {
    [] -> {
      rewrite each l as [k] in (dls p l prev_ptr tail last_ptr);
      unfold (dls p [k] prev_ptr tail last_ptr);
      with v. assert (pts_to p v);
      rewrite (pts_to p v) as (pts_to tail v);
      fold (dls_rev tail [k] last_ptr p prev_ptr);
      rewrite each [k] as (L.rev l)
    }
    r0 :: rs -> {
      rewrite each l as (k :: r0 :: rs) in (dls p l prev_ptr tail last_ptr);
      unfold (dls p (k :: r0 :: rs) prev_ptr tail last_ptr);
      with v np. assert (pts_to p v);
      rewrite each (r0 :: rs) as rest;
      dls_to_dls_rev np (Some p) tail last_ptr;
      dls_rev_snoc tail last_ptr np p v prev_ptr;
      rewrite each v.key as k;
      rev_cons k rest;
      rewrite each (L.rev rest @ [k]) as (L.rev (k :: rest));
      rewrite each (k :: rest) as l
    }
  }
}
#pop-options

// --- dls_rev_to_dls: Convert dls_rev back to dls ---
#push-options "--fuel 2"
ghost
fn rec dls_rev_to_dls
  (p: box node)
  (#l: erased (list int) {Cons? l})
  (next_ptr: dptr) (head: box node) (first_ptr: dptr)
  requires dls_rev p l next_ptr head first_ptr
  ensures dls head (L.rev l) first_ptr p next_ptr
  decreases L.length l
{
  let k = L.hd l;
  let rest = L.tl l;
  match rest {
    [] -> {
      rewrite each l as [k] in (dls_rev p l next_ptr head first_ptr);
      unfold (dls_rev p [k] next_ptr head first_ptr);
      with v. assert (pts_to p v);
      rewrite (pts_to p v) as (pts_to head v);
      fold (dls head [k] first_ptr p next_ptr);
      rewrite each [k] as (L.rev l)
    }
    r0 :: rs -> {
      rewrite each l as (k :: r0 :: rs) in (dls_rev p l next_ptr head first_ptr);
      unfold (dls_rev p (k :: r0 :: rs) next_ptr head first_ptr);
      with v pp. assert (pts_to p v);
      rewrite each (r0 :: rs) as rest;
      dls_rev_to_dls pp (Some p) head first_ptr;
      fold (dls p [k] (Some pp) p next_ptr);
      dls_append head pp p p;
      rev_cons k rest;
      rewrite each (L.rev rest @ [k]) as (L.rev (k :: rest));
      rewrite each (k :: rest) as l
    }
  }
}
#pop-options

// --- LIST-INSERT-TAIL ---

// Pure helper: rev (x :: rev l) == l @ [x]
let rev_cons_rev (#a:Type) (x:a) (l:list a)
  : Lemma (L.rev (x :: L.rev l) == l @ [x])
  = FStar.List.Tot.Properties.rev_involutive l

//SNIPPET_START: dll_list_insert_tail
fn list_insert_tail (hd_ref tl_ref: ref dptr) (x: int) (#l: erased (list int))
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (l @ [x])
//SNIPPET_END: dll_list_insert_tail
{
  let hd = Pulse.Lib.Reference.(!hd_ref);
  let tl = Pulse.Lib.Reference.(!tl_ref);
  match hd {
    norewrite None -> {
      // Empty list: hd = None => l = []
      dll_none_nil hd tl;
      rewrite each l as ([] #int) in (dll hd tl l);
      unfold (dll hd tl []);
      let nd = Box.alloc #node { key = x; prev = None; next = None };
      fold (dls nd [x] None nd None);
      fold (dll (Some nd) (Some nd) [x]);
      rewrite each [x] as (l @ [x]) in (dll (Some nd) (Some nd) [x]);
      Pulse.Lib.Reference.(hd_ref := Some nd);
      Pulse.Lib.Reference.(tl_ref := Some nd)
    }
    norewrite Some old_hp -> {
      // Non-empty list: O(1) runtime tail insertion
      dll_some_cons hd tl;
      unfold_dll_cons hd tl;
      with hp tp. _;
      rewrite each hp as old_hp;
      let concrete_tp = Some?.v tl;
      rewrite each tp as concrete_tp;
      // dls old_hp l None concrete_tp None

      // Ghost: convert dls to dls_rev (O(n) ghost traversal)
      dls_to_dls_rev old_hp None concrete_tp None;
      // dls_rev concrete_tp (rev l) None old_hp None

      // Ghost: factor to expose tail node's pts_to
      let rl = hide (L.rev (reveal l));
      rewrite each (L.rev (reveal l)) as (reveal rl)
        in (dls_rev concrete_tp (L.rev (reveal l)) None old_hp None);
      factor_dls_rev concrete_tp (reveal rl) None old_hp None;
      unfold (dls_rev_factored concrete_tp (reveal rl) None old_hp None);
      with v_tail. assert (pts_to concrete_tp v_tail);

      // Runtime O(1): read tail, alloc new node, update tail's next
      let nd = Box.alloc #node { key = x; prev = Some concrete_tp; next = None };
      let v_tail_nd = Box.(!concrete_tp);
      Box.(concrete_tp := { v_tail_nd with next = Some nd });

      // Ghost: refold dls_rev_factored with new next_ptr
      fold (dls_rev_factored concrete_tp (reveal rl) (Some nd) old_hp None);
      unfactor_dls_rev concrete_tp (reveal rl) (Some nd) old_hp None;
      // dls_rev concrete_tp (rev l) (Some nd) old_hp None

      // Ghost: fold new node into dls_rev
      let rl_hd = hide (L.hd (reveal rl));
      let rl_tl = hide (L.tl (reveal rl));
      rewrite each (reveal rl) as (reveal rl_hd :: reveal rl_tl)
        in (dls_rev concrete_tp (reveal rl) (Some nd) old_hp None);
      fold (dls_rev nd (x :: reveal rl_hd :: reveal rl_tl) None old_hp None);
      rewrite each (x :: reveal rl_hd :: reveal rl_tl) as (x :: reveal rl);
      rewrite each (reveal rl) as (L.rev (reveal l));
      // dls_rev nd (x :: rev l) None old_hp None

      // Ghost: convert back to dls (O(n) ghost traversal)
      dls_rev_to_dls nd None old_hp None;
      // dls old_hp (rev (x :: rev l)) None nd None

      // Use lemma: rev (x :: rev l) == l @ [x]
      rev_cons_rev x (reveal l);
      rewrite each (L.rev (x :: L.rev (reveal l))) as (l @ [x])
        in (dls old_hp (L.rev (x :: L.rev (reveal l))) None nd None);
      // dls old_hp (l @ [x]) None nd None

      dls_to_dll old_hp nd;
      Pulse.Lib.Reference.(hd_ref := Some old_hp);
      rewrite each (Some old_hp) as hd;
      Pulse.Lib.Reference.(tl_ref := Some nd)
    }
  }
}

// --- LIST-SEARCH ---

// Search within DLS segment (last_ptr=None, i.e., full DLL or sub-segment).
// Factor to read head node, use ghost helpers to determine
// singleton vs multi-element, recurse.
fn rec search_dls
  (p: box node) (k: int)
  (#l: erased (list int) {Cons? l})
  (#prev_ptr: erased dptr)
  (#tail: erased (box node))
  preserves dls p l prev_ptr tail None
  returns found: bool
  ensures pure (found <==> L.mem k l)
{
  factor_dls p l prev_ptr tail None;
  unfold (dls_factored p l prev_ptr tail None);
  with v. assert (pts_to p v);
  let nd = Box.(!p);
  let nxt = nd.next;
  if (nd.key = k) {
    fold (dls_factored p l prev_ptr tail None);
    unfactor_dls p l prev_ptr tail None;
    true
  } else {
    match nxt {
      norewrite None -> {
        // nd.next == None with last_ptr == None => singleton
        factored_next_none_nil p;
        fold (dls_factored p l prev_ptr tail None);
        unfactor_dls p l prev_ptr tail None;
        false
      }
      norewrite Some np -> {
        // nd.next == Some np with last_ptr == None => multi-element
        factored_next_some_cons p np;
        // Extract tail segment, recurse, reinsert
        elim_factored_next p np;
        let r = search_dls np k;
        intro_factored_next p np;
        rewrite each (Some np) as v.next;
        fold (dls_factored p l prev_ptr tail None);
        unfactor_dls p l prev_ptr tail None;
        r
      }
    }
  }
}

//SNIPPET_START: dll_list_search
fn list_search (hd tl: dptr) (k: int)
  preserves dll hd tl 'l
  returns found: bool
  ensures pure (found <==> L.mem k 'l)
//SNIPPET_END: dll_list_search
{
  match hd {
    norewrite None -> {
      dll_none_nil hd tl;
      false
    }
    norewrite Some hp -> {
      dll_some_cons hd tl;
      let lk = hide (L.hd 'l);
      let lr = hide (L.tl 'l);
      rewrite each 'l as (reveal lk :: reveal lr) in (dll hd tl 'l);
      unfold (dll hd tl (reveal lk :: reveal lr));
      with hp' tp. _;
      rewrite each hp' as hp;
      let r = search_dls hp k;
      fold (dll (Some hp) (Some tp) (reveal lk :: reveal lr));
      rewrite each (Some hp) as hd;
      rewrite each (Some tp) as tl;
      rewrite each (reveal lk :: reveal lr) as 'l;
      r
    }
  }
}

// --- LIST-SEARCH-PTR: Return pointer to found node ---

// Search within DLS segment returning pointer to found node
fn rec search_dls_ptr
  (p: box node) (k: int)
  (#l: erased (list int) {Cons? l})
  (#prev_ptr: erased dptr)
  (#tail: erased (box node))
  preserves dls p l prev_ptr tail None
  returns result: dptr
  ensures pure (
    match result with
    | None -> ~(L.mem k l)
    | Some _ -> L.mem k l
  )
{
  factor_dls p l prev_ptr tail None;
  unfold (dls_factored p l prev_ptr tail None);
  with v. assert (pts_to p v);
  let nd = Box.(!p);
  let nxt = nd.next;
  if (nd.key = k) {
    fold (dls_factored p l prev_ptr tail None);
    unfactor_dls p l prev_ptr tail None;
    Some p
  } else {
    match nxt {
      norewrite None -> {
        // nd.next == None with last_ptr == None => singleton
        factored_next_none_nil p;
        fold (dls_factored p l prev_ptr tail None);
        unfactor_dls p l prev_ptr tail None;
        None
      }
      norewrite Some np -> {
        // nd.next == Some np with last_ptr == None => multi-element
        factored_next_some_cons p np;
        // Extract tail segment, recurse, reinsert
        elim_factored_next p np;
        let r = search_dls_ptr np k;
        intro_factored_next p np;
        rewrite each (Some np) as v.next;
        fold (dls_factored p l prev_ptr tail None);
        unfactor_dls p l prev_ptr tail None;
        r
      }
    }
  }
}

fn list_search_ptr (hd tl: dptr) (k: int)
  preserves dll hd tl 'l
  returns result: dptr
  ensures pure (
    match result with
    | None -> ~(L.mem k 'l)
    | Some _ -> L.mem k 'l
  )
{
  match hd {
    norewrite None -> {
      dll_none_nil hd tl;
      None
    }
    norewrite Some hp -> {
      dll_some_cons hd tl;
      let lk = hide (L.hd 'l);
      let lr = hide (L.tl 'l);
      rewrite each 'l as (reveal lk :: reveal lr) in (dll hd tl 'l);
      unfold (dll hd tl (reveal lk :: reveal lr));
      with hp' tp. _;
      rewrite each hp' as hp;
      let r = search_dls_ptr hp k;
      fold (dll (Some hp) (Some tp) (reveal lk :: reveal lr));
      rewrite each (Some hp) as hd;
      rewrite each (Some tp) as tl;
      rewrite each (reveal lk :: reveal lr) as 'l;
      r
    }
  }
}

// --- LIST-SEARCH-BACK: Search from tail to head ---

// Search within dls_rev segment (first_ptr=None, full DLL reversed).
fn rec search_dls_rev
  (p: box node) (k: int)
  (#rl: erased (list int) {Cons? rl})
  (#next_ptr: erased dptr)
  (#head: erased (box node))
  preserves dls_rev p rl next_ptr head None
  returns found: bool
  ensures pure (found <==> L.mem k rl)
{
  factor_dls_rev p rl next_ptr head None;
  unfold (dls_rev_factored p rl next_ptr head None);
  with v. assert (pts_to p v);
  let nd = Box.(!p);
  let prv = nd.prev;
  if (nd.key = k) {
    fold (dls_rev_factored p rl next_ptr head None);
    unfactor_dls_rev p rl next_ptr head None;
    true
  } else {
    match prv {
      norewrite None -> {
        factored_prev_none_nil p;
        fold (dls_rev_factored p rl next_ptr head None);
        unfactor_dls_rev p rl next_ptr head None;
        false
      }
      norewrite Some pp -> {
        factored_prev_some_cons p pp;
        elim_factored_prev p pp;
        let r = search_dls_rev pp k;
        intro_factored_prev p pp;
        rewrite each (Some pp) as v.prev;
        fold (dls_rev_factored p rl next_ptr head None);
        unfactor_dls_rev p rl next_ptr head None;
        r
      }
    }
  }
}

#push-options "--fuel 2"
fn list_search_back (hd tl: dptr) (k: int)
  preserves dll hd tl 'l
  returns found: bool
  ensures pure (found <==> L.mem k 'l)
{
  match hd {
    norewrite None -> {
      dll_none_nil hd tl;
      false
    }
    norewrite Some hp -> {
      dll_some_cons hd tl;
      let lk = hide (L.hd 'l);
      let lr = hide (L.tl 'l);
      rewrite each 'l as (reveal lk :: reveal lr) in (dll hd tl 'l);
      unfold (dll hd tl (reveal lk :: reveal lr));
      with hp' tp. _;
      rewrite each hp' as hp;
      let concrete_tp = Some?.v tl;
      rewrite each tp as concrete_tp;
      // dls hp (reveal lk :: reveal lr) None concrete_tp None
      dls_to_dls_rev hp None concrete_tp None;
      // dls_rev concrete_tp (L.rev ...) None hp None
      mem_rev k (reveal lk :: reveal lr);
      let r = search_dls_rev concrete_tp k;
      // Convert back
      dls_rev_to_dls concrete_tp None hp None;
      FStar.List.Tot.Properties.rev_involutive (reveal lk :: reveal lr);
      rewrite each (L.rev (L.rev (reveal lk :: reveal lr)))
                as (reveal lk :: reveal lr);
      fold (dll (Some hp) (Some concrete_tp) (reveal lk :: reveal lr));
      rewrite each (Some hp) as hd;
      rewrite each (Some concrete_tp) as tl;
      rewrite each (reveal lk :: reveal lr) as 'l;
      r
    }
  }
}
#pop-options

// --- O(1) delete: see list_delete_node after list_delete ---

// --- LIST-DELETE ---

// remove_first is defined in CLRS.Ch10.DLL.Impl.fsti

let remove_first_head (k: int) (l: list int)
  : Lemma (requires Cons? l /\ L.hd l = k)
          (ensures remove_first k l == L.tl l) = ()

let remove_first_skip (k: int) (l: list int)
  : Lemma (requires Cons? l /\ L.hd l <> k)
          (ensures remove_first k l == L.hd l :: remove_first k (L.tl l)) = ()

// --- delete_in_dls: returns dls or empty ---
// The result of delete_in_dls:
//   If remove_first k l is [], postcondition is emp
//   If remove_first k l is Cons, postcondition is dls with same prev_ptr

// Helper: result predicate for delete — either empty or dls segment
let delete_result (hd tl: dptr) (prev_ptr: dptr) (l: list int) : slprop =
  match l with
  | [] -> pure (hd == None /\ tl == None)
  | k :: rest ->
    exists* (hp tp: box node).
      dls hp (k :: rest) prev_ptr tp None **
      pure (hd == Some hp /\ tl == Some tp)

ghost
fn fold_delete_result_nil (hd tl: dptr) (prev_ptr: dptr)
  requires pure (hd == None /\ tl == None)
  ensures delete_result hd tl prev_ptr ([] #int)
{
  fold (delete_result hd tl prev_ptr ([] #int))
}

ghost
fn fold_delete_result_cons
  (hp tp: box node) (prev_ptr: dptr) (l: list int {Cons? l})
  requires dls hp l prev_ptr tp None
  ensures delete_result (Some hp) (Some tp) prev_ptr l
{
  let k = L.hd l;
  let rest = L.tl l;
  rewrite each l as (k :: rest);
  fold (delete_result (Some hp) (Some tp) prev_ptr (k :: rest));
  rewrite each (k :: rest) as l
}

ghost
fn unfold_delete_result_nil (hd tl: dptr) (prev_ptr: dptr) (#l: erased (list int))
  preserves delete_result hd tl prev_ptr l
  requires pure (hd == None)
  ensures pure (l == ([] #int))
{
  let ll = reveal l;
  match ll {
    [] -> { () }
    k :: rest -> {
      rewrite each l as (k :: rest) in (delete_result hd tl prev_ptr l);
      unfold (delete_result hd tl prev_ptr (k :: rest));
      unreachable ()
    }
  }
}

ghost
fn unfold_delete_result_cons (hd tl: dptr) (prev_ptr: dptr) (#l: erased (list int))
  preserves delete_result hd tl prev_ptr l
  requires pure (Some? hd)
  ensures pure (Cons? l)
{
  let ll = reveal l;
  match ll {
    [] -> {
      rewrite each l as ([] #int) in (delete_result hd tl prev_ptr l);
      unfold (delete_result hd tl prev_ptr []);
      unreachable ()
    }
    k :: rest -> { () }
  }
}

ghost
fn extract_delete_result_cons (hd tl: dptr) (prev_ptr: dptr) (#l: erased (list int) {Cons? l})
  requires delete_result hd tl prev_ptr l
  ensures exists* (hp tp: box node).
    dls hp l prev_ptr tp None **
    pure (hd == Some hp /\ tl == Some tp)
{
  let k = L.hd l;
  let rest = L.tl l;
  rewrite each l as (k :: rest) in (delete_result hd tl prev_ptr l);
  unfold (delete_result hd tl prev_ptr (k :: rest));
  rewrite each (k :: rest) as l
}

ghost
fn delete_result_to_dll (hd tl: dptr) (#l: erased (list int))
  requires delete_result hd tl None l
  ensures dll hd tl l
{
  let ll = reveal l;
  match ll {
    [] -> {
      rewrite each l as ([] #int) in (delete_result hd tl None l);
      unfold (delete_result hd tl None ([] #int));
      fold (dll hd tl ([] #int));
      rewrite each ([] #int) as l
    }
    k :: rest -> {
      rewrite each l as (k :: rest) in (delete_result hd tl None l);
      unfold (delete_result hd tl None (k :: rest));
      fold (dll hd tl (k :: rest));
      rewrite each (k :: rest) as l
    }
  }
}

// Recursive delete within a DLS segment.
// Returns delete_result with the same prev_ptr.
fn rec delete_in_dls
  (p: box node) (k: int) (prev_ptr: dptr) (tail_ptr: box node)
  (#l: erased (list int) {Cons? l})
  requires dls p l prev_ptr tail_ptr None
  returns r: (dptr & dptr)
  ensures delete_result (fst r) (snd r) prev_ptr (remove_first k l)
{
  factor_dls p l prev_ptr tail_ptr None;
  unfold (dls_factored p l prev_ptr tail_ptr None);
  with v. assert (pts_to p v);
  let nd = Box.(!p);
  let nxt = nd.next;
  if (nd.key = k) {
    // Found key at head — splice it out
    remove_first_head k l;
    match nxt {
      norewrite None -> {
        // Singleton: free node, return empty
        factored_next_none_nil p;
        let hd_l = hide (L.hd l);
        rewrite each l as [reveal hd_l] in (dls_factored_next p l tail_ptr None None);
        unfold (dls_factored_next p [reveal hd_l] tail_ptr None None);
        Box.free p;
        let none_ptr : dptr = None;
        fold_delete_result_nil none_ptr none_ptr prev_ptr;
        rewrite each ([] #int) as (remove_first k l);
        (none_ptr, none_ptr)
      }
      norewrite Some np -> {
        // Multi: free head, return tail with updated prev
        factored_next_some_cons p np;
        elim_factored_next p np;
        Box.free p;
        set_prev np prev_ptr;
        // dls np (L.tl l) prev_ptr tail_ptr None
        fold_delete_result_cons np tail_ptr prev_ptr (L.tl l);
        rewrite each (L.tl l) as (remove_first k l);
        (Some np, Some tail_ptr)
      }
    }
  } else {
    // Key doesn't match head — recurse on tail
    remove_first_skip k l;
    match nxt {
      norewrite None -> {
        // Singleton, key not found: return as-is
        factored_next_none_nil p;
        fold (dls_factored p l prev_ptr tail_ptr None);
        unfactor_dls p l prev_ptr tail_ptr None;
        // remove_first k l == L.hd l :: remove_first k (L.tl l)
        // But L.tl l == [] so remove_first k [] == []
        // So remove_first k l == [L.hd l] == l
        // dls p l prev_ptr tail_ptr None is what we have
        fold_delete_result_cons p tail_ptr prev_ptr l;
        rewrite each l as (remove_first k l);
        (Some p, Some tail_ptr)
      }
      norewrite Some np -> {
        // Multi: recurse on tail segment
        factored_next_some_cons p np;
        elim_factored_next p np;
        // dls np (L.tl l) (Some p) tail_ptr None
        let r = delete_in_dls np k (Some p) tail_ptr;
        let new_hd = fst r;
        let new_tl = snd r;
        rewrite each (fst r) as new_hd in
          (delete_result (fst r) (snd r) (Some p) (remove_first k (L.tl l)));
        rewrite each (snd r) as new_tl in
          (delete_result new_hd (snd r) (Some p) (remove_first k (L.tl l)));
        // delete_result new_hd new_tl (Some p) (remove_first k (L.tl l))
        match new_hd {
          norewrite None -> {
            // Tail became empty after delete
            unfold_delete_result_nil new_hd new_tl (Some p);
            rewrite each (remove_first k (L.tl l))
                      as ([] #int)
                      in (delete_result new_hd new_tl (Some p) (remove_first k (L.tl l)));
            unfold (delete_result new_hd new_tl (Some p) []);
            Box.(p := { nd with next = None });
            fold (dls p [nd.key] prev_ptr p None);
            // remove_first k l == nd.key :: remove_first k (L.tl l) == nd.key :: [] == [nd.key]
            fold_delete_result_cons p p prev_ptr [nd.key];
            rewrite each [nd.key] as (remove_first k l);
            (Some p, Some p)
          }
          norewrite Some new_hp -> {
            // Tail still has elements after delete
            unfold_delete_result_cons new_hd new_tl (Some p);
            extract_delete_result_cons new_hd new_tl (Some p);
            with hp' tp'. _;
            rewrite each hp' as new_hp;
            let concrete_tp = Some?.v new_tl;
            rewrite each tp' as concrete_tp;
            Box.(p := { nd with next = Some new_hp });
            let nd' = { nd with next = Some new_hp };
            fold_dls_cons p nd.key (remove_first k (L.tl l)) prev_ptr concrete_tp None nd' new_hp;
            // dls p (nd.key :: remove_first k (L.tl l)) prev_ptr concrete_tp None
            fold_delete_result_cons p concrete_tp prev_ptr (nd.key :: remove_first k (L.tl l));
            rewrite each (nd.key :: remove_first k (L.tl l)) as (remove_first k l);
            (Some p, Some concrete_tp)
          }
        }
      }
    }
  }
}

//SNIPPET_START: dll_list_delete
fn list_delete (hd_ref tl_ref: ref dptr) (k: int) (#l: erased (list int))
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_first k l)
//SNIPPET_END: dll_list_delete
{
  let hd = Pulse.Lib.Reference.(!hd_ref);
  let tl = Pulse.Lib.Reference.(!tl_ref);
  match hd {
    norewrite None -> {
      // Empty list: nothing to delete
      dll_none_nil hd tl;
      // l == [], so remove_first k l == remove_first k [] == [] == l
      rewrite each l as (remove_first k l) in (dll hd tl l);
      Pulse.Lib.Reference.(hd_ref := hd);
      Pulse.Lib.Reference.(tl_ref := tl)
    }
    norewrite Some hp -> {
      // Non-empty: search and delete
      dll_some_cons hd tl;
      unfold_dll_cons hd tl;
      with hp' tp. _;
      rewrite each hp' as hp;
      let concrete_tp = Some?.v tl;
      rewrite each tp as concrete_tp;
      let r = delete_in_dls hp k None concrete_tp;
      let new_hd = fst r;
      let new_tl = snd r;
      rewrite each (fst r) as new_hd in
        (delete_result (fst r) (snd r) None (remove_first k l));
      rewrite each (snd r) as new_tl in
        (delete_result new_hd (snd r) None (remove_first k l));
      delete_result_to_dll new_hd new_tl;
      Pulse.Lib.Reference.(hd_ref := new_hd);
      Pulse.Lib.Reference.(tl_ref := new_tl)
    }
  }
}

// --- P0.4.24: LIST-DELETE-NODE — O(n) indexed deletion ---
// CLRS LIST-DELETE(L, x): Given index i, delete the node at position i.
//
// Implementation uses recursive traversal to position i (O(n)), then performs
// O(1) pointer surgery. The recursive structure naturally handles the ghost
// predicate split/join without admits.
//
// Precondition: caller provides the dll and an erased index i < L.length l.
// Postcondition: dll with the element at position i removed.

// remove_at is defined in CLRS.Ch10.DLL.Impl.fsti

// Recursive delete at index i within a DLS segment.
// Similar to delete_in_dls, but uses position index instead of key search.
fn rec delete_at_in_dls
  (p: box node) (i: nat) (prev_ptr: dptr) (tail_ptr: box node)
  (#l: erased (list int) {Cons? l /\ i < L.length l})
  requires dls p l prev_ptr tail_ptr None
  returns r: (dptr & dptr)
  ensures delete_result (fst r) (snd r) prev_ptr (remove_at i l)
  decreases L.length l
{
  factor_dls p l prev_ptr tail_ptr None;
  unfold (dls_factored p l prev_ptr tail_ptr None);
  with v. assert (pts_to p v);
  let nd = Box.(!p);
  let nxt = nd.next;
  if (i = 0) {
    // Found position 0 — delete current node
    match nxt {
      norewrite None -> {
        // Singleton: free node, return empty
        factored_next_none_nil p;
        let hd_l = hide (L.hd l);
        rewrite each l as [reveal hd_l] in (dls_factored_next p l tail_ptr None None);
        unfold (dls_factored_next p [reveal hd_l] tail_ptr None None);
        Box.free p;
        let none_ptr : dptr = None;
        fold_delete_result_nil none_ptr none_ptr prev_ptr;
        rewrite each ([] #int) as (remove_at i l);
        (none_ptr, none_ptr)
      }
      norewrite Some np -> {
        // Multi: free head, return tail with updated prev
        factored_next_some_cons p np;
        elim_factored_next p np;
        Box.free p;
        set_prev np prev_ptr;
        fold_delete_result_cons np tail_ptr prev_ptr (L.tl l);
        rewrite each (L.tl l) as (remove_at i l);
        (Some np, Some tail_ptr)
      }
    }
  } else {
    // Position i > 0 — recurse on tail
    match nxt {
      norewrite None -> {
        // Singleton, but i > 0: impossible given i < L.length l
        factored_next_none_nil p;
        unreachable()
      }
      norewrite Some np -> {
        // Multi: recurse on tail segment with i-1
        factored_next_some_cons p np;
        elim_factored_next p np;
        let r = delete_at_in_dls np (i - 1) (Some p) tail_ptr;
        let new_hd = fst r;
        let new_tl = snd r;
        rewrite each (fst r) as new_hd in
          (delete_result (fst r) (snd r) (Some p) (remove_at (i - 1) (L.tl l)));
        rewrite each (snd r) as new_tl in
          (delete_result new_hd (snd r) (Some p) (remove_at (i - 1) (L.tl l)));
        match new_hd {
          norewrite None -> {
            unfold_delete_result_nil new_hd new_tl (Some p);
            rewrite each (remove_at (i - 1) (L.tl l))
                      as ([] #int)
                      in (delete_result new_hd new_tl (Some p) (remove_at (i - 1) (L.tl l)));
            unfold (delete_result new_hd new_tl (Some p) []);
            Box.(p := { nd with next = None });
            fold (dls p [nd.key] prev_ptr p None);
            fold_delete_result_cons p p prev_ptr [nd.key];
            rewrite each [nd.key] as (remove_at i l);
            (Some p, Some p)
          }
          norewrite Some new_hp -> {
            unfold_delete_result_cons new_hd new_tl (Some p);
            extract_delete_result_cons new_hd new_tl (Some p);
            with hp' tp'. _;
            rewrite each hp' as new_hp;
            let concrete_tp = Some?.v new_tl;
            rewrite each tp' as concrete_tp;
            Box.(p := { nd with next = Some new_hp });
            let nd' = { nd with next = Some new_hp };
            fold_dls_cons p nd.key (remove_at (i - 1) (L.tl l)) prev_ptr concrete_tp None nd' new_hp;
            fold_delete_result_cons p concrete_tp prev_ptr (nd.key :: remove_at (i - 1) (L.tl l));
            rewrite each (nd.key :: remove_at (i - 1) (L.tl l)) as (remove_at i l);
            (Some p, Some concrete_tp)
          }
        }
      }
    }
  }
}

fn list_delete_node
  (hd_ref tl_ref: ref dptr)
  (#l: erased (list int) {Cons? l})
  (i: nat {i < L.length l})
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_at i l)
{
  let hd = Pulse.Lib.Reference.(!hd_ref);
  let tl = Pulse.Lib.Reference.(!tl_ref);
  unfold_dll_cons hd tl;
  with hp tp. _;
  let concrete_hp = Some?.v hd;
  let concrete_tp = Some?.v tl;
  rewrite each hp as concrete_hp;
  rewrite each tp as concrete_tp;
  
  let r = delete_at_in_dls concrete_hp i None concrete_tp;
  let new_hd = fst r;
  let new_tl = snd r;
  rewrite each (fst r) as new_hd in
    (delete_result (fst r) (snd r) None (remove_at i l));
  rewrite each (snd r) as new_tl in
    (delete_result new_hd (snd r) None (remove_at i l));
  delete_result_to_dll new_hd new_tl;
  Pulse.Lib.Reference.(hd_ref := new_hd);
  Pulse.Lib.Reference.(tl_ref := new_tl)
}

// --- LIST-DELETE-LAST ---
// Delete the last occurrence of key k from the DLL.
// Uses forward search to determine whether k appears in the tail,
// then either deletes at the current position or recurses.

// remove_last is defined in CLRS.Ch10.DLL.Impl.fsti

let remove_last_head (k: int) (l: list int)
  : Lemma (requires Cons? l /\ L.hd l = k /\ not (L.mem k (L.tl l)))
          (ensures remove_last k l == L.tl l) = ()

let remove_last_skip (k: int) (l: list int)
  : Lemma (requires Cons? l /\ L.mem k (L.tl l))
          (ensures remove_last k l == L.hd l :: remove_last k (L.tl l)) = ()

let remove_last_miss (k: int) (l: list int)
  : Lemma (requires Cons? l /\ L.hd l <> k /\ not (L.mem k (L.tl l)))
          (ensures remove_last k l == l) = ()

fn rec delete_last_in_dls
  (p: box node) (k: int) (prev_ptr: dptr) (tail_ptr: box node)
  (#l: erased (list int) {Cons? l})
  requires dls p l prev_ptr tail_ptr None
  returns r: (dptr & dptr)
  ensures delete_result (fst r) (snd r) prev_ptr (remove_last k l)
{
  factor_dls p l prev_ptr tail_ptr None;
  unfold (dls_factored p l prev_ptr tail_ptr None);
  with v. assert (pts_to p v);
  let nd = Box.(!p);
  let nxt = nd.next;
  match nxt {
    norewrite None -> {
      // Singleton list
      factored_next_none_nil p;
      if (nd.key = k) {
        // Only element matches — delete it
        remove_last_head k l;
        let hd_l = hide (L.hd l);
        rewrite each l as [reveal hd_l] in (dls_factored_next p l tail_ptr None None);
        unfold (dls_factored_next p [reveal hd_l] tail_ptr None None);
        Box.free p;
        let none_ptr : dptr = None;
        fold_delete_result_nil none_ptr none_ptr prev_ptr;
        rewrite each ([] #int) as (remove_last k l);
        (none_ptr, none_ptr)
      } else {
        // Key not found
        remove_last_miss k l;
        fold (dls_factored p l prev_ptr tail_ptr None);
        unfactor_dls p l prev_ptr tail_ptr None;
        fold_delete_result_cons p tail_ptr prev_ptr l;
        rewrite each l as (remove_last k l);
        (Some p, Some tail_ptr)
      }
    }
    norewrite Some np -> {
      // Multi-element list
      factored_next_some_cons p np;
      elim_factored_next p np;
      // dls np (L.tl l) (Some p) tail_ptr None
      // Search the tail for k
      let in_tail = search_dls np k;
      if in_tail {
        // k appears in tail — recurse (this is not the last occurrence)
        remove_last_skip k l;
        let r = delete_last_in_dls np k (Some p) tail_ptr;
        let new_hd = fst r;
        let new_tl = snd r;
        rewrite each (fst r) as new_hd in
          (delete_result (fst r) (snd r) (Some p) (remove_last k (L.tl l)));
        rewrite each (snd r) as new_tl in
          (delete_result new_hd (snd r) (Some p) (remove_last k (L.tl l)));
        match new_hd {
          norewrite None -> {
            // Tail became empty after delete
            unfold_delete_result_nil new_hd new_tl (Some p);
            rewrite each (remove_last k (L.tl l))
                      as ([] #int)
                      in (delete_result new_hd new_tl (Some p) (remove_last k (L.tl l)));
            unfold (delete_result new_hd new_tl (Some p) []);
            Box.(p := { nd with next = None });
            fold (dls p [nd.key] prev_ptr p None);
            fold_delete_result_cons p p prev_ptr [nd.key];
            rewrite each [nd.key] as (remove_last k l);
            (Some p, Some p)
          }
          norewrite Some new_hp -> {
            // Tail still has elements after delete
            unfold_delete_result_cons new_hd new_tl (Some p);
            extract_delete_result_cons new_hd new_tl (Some p);
            with hp' tp'. _;
            rewrite each hp' as new_hp;
            let concrete_tp = Some?.v new_tl;
            rewrite each tp' as concrete_tp;
            Box.(p := { nd with next = Some new_hp });
            let nd' = { nd with next = Some new_hp };
            fold_dls_cons p nd.key (remove_last k (L.tl l)) prev_ptr concrete_tp None nd' new_hp;
            fold_delete_result_cons p concrete_tp prev_ptr (nd.key :: remove_last k (L.tl l));
            rewrite each (nd.key :: remove_last k (L.tl l)) as (remove_last k l);
            (Some p, Some concrete_tp)
          }
        }
      } else if (nd.key = k) {
        // This IS the last occurrence — delete this node
        remove_last_head k l;
        Box.free p;
        set_prev np prev_ptr;
        fold_delete_result_cons np tail_ptr prev_ptr (L.tl l);
        rewrite each (L.tl l) as (remove_last k l);
        (Some np, Some tail_ptr)
      } else {
        // Key not found anywhere
        remove_last_miss k l;
        intro_factored_next p np;
        rewrite each (Some np) as v.next;
        fold (dls_factored p l prev_ptr tail_ptr None);
        unfactor_dls p l prev_ptr tail_ptr None;
        fold_delete_result_cons p tail_ptr prev_ptr l;
        rewrite each l as (remove_last k l);
        (Some p, Some tail_ptr)
      }
    }
  }
}

fn list_delete_last (hd_ref tl_ref: ref dptr) (k: int) (#l: erased (list int))
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_last k l)
{
  let hd = Pulse.Lib.Reference.(!hd_ref);
  let tl = Pulse.Lib.Reference.(!tl_ref);
  match hd {
    norewrite None -> {
      dll_none_nil hd tl;
      // l == [], so remove_last k l == remove_last k [] == [] == l
      rewrite each l as (remove_last k l) in (dll hd tl l);
      Pulse.Lib.Reference.(hd_ref := hd);
      Pulse.Lib.Reference.(tl_ref := tl)
    }
    norewrite Some hp -> {
      dll_some_cons hd tl;
      unfold_dll_cons hd tl;
      with hp' tp. _;
      rewrite each hp' as hp;
      let concrete_tp = Some?.v tl;
      rewrite each tp as concrete_tp;
      let r = delete_last_in_dls hp k None concrete_tp;
      let new_hd = fst r;
      let new_tl = snd r;
      rewrite each (fst r) as new_hd in
        (delete_result (fst r) (snd r) None (remove_last k l));
      rewrite each (snd r) as new_tl in
        (delete_result new_hd (snd r) None (remove_last k l));
      delete_result_to_dll new_hd new_tl;
      Pulse.Lib.Reference.(hd_ref := new_hd);
      Pulse.Lib.Reference.(tl_ref := new_tl)
    }
  }
}
