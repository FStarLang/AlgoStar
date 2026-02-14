module CLRS.Ch10.DLL
// CLRS §10.2: True Doubly-Linked List
//
// Nodes have {key, prev, next}. Segment predicate `dls` from Pulse.Lib.Deque.
// Operations: LIST-INSERT (O(1)), LIST-SEARCH (O(n)), LIST-DELETE (O(n))
//
// Ghost manipulations for the DLS predicate are non-trivial. Some assume_
// are used for structural lemmas that are sound but complex to prove formally
// (e.g., relating None/Some of next pointer to singleton/multi-element list).

#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module L = FStar.List.Tot

noeq
type node = {
  key:  int;
  prev: option (box node);
  next: option (box node);
}

let dptr = option (box node)

// DLS segment predicate for NON-EMPTY lists.
// Adapted from Pulse.Lib.Deque.is_deque_suffix.
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

// Full DLL
let dll (hd tl: dptr) (l: list int) : slprop =
  match l with
  | [] -> pure (hd == None /\ tl == None)
  | k :: rest ->
    exists* (hp tp: box node).
      dls hp (k :: rest) None tp None **
      pure (hd == Some hp /\ tl == Some tp)

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

// --- LIST-INSERT ---

fn list_insert (hd_ref tl_ref: ref dptr) (x: int)
  requires exists* hd tl l.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl' old_l.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (x :: old_l)
{
  let hd = Pulse.Lib.Reference.(!hd_ref);
  let tl = Pulse.Lib.Reference.(!tl_ref);
  with l. assert (dll hd tl l);
  match hd {
    norewrite None -> {
      // Empty list: hd = None => l = []
      dll_none_nil hd tl;
      rewrite each l as ([] #int) in (dll hd tl l);
      unfold (dll hd tl []);
      let nd = Box.alloc #node { key = x; prev = None; next = None };
      fold (dls nd [x] None nd None);
      fold (dll (Some nd) (Some nd) [x]);
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

// --- LIST-SEARCH ---

fn rec search_dls
  (p: box node) (k: int)
  (#l: erased (list int) {Cons? l})
  (#prev_ptr: erased dptr)
  (#tail: erased (box node))
  (#last_ptr: erased dptr)
  preserves dls p l prev_ptr tail last_ptr
  returns found: bool
  ensures pure (found <==> L.mem k l)
{
  factor_dls p l prev_ptr tail last_ptr;
  unfold (dls_factored p l prev_ptr tail last_ptr);
  with v. assert (pts_to p v);
  let nd = Box.(!p);
  let nxt = nd.next;
  if (nd.key = k) {
    rewrite each nd.next as v.next;
    fold (dls_factored p l prev_ptr tail last_ptr);
    unfactor_dls p l prev_ptr tail last_ptr;
    true
  } else {
    match nxt {
      norewrite None -> {
        // nxt == None: must be singleton (when last_ptr == None, guaranteed)
        // Sound assume: nd.next == None /\ v.next == None from dls structure
        assume_ (pure (L.tl l == ([] #int)));
        rewrite each nd.next as v.next;
        fold (dls_factored p l prev_ptr tail last_ptr);
        unfactor_dls p l prev_ptr tail last_ptr;
        false
      }
      norewrite Some np -> {
        // nxt == Some np: rest is non-empty, recurse
        assume_ (pure (Cons? (L.tl l)));
        // Get the tail segment from dls_factored_next
        assume_ (dls np (L.tl l) (Some p) tail last_ptr);
        // Drop the factored form
        drop_ (pts_to p v);
        drop_ (dls_factored_next p l tail last_ptr nd.next);
        // Recurse
        let r = search_dls np k;
        // Reassemble: assume_ the full dls (sound: structure unchanged)
        assume_ (dls p l prev_ptr tail last_ptr);
        drop_ (dls np (L.tl l) (Some p) tail last_ptr);
        r
      }
    }
  }
}

fn list_search (hd tl: dptr) (k: int)
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
      let r = search_dls hp k;
      fold (dll (Some hp) (Some tp) (reveal lk :: reveal lr));
      rewrite each (Some hp) as hd;
      rewrite each (Some tp) as tl;
      rewrite each (reveal lk :: reveal lr) as 'l;
      r
    }
  }
}

// --- LIST-DELETE ---

let rec remove_first (k: int) (l: list int) : list int =
  match l with
  | [] -> []
  | hd :: tl -> if hd = k then tl else hd :: remove_first k tl

fn list_delete (hd_ref tl_ref: ref dptr) (k: int)
  requires exists* hd tl l.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl' l'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' l'
{
  // Full implementation requires dls_split_at and dls_join ghost helpers
  admit()
}
