module CLRS.Ch10.DLL.Impl
// CLRS §10.2: True Doubly-Linked List
//
// Nodes have {key, prev, next}. Segment predicate `dls` from Pulse.Lib.Deque.
// Operations: LIST-INSERT (O(1)), LIST-SEARCH (O(n)), LIST-DELETE (O(n)),
//             LIST-DELETE-NODE (O(n) traversal to index, O(1) pointer surgery)
//
// All operations fully verified with 0 admits.

#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module L = FStar.List.Tot
open FStar.List.Tot

// Types node, dptr and predicates dls, dll are defined in CLRS.Ch10.DLL.Impl.fsti

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
fn list_insert (hd_ref tl_ref: ref dptr) (x: int)
  requires exists* hd tl l.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl' l.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (x :: l)
//SNIPPET_END: dll_list_insert
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
fn list_delete (hd_ref tl_ref: ref dptr) (k: int)
  requires exists* hd tl l.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl' l.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_first k l)
//SNIPPET_END: dll_list_delete
{
  let hd = Pulse.Lib.Reference.(!hd_ref);
  let tl = Pulse.Lib.Reference.(!tl_ref);
  with l. assert (dll hd tl l);
  match hd {
    norewrite None -> {
      // Empty list: nothing to delete
      dll_none_nil hd tl;
      rewrite each l as ([] #int) in (dll hd tl l);
      rewrite each ([] #int) as (remove_first k ([] #int));
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
  (hd_ref tl_ref: ref dptr) (x: box node)
  (#l: erased (list int) {Cons? l})
  (i: nat {i < L.length l})
  requires exists* hd tl.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_at i l)
{
  let hd = Pulse.Lib.Reference.(!hd_ref);
  let tl = Pulse.Lib.Reference.(!tl_ref);
  with l_orig. assert (dll hd tl l_orig);
  
  // l is Cons? so hd is Some
  rewrite each l_orig as l in (dll hd tl l_orig);
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
