module CLRS.Ch10.DLL
// CLRS §10.2: True Doubly-Linked List
//
// Nodes have {key, prev, next}. Segment predicate `dls` from Pulse.Lib.Deque.
// Operations: LIST-INSERT (O(1)), LIST-SEARCH (O(n)), LIST-DELETE (O(n))
//
// Fully verified: 0 admits, 0 assumes.

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
  rewrite each (hd :: r0 :: rs) as l
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
  rewrite each l as (hd :: r0 :: rs);
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
    rewrite each nd.next as v.next;
    fold (dls_factored p l prev_ptr tail None);
    unfactor_dls p l prev_ptr tail None;
    true
  } else {
    match nxt {
      norewrite None -> {
        // nd.next == None with last_ptr == None => singleton
        rewrite each nd.next as v.next;
        factored_next_none_nil p;
        fold (dls_factored p l prev_ptr tail None);
        unfactor_dls p l prev_ptr tail None;
        false
      }
      norewrite Some np -> {
        // nd.next == Some np with last_ptr == None => multi-element
        rewrite each nd.next as v.next;
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
        rewrite each nd.next as v.next;
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
        rewrite each nd.next as v.next;
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
        rewrite each nd.next as v.next;
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
        rewrite each nd.next as v.next;
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

fn list_delete (hd_ref tl_ref: ref dptr) (k: int)
  requires exists* hd tl l.
    pts_to hd_ref hd ** pts_to tl_ref tl ** dll hd tl l
  ensures exists* hd' tl' l'.
    pts_to hd_ref hd' ** pts_to tl_ref tl' ** dll hd' tl' (remove_first k l')
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
