module CLRS.Ch10.Stack
#lang-pulse
open Pulse.Lib.Pervasives

module V = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

open Pulse.Lib.Vec
open Pulse.Lib.Box

// Helper lemma: empty list has all indices valid (vacuous)
let lemma_empty_list_inv (arr_seq: Seq.seq 'a) 
  : Lemma (forall (i:nat). i < L.length ([]) ==> 
           Seq.index arr_seq i == L.index ([] <: list 'a) i)
  = ()

// Helper lemma: indexing into append
let rec lemma_index_append (#a:Type) (l1 l2: list a) (i:nat)
  : Lemma 
    (requires i < L.length (L.append l1 l2))
    (ensures 
      (if i < L.length l1 
       then L.index (L.append l1 l2) i == L.index l1 i
       else (i - L.length l1 < L.length l2 /\
             L.index (L.append l1 l2) i == L.index l2 (i - L.length l1))))
    (decreases l1)
  = match l1 with
    | [] -> ()
    | x :: xs -> if i = 0 then () else lemma_index_append xs l2 (i - 1)

// Helper lemma: length of append
let rec lemma_append_length (#a:Type) (l1 l2: list a)
  : Lemma (L.length (L.append l1 l2) == L.length l1 + L.length l2)
  = match l1 with
    | [] -> ()
    | x :: xs -> lemma_append_length xs l2

// Helper lemma: after updating array at position n with new_elem, 
// the correspondence between array and list is maintained
let lemma_array_update_preserves_prefix 
  (#a:Type)
  (arr_seq: Seq.seq a)
  (xs: list a)
  (new_elem: a)
  (n: nat)
  : Lemma 
    (requires 
      n == L.length xs /\
      n < Seq.length arr_seq /\
      (forall (i:nat). i < L.length xs ==> Seq.index arr_seq i == L.index xs i))
    (ensures 
      (let new_seq = Seq.upd arr_seq n new_elem in
       let new_list = L.append xs [new_elem] in
       L.length new_list == n + 1 /\
       Seq.length new_seq == Seq.length arr_seq /\
       (forall (i:nat). i < n ==> Seq.index new_seq i == L.index new_list i) /\
       Seq.index new_seq n == new_elem /\
       L.index new_list n == new_elem))
  = let new_seq = Seq.upd arr_seq n new_elem in
    let new_list = L.append xs [new_elem] in
    lemma_append_length xs [new_elem];
    lemma_index_append xs [new_elem] n;
    // Prove that earlier indices are preserved
    let aux (i:nat{i < n}) : Lemma (Seq.index new_seq i == L.index new_list i) =
      lemma_index_append xs [new_elem] i
    in
    Classical.forall_intro aux

// Helper lemma: init has one fewer element
let rec lemma_init_length (#a:Type) (xs: list a{L.length xs > 0})
  : Lemma (ensures L.length (L.init xs) == L.length xs - 1)
          (decreases xs)
  = match xs with
    | [x] -> ()
    | x :: xs' -> lemma_init_length xs'

// Helper lemma: init gives us all but last element
let rec lemma_init_index (#a:Type) (xs: list a{L.length xs > 0}) (i:nat{i < L.length (L.init xs)})
  : Lemma 
    (ensures 
      i < L.length xs /\
      L.index (L.init xs) i == L.index xs i)
    (decreases xs)
  = lemma_init_length xs;
    match xs with
    | [x] -> ()
    | x :: xs' -> 
        if i = 0 then () 
        else (
          lemma_init_index xs' (i - 1)
        )

// Helper lemma: last element equals index at length-1
let rec lemma_last_index (#a:Type) (xs: list a{L.length xs > 0})
  : Lemma (ensures L.last xs == L.index xs (L.length xs - 1))
          (decreases xs)
  = match xs with
    | [x] -> ()
    | x :: xs' -> lemma_last_index xs'

// Helper lemma: init and last reconstruct the original list
let rec lemma_init_last_append (#a:Type) (xs: list a{L.length xs > 0})
  : Lemma (ensures L.append (L.init xs) [L.last xs] == xs)
          (decreases xs)
  = match xs with
    | [x] -> ()
    | x :: xs' -> lemma_init_last_append xs'

// Helper lemma: removing last element preserves prefix invariant - simplified version
let lemma_prefix_after_pop
  (#a:Type)
  (arr_seq: Seq.seq a)
  (xs: list a{L.length xs > 0})
  : Lemma 
    (requires 
      L.length xs <= Seq.length arr_seq /\
      (forall (i:nat). i < L.length xs ==> Seq.index arr_seq i == L.index xs i))
    (ensures 
      L.length (L.init xs) == L.length xs - 1 /\
      L.length (L.init xs) < Seq.length arr_seq /\
      (forall (i:nat). i < L.length (L.init xs) ==> 
         i < L.length xs /\ L.index (L.init xs) i == L.index xs i))
  = lemma_init_length xs;
    let aux (i:nat{i < L.length (L.init xs)}) : Lemma (L.index (L.init xs) i == L.index xs i /\ i < L.length xs) =
      lemma_init_index xs i
    in
    Classical.forall_intro aux

// Create a new empty stack with given capacity
fn create_stack (t:Type0) (default_val: t) (capacity: SZ.t)
  requires emp ** pure (SZ.v capacity > 0 /\ SZ.fits (SZ.v capacity + 1))
  returns s: stack t
  ensures stack_inv s (hide []) ** 
          pure (reveal s.capacity == SZ.v capacity /\ SZ.v capacity > 0)
{
  let arr = V.alloc default_val capacity;
  with arr_seq. assert (V.pts_to arr arr_seq);
  let top_ref = B.alloc 0sz;
  
  let s : stack t = {
    data = arr;
    top = top_ref;
    capacity = hide (SZ.v capacity);
  };
  
  // Rewrite to use s.data and s.top
  rewrite (V.pts_to arr arr_seq) as (V.pts_to s.data arr_seq);
  rewrite (B.pts_to top_ref 0sz) as (B.pts_to s.top 0sz);
  
  // Prove the invariant for empty list
  lemma_empty_list_inv #t arr_seq;
  
  // Assert pure facts before folding
  assert (pure (reveal s.capacity == SZ.v capacity));
  assert (pure (SZ.v capacity > 0));
  
  // Establish the invariant
  fold (stack_inv s (hide []));
  
  s
}

// Check if stack is empty
fn stack_empty (#t:Type0) (s: stack t) (#contents: erased (list t))
  requires stack_inv s contents
  returns b: bool
  ensures stack_inv s contents **
          pure (b <==> L.length (reveal contents) == 0)
{
  unfold (stack_inv s contents);
  with arr_seq top_v. _;
  
  let top_val = !s.top;
  
  let is_empty = (top_val = 0sz);
  
  fold (stack_inv s contents);
  is_empty
}

// Push an element onto the stack
fn push (#t:Type0) (s: stack t) (#contents: erased (list t)) (x: t)
  requires stack_inv s contents **
           pure (L.length (reveal contents) < reveal s.capacity)
  returns unit
  ensures stack_inv s (hide (L.append (reveal contents) [x]))
{
  unfold (stack_inv s contents);
  with arr_seq top_v. _;
  
  // Read current top
  let top_val = !s.top;
  
  // Write element at top position
  s.data.(top_val) <- x;
  with new_arr_seq. assert (V.pts_to s.data new_arr_seq);
  
  // Prove the array invariant is maintained
  lemma_array_update_preserves_prefix arr_seq (reveal contents) x (SZ.v top_val);
  
  // Prove that incrementing is safe
  // We have: SZ.v top_val <= reveal s.capacity and SZ.fits (reveal s.capacity + 1)
  // So: SZ.fits (SZ.v top_val + 1)
  assert (pure (SZ.v top_val + 1 <= reveal s.capacity + 1));
  assert (pure (SZ.fits (SZ.v top_val + 1)));
  
  // Increment top
  let new_top = SZ.add top_val 1sz;
  
  // Update top pointer
  s.top := new_top;
  
  // Establish new invariant
  fold (stack_inv s (hide (L.append (reveal contents) [x])))
}

// Pop an element from the stack
fn pop (#t:Type0) (s: stack t) (#contents: erased (list t))
  requires stack_inv s contents
  requires pure (L.length (reveal contents) > 0)
  returns x: t
  ensures exists* xs. 
    stack_inv s (hide xs) **
    pure (L.append xs [x] == reveal contents)
{
  unfold (stack_inv s contents);
  with arr_seq top_v. _;
  
  // Read current top (points to next free slot)
  let top_val = !s.top;
  
  // Decrement top to point to the element to pop
  let new_top = SZ.sub top_val 1sz;
  
  // Read the element at the top
  let elem = s.data.(new_top);
  
  // Update top pointer
  s.top := new_top;
  
  // Prove that the element we read is the last element
  // From invariant: SZ.v top_v == L.length contents
  // So: SZ.v new_top == SZ.v top_v - 1 == L.length contents - 1
  assert (pure (SZ.v new_top == L.length (reveal contents) - 1));
  // From invariant: Seq.index arr_seq i == L.index contents i for i < length
  assert (pure (Seq.index arr_seq (SZ.v new_top) == L.index (reveal contents) (L.length (reveal contents) - 1)));
  // Prove last equals index at length-1
  lemma_last_index (reveal contents);
  assert (pure (elem == L.last (reveal contents)));
  
  // Prove the invariant for the remaining elements
  let remaining = hide (L.init (reveal contents));
  lemma_prefix_after_pop arr_seq (reveal contents);
  lemma_init_last_append (reveal contents);
  
  // Establish new invariant
  fold (stack_inv s remaining);
  
  elem
}

// Peek at the top element without removing it  
fn peek (#t:Type0) (s: stack t) (#contents: erased (list t))
  requires stack_inv s contents
  requires pure (Cons? (reveal contents))
  returns x: t
  ensures stack_inv s contents **
          pure (exists (init:list t). L.append init [x] == reveal contents)
{
  unfold (stack_inv s contents);
  with arr_seq top_v. _;
  
  // Read current top (points to next free slot)
  let top_val = !s.top;
  
  // Read the element at top-1 (the actual top of stack)
  let idx = SZ.sub top_val 1sz;
  let elem = s.data.(idx);
  
  // Prove that elem is the last element
  assert (pure (SZ.v idx == L.length (reveal contents) - 1));
  assert (pure (elem == L.index (reveal contents) (L.length (reveal contents) - 1)));
  lemma_last_index (reveal contents);
  lemma_init_last_append (reveal contents);
  assert (pure (elem == L.last (reveal contents)));
  
  // Restore invariant
  fold (stack_inv s contents);
  
  elem
}
