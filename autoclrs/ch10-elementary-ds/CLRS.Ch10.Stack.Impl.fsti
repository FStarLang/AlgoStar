module CLRS.Ch10.Stack.Impl
#lang-pulse
open Pulse.Lib.Pervasives

module V = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

// Stack data structure: array-based with top pointer
//SNIPPET_START: stack_type
noeq type stack (t:Type) = {
  data: V.vec t;
  top: B.box SZ.t;      // Index of next free slot (0 = empty)
  capacity: erased nat;
}
//SNIPPET_END: stack_type

// Stack invariant: relates array to logical list of elements
//SNIPPET_START: stack_inv
let stack_inv (#t:Type) (s: stack t) (contents: erased (list t)) : slprop = 
  exists* arr_seq top_v.
    V.pts_to s.data arr_seq **
    B.pts_to s.top top_v **
    pure (
      SZ.v top_v == L.length contents /\
      SZ.v top_v <= reveal s.capacity /\
      Seq.length arr_seq == reveal s.capacity /\
      SZ.fits (reveal s.capacity + 1) /\  // Ensure we can increment up to capacity
      // Array stores elements in same order as list: list index = array index
      (forall (i:nat). i < L.length contents ==> 
        Seq.index arr_seq i == L.index contents i)
    )
//SNIPPET_END: stack_inv

//SNIPPET_START: stack_ops
// Create a new empty stack with given capacity
fn create_stack (t:Type0) (default_val: t) (capacity: SZ.t)
  requires emp ** pure (SZ.v capacity > 0 /\ SZ.fits (SZ.v capacity + 1))
  returns s: stack t
  ensures stack_inv s (hide []) ** 
          pure (reveal s.capacity == SZ.v capacity /\ SZ.v capacity > 0)

// Check if stack is empty
fn stack_empty (#t:Type0) (s: stack t) (#contents: erased (list t))
  requires stack_inv s contents
  returns b: bool
  ensures stack_inv s contents **
          pure (b <==> L.length (reveal contents) == 0)

// Push an element onto the stack (adds to end of list)
fn push (#t:Type0) (s: stack t) (#contents: erased (list t)) (x: t)
  requires stack_inv s contents **
           pure (L.length (reveal contents) < reveal s.capacity)
  returns unit
  ensures stack_inv s (hide (L.append (reveal contents) [x]))

// Pop an element from the stack (removes from end of list)
fn pop (#t:Type0) (s: stack t) (#contents: erased (list t))
  requires stack_inv s contents
  requires pure (L.length (reveal contents) > 0)
  returns x: t
  ensures exists* xs. 
    stack_inv s (hide xs) **
    pure (L.append xs [x] == reveal contents)

// Peek at the top element without removing it (last element in list)
fn peek (#t:Type0) (s: stack t) (#contents: erased (list t))
  requires stack_inv s contents
  requires pure (Cons? (reveal contents))
  returns x: t
  ensures stack_inv s contents **
          pure (Cons? (reveal contents) /\
                (if Cons? (reveal contents) then x == L.last (reveal contents) else True))
//SNIPPET_END: stack_ops
