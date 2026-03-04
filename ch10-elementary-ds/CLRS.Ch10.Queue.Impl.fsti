module CLRS.Ch10.Queue
#lang-pulse
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

// Queue data structure: circular buffer with head, tail, and size tracking
//
// Design note: CLRS uses a 2-field design (head + tail) where an empty slot
// distinguishes full from empty (at most n−1 elements in an n-slot array).
// We use a 3-field design (head + tail + size) which allows the full capacity
// to be used and simplifies the full/empty invariant at the cost of one extra
// field. The ENQUEUE/DEQUEUE logic is otherwise identical to CLRS §10.1.
//SNIPPET_START: queue_type
noeq type queue (t:Type) = {
  data: V.vec t;
  head: B.box SZ.t;     // Front of queue (dequeue position)
  tail: B.box SZ.t;     // Next insertion point (enqueue position)
  size: B.box SZ.t;     // Current number of elements
  capacity_sz: SZ.t;    // Runtime capacity value
  capacity: erased nat; // Ghost capacity for specification
}
//SNIPPET_END: queue_type

// Queue invariant: relates circular buffer to logical list of elements
//SNIPPET_START: queue_inv
let queue_inv (#t:Type) (q: queue t) (contents: erased (list t)) : slprop = 
  exists* arr_seq head_v tail_v size_v.
    V.pts_to q.data arr_seq **
    B.pts_to q.head head_v **
    B.pts_to q.tail tail_v **
    B.pts_to q.size size_v **
    pure (
      SZ.v q.capacity_sz == reveal q.capacity /\
      SZ.v size_v == L.length contents /\
      SZ.v size_v <= reveal q.capacity /\
      SZ.v head_v < reveal q.capacity /\
      SZ.v tail_v < reveal q.capacity /\
      SZ.v tail_v == (SZ.v head_v + SZ.v size_v) % reveal q.capacity /\
      Seq.length arr_seq == reveal q.capacity /\
      reveal q.capacity > 0 /\
      // Queue elements are stored in circular fashion
      (forall (i:nat). i < SZ.v size_v ==> 
        Seq.index arr_seq ((SZ.v head_v + i) % reveal q.capacity) == 
        L.index contents i)
    )
//SNIPPET_END: queue_inv

//SNIPPET_START: queue_ops
// Create a new empty queue with given capacity
fn create_queue (t:Type0) (default_val: t) (capacity: SZ.t)
  requires emp
  requires pure (SZ.v capacity > 0 /\ SZ.fits (SZ.v capacity + 1))
  returns q: queue t
  ensures queue_inv q (hide []) ** 
          pure (reveal q.capacity == SZ.v capacity)

// Check if queue is empty
fn queue_empty (#t:Type0) (q: queue t) (#contents: erased (list t))
  requires queue_inv q contents
  returns b: bool
  ensures queue_inv q contents **
          pure (b <==> L.length (reveal contents) == 0)

// Enqueue an element at the tail
fn enqueue (#t:Type0) (q: queue t) (#contents: erased (list t)) (x: t)
  requires queue_inv q contents **
           pure (L.length (reveal contents) < reveal q.capacity)
  returns unit
  ensures queue_inv q (hide (L.append (reveal contents) [x]))

// Dequeue an element from the head
fn dequeue (#t:Type0) (q: queue t) (#contents: erased (list t))
  requires queue_inv q contents
  requires pure (L.length (reveal contents) > 0)
  returns x: t
  ensures exists* xs. 
    queue_inv q (hide xs) **
    pure (reveal contents == x :: xs)
//SNIPPET_END: queue_ops
