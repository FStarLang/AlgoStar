module CLRS.Ch10.Queue.Test
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.Queue.Impl

module Q = CLRS.Ch10.Queue.Impl
module SZ = FStar.SizeT
module L = FStar.List.Tot

// Test basic queue operations
fn test_queue ()
  requires emp
  returns _:unit
  ensures exists* (q:Q.queue int) (contents:Ghost.erased (list int)). Q.queue_inv q contents
{
  // Create a queue with capacity 5
  let q = Q.create_queue int 0 5sz;
  
  // Check if empty
  let is_empty = Q.queue_empty q;
  assert (pure (is_empty == true));
  
  // Enqueue some elements
  Q.enqueue q 10;
  Q.enqueue q 20;
  Q.enqueue q 30;
  
  // Check if not empty
  let is_empty2 = Q.queue_empty q;
  assert (pure (is_empty2 == false));
  
  // Dequeue elements and check FIFO order
  let x1 = Q.dequeue q;
  assert (pure (x1 == 10));
  
  let x2 = Q.dequeue q;
  assert (pure (x2 == 20));
  
  let x3 = Q.dequeue q;
  assert (pure (x3 == 30));
  
  // Check if empty again
  let is_empty3 = Q.queue_empty q;
  assert (pure (is_empty3 == true));
  
  // Test wraparound: fill to capacity
  Q.enqueue q 1;
  Q.enqueue q 2;
  Q.enqueue q 3;
  Q.enqueue q 4;
  Q.enqueue q 5; // Queue is now full (capacity 5)
  
  // Dequeue 3 elements
  let y1 = Q.dequeue q;
  assert (pure (y1 == 1));
  let y2 = Q.dequeue q;
  assert (pure (y2 == 2));
  let y3 = Q.dequeue q;
  assert (pure (y3 == 3));
  
  // Now enqueue 3 more elements (this will test wraparound)
  Q.enqueue q 6;
  Q.enqueue q 7;
  Q.enqueue q 8;
  
  // Dequeue all and verify order
  let z1 = Q.dequeue q;
  assert (pure (z1 == 4));
  let z2 = Q.dequeue q;
  assert (pure (z2 == 5));
  let z3 = Q.dequeue q;
  assert (pure (z3 == 6));
  let z4 = Q.dequeue q;
  assert (pure (z4 == 7));
  let z5 = Q.dequeue q;
  assert (pure (z5 == 8));
  
  ()
}
