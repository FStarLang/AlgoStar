(**
   Spec validation test for CLRS.Ch10.Queue.Impl — CLRS §10.1.

   Adapted from Test.Queue.fst in
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.Queue.fst

   Tests:
   1. Precondition satisfiability — create_queue, enqueue, dequeue all callable
   2. Postcondition precision — after enqueue [10;20;30] and dequeue, we can
      prove the dequeued values are exactly 10, 20, 30 in FIFO order.
   3. queue_empty returns true iff the queue is empty.
   4. Wraparound correctness — enqueue after dequeue exercises circular buffer.

   No admits. No assumes.
*)
module CLRS.Ch10.Queue.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.Queue.Impl

module Q  = CLRS.Ch10.Queue.Impl
module SZ = FStar.SizeT
module L  = FStar.List.Tot

```pulse
(** Main spec-validation test for Queue.

    Scenario 1: create queue of capacity 5, enqueue 10, 20, 30.
    Dequeue all three and verify FIFO order: 10, 20, 30.

    Scenario 2 (wraparound): after emptying, enqueue 40, 50, dequeue 40,
    enqueue 60, dequeue 50, dequeue 60. This exercises the circular buffer
    wraparound.
*)
fn test_queue_spec_validation ()
  requires emp
  returns _:unit
  ensures exists* (q:Q.queue int) (contents:Ghost.erased (list int)). Q.queue_inv q contents
{
  // 1. Create an empty queue with capacity 5
  let q = Q.create_queue int 0 5sz;

  // 2. Verify empty
  let b0 = Q.queue_empty q;
  assert (pure (b0 == true));

  // 3. Enqueue 10 → contents = [10]
  Q.enqueue q 10;

  // 4. Enqueue 20 → contents = [10; 20]
  Q.enqueue q 20;

  // 5. Enqueue 30 → contents = [10; 20; 30]
  Q.enqueue q 30;

  // 6. Verify not empty
  let b1 = Q.queue_empty q;
  assert (pure (b1 == false));

  // 7. Dequeue — postcondition says contents == x :: xs
  //    Since contents was [10; 20; 30], x must be 10
  let x1 = Q.dequeue q;
  assert (pure (x1 == 10));

  // 8. Dequeue — contents was [20; 30], x must be 20
  let x2 = Q.dequeue q;
  assert (pure (x2 == 20));

  // 9. Dequeue — contents was [30], x must be 30
  let x3 = Q.dequeue q;
  assert (pure (x3 == 30));

  // 10. Queue should now be empty
  let b2 = Q.queue_empty q;
  assert (pure (b2 == true));

  // --- Scenario 2: Wraparound test ---

  // 11. Enqueue 40, 50
  Q.enqueue q 40;
  Q.enqueue q 50;

  // 12. Dequeue 40
  let y1 = Q.dequeue q;
  assert (pure (y1 == 40));

  // 13. Enqueue 60 (this wraps around in the circular buffer)
  Q.enqueue q 60;

  // 14. Dequeue 50
  let y2 = Q.dequeue q;
  assert (pure (y2 == 50));

  // 15. Dequeue 60
  let y3 = Q.dequeue q;
  assert (pure (y3 == 60));

  // 16. Empty again
  let b3 = Q.queue_empty q;
  assert (pure (b3 == true));

  ()
}
```
