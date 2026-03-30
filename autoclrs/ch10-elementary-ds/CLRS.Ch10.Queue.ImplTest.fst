(**
   Spec validation test for CLRS.Ch10.Queue.Impl — CLRS §10.1.

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        Ghost assert(pure(...)) statements verify correctness at proof time.
     2. RUNTIME (computational, survives extraction to C):
        int_eq / bool_eq comparisons check concrete values.
        Returns bool — caller can verify at runtime.

   No admits. No assumes.
*)
module CLRS.Ch10.Queue.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.Queue.Impl

module Q  = CLRS.Ch10.Queue.Impl
module SZ = FStar.SizeT
module L  = FStar.List.Tot

inline_for_extraction
let int_eq (a b: int) : (r:bool{r <==> a = b}) = a = b

inline_for_extraction
let bool_eq (a b: bool) : (r:bool{r <==> a = b}) = (a = b)

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
  returns r: bool
  ensures pure (r == true)
{
  // 1. Create an empty queue with capacity 5
  let q = Q.create_queue int 0 5sz;

  // 2. Verify empty
  let b0 = Q.queue_empty q;
  assert (pure (b0 == true));
  let pass = bool_eq b0 true;

  // 3. Enqueue 10, 20, 30
  Q.enqueue q 10;
  Q.enqueue q 20;
  Q.enqueue q 30;

  // 4. Verify not empty
  let b1 = Q.queue_empty q;
  assert (pure (b1 == false));
  let pass = pass && bool_eq b1 false;

  // 5. Dequeue — FIFO: must be 10
  let x1 = Q.dequeue q;
  assert (pure (x1 == 10));
  let pass = pass && int_eq x1 10;

  // 6. Dequeue — must be 20
  let x2 = Q.dequeue q;
  assert (pure (x2 == 20));
  let pass = pass && int_eq x2 20;

  // 7. Dequeue — must be 30
  let x3 = Q.dequeue q;
  assert (pure (x3 == 30));
  let pass = pass && int_eq x3 30;

  // 8. Queue should now be empty
  let b2 = Q.queue_empty q;
  assert (pure (b2 == true));
  let pass = pass && bool_eq b2 true;

  // --- Scenario 2: Wraparound test ---

  // 9. Enqueue 40, 50
  Q.enqueue q 40;
  Q.enqueue q 50;

  // 10. Dequeue 40
  let y1 = Q.dequeue q;
  assert (pure (y1 == 40));
  let pass = pass && int_eq y1 40;

  // 11. Enqueue 60 (this wraps around in the circular buffer)
  Q.enqueue q 60;

  // 12. Dequeue 50
  let y2 = Q.dequeue q;
  assert (pure (y2 == 50));
  let pass = pass && int_eq y2 50;

  // 13. Dequeue 60
  let y3 = Q.dequeue q;
  assert (pure (y3 == 60));
  let pass = pass && int_eq y3 60;

  // 14. Empty again
  let b3 = Q.queue_empty q;
  assert (pure (b3 == true));
  let pass = pass && bool_eq b3 true;

  // Cleanup (test-only: drop invariant, OS reclaims at exit)
  with contents. assert (Q.queue_inv q contents);
  drop_ (Q.queue_inv q contents);

  pass
}
```
