(**
   Spec validation test for CLRS.Ch10.Stack.Impl — CLRS §10.1.

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        Ghost assert(pure(...)) statements verify correctness at proof time.
     2. RUNTIME (computational, survives extraction to C):
        int_eq / bool_eq comparisons check concrete values.
        Returns bool — caller can verify at runtime.

   No admits. No assumes.
*)
module CLRS.Ch10.Stack.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.Stack.Impl

module SZ = FStar.SizeT
module L  = FStar.List.Tot

inline_for_extraction
let int_eq (a b: int) : (r:bool{r <==> a = b}) = a = b

inline_for_extraction
let bool_eq (a b: bool) : (r:bool{r <==> a = b}) = (a = b)

```pulse
(** Main spec-validation test for Stack.

    Scenario: create a stack of capacity 5, push 1, 2, 3.
    Then:
      - peek → must be 3 (LIFO top)
      - pop → must be 3
      - pop → must be 2
      - pop → must be 1
      - stack_empty → must be true
*)
fn test_stack_spec_validation ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // 1. Create an empty stack with capacity 5
  let s = create_stack int 0 5sz;

  // 2. Verify empty
  let b0 = stack_empty s;
  assert (pure (b0 == true));
  let pass = bool_eq b0 true;

  // 3. Push 1, 2, 3
  push s 1;
  push s 2;
  push s 3;

  // 4. Verify not empty
  let b1 = stack_empty s;
  assert (pure (b1 == false));
  let pass = pass && bool_eq b1 false;

  // 5. Peek — LIFO top is 3
  let top3 = peek s;
  assert (pure (top3 == 3));
  let pass = pass && int_eq top3 3;

  // 6. Pop — should be 3
  let x3 = pop s;
  assert (pure (x3 == 3));
  let pass = pass && int_eq x3 3;

  // 7. Peek — top is now 2
  let top2 = peek s;
  assert (pure (top2 == 2));
  let pass = pass && int_eq top2 2;

  // 8. Pop — should be 2
  let x2 = pop s;
  assert (pure (x2 == 2));
  let pass = pass && int_eq x2 2;

  // 9. Pop — should be 1
  let x1 = pop s;
  assert (pure (x1 == 1));
  let pass = pass && int_eq x1 1;

  // 10. Stack should now be empty
  let b2 = stack_empty s;
  assert (pure (b2 == true));
  let pass = pass && bool_eq b2 true;

  // Cleanup (test-only: drop invariant, OS reclaims at exit)
  with contents. assert (stack_inv s contents);
  drop_ (stack_inv s contents);

  pass
}
```
