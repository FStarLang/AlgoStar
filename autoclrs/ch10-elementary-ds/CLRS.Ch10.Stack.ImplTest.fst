(** 
   Spec validation test for CLRS.Ch10.Stack.Impl — CLRS §10.1.

   Adapted from Test.Stack.fst in
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.Stack.fst

   Tests:
   1. Precondition satisfiability — create_stack, push, pop, peek all callable
   2. Postcondition precision — after push [1;2;3] and pop, we can prove
      the popped value is exactly 3 (LIFO), and peek returns exactly 2.
   3. stack_empty returns true iff the stack is empty.

   No admits. No assumes.
*)
module CLRS.Ch10.Stack.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.Stack.Impl

module SZ = FStar.SizeT
module L  = FStar.List.Tot

// Peek lemma: if exists init. L.append init [x] == [a;b;c], then x == c.
// Since peek returns a Prims.exists, we need to eliminate it.
let peek_last_3 (x: int)
  : Lemma (requires exists (init:list int). L.append init [x] == [1; 2; 3])
          (ensures  x == 3)
  = let aux (init:list int) : Lemma (requires L.append init [x] == [1;2;3]) (ensures x == 3)
      = L.append_length init [x]
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let peek_last_2 (x: int)
  : Lemma (requires exists (init:list int). L.append init [x] == [1; 2])
          (ensures  x == 2)
  = let aux (init:list int) : Lemma (requires L.append init [x] == [1;2]) (ensures x == 2)
      = L.append_length init [x]
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

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
  returns _:unit
  ensures exists* (s:stack int) (contents:Ghost.erased (list int)). stack_inv s contents
{
  // 1. Create an empty stack with capacity 5
  let s = create_stack int 0 5sz;

  // 2. Verify empty
  let b0 = stack_empty s;
  assert (pure (b0 == true));

  // 3. Push 1 → contents = [1]
  push s 1;

  // 4. Push 2 → contents = [1; 2]
  push s 2;

  // 5. Push 3 → contents = [1; 2; 3]
  push s 3;

  // 6. Verify not empty
  let b1 = stack_empty s;
  assert (pure (b1 == false));

  // 7. Pop — postcondition: exists* xs. stack_inv s xs ** pure (L.append xs [x] == [1;2;3])
  //    Z3 determines x3 == 3 and xs == [1;2]
  let x3 = pop s;
  assert (pure (x3 == 3));

  // 8. Peek — postcondition: pure (exists init. L.append init [x] == [1;2])
  //    Our lemma eliminates the Prims.exists to conclude top == 2
  let top2 = peek s;
  peek_last_2 top2;
  assert (pure (top2 == 2));

  // 9. Pop — should be 2
  let x2 = pop s;
  assert (pure (x2 == 2));

  // 10. Pop — should be 1
  let x1 = pop s;
  assert (pure (x1 == 1));

  // 11. Stack should now be empty
  let b2 = stack_empty s;
  assert (pure (b2 == true));

  ()
}
```
