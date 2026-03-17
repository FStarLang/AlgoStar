(**
   Spec validation test for CLRS.Ch10.SinglyLinkedList.Impl — CLRS §10.2.

   Adapted from Test.SLL.fst in
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.SLL.fst

   Tests:
   1. Precondition satisfiability — list_insert, list_search, list_delete callable
   2. Postcondition precision for list_insert — after insert 3, 2, 1 the list
      is precisely [1; 2; 3]
   3. Postcondition precision for list_search — search returns true iff element
      is a member
   4. Postcondition precision for list_delete — after deleting 2 from [1;2;3],
      the list is precisely [1;3], and searching for 2 returns false
   5. Full round-trip: insert all, delete all, list is empty

   No admits. No assumes.
*)
module CLRS.Ch10.SinglyLinkedList.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.SinglyLinkedList.Base
open CLRS.Ch10.SinglyLinkedList.Impl

module L = FStar.List.Tot

// Auxiliary: remove_first 2 [1;2;3] == [1;3]
let remove_first_2_from_123 ()
  : Lemma (remove_first 2 [1; 2; 3] == [1; 3])
  = ()

// Auxiliary: mem 1 [1;3] == true
let mem_1_in_13 ()
  : Lemma (L.mem 1 [1; 3] == true)
  = ()

// Auxiliary: mem 3 [1;3] == true
let mem_3_in_13 ()
  : Lemma (L.mem 3 [1; 3] == true)
  = ()

// Auxiliary: mem 2 [1;3] == false
let not_mem_2_in_13 ()
  : Lemma (L.mem 2 [1; 3] == false)
  = ()

// Auxiliary: remove_first 1 [1;3] == [3]
let remove_first_1_from_13 ()
  : Lemma (remove_first 1 [1; 3] == [3])
  = ()

// Auxiliary: remove_first 3 [3] == []
let remove_first_3_from_3 ()
  : Lemma (remove_first 3 [3] == [])
  = ()

```pulse
(** Main spec-validation test for Singly Linked List.

    Scenario: start empty, insert 3, 2, 1 (at head each time).
    List is [1; 2; 3].
    Search for 2 → true, search for 99 → false.
    Delete 2 → list is [1; 3].
    Search for 2 → false, search for 1 → true, search for 3 → true.
    Delete 1 → list is [3].
    Delete 3 → list is [].
*)
fn test_sll_spec_validation ()
  requires emp
  returns _:unit
  ensures emp
{
  // 1. Start with empty list
  let hd : dlist = None;
  intro_is_dlist_nil hd;

  // 2. Insert 3 → list is [3]
  let hd = list_insert 3 hd;

  // 3. Insert 2 → list is [2; 3]
  let hd = list_insert 2 hd;

  // 4. Insert 1 → list is [1; 2; 3]
  let hd = list_insert 1 hd;

  // 5. Search for 2 — postcondition: found <==> L.mem 2 [1;2;3]
  //    L.mem 2 [1;2;3] == true, so found == true
  let found = list_search hd 2;
  assert (pure (found == true));

  // 6. Search for 99 — not in list
  let not_found = list_search hd 99;
  assert (pure (not_found == false));

  // 7. Delete 2 — postcondition: is_dlist new_head (remove_first 2 [1;2;3])
  //    remove_first 2 [1;2;3] == [1;3]
  let hd = list_delete hd 2;

  // 7a. Delete 99 (not in list) — list should be unchanged [1;3]
  //     remove_first 99 [1;3] == [1;3]
  let hd = list_delete hd 99;

  // 8. Search for 2 after delete — should be false
  let gone = list_search hd 2;
  assert (pure (gone == false));

  // 9. Search for 1 — still present in [1;3]
  let still1 = list_search hd 1;
  assert (pure (still1 == true));

  // 10. Search for 3 — still present in [1;3]
  let still3 = list_search hd 3;
  assert (pure (still3 == true));

  // 11. Delete 1 → list is [3]
  let hd = list_delete hd 1;

  // 12. Delete 3 → list is []
  let hd = list_delete hd 3;

  // 13. List should be empty — unfold predicate to recover emp
  elim_is_dlist_nil hd;
  ()
}
```
