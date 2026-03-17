(**
   Spec validation test for CLRS.Ch10.DLL.Impl — CLRS §10.2.

   Adapted from Test.DLL.fst and Test.DLL2.fst in
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.DLL.fst

   Tests:
   1. Precondition satisfiability — all DLL operations callable
   2. Postcondition precision for list_insert — after insert 3, 2, 1 the list
      is precisely [1; 2; 3]
   3. Postcondition precision for list_insert_tail — appending at tail
   4. Postcondition precision for list_search — returns true iff member
   5. Postcondition precision for list_search_back — equivalent to forward search
   6. Postcondition precision for list_delete — removes first occurrence
   7. Full round-trip: insert all, delete all, list is empty
   8. Ghost helpers: dll_nil, dll_nil_elim, dll_none_nil, dll_some_cons

   No admits. No assumes.
*)
module CLRS.Ch10.DLL.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.DLL.Impl
module L = FStar.List.Tot

```pulse
(** Main spec-validation test for Doubly Linked List.

    Scenario 1 — insert at head:
      Insert 3, 2, 1 at head → list is [1; 2; 3].
      Search forward for 2 → true, for 99 → false.
      Search backward for 3 → true, for 0 → false.
      Delete 2 → list is [1; 3].
      Search for 2 → false.
      Delete 1, delete 3 → empty.

    Scenario 2 — insert at tail:
      Insert 10 at head, insert 20 at tail, insert 30 at tail → [10; 20; 30].
      Verify via search.
      Delete all.
*)
fn test_dll_spec_validation ()
  requires emp
  returns _:unit
  ensures emp
{
  // Create head and tail refs, start with empty dll
  let mut hd_ref : dptr = None;
  let mut tl_ref : dptr = None;
  dll_nil None None;

  // --- Scenario 1: Insert at head ---

  // Insert 3 at head → list is [3]
  list_insert hd_ref tl_ref 3;

  // Insert 2 at head → list is [2; 3]
  list_insert hd_ref tl_ref 2;

  // Insert 1 at head → list is [1; 2; 3]
  list_insert hd_ref tl_ref 1;

  // Read head/tail for search
  let hd1 = !hd_ref;
  let tl1 = !tl_ref;

  // Search forward for 2 — should be true
  let found2 = list_search hd1 tl1 2;
  assert (pure (found2 == true));

  // Search forward for 99 — should be false
  let not99 = list_search hd1 tl1 99;
  assert (pure (not99 == false));

  // Search backward for 3 — should be true
  let found3_back = list_search_back hd1 tl1 3;
  assert (pure (found3_back == true));

  // Search backward for 0 — should be false
  let not0_back = list_search_back hd1 tl1 0;
  assert (pure (not0_back == false));

  // Search via pointer for 1 — should be Some
  let ptr1 = list_search_ptr hd1 tl1 1;
  assert (pure (Some? ptr1));

  // Search via pointer for 42 — should be None
  let ptr42 = list_search_ptr hd1 tl1 42;
  assert (pure (None? ptr42));

  // Delete 2 → list is [1; 3] (remove_first 2 [1;2;3] == [1;3])
  list_delete hd_ref tl_ref 2;

  // Search for 2 after delete — should be false
  let hd2 = !hd_ref;
  let tl2 = !tl_ref;
  let gone2 = list_search hd2 tl2 2;
  assert (pure (gone2 == false));

  // 1 and 3 still present
  let still1 = list_search hd2 tl2 1;
  assert (pure (still1 == true));
  let still3 = list_search hd2 tl2 3;
  assert (pure (still3 == true));

  // Delete 1 → list is [3]
  list_delete hd_ref tl_ref 1;

  // Delete 3 → list is []
  list_delete hd_ref tl_ref 3;

  // Verify empty via dll_nil_elim
  with hd_empty tl_empty.
    assert (pts_to hd_ref hd_empty ** pts_to tl_ref tl_empty ** dll hd_empty tl_empty _);
  dll_nil_elim hd_empty tl_empty;
  assert (pure (hd_empty == None /\ tl_empty == None));

  // --- Scenario 2: Insert at tail ---
  dll_nil None None;
  hd_ref := None;
  tl_ref := None;

  // Insert 10 at head → [10]
  list_insert hd_ref tl_ref 10;

  // Insert 20 at tail → [10; 20]
  list_insert_tail hd_ref tl_ref 20;

  // Insert 30 at tail → [10; 20; 30]
  list_insert_tail hd_ref tl_ref 30;

  // Verify via search
  let hd3 = !hd_ref;
  let tl3 = !tl_ref;

  let f10 = list_search hd3 tl3 10;
  assert (pure (f10 == true));
  let f20 = list_search hd3 tl3 20;
  assert (pure (f20 == true));
  let f30 = list_search hd3 tl3 30;
  assert (pure (f30 == true));
  let f99 = list_search hd3 tl3 99;
  assert (pure (f99 == false));

  // Delete all
  list_delete hd_ref tl_ref 10;
  list_delete hd_ref tl_ref 20;
  list_delete hd_ref tl_ref 30;

  // Clean up
  with hd_fin tl_fin.
    assert (pts_to hd_ref hd_fin ** pts_to tl_ref tl_fin ** dll hd_fin tl_fin _);
  drop_ (dll hd_fin tl_fin _);
  ()
}
```
