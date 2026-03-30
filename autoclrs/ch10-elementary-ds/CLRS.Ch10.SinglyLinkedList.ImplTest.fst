(**
   Spec validation test for CLRS.Ch10.SinglyLinkedList.Impl — CLRS §10.2.

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        Ghost assert(pure(...)) statements verify correctness at proof time.
     2. RUNTIME (computational, survives extraction to C):
        int_eq / bool_eq comparisons check concrete values.
        Returns bool — caller can verify at runtime.

   No admits. No assumes.
*)
module CLRS.Ch10.SinglyLinkedList.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.SinglyLinkedList.Base
open CLRS.Ch10.SinglyLinkedList.Impl

module L = FStar.List.Tot

inline_for_extraction
let bool_eq (a b: bool) : (r:bool{r <==> a = b}) = (a = b)

// Auxiliary lemmas (concrete data, verified by normalization)
let remove_first_2_from_123 ()
  : Lemma (remove_first 2 [1; 2; 3] == [1; 3])
  = ()

let mem_1_in_13 ()
  : Lemma (L.mem 1 [1; 3] == true)
  = ()

let mem_3_in_13 ()
  : Lemma (L.mem 3 [1; 3] == true)
  = ()

let not_mem_2_in_13 ()
  : Lemma (L.mem 2 [1; 3] == false)
  = ()

let remove_first_1_from_13 ()
  : Lemma (remove_first 1 [1; 3] == [3])
  = ()

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
  returns r: bool
  ensures pure (r == true)
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

  // 5. Search for 2 — should be true
  let found = list_search hd 2;
  assert (pure (found == true));
  let pass = bool_eq found true;

  // 6. Search for 99 — not in list
  let not_found = list_search hd 99;
  assert (pure (not_found == false));
  let pass = pass && bool_eq not_found false;

  // 7. Delete 2 → list is [1; 3]
  let hd = list_delete hd 2;

  // 7a. Delete 99 (not in list) — list unchanged [1; 3]
  let hd = list_delete hd 99;

  // 8. Search for 2 after delete — should be false
  let gone = list_search hd 2;
  assert (pure (gone == false));
  let pass = pass && bool_eq gone false;

  // 9. Search for 1 — still present in [1; 3]
  let still1 = list_search hd 1;
  assert (pure (still1 == true));
  let pass = pass && bool_eq still1 true;

  // 10. Search for 3 — still present in [1; 3]
  let still3 = list_search hd 3;
  assert (pure (still3 == true));
  let pass = pass && bool_eq still3 true;

  // 11. Delete 1 → list is [3]
  let hd = list_delete hd 1;

  // 12. Delete 3 → list is []
  let hd = list_delete hd 3;

  // 13. List should be empty — unfold predicate to recover emp
  elim_is_dlist_nil hd;

  pass
}
```
