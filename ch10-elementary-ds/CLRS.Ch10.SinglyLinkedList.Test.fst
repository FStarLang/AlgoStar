module CLRS.Ch10.SinglyLinkedList.Test
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.SinglyLinkedList.Base
open CLRS.Ch10.SinglyLinkedList

// Test basic SLL operations: insert, search, delete
fn test_sll ()
  requires emp
  returns _:unit
  ensures emp
{
  // Start with empty list
  let hd : dlist = None;
  intro_is_dlist_nil hd;

  // Insert 10, 20, 30 at head → list is [30; 20; 10]
  let hd = list_insert 10 hd;
  let hd = list_insert 20 hd;
  let hd = list_insert 30 hd;

  // Search for 20 (present)
  let found = list_search hd 20;
  assert (pure (found == true));

  // Search for 99 (absent)
  let not_found = list_search hd 99;
  assert (pure (not_found == false));

  // Delete 20 → list is [30; 10]
  let hd = list_delete hd 20;

  // Verify 20 no longer found
  let gone = list_search hd 20;
  assert (pure (gone == false));

  // Delete remaining elements
  let hd = list_delete hd 30;
  let hd = list_delete hd 10;

  // List should be empty — unfold predicate to recover emp
  elim_is_dlist_nil hd;
  ()
}
