module CLRS.Ch10.DLL.Test
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.DLL.Impl

// Test basic DLL operations: insert, search, delete
fn test_dll ()
  requires emp
  returns _:unit
  ensures emp
{
  // Create head and tail refs as local mutables, start with empty dll
  let mut hd_ref : dptr = None;
  let mut tl_ref : dptr = None;
  dll_nil None None;

  // Insert 10, 20, 30 at head → list is [30; 20; 10]
  list_insert hd_ref tl_ref 10;
  list_insert hd_ref tl_ref 20;
  list_insert hd_ref tl_ref 30;

  // Read head/tail for search
  let hd = !hd_ref;
  let tl = !tl_ref;

  // Search for 20 (present)
  let found = list_search hd tl 20;

  // Search for 99 (absent)
  let not_found = list_search hd tl 99;

  // Delete 20
  list_delete hd_ref tl_ref 20;

  // Delete remaining elements
  list_delete hd_ref tl_ref 30;
  list_delete hd_ref tl_ref 10;

  // Clean up — after deleting all elements the dll is empty
  with hd3 tl3.
    assert (pts_to hd_ref hd3 ** pts_to tl_ref tl3 ** dll hd3 tl3 _);
  drop_ (dll hd3 tl3 _);
  ()
}
