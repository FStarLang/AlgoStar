module CLRS.Ch10.LinkedList.Test
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.LinkedList

module SZ = FStar.SizeT

fn test_linked_list ()
  requires emp
  returns _:unit
  ensures exists* (lst:linked_list int) (contents:Ghost.erased (list int)). list_inv lst contents
{
  // Create a list with capacity 10
  let lst = create_list int 0 10sz;
  
  // Insert some elements
  list_insert lst 42;
  list_insert lst 17;
  list_insert lst 99;
  
  // Search for an element
  let result1 = list_search lst 17;
  
  // Search for non-existent element
  let result2 = list_search lst 55;
  
  ()
}
