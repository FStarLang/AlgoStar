module CLRS.Ch10.Stack.Test
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.Stack.Impl

module SZ = FStar.SizeT

// Test the stack with integers
fn test_stack_basic ()
  requires emp
  returns _:unit
  ensures exists* (s:stack int) (contents:Ghost.erased (list int)). stack_inv s contents
{
  // Create a stack with capacity 10
  let s = create_stack int 0 10sz;
  
  // Push some elements
  push s 42;
  push s 17;
  push s 99;
  
  // Peek at top
  let top = peek s;
  
  // Pop elements
  let x1 = pop s;
  let x2 = pop s;
  let x3 = pop s;
  
  // Check if empty
  let empty = stack_empty s;
  
  ()
}
