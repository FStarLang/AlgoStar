module CLRS.Ch10.Stack.Spec

(**
   Pure functional specification for array-based Stack from CLRS §10.1.
   
   The stack is modeled as a list where the head is the top element.
   Provides the LIFO (Last In, First Out) abstract data type.
*)

open FStar.List.Tot
open FStar.List.Tot.Properties

//SNIPPET_START: stack_spec
/// Abstract stack type: simply a list where head is the top
type stack (a: Type) = list a

/// Empty stack
let stack_empty (#a: Type) : stack a = []

/// Push an element onto the stack
let stack_push (#a: Type) (s: stack a) (x: a) : stack a = 
  x :: s

/// Pop an element from a non-empty stack, returning the element and new stack
let stack_pop (#a: Type) (s: stack a{Cons? s}) : (a & stack a) =
  match s with
  | hd :: tl -> (hd, tl)
//SNIPPET_END: stack_spec

/// Check if stack is empty
let stack_is_empty (#a: Type) (s: stack a) : bool =
  match s with
  | [] -> true
  | _ -> false

/// Get the size of a stack
let stack_size (#a: Type) (s: stack a) : nat =
  length s
