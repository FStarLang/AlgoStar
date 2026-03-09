module CLRS.Ch10.Stack.Lemmas

(**
   Proofs of correctness lemmas about the pure Stack specification.
   
   Proves the fundamental LIFO properties:
   - Pop after push returns the pushed element
   - Pop after push restores the original stack
   - Size invariants for push/pop
*)

open CLRS.Ch10.Stack.Spec

//SNIPPET_START: stack_lifo
/// LIFO Property 1: Popping a pushed element returns that element
val lemma_stack_lifo_pop_push (#a: Type) (s: stack a) (x: a)
  : Lemma (fst (stack_pop (stack_push s x)) == x)

/// LIFO Property 2: Popping a pushed element returns the original stack
val lemma_stack_lifo_stack_preserved (#a: Type) (s: stack a) (x: a)
  : Lemma (snd (stack_pop (stack_push s x)) == s)
//SNIPPET_END: stack_lifo

/// Push makes stack non-empty
val lemma_stack_push_non_empty (#a: eqtype) (s: stack a) (x: a)
  : Lemma (stack_push s x <> stack_empty)

/// Size increases by one after push
val lemma_stack_push_size (#a: Type) (s: stack a) (x: a)
  : Lemma (stack_size (stack_push s x) == stack_size s + 1)

/// Size decreases by one after pop
val lemma_stack_pop_size (#a: Type) (s: stack a{Cons? s})
  : Lemma (stack_size (snd (stack_pop s)) == stack_size s - 1)

/// Empty stack has size 0
val lemma_stack_empty_size (#a: Type)
  : Lemma (stack_size (stack_empty #a) == 0)
