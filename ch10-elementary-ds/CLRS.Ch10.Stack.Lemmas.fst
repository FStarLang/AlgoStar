module CLRS.Ch10.Stack.Lemmas

(**
   Proofs of correctness lemmas about the pure Stack specification.
   All proofs are trivial — the LIFO properties follow directly from
   the cons/match structure of the stack representation.
   
   NO admits. NO assumes.
*)

open CLRS.Ch10.Stack.Spec

let lemma_stack_lifo_pop_push (#a: Type) (s: stack a) (x: a)
  : Lemma (fst (stack_pop (stack_push s x)) == x)
  = ()

let lemma_stack_lifo_stack_preserved (#a: Type) (s: stack a) (x: a)
  : Lemma (snd (stack_pop (stack_push s x)) == s)
  = ()

let lemma_stack_push_non_empty (#a: eqtype) (s: stack a) (x: a)
  : Lemma (stack_push s x <> stack_empty)
  = ()

let lemma_stack_push_size (#a: Type) (s: stack a) (x: a)
  : Lemma (stack_size (stack_push s x) == stack_size s + 1)
  = ()

let lemma_stack_pop_size (#a: Type) (s: stack a{Cons? s})
  : Lemma (stack_size (snd (stack_pop s)) == stack_size s - 1)
  = ()

let lemma_stack_empty_size (#a: Type)
  : Lemma (stack_size (stack_empty #a) == 0)
  = ()
