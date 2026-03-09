module CLRS.Ch10.Queue.Lemmas

(**
   Proofs of correctness lemmas about the pure Queue specification.
   
   Proves the fundamental FIFO properties:
   - Enqueue appends to logical list view
   - Dequeue returns head of logical list view
   - Size invariants for enqueue/dequeue
*)

open FStar.List.Tot
open FStar.List.Tot.Properties
open CLRS.Ch10.Queue.Spec

/// Enqueue preserves invariant
val lemma_queue_enqueue_inv (#a: Type) (q: wf_queue a) (x: a)
  : Lemma (queue_inv (queue_enqueue q x))

/// Queue-to-list view: enqueue adds element at the end
val lemma_queue_enqueue_append (#a: Type) (q: wf_queue a) (x: a)
  : Lemma (queue_to_list (queue_enqueue q x) == queue_to_list q @ [x])

/// Empty queue has empty list view
val lemma_queue_empty_to_list (#a: Type)
  : Lemma (queue_to_list (queue_empty #a) == [])

/// Normalize preserves queue contents
val lemma_queue_normalize_preserves_contents (#a: Type) (q: queue a{Nil? q.front /\ Cons? q.back})
  : Lemma (queue_to_list (queue_normalize q) == queue_to_list q)

/// Dequeue from non-empty queue succeeds
val lemma_queue_dequeue_some (#a: Type) (q: wf_queue a{~(queue_is_empty q)})
  : Lemma (Some? (queue_dequeue q))

/// Dequeue from empty queue fails
val lemma_queue_dequeue_none (#a: Type) (q: wf_queue a{queue_is_empty q})
  : Lemma (queue_dequeue q == None)

/// FIFO Property: dequeue from single-element queue returns that element
val lemma_queue_fifo_single (#a: Type) (x: a)
  : Lemma (
      let q = queue_enqueue queue_empty x in
      queue_dequeue q == Some (x, queue_empty))

//SNIPPET_START: queue_fifo
/// FIFO Property: dequeue returns head of queue-to-list view
val lemma_queue_dequeue_preserves_contents (#a: Type) (q: wf_queue a{~(queue_is_empty q)})
  : Lemma (
      let Some (x, q') = queue_dequeue q in
      queue_to_list q == x :: queue_to_list q')
//SNIPPET_END: queue_fifo

/// Size increases by one after enqueue
val lemma_queue_enqueue_size (#a: Type) (q: wf_queue a) (x: a)
  : Lemma (queue_size (queue_enqueue q x) == queue_size q + 1)

/// Size decreases by one after dequeue
val lemma_queue_dequeue_size (#a: Type) (q: wf_queue a{~(queue_is_empty q)})
  : Lemma (
      let Some (_, q') = queue_dequeue q in
      queue_size q' == queue_size q - 1)

/// Queue size matches list view length
val lemma_queue_size_to_list (#a: Type) (q: queue a)
  : Lemma (queue_size q == length (queue_to_list q))

/// Empty queue has size 0
val lemma_queue_empty_size (#a: Type)
  : Lemma (queue_size (queue_empty #a) == 0)
