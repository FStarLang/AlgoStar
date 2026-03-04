module CLRS.Ch10.Queue.Lemmas

(**
   Proofs of correctness lemmas about the pure Queue specification.
   
   NO admits. NO assumes.
*)

open FStar.List.Tot
open FStar.List.Tot.Properties
open CLRS.Ch10.Queue.Spec

let lemma_queue_enqueue_inv (#a: Type) (q: wf_queue a) (x: a)
  : Lemma (queue_inv (queue_enqueue q x))
  = ()

let lemma_queue_enqueue_append (#a: Type) (q: wf_queue a) (x: a)
  : Lemma (queue_to_list (queue_enqueue q x) == queue_to_list q @ [x])
  = match q.front with
    | [] -> ()
    | _ -> 
        rev_append [x] q.back;
        append_assoc q.front (rev q.back) [x]

let lemma_queue_empty_to_list (#a: Type)
  : Lemma (queue_to_list (queue_empty #a) == [])
  = ()

let lemma_queue_normalize_preserves_contents (#a: Type) (q: queue a{Nil? q.front /\ Cons? q.back})
  : Lemma (queue_to_list (queue_normalize q) == queue_to_list q)
  = ()

let lemma_queue_dequeue_some (#a: Type) (q: wf_queue a{~(queue_is_empty q)})
  : Lemma (Some? (queue_dequeue q))
  = ()

let lemma_queue_dequeue_none (#a: Type) (q: wf_queue a{queue_is_empty q})
  : Lemma (queue_dequeue q == None)
  = ()

let lemma_queue_fifo_single (#a: Type) (x: a)
  : Lemma (
      let q = queue_enqueue queue_empty x in
      queue_dequeue q == Some (x, queue_empty))
  = ()

let lemma_queue_dequeue_preserves_contents (#a: Type) (q: wf_queue a{~(queue_is_empty q)})
  : Lemma (
      let Some (x, q') = queue_dequeue q in
      queue_to_list q == x :: queue_to_list q')
  = match q.front with
    | [x] -> 
        (match q.back with
         | [] -> ()
         | _ -> lemma_queue_normalize_preserves_contents { front = []; back = q.back })
    | x :: front_tl -> ()

let lemma_queue_enqueue_size (#a: Type) (q: wf_queue a) (x: a)
  : Lemma (queue_size (queue_enqueue q x) == queue_size q + 1)
  = ()

let lemma_queue_dequeue_size (#a: Type) (q: wf_queue a{~(queue_is_empty q)})
  : Lemma (
      let Some (_, q') = queue_dequeue q in
      queue_size q' == queue_size q - 1)
  = match q.front with
    | [x] -> 
        (match q.back with
         | [] -> ()
         | _ -> rev_length q.back)
    | x :: front_tl -> ()

let lemma_queue_size_to_list (#a: Type) (q: queue a)
  : Lemma (queue_size q == length (queue_to_list q))
  = append_length q.front (rev q.back);
    rev_length q.back

let lemma_queue_empty_size (#a: Type)
  : Lemma (queue_size (queue_empty #a) == 0)
  = ()
