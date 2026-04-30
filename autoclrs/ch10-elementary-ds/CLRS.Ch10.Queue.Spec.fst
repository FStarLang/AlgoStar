module CLRS.Ch10.Queue.Spec

(**
   Pure functional specification for circular-buffer Queue from CLRS §10.1.
   
   The queue is modeled as a two-list implementation for efficient operations.
   Provides the FIFO (First In, First Out) abstract data type.
*)

open FStar.List.Tot
open FStar.List.Tot.Properties

//SNIPPET_START: queue_spec
/// Abstract queue type: two-list implementation for efficient operations
/// - front: elements to dequeue from
/// - back: elements recently enqueued (stored in reverse)
/// Invariant: if front is empty, back must also be empty
type queue (a: Type) = {
  front: list a;
  back: list a;
}

/// Queue invariant: front empty implies back empty
let queue_inv (#a: Type) (q: queue a) : prop =
  Cons? q.front \/ (Nil? q.front /\ Nil? q.back)

/// Well-formed queue
type wf_queue (a: Type) = q: queue a{queue_inv q}

/// Empty queue
let queue_empty (#a: Type) : wf_queue a = 
  { front = []; back = [] }

/// Convert queue to a list (abstract view of queue contents)
/// Elements appear in FIFO order: front elements, then back elements (reversed)
let queue_to_list (#a: Type) (q: queue a) : list a =
  q.front @ rev q.back

/// Enqueue an element to the back of the queue
let queue_enqueue (#a: Type) (q: wf_queue a) (x: a) : wf_queue a =
  match q.front with
  | [] -> { front = [x]; back = [] }
  | _ -> { front = q.front; back = x :: q.back }

/// Internal: normalize queue by moving reversed back to front
let queue_normalize (#a: Type) (q: queue a{Nil? q.front /\ Cons? q.back}) : wf_queue a =
  { front = rev q.back; back = [] }

/// Dequeue an element from the front of the queue
let queue_dequeue (#a: Type) (q: wf_queue a) : option (a & wf_queue a) =
  match q.front with
  | [] -> None
  | [x] -> 
      (match q.back with
       | [] -> Some (x, queue_empty)
       | _ -> Some (x, queue_normalize { front = []; back = q.back }))
  | x :: front_tl ->
      Some (x, { front = front_tl; back = q.back })
//SNIPPET_END: queue_spec

/// Check if queue is empty
let queue_is_empty (#a: Type) (q: wf_queue a) : bool =
  Nil? q.front

/// Get the size of a queue
let queue_size (#a: Type) (q: queue a) : nat =
  length q.front + length q.back
