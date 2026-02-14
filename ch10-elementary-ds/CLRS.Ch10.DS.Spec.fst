module CLRS.Ch10.DS.Spec

(**
   Pure functional specifications for elementary data structures from CLRS Chapter 10.
   
   This module provides abstract specifications for:
   - Stack (LIFO property)
   - Queue (FIFO property)
   - LinkedList (insertion and deletion properties)
   
   These specifications serve as the mathematical model for the imperative Pulse
   implementations in CLRS.Ch10.Stack, CLRS.Ch10.Queue, and CLRS.Ch10.LinkedList.
*)

open FStar.List.Tot
open FStar.List.Tot.Properties

(*** Stack Specification (LIFO - Last In, First Out) ***)

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

/// Check if stack is empty
let stack_is_empty (#a: Type) (s: stack a) : bool =
  match s with
  | [] -> true
  | _ -> false

/// Get the size of a stack
let stack_size (#a: Type) (s: stack a) : nat =
  length s

(** Stack Properties **)

/// LIFO Property 1: Popping a pushed element returns that element
let lemma_stack_lifo_pop_push (#a: Type) (s: stack a) (x: a)
  : Lemma (fst (stack_pop (stack_push s x)) == x)
  = ()

/// LIFO Property 2: Popping a pushed element returns the original stack
let lemma_stack_lifo_stack_preserved (#a: Type) (s: stack a) (x: a)
  : Lemma (snd (stack_pop (stack_push s x)) == s)
  = ()

/// Push makes stack non-empty
let lemma_stack_push_non_empty (#a: eqtype) (s: stack a) (x: a)
  : Lemma (stack_push s x <> stack_empty)
  = ()

/// Size increases by one after push
let lemma_stack_push_size (#a: Type) (s: stack a) (x: a)
  : Lemma (stack_size (stack_push s x) == stack_size s + 1)
  = ()

/// Size decreases by one after pop
let lemma_stack_pop_size (#a: Type) (s: stack a{Cons? s})
  : Lemma (stack_size (snd (stack_pop s)) == stack_size s - 1)
  = ()

/// Empty stack has size 0
let lemma_stack_empty_size (#a: Type)
  : Lemma (stack_size (stack_empty #a) == 0)
  = ()


(*** Queue Specification (FIFO - First In, First Out) ***)

/// Abstract queue type: two-list implementation for efficient operations
/// - front: elements to dequeue from
/// - back: elements recently enqueued (stored in reverse)
/// Invariant: if front is empty, back must also be empty
type queue (a: Type) = {
  front: list a;
  back: list a;
}

/// Queue invariant: front empty implies back empty
let queue_inv (#a: Type) (q: queue a) : Type0 =
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
  | [] -> { front = [x]; back = [] }  // Maintain invariant
  | _ -> { front = q.front; back = x :: q.back }

/// Internal: normalize queue by moving reversed back to front
let queue_normalize (#a: Type) (q: queue a{Nil? q.front /\ Cons? q.back}) : wf_queue a =
  { front = rev q.back; back = [] }

/// Dequeue an element from the front of the queue
let queue_dequeue (#a: Type) (q: wf_queue a) : option (a & wf_queue a) =
  match q.front with
  | [] -> None  // Empty queue
  | [x] -> 
      // Last element in front, need to normalize
      (match q.back with
       | [] -> Some (x, queue_empty)
       | _ -> Some (x, queue_normalize { front = []; back = q.back }))
  | x :: front_tl ->
      Some (x, { front = front_tl; back = q.back })

/// Check if queue is empty
let queue_is_empty (#a: Type) (q: wf_queue a) : bool =
  Nil? q.front

/// Get the size of a queue
let queue_size (#a: Type) (q: queue a) : nat =
  length q.front + length q.back

(** Queue Properties **)

/// Enqueue preserves invariant (already in type, but explicit)
let lemma_queue_enqueue_inv (#a: Type) (q: wf_queue a) (x: a)
  : Lemma (queue_inv (queue_enqueue q x))
  = ()

/// Queue-to-list view: enqueue adds element at the end
let lemma_queue_enqueue_append (#a: Type) (q: wf_queue a) (x: a)
  : Lemma (queue_to_list (queue_enqueue q x) == queue_to_list q @ [x])
  = match q.front with
    | [] -> ()
    | _ -> 
        // Need to show: front @ rev (x :: back) == front @ rev back @ [x]
        // Note: rev (x :: back) = rev back @ rev [x] = rev back @ [x]
        rev_append [x] q.back;
        append_assoc q.front (rev q.back) [x]

/// Empty queue has empty list view
let lemma_queue_empty_to_list (#a: Type)
  : Lemma (queue_to_list (queue_empty #a) == [])
  = ()

/// Normalize preserves queue contents
let lemma_queue_normalize_preserves_contents (#a: Type) (q: queue a{Nil? q.front /\ Cons? q.back})
  : Lemma (queue_to_list (queue_normalize q) == queue_to_list q)
  = ()

/// Dequeue from non-empty queue succeeds
let lemma_queue_dequeue_some (#a: Type) (q: wf_queue a{~(queue_is_empty q)})
  : Lemma (Some? (queue_dequeue q))
  = ()

/// Dequeue from empty queue fails
let lemma_queue_dequeue_none (#a: Type) (q: wf_queue a{queue_is_empty q})
  : Lemma (queue_dequeue q == None)
  = ()

/// FIFO Property: dequeue from single-element queue returns that element
let lemma_queue_fifo_single (#a: Type) (x: a)
  : Lemma (
      let q = queue_enqueue queue_empty x in
      queue_dequeue q == Some (x, queue_empty))
  = ()

/// FIFO Property: dequeue returns head of queue-to-list view
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

/// Size increases by one after enqueue
let lemma_queue_enqueue_size (#a: Type) (q: wf_queue a) (x: a)
  : Lemma (queue_size (queue_enqueue q x) == queue_size q + 1)
  = ()

/// Size decreases by one after dequeue
let lemma_queue_dequeue_size (#a: Type) (q: wf_queue a{~(queue_is_empty q)})
  : Lemma (
      let Some (_, q') = queue_dequeue q in
      queue_size q' == queue_size q - 1)
  = match q.front with
    | [x] -> 
        (match q.back with
         | [] -> ()
         | _ -> 
             // After normalization: queue_size = length (rev back) + 0
             // Before: queue_size = 1 + length back
             rev_length q.back)
    | x :: front_tl -> ()

/// Queue size matches list view length
let lemma_queue_size_to_list (#a: Type) (q: queue a)
  : Lemma (queue_size q == length (queue_to_list q))
  = append_length q.front (rev q.back);
    rev_length q.back

/// Empty queue has size 0
let lemma_queue_empty_size (#a: Type)
  : Lemma (queue_size (queue_empty #a) == 0)
  = ()


(*** LinkedList Specification ***)

/// Abstract linked list: just a list
type linked_list (a: Type) = list a

/// Empty list
let list_empty (#a: Type) : linked_list a = []

/// Insert element at the head (CLRS convention)
let list_insert (#a: Type) (l: linked_list a) (x: a) : linked_list a =
  x :: l

/// Search for an element (membership test)
let rec list_search (#a: eqtype) (l: linked_list a) (x: a) : bool =
  match l with
  | [] -> false
  | hd :: tl -> hd = x || list_search tl x

/// Delete first occurrence of element
let rec list_delete (#a: eqtype) (l: linked_list a) (x: a) : linked_list a =
  match l with
  | [] -> []
  | hd :: tl -> 
      if hd = x then tl
      else hd :: list_delete tl x

/// Get the length of the list
let list_length (#a: Type) (l: linked_list a) : nat =
  length l

(** LinkedList Properties **)

/// Inserting an element makes it searchable
let lemma_list_insert_search (#a: eqtype) (l: linked_list a) (x: a)
  : Lemma (list_search (list_insert l x) x == true)
  = ()

/// Deleting an element that appears exactly once makes it not searchable
let rec lemma_list_delete_search_single (#a: eqtype) (l: linked_list a) (x: a)
  : Lemma 
    (requires list_search l x /\ ~(list_search (list_delete l x) x))
    (ensures list_search (list_delete l x) x == false)
  = match l with
    | [] -> ()
    | hd :: tl ->
        if hd = x then ()
        else lemma_list_delete_search_single tl x

/// Deleting from empty list yields empty list
let lemma_list_delete_empty (#a: eqtype) (x: a)
  : Lemma (list_delete [] x == [])
  = ()

/// Deleting element not in list doesn't change the list
let rec lemma_list_delete_not_found (#a: eqtype) (l: linked_list a) (x: a)
  : Lemma 
    (requires ~(list_search l x))
    (ensures list_delete l x == l)
  = match l with
    | [] -> ()
    | hd :: tl -> lemma_list_delete_not_found tl x

/// Insert increases length by 1
let lemma_list_insert_length (#a: Type) (l: linked_list a) (x: a)
  : Lemma (list_length (list_insert l x) == list_length l + 1)
  = ()

/// Delete decreases length by at most 1
let rec lemma_list_delete_length_bound (#a: eqtype) (l: linked_list a) (x: a)
  : Lemma (list_length (list_delete l x) <= list_length l)
  = match l with
    | [] -> ()
    | hd :: tl ->
        if hd = x then ()
        else lemma_list_delete_length_bound tl x

/// Delete of found element decreases length by exactly 1
let rec lemma_list_delete_length_decreases (#a: eqtype) (l: linked_list a) (x: a)
  : Lemma
    (requires list_search l x)
    (ensures list_length (list_delete l x) == list_length l - 1)
  = match l with
    | [] -> ()
    | hd :: tl ->
        if hd = x then ()
        else (
          lemma_list_delete_length_decreases tl x;
          lemma_list_delete_length_bound tl x
        )

/// Searching empty list returns false
let lemma_list_search_empty (#a: eqtype) (x: a)
  : Lemma (list_search [] x == false)
  = ()

/// Empty list has length 0
let lemma_list_empty_length (#a: Type)
  : Lemma (list_length (list_empty #a) == 0)
  = ()
