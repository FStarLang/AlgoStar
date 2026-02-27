module CLRS.Ch10.Queue
#lang-pulse
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot
module Math = FStar.Math.Lemmas
open CLRS.Common.ListLemmas

// Helper lemma: modular arithmetic for addition
let lemma_mod_add_assoc (a b: nat) (n: pos)
  : Lemma ((a + b) % n == ((a % n) + b) % n)
  = // Use the fact that (a + b) % n = ((a % n) + (b % n)) % n
    // Then ((a % n) + b) % n = ((a % n) + (b % n)) % n since (b % n) cancels
    Math.lemma_mod_add_distr (a % n) b n;
    Math.lemma_mod_add_distr a b n

// Helper lemma: specific case for wraparound
let lemma_tail_update (head size: nat) (capacity: pos)
  : Lemma
    (requires size < capacity /\ head < capacity)
    (ensures
      (let old_tail = (head + size) % capacity in
       let new_tail = (old_tail + 1) % capacity in
       let new_size = size + 1 in
       new_tail == (head + new_size) % capacity))
  = lemma_mod_add_assoc head (size + 1) capacity

// Helper lemma: dequeue tail invariant
let lemma_tail_dequeue (head size: nat) (capacity: pos)
  : Lemma
    (requires size > 0 /\ head < capacity /\ size <= capacity)
    (ensures
      (let tail = (head + size) % capacity in
       let new_head = (head + 1) % capacity in
       let new_size = size - 1 in
       tail == (new_head + new_size) % capacity))
  = lemma_mod_add_assoc head size capacity

// Helper lemma: wraparound logic matches modulo
let lemma_wraparound_eq_mod (old_val: nat) (capacity: pos)
  : Lemma
    (requires old_val < capacity)
    (ensures
      (let new_val_raw = old_val + 1 in
       let new_val = if new_val_raw >= capacity then 0 else new_val_raw in
       new_val == (old_val + 1) % capacity))
  = if old_val + 1 >= capacity then (
      // old_val = capacity - 1, so (old_val + 1) = capacity
      // new_val = 0
      // (old_val + 1) % capacity = capacity % capacity = 0
      assert (old_val == capacity - 1);
      Math.lemma_mod_spec capacity capacity
    ) else (
      // old_val < capacity - 1, so old_val + 1 < capacity
      // new_val = old_val + 1
      // (old_val + 1) % capacity = old_val + 1 (since old_val + 1 < capacity)
      Math.lemma_mod_spec (old_val + 1) capacity
    )

// Helper lemma: modular arithmetic for addition - different indices
let lemma_mod_index_ne (head: nat) (i: nat) (len: nat) (capacity: pos)
  : Lemma
    (requires i < len /\ len < capacity /\ head < capacity)
    (ensures (head + i) % capacity <> (head + len) % capacity)
  = // Since i < len < capacity and head < capacity:
    // If head + len < capacity: no wraparound, so (head + i) < (head + len) < capacity
    //   Thus (head + i) % capacity = head + i and (head + len) % capacity = head + len
    //   These are different since i < len
    // If head + len >= capacity: (head + len) % capacity = head + len - capacity
    //   Since len < capacity, we have head + len < head + capacity < 2*capacity
    //   So head + len - capacity < head
    //   If head + i < capacity: (head + i) % capacity = head + i >= head > head + len - capacity
    //   If head + i >= capacity: (head + i) % capacity = head + i - capacity < head + len - capacity
    //     Since i < len
    ()

// Helper lemma: modular arithmetic associativity for indices
let lemma_mod_index_shift (head: nat) (i: nat) (capacity: pos)
  : Lemma
    (requires head < capacity)
    (ensures (let new_head = (head + 1) % capacity in
             ((new_head + i) % capacity == (head + (i + 1)) % capacity)))
  = let new_head = (head + 1) % capacity in
    // By modular arithmetic: ((a % n) + b) % n = (a + b) % n
    lemma_mod_add_assoc (head + 1) i capacity

// Helper lemma: empty queue satisfies invariant (vacuous forall)
let lemma_empty_queue_inv (arr_seq: Seq.seq 'a) (capacity: pos)
  : Lemma 
    (requires Seq.length arr_seq == capacity)
    (ensures forall (i:nat). i < 0 ==> 
             Seq.index arr_seq (i % capacity) == L.index ([] <: list 'a) i)
  = ()

// Helper lemma: updating array preserves queue invariant when enqueuing
let lemma_enqueue_invariant
  (#a:Type)
  (arr_seq: Seq.seq a)
  (contents: list a)
  (new_elem: a)
  (head: nat)
  (tail: nat{tail < Seq.length arr_seq})
  (capacity: pos)
  : Lemma
    (requires
      Seq.length arr_seq == capacity /\
      L.length contents < capacity /\
      head < capacity /\
      tail < capacity /\
      tail == (head + L.length contents) % capacity /\
      (forall (i:nat). i < L.length contents ==> 
        Seq.index arr_seq ((head + i) % capacity) == L.index contents i))
    (ensures
      (let new_seq = Seq.upd arr_seq tail new_elem in
       let new_contents = L.append contents [new_elem] in
       L.length new_contents == L.length contents + 1 /\
       Seq.length new_seq == capacity /\
       (forall (i:nat). i < L.length new_contents ==>
         Seq.index new_seq ((head + i) % capacity) == L.index new_contents i)))
  = let new_seq = Seq.upd arr_seq tail new_elem in
    Seq.lemma_len_upd tail new_elem arr_seq;
    let new_contents = L.append contents [new_elem] in
    lemma_append_length contents [new_elem];
    // Key insight: tail == (head + |contents|) % capacity
    // Prove for all indices
    let aux (i:nat{i < L.length new_contents}) 
      : Lemma (ensures 
          (let idx = (head + i) % capacity in
           idx < Seq.length new_seq /\
           Seq.index new_seq idx == L.index new_contents i))
      = lemma_index_append contents [new_elem] i;
        let idx = (head + i) % capacity in
        // idx < capacity by definition of modulo
        assert (idx < capacity);
        // Seq.length new_seq == capacity by lemma_len_upd
        assert (idx < Seq.length new_seq);
        if i < L.length contents then (
          // Old elements
          // idx = (head + i) % capacity and i < |contents|
          // tail == (head + |contents|) % capacity
          // So idx != tail (they differ by the modulo operation)
          if L.length contents > 0 then (
            // Need to prove idx != tail
            lemma_mod_index_ne head i (L.length contents) capacity;
            // idx != tail, so new_seq[idx] == arr_seq[idx]
            Seq.lemma_index_upd2 arr_seq tail new_elem idx
          ) else ()
        ) else (
          // New element: i == L.length contents
          // idx = (head + |contents|) % capacity = tail
          // new_seq[tail] == new_elem == new_contents[|contents|]
          assert (i == L.length contents);
          assert (idx == tail);
          Seq.lemma_index_upd1 arr_seq tail new_elem
        )
    in
    Classical.forall_intro aux

// Helper lemma: tail position in non-full queue
let lemma_tail_position
  (head: nat)
  (size: nat)
  (capacity: nat)
  : Lemma
    (requires capacity > 0 /\ size < capacity /\ head < capacity)
    (ensures (head + size) % capacity < capacity)
  = ()

// Helper lemma: indexing into tail
let rec lemma_index_tl (#a:Type) (xs: list a{L.length xs > 0}) (i:nat{i < L.length (L.tl xs)})
  : Lemma (L.index (L.tl xs) i == L.index xs (i + 1))
  = match xs with
    | [x] -> ()
    | x :: xs' -> if i = 0 then () else lemma_index_tl xs' (i - 1)

// Helper lemma: after dequeue, remaining elements maintain invariant
let lemma_dequeue_invariant
  (#a:Type)
  (arr_seq: Seq.seq a)
  (contents: list a)
  (head: nat)
  (capacity: pos)
  : Lemma
    (requires
      Seq.length arr_seq == capacity /\
      L.length contents > 0 /\
      head < capacity /\
      (forall (i:nat). i < L.length contents ==> 
        Seq.index arr_seq ((head + i) % capacity) == L.index contents i))
    (ensures
      (let new_head = (head + 1) % capacity in
       let new_contents = L.tl contents in
       (forall (i:nat). i < L.length new_contents ==>
         Seq.index arr_seq ((new_head + i) % capacity) == L.index new_contents i)))
  = let new_head = (head + 1) % capacity in
    let new_contents = L.tl contents in
    let aux (i:nat{i < L.length new_contents})
      : Lemma (Seq.index arr_seq ((new_head + i) % capacity) == L.index new_contents i)
      = // new_contents == L.tl contents
        // new_contents[i] == contents[i+1]
        lemma_index_tl contents i;
        // new_head = (head + 1) % capacity
        // So (new_head + i) % capacity = ((head + 1) % capacity + i) % capacity
        // By modular arithmetic, this equals (head + 1 + i) % capacity = (head + (i+1)) % capacity
        // And arr_seq[(head + (i+1)) % capacity] == contents[i+1] from the precondition
        // Since i < |new_contents| = |contents| - 1, we have i+1 < |contents|
        assert (i + 1 < L.length contents);
        // Use the precondition: arr_seq[(head + (i+1)) % capacity] == contents[i+1]
        lemma_mod_index_shift head i capacity
    in
    Classical.forall_intro aux

// Create a new empty queue with given capacity
fn create_queue (t:Type0) (default_val: t) (capacity: SZ.t)
  requires emp
  requires pure (SZ.v capacity > 0 /\ SZ.fits (SZ.v capacity + 1))
  returns q: queue t
  ensures queue_inv q (hide []) ** 
          pure (reveal q.capacity == SZ.v capacity)
{
  let arr = V.alloc default_val capacity;
  with arr_seq. assert (V.pts_to arr arr_seq);
  
  let head_ref = B.alloc 0sz;
  let tail_ref = B.alloc 0sz;
  let size_ref = B.alloc 0sz;
  
  let q : queue t = {
    data = arr;
    head = head_ref;
    tail = tail_ref;
    size = size_ref;
    capacity_sz = capacity;
    capacity = hide (SZ.v capacity);
  };
  
  // Rewrite to use q.data, q.head, q.tail, q.size
  rewrite (V.pts_to arr arr_seq) as (V.pts_to q.data arr_seq);
  rewrite (B.pts_to head_ref 0sz) as (B.pts_to q.head 0sz);
  rewrite (B.pts_to tail_ref 0sz) as (B.pts_to q.tail 0sz);
  rewrite (B.pts_to size_ref 0sz) as (B.pts_to q.size 0sz);
  
  // Prove the invariant for empty queue
  lemma_empty_queue_inv #t arr_seq (SZ.v capacity);
  
  // Establish the invariant for empty queue
  fold (queue_inv q (hide []));
  
  q
}

// Check if queue is empty
fn queue_empty (#t:Type0) (q: queue t) (#contents: erased (list t))
  requires queue_inv q contents
  returns b: bool
  ensures queue_inv q contents **
          pure (b <==> L.length (reveal contents) == 0)
{
  unfold (queue_inv q contents);
  with arr_seq head_v tail_v size_v. _;
  
  let size_val = B.(!q.size);
  
  let is_empty = (size_val = 0sz);
  
  fold (queue_inv q contents);
  is_empty
}

// Enqueue an element at the tail
fn enqueue (#t:Type0) (q: queue t) (#contents: erased (list t)) (x: t)
  requires queue_inv q contents **
           pure (L.length (reveal contents) < reveal q.capacity)
  returns unit
  ensures queue_inv q (hide (L.append (reveal contents) [x]))
{
  unfold (queue_inv q contents);
  with arr_seq head_v tail_v size_v. _;
  
  // Read current tail and size
  let tail_val = B.(!q.tail);
  let size_val = B.(!q.size);
  
  // Write element at tail position
  V.op_Array_Assignment q.data tail_val x;
  with new_arr_seq. assert (V.pts_to q.data new_arr_seq);
  
  // Calculate new tail with wraparound
  // We know: tail_val < capacity, so tail_val + 1 <= capacity
  // And capacity > 0, so SZ.fits (capacity + 1) from precondition
  // Therefore SZ.fits (tail_val + 1)
  assert (pure (SZ.v tail_val < reveal q.capacity));
  assert (pure (SZ.v tail_val + 1 <= reveal q.capacity));
  assert (pure (SZ.fits (SZ.v tail_val + 1)));
  
  let new_tail_raw = SZ.add tail_val 1sz;
  let cap_sz = q.capacity_sz;
  
  let mut new_tail : SZ.t = 0sz;
  if (SZ.(new_tail_raw >=^ cap_sz)) {
    new_tail := 0sz;
  } else {
    new_tail := new_tail_raw;
  };
  
  let new_tail_v = !new_tail;
  
  // Prove new_tail_v is correct modulo value
  assert (pure (SZ.v q.capacity_sz == reveal q.capacity));
  lemma_wraparound_eq_mod (SZ.v tail_val) (reveal q.capacity);
  assert (pure (SZ.v new_tail_v == (SZ.v tail_val + 1) % reveal q.capacity));
  
  // Increment size
  let new_size = SZ.add size_val 1sz;
  
  // Update tail and size
  with _old_tail. assert (B.pts_to q.tail _old_tail);
  B.op_Colon_Equals q.tail new_tail_v;
  
  with _old_size. assert (B.pts_to q.size _old_size);
  B.op_Colon_Equals q.size new_size;
  
  // Prove the invariant is maintained
  // Old invariant: tail_val == (head_v + size_v) % capacity
  // New invariant: new_tail_v == (head_v + new_size) % capacity
  lemma_tail_update (SZ.v head_v) (SZ.v size_val) (reveal q.capacity);
  
  lemma_enqueue_invariant arr_seq (reveal contents) x (SZ.v head_v) (SZ.v tail_val) (reveal q.capacity);
  
  // Establish new invariant
  fold (queue_inv q (hide (L.append (reveal contents) [x])))
}

// Dequeue an element from the head
#push-options "--z3rlimit 40"
fn dequeue (#t:Type0) (q: queue t) (#contents: erased (list t))
  requires queue_inv q contents
  requires pure (L.length (reveal contents) > 0)
  returns x: t
  ensures exists* xs. 
    queue_inv q (hide xs) **
    pure (reveal contents == x :: xs)
{
  unfold (queue_inv q contents);
  with arr_seq head_v tail_v size_v. _;
  
  // Read current head and size
  let head_val = B.(!q.head);
  let size_val = B.(!q.size);
  
  // Read the element at the head
  let elem = V.op_Array_Access q.data head_val;
  
  // Prove elem is the first element of contents
  assert (pure (SZ.v head_v < reveal q.capacity));
  // elem == Seq.index arr_seq (SZ.v head_val) from Vec read
  // head_val == head_v from Box read
  // head_v < capacity, so head_v % capacity == head_v
  assert (pure (SZ.v head_v % reveal q.capacity == SZ.v head_v));
  // From invariant with i=0: arr_seq[(head_v + 0) % capacity] == contents[0]
  assert (pure (Seq.index arr_seq ((SZ.v head_v + 0) % reveal q.capacity) == L.index (reveal contents) 0));
  assert (pure (Seq.index arr_seq (SZ.v head_v) == L.index (reveal contents) 0));
  assert (pure (L.index (reveal contents) 0 == L.hd (reveal contents)));
  assert (pure (elem == L.hd (reveal contents)));
  
  // Calculate new head with wraparound
  // We know: head_v < capacity, so head_v + 1 <= capacity
  // And SZ.fits (capacity + 1) from precondition
  // Therefore SZ.fits (head_v + 1)
  assert (pure (SZ.v head_val + 1 <= reveal q.capacity));
  assert (pure (SZ.fits (SZ.v head_val + 1)));
  
  let new_head_raw = SZ.add head_val 1sz;
  let cap_sz = q.capacity_sz;
  
  let mut new_head : SZ.t = 0sz;
  if (SZ.(new_head_raw >=^ cap_sz)) {
    new_head := 0sz;
  } else {
    new_head := new_head_raw;
  };
  
  let new_head_v = !new_head;
  
  // Prove new_head_v is correct modulo value
  assert (pure (SZ.v q.capacity_sz == reveal q.capacity));
  lemma_wraparound_eq_mod (SZ.v head_val) (reveal q.capacity);
  assert (pure (SZ.v new_head_v == (SZ.v head_val + 1) % reveal q.capacity));
  
  // Decrement size
  let new_size = SZ.sub size_val 1sz;
  
  // Update head and size
  with _old_head. assert (B.pts_to q.head _old_head);
  B.op_Colon_Equals q.head new_head_v;
  
  with _old_size. assert (B.pts_to q.size _old_size);
  B.op_Colon_Equals q.size new_size;
  
  // Prove the invariant for remaining elements
  // Old invariant: tail_v == (head_val + size_val) % capacity
  // New invariant: tail_v == (new_head_v + new_size) % capacity
  lemma_tail_dequeue (SZ.v head_val) (SZ.v size_val) (reveal q.capacity);
  
  lemma_dequeue_invariant arr_seq (reveal contents) (SZ.v head_val) (reveal q.capacity);
  
  // Establish new invariant
  fold (queue_inv q (hide (L.tl (reveal contents))));
  
  elem
}
#pop-options
