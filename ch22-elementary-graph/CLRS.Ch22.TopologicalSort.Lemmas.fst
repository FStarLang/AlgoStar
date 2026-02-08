module CLRS.Ch22.TopologicalSort.Lemmas

open FStar.Seq
open FStar.Mul

(* Topological ordering: for every vertex w at output position j,
   every predecessor u of w appears at some earlier position k < j. *)

let strong_order_inv (adj: seq int) (n: nat) (output: seq int) (count: nat) : prop =
  count <= Seq.length output /\
  Seq.length adj == n * n /\
  (forall (j: nat). j < count ==>
    (let w = Seq.index output j in
     w >= 0 /\ w < n ==>
     (forall (u: nat). u < n /\ u * n + w < n * n /\ Seq.index adj (u * n + w) <> 0 ==>
       (exists (k: nat). k < j /\ Seq.index output k == u))))

(* Extending strong_order_inv: when adding a vertex v at position count
   whose all predecessors are already in output[0..count) *)
let lemma_strong_order_extend 
  (adj: seq int) (n: nat) (output_old output_new: seq int) (count: nat) (v: int)
  : Lemma
    (requires
      strong_order_inv adj n output_old count /\
      count < Seq.length output_new /\
      Seq.length output_new == Seq.length output_old /\
      Seq.index output_new count == v /\
      (forall (k: nat). k < count ==> Seq.index output_new k == Seq.index output_old k) /\
      v >= 0 /\ v < n /\
      Seq.length adj == n * n /\
      (forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==>
        (exists (k: nat). k < count /\ Seq.index output_old k == u)))
    (ensures strong_order_inv adj n output_new (count + 1))
  = ()

(* Base case: strong_order_inv trivially holds at count 0 *)
let lemma_strong_order_base (adj: seq int) (n: nat) (output: seq int)
  : Lemma
    (requires Seq.length adj == n * n /\ 0 <= Seq.length output)
    (ensures strong_order_inv adj n output 0)
  = ()

(* Queue property: every vertex in queue[qh..qt) has all predecessors in output[0..count) *)
let queue_preds_in_output (adj: seq int) (n: nat) (queue: seq int) (qh qt: nat) 
                          (output: seq int) (count: nat) : prop =
  qh <= qt /\ qt <= Seq.length queue /\
  count <= Seq.length output /\
  Seq.length adj == n * n /\
  (forall (qi: nat). qh <= qi /\ qi < qt ==>
    (let w = Seq.index queue qi in
     w >= 0 /\ w < n /\
     (forall (u: nat). u < n /\ u * n + w < n * n /\ Seq.index adj (u * n + w) <> 0 ==>
       (exists (k: nat). k < count /\ Seq.index output k == u))))

(* For SizeT queue: use SZ.v to get int value *)
let queue_preds_in_output_sz (adj: seq int) (n: nat) (queue: seq FStar.SizeT.t) (qh qt: nat)
                              (output: seq int) (count: nat) : prop =
  qh <= qt /\ qt <= Seq.length queue /\
  count <= Seq.length output /\
  Seq.length adj == n * n /\
  (forall (qi: nat). qh <= qi /\ qi < qt ==>
    (let w = FStar.SizeT.v (Seq.index queue qi) in
     w >= 0 /\ w < n /\
     (forall (u: nat). u < n /\ u * n + w < n * n /\ Seq.index adj (u * n + w) <> 0 ==>
       (exists (k: nat). k < count /\ Seq.index output k == u))))

(* Dequeuing from queue preserves the property for the rest *)
let lemma_queue_preds_dequeue (adj: seq int) (n: nat) (queue: seq FStar.SizeT.t) 
                               (qh qt: nat) (output: seq int) (count: nat)
  : Lemma
    (requires queue_preds_in_output_sz adj n queue qh qt output count /\ qh < qt)
    (ensures queue_preds_in_output_sz adj n queue (qh + 1) qt output count)
  = ()

(* When we extend output by writing the dequeued vertex u at position count,
   the queue preds property is preserved because output[0..count+1) contains everything
   that output[0..count) contained plus u. Since queue preds were in output[0..count),
   they're also in output[0..count+1). *)
let lemma_queue_preds_extend_output
  (adj: seq int) (n: nat) (queue: seq FStar.SizeT.t) (qh qt: nat)
   (output_old output_new: seq int) (count: nat) (v: int)
  : Lemma
    (requires
      queue_preds_in_output_sz adj n queue qh qt output_old count /\
      count < Seq.length output_new /\
      Seq.length output_new == Seq.length output_old /\
      Seq.index output_new count == v /\
      (forall (k: nat). k < count ==> Seq.index output_new k == Seq.index output_old k))
    (ensures queue_preds_in_output_sz adj n queue qh qt output_new (count + 1))
  = ()

(* When a vertex w is newly enqueued (added at position qt in queue),
   and all predecessors of w are in output[0..count+1),
   the queue preds property extends *)
let lemma_queue_preds_enqueue
  (adj: seq int) (n: nat) (queue_old queue_new: seq FStar.SizeT.t) (qh qt: nat)
   (output: seq int) (count: nat) (w: FStar.SizeT.t)
  : Lemma
    (requires
      queue_preds_in_output_sz adj n queue_old qh qt output count /\
      qt < Seq.length queue_new /\
      Seq.length queue_new == Seq.length queue_old /\
      FStar.SizeT.v (Seq.index queue_new qt) == FStar.SizeT.v w /\
      (forall (qi: nat). qh <= qi /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi) /\
      FStar.SizeT.v w >= 0 /\ FStar.SizeT.v w < n /\
      Seq.length adj == n * n /\
      count <= Seq.length output /\
      (forall (u: nat). u < n /\ u * n + FStar.SizeT.v w < n * n /\ 
        Seq.index adj (u * n + FStar.SizeT.v w) <> 0 ==>
        (exists (k: nat). k < count /\ Seq.index output k == u)))
    (ensures queue_preds_in_output_sz adj n queue_new qh (qt + 1) output count)
  = ()

(* When a vertex is NOT enqueued (just overwriting some position in queue
   but not advancing qt), queue_preds is preserved if the overwrite is
   outside the [qh, qt) range *)
let lemma_queue_preds_no_enqueue
  (adj: seq int) (n: nat) (queue_old queue_new: seq FStar.SizeT.t) (qh qt: nat)
   (output: seq int) (count: nat) (write_pos: nat)
  : Lemma
    (requires
      queue_preds_in_output_sz adj n queue_old qh qt output count /\
      Seq.length queue_new == Seq.length queue_old /\
      (forall (qi: nat). qh <= qi /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi))
    (ensures queue_preds_in_output_sz adj n queue_new qh qt output count)
  = ()

(* Initial queue: vertices with in-degree 0 in the original graph have no predecessors,
   so their predecessors are trivially all in output (which is empty). *)
let initial_indeg_zero_no_preds (adj: seq int) (n: nat) (in_deg: seq int) (v: nat)
  : Lemma
    (requires 
      v < n /\ Seq.length adj == n * n /\ Seq.length in_deg >= n /\
      Seq.index in_deg v == 0 /\
      // in_deg[v] correctly counts predecessors (initial in-degrees)
      (forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==>
        Seq.index in_deg v > 0))
    (ensures
      forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==> false)
  = ()

(* --- In-degree correctness --- *)

(* Check if vertex x is in output[0..count) *)
let rec is_in_output (output: seq int) (count: nat) (x: int) : Tot bool (decreases count) =
  if count = 0 then false
  else if count > Seq.length output then false
  else if Seq.index output (count - 1) = x then true
  else is_in_output output (count - 1) x

(* Count predecessors of v not yet in output[0..count), scanning u from 0 to scan *)
let rec count_remaining_preds (adj: seq int) (n: nat) (output: seq int) (count: nat)
                               (v: nat) (scan: nat) : Tot nat (decreases scan) =
  if scan = 0 then 0
  else
    let u = scan - 1 in
    let rest = count_remaining_preds adj n output count v u in
    if u < n && v < n && Seq.length adj = n * n && u * n + v < Seq.length adj &&
       Seq.index adj (u * n + v) <> 0 && count <= Seq.length output &&
       not (is_in_output output count u)
    then 1 + rest
    else rest

(* In-degree correctness: in_deg[v] == number of predecessors of v NOT in output *)
let indeg_correct (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat) : prop =
  Seq.length in_deg >= n /\ Seq.length adj == n * n /\ count <= Seq.length output /\
  (forall (v: nat). v < n ==> Seq.index in_deg v == count_remaining_preds adj n output count v n)

(* Key lemma: if in_deg[v] == 0 under indeg_correct, then all predecessors are in output *)
let rec lemma_zero_means_all_preds_output 
  (adj: seq int) (n: nat) (output: seq int) (count: nat) (v: nat) (scan: nat)
  : Lemma
    (requires
      v < n /\ Seq.length adj == n * n /\ count <= Seq.length output /\
      scan <= n /\ count_remaining_preds adj n output count v scan == 0)
    (ensures
      forall (u: nat). u < scan /\ u < n /\ u * n + v < Seq.length adj /\
        Seq.index adj (u * n + v) <> 0 ==> is_in_output output count u)
    (decreases scan)
  = if scan = 0 then ()
    else lemma_zero_means_all_preds_output adj n output count v (scan - 1)

(* Corollary at full scan *)
let lemma_zero_indeg_all_preds_output
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat) (v: nat)
  : Lemma
    (requires indeg_correct adj n in_deg output count /\ v < n /\ Seq.index in_deg v == 0)
    (ensures forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==>
      is_in_output output count u)
  = lemma_zero_means_all_preds_output adj n output count v n

(* is_in_output implies exists k < count *)
let rec lemma_is_in_output_exists (output: seq int) (count: nat) (x: nat)
  : Lemma
    (requires count <= Seq.length output /\ is_in_output output count x)
    (ensures exists (k: nat). k < count /\ Seq.index output k == x)
    (decreases count)
  = if count = 0 then ()
    else if Seq.index output (count - 1) = x then ()
    else lemma_is_in_output_exists output (count - 1) x

(* Combined: zero in-degree + indeg_correct ==> all preds are in output (exists form) *)
let lemma_zero_indeg_preds_exist
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat) (v: nat)
  : Lemma
    (requires indeg_correct adj n in_deg output count /\ v < n /\ Seq.index in_deg v == 0)
    (ensures forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==>
      (exists (k: nat). k < count /\ Seq.index output k == u))
  = lemma_zero_indeg_all_preds_output adj n in_deg output count v;
    let aux (u: nat)
      : Lemma (requires u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0)
              (ensures exists (k: nat). k < count /\ Seq.index output k == u)
      = lemma_is_in_output_exists output count u
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(* Adding a vertex to output: count_remaining_preds decreases by 1 for successors,
   stays the same for non-successors *)

(* Key: when we add vertex new_v to output at position count,
   and new_v has an edge to v (is a predecessor of v),
   count_remaining_preds decreases by 1 *)

(* For the inner loop: after decrementing in_degree for all neighbors of u,
   indeg_correct transitions from count to count+1 *)

(* This is complex. Let me provide a simpler lemma that the inner loop needs:
   After the inner loop that decrements in_deg for each neighbor of u,
   if the original in_deg satisfied indeg_correct ... count,
   the new in_deg satisfies indeg_correct ... (count + 1),
   where output_new has u at position count *)

// Helper: is_in_output is preserved when writing beyond count
let rec lemma_is_in_output_extend (output: seq int) (count: nat) (x: nat) (pos: nat) (v: int)
  : Lemma
    (requires count <= Seq.length output /\ pos >= count /\ pos < Seq.length output /\ 
             is_in_output output count x)
    (ensures is_in_output (Seq.upd output pos v) count x)
    (decreases count)
  = if count = 0 then ()
    else begin
      assert (Seq.index (Seq.upd output pos v) (count - 1) == Seq.index output (count - 1));
      if Seq.index output (count - 1) = x then ()
      else lemma_is_in_output_extend output (count - 1) x pos v
    end

// After writing u_val at output[count], is_in_output (count+1) u_val holds
let lemma_is_in_output_new (output: seq int) (count: nat) (u_val: int)
  : Lemma
    (requires count < Seq.length output)
    (ensures is_in_output (Seq.upd output count u_val) (count + 1) u_val)
  = let output' = Seq.upd output count u_val in
    assert (Seq.index output' count == u_val)

