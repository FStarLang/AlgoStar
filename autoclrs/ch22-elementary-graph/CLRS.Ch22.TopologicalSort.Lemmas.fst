module CLRS.Ch22.TopologicalSort.Lemmas

open FStar.Seq
open FStar.Mul

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
#push-options "--z3rlimit 20"
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
#pop-options

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

(* Transfer queue_preds from old queue to new queue, extending the range.
   For qi in [qh, qt_old): uses preservation of queue entries.
   For qi in [qt_old, qt_new): uses provided forall about new entries. *)
let lemma_queue_preds_transfer_and_extend
  (adj: seq int) (n: nat) (queue_old queue_new: seq FStar.SizeT.t) (qh qt_old qt_new: nat)
   (output: seq int) (count: nat)
  : Lemma
    (requires
      queue_preds_in_output_sz adj n queue_old qh qt_old output count /\
      qt_old <= qt_new /\ qt_new <= Seq.length queue_new /\
      (forall (qi: nat). {:pattern (Seq.index queue_new qi)}
        qh <= qi /\ qi < qt_old ==> Seq.index queue_new qi == Seq.index queue_old qi) /\
      (forall (qi: nat). {:pattern (Seq.index queue_new qi)}
        qt_old <= qi /\ qi < qt_new ==>
          (let w = FStar.SizeT.v (Seq.index queue_new qi) in
           w >= 0 /\ w < n /\
           (forall (u: nat). u < n /\ u * n + w < n * n /\ Seq.index adj (u * n + w) <> 0 ==>
             (exists (k: nat). k < count /\ Seq.index output k == u)))))
    (ensures queue_preds_in_output_sz adj n queue_new qh qt_new output count)
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

(* Contrapositive: if no index k < count has output[k] == x, then not is_in_output *)
let rec lemma_not_in_output_from_forall (output: seq int) (count: nat) (x: int)
  : Lemma
    (requires count <= Seq.length output /\
      (forall (k: nat). k < count ==> Seq.index output k <> x))
    (ensures not (is_in_output output count x))
    (decreases count)
  = if count = 0 then ()
    else lemma_not_in_output_from_forall output (count - 1) x

(* Reverse: not is_in_output implies forall k < count. output[k] <> x *)
let rec lemma_not_is_in_output_implies_forall (output: seq int) (count: nat) (x: int)
  : Lemma
    (requires count <= Seq.length output /\ not (is_in_output output count x))
    (ensures forall (k: nat). k < count ==> Seq.index output k <> x)
    (decreases count)
  = if count = 0 then ()
    else lemma_not_is_in_output_implies_forall output (count - 1) x

(* Reverse: exists k < count with output[k] == x implies is_in_output *)
let rec lemma_exists_to_is_in_output (output: seq int) (count: nat) (x: int)
  : Lemma
    (requires count <= Seq.length output /\
      (exists (k: nat). k < count /\ Seq.index output k == x))
    (ensures is_in_output output count x)
    (decreases count)
  = if count = 0 then ()
    else if Seq.index output (count - 1) = x then ()
    else begin
      assert (exists (k: nat). k < count - 1 /\ Seq.index output k == x);
      lemma_exists_to_is_in_output output (count - 1) x
    end

(* If all predecessors of w are in output (as is_in_output), count_remaining_preds == 0 *)
let rec lemma_zero_crp_from_all_preds (adj: seq int) (n: nat) (output: seq int) (count: nat)
                                       (w: nat) (scan: nat)
  : Lemma
    (requires
      w < n /\ Seq.length adj == n * n /\ count <= Seq.length output /\
      scan <= n /\
      (forall (u: nat). u < n /\ u * n + w < n * n /\ Seq.index adj (u * n + w) <> 0 ==>
        is_in_output output count u))
    (ensures count_remaining_preds adj n output count w scan == 0)
    (decreases scan)
  = if scan = 0 then ()
    else lemma_zero_crp_from_all_preds adj n output count w (scan - 1)

(* Corollary: queue_preds + indeg_correct implies in_deg == 0 for each queue entry *)
let lemma_queue_entry_zero_indeg
  (adj: seq int) (n: nat) (in_deg: seq int) (queue: seq FStar.SizeT.t)
  (output: seq int) (count: nat) (qh qt: nat) (qi: nat)
  : Lemma
    (requires
      queue_preds_in_output_sz adj n queue qh qt output count /\
      indeg_correct adj n in_deg output count /\
      qi >= qh /\ qi < qt)
    (ensures Seq.index in_deg (FStar.SizeT.v (Seq.index queue qi)) == 0)
  = let w = FStar.SizeT.v (Seq.index queue qi) in
    // Step 1: queue_preds gives exists form for all preds of w
    // Step 2: convert exists → is_in_output for each pred
    let aux (u: nat)
      : Lemma
        (requires u < n /\ u * n + w < n * n /\ Seq.index adj (u * n + w) <> 0)
        (ensures is_in_output output count u)
      = lemma_exists_to_is_in_output output count u
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    // Step 3: all preds in output → count_remaining_preds == 0
    lemma_zero_crp_from_all_preds adj n output count w n

(* Forall-lifted: all old queue entries have zero in-degree.
   NOTE: ensures includes bounds conjuncts for Seq.index well-formedness *)
let lemma_queue_entry_zero_indeg_forall
  (adj: seq int) (n: nat) (in_deg: seq int) (queue: seq FStar.SizeT.t)
  (output: seq int) (count: nat) (qh qt: nat)
  : Lemma
    (requires
      queue_preds_in_output_sz adj n queue qh qt output count /\
      indeg_correct adj n in_deg output count /\
      qh <= qt /\ qt <= Seq.length queue /\
      Seq.length in_deg == n /\ Seq.length adj == n * n)
    (ensures forall (qi: nat).
      qh <= qi /\ qi < qt ==>
        qi < Seq.length queue /\
        FStar.SizeT.v (Seq.index queue qi) < Seq.length in_deg /\
        Seq.index in_deg (FStar.SizeT.v (Seq.index queue qi)) == 0)
  = let aux (qi: nat)
      : Lemma (requires qh <= qi /\ qi < qt)
              (ensures
                qi < Seq.length queue /\
                FStar.SizeT.v (Seq.index queue qi) < Seq.length in_deg /\
                Seq.index in_deg (FStar.SizeT.v (Seq.index queue qi)) == 0)
    = lemma_queue_entry_zero_indeg adj n in_deg queue output count qh qt qi
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

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

(* Forall-lifted version: for all v with in_deg 0, all preds are in output *)
let lemma_zero_indeg_preds_exist_forall
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat)
  : Lemma
    (requires indeg_correct adj n in_deg output count)
    (ensures forall (v: nat). {:pattern (Seq.index in_deg v)}
      v < n /\ Seq.index in_deg v == 0 ==>
        (forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==>
          (exists (k: nat). k < count /\ Seq.index output k == u)))
  = let aux (v: nat)
      : Lemma (requires v < n /\ Seq.index in_deg v == 0)
              (ensures forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==>
                (exists (k: nat). k < count /\ Seq.index output k == u))
    = lemma_zero_indeg_preds_exist adj n in_deg output count v
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

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

(* NOT is_in_output is preserved when writing beyond count *)
let rec lemma_is_in_output_extend_neg
  (output: seq int) (count: nat) (x: int) (pos: nat) (v: int)
  : Lemma
    (requires count <= Seq.length output /\ pos >= count /\ pos < Seq.length output /\
             not (is_in_output output count x))
    (ensures not (is_in_output (Seq.upd output pos v) count x))
    (decreases count)
  = if count = 0 then ()
    else begin
      assert (Seq.index (Seq.upd output pos v) (count - 1) == Seq.index output (count - 1));
      if Seq.index output (count - 1) = x then ()
      else lemma_is_in_output_extend_neg output (count - 1) x pos v
    end

(* For x != u_val: NOT is_in_output at count implies NOT at count+1 after Seq.upd *)
let lemma_not_in_output_upd_neq
  (output: seq int) (count: nat) (u_val: int) (x: int)
  : Lemma
    (requires count < Seq.length output /\ x <> u_val /\ not (is_in_output output count x))
    (ensures not (is_in_output (Seq.upd output count u_val) (count + 1) x))
  = let output' = Seq.upd output count u_val in
    assert (Seq.index output' count == u_val);
    // is_in_output output' (count+1) x checks output'[count] (= u_val <> x) then recurses
    // Need: not (is_in_output output' count x)
    lemma_is_in_output_extend_neg output count x count u_val

(* Key transition lemma: how count_remaining_preds changes when extending output by one vertex *)
#push-options "--z3rlimit 40 --fuel 2"
let rec lemma_crp_extend
  (adj: seq int) (n: nat) (output: seq int) (count: nat) (u_val: int) (v: nat) (scan: nat)
  : Lemma
    (requires
      count < Seq.length output /\ scan <= n /\ v < n /\
      Seq.length adj == n * n /\
      u_val >= 0 /\ u_val < n /\
      not (is_in_output output count u_val))
    (ensures (
      let delta = (if u_val < scan && u_val * n + v < n * n && Seq.index adj (u_val * n + v) <> 0 then 1 else 0) in
      count_remaining_preds adj n (Seq.upd output count u_val) (count + 1) v scan ==
        count_remaining_preds adj n output count v scan - delta))
    (decreases scan)
  = if scan = 0 then ()
    else begin
      let u = scan - 1 in
      let output' = Seq.upd output count u_val in
      lemma_crp_extend adj n output count u_val v (scan - 1);
      if u = u_val then begin
        lemma_is_in_output_new output count u_val;
        ()
      end else begin
        if u < n && v < n && Seq.length adj = n * n && u * n + v < Seq.length adj &&
           Seq.index adj (u * n + v) <> 0 && count <= Seq.length output then begin
          if is_in_output output count u then begin
            lemma_is_in_output_extend output count u count u_val;
            ()
          end else begin
            lemma_not_in_output_upd_neq output count u_val u;
            ()
          end
        end else ()
      end
    end
#pop-options

(* Main transition lemma: after inner loop processes all neighbors of u,
   indeg_correct transitions from count to count+1 *)
let lemma_indeg_transition
  (adj: seq int) (n: nat) (in_deg_old in_deg_new: seq int)
  (output: seq int) (count: nat) (u_val: int)
  : Lemma
    (requires
      indeg_correct adj n in_deg_old output count /\
      count < Seq.length output /\
      Seq.length in_deg_new >= n /\
      u_val >= 0 /\ u_val < n /\
      not (is_in_output output count u_val) /\
      (forall (v: nat). v < n ==>
        Seq.index in_deg_new v ==
          Seq.index in_deg_old v -
            (if u_val * n + v < n * n && Seq.index adj (u_val * n + v) <> 0 then 1 else 0)))
    (ensures
      indeg_correct adj n in_deg_new (Seq.upd output count u_val) (count + 1))
  = let output' = Seq.upd output count u_val in
    let aux (v: nat)
      : Lemma (requires v < n)
              (ensures v < Seq.length in_deg_new /\
                       Seq.index in_deg_new v == count_remaining_preds adj n output' (count + 1) v n)
    = lemma_crp_extend adj n output count u_val v n
    in
    Classical.forall_intro (Classical.move_requires aux)

(* ================================================================
   OUTPUT-VERTEX IN-DEGREE ZERO LEMMA
   ================================================================ *)

(* Helper: if exists k < count. output[k] == x, then is_in_output output count x *)
let rec lemma_exists_implies_is_in_output (output: seq int) (count: nat) (x: int) (k: nat)
  : Lemma
    (requires k < count /\ count <= Seq.length output /\ Seq.index output k == x)
    (ensures is_in_output output count x)
    (decreases count)
  = if count = 0 then ()
    else if Seq.index output (count - 1) = x then ()
    else lemma_exists_implies_is_in_output output (count - 1) x k

(* is_in_output is monotone: if x is in output[0..c1), it's in output[0..c2) for c2 >= c1 *)
let rec lemma_is_in_output_monotone (output: seq int) (c1 c2: nat) (x: int)
  : Lemma
    (requires c1 <= c2 /\ c2 <= Seq.length output /\ is_in_output output c1 x)
    (ensures is_in_output output c2 x)
    (decreases c2)
  = if c1 = c2 then ()
    else if Seq.index output (c2 - 1) = x then ()
    else lemma_is_in_output_monotone output c1 (c2 - 1) x

(* Helper: if all predecessors of v are in output[0..count), then crp == 0 *)
let rec lemma_crp_zero_when_all_preds_in_output
  (adj: seq int) (n: nat) (output: seq int) (count: nat) (v: nat) (scan: nat)
  : Lemma
    (requires
      v < n /\ scan <= n /\ count <= Seq.length output /\ Seq.length adj == n * n /\
      (forall (u: nat). u < scan /\ u < n /\ u * n + v < n * n /\
        Seq.index adj (u * n + v) <> 0 ==> is_in_output output count u))
    (ensures count_remaining_preds adj n output count v scan == 0)
    (decreases scan)
  = if scan = 0 then ()
    else lemma_crp_zero_when_all_preds_in_output adj n output count v (scan - 1)

(* Main lemma: under strong_order_inv + indeg_correct, output verts have in_deg == 0 *)
#push-options "--z3rlimit 20"
let lemma_output_vert_zero_indeg
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat) (j: nat)
  : Lemma
    (requires
      strong_order_inv adj n output count /\
      indeg_correct adj n in_deg output count /\
      j < count /\ Seq.index output j >= 0 /\ Seq.index output j < n)
    (ensures Seq.index in_deg (Seq.index output j) == 0)
  = let w = Seq.index output j in
    let aux (u: nat)
      : Lemma
        (requires u < n /\ u * n + w < n * n /\ Seq.index adj (u * n + w) <> 0)
        (ensures is_in_output output count u)
      = assert (exists (k: nat). k < j /\ Seq.index output k == u);
        let aux2 (k: nat)
          : Lemma (requires k < j /\ Seq.index output k == u)
                  (ensures is_in_output output count u)
          = lemma_exists_implies_is_in_output output j u k;
            lemma_is_in_output_monotone output j count u
        in
        Classical.forall_intro (Classical.move_requires aux2)
    in
    Classical.forall_intro (Classical.move_requires aux);
    lemma_crp_zero_when_all_preds_in_output adj n output count w n
#pop-options

(* Contrapositive: if in_deg[v] > 0 under strong_order_inv + indeg_correct,
   then v is NOT in output[0..count). Requires output entries to be valid. *)
let lemma_positive_indeg_not_in_output
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat) (v: nat)
  : Lemma
    (requires
      strong_order_inv adj n output count /\
      indeg_correct adj n in_deg output count /\
      v < n /\ Seq.index in_deg v > 0 /\
      (forall (k: nat). k < count ==> Seq.index output k >= 0 /\ Seq.index output k < n))
    (ensures not (is_in_output output count v))
  = if is_in_output output count v then begin
      lemma_is_in_output_exists output count v;
      let aux (k: nat)
        : Lemma (requires k < count /\ Seq.index output k == v)
                (ensures False)
        = lemma_output_vert_zero_indeg adj n in_deg output count k
      in
      Classical.forall_intro (Classical.move_requires aux);
      ()
    end else ()

(* Forall-lifted: for all v with positive in_deg, v is not in output *)
let lemma_positive_indeg_not_in_output_forall
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat)
  : Lemma
    (requires
      strong_order_inv adj n output count /\
      indeg_correct adj n in_deg output count /\
      (forall (k: nat). k < count ==> Seq.index output k >= 0 /\ Seq.index output k < n))
    (ensures forall (v: nat). {:pattern (Seq.index in_deg v)}
      v < n /\ Seq.index in_deg v > 0 ==> not (is_in_output output count v))
  = let aux (v: nat)
      : Lemma (requires v < n /\ Seq.index in_deg v > 0)
              (ensures not (is_in_output output count v))
    = lemma_positive_indeg_not_in_output adj n in_deg output count v
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(* Forall-lifted: not in output implies forall k, output[k] <> v *)
let lemma_not_in_output_implies_forall_all
  (output: seq int) (count: nat)
  : Lemma
    (requires count <= Seq.length output)
    (ensures forall (v: nat).
      not (is_in_output output count v) ==>
        (forall (k: nat). k < count ==> Seq.index output k <> v))
  = let aux (v: nat)
      : Lemma (requires not (is_in_output output count v))
              (ensures forall (k: nat). k < count ==> Seq.index output k <> v)
    = lemma_not_is_in_output_implies_forall output count v
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(* Combined: positive in-degree → fresh against output (chains both steps) *)
let lemma_positive_indeg_implies_fresh_forall
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat)
  : Lemma
    (requires
      strong_order_inv adj n output count /\
      indeg_correct adj n in_deg output count /\
      count <= Seq.length output /\
      (forall (k: nat). k < count ==> Seq.index output k >= 0 /\ Seq.index output k < n))
    (ensures forall (v: nat). {:pattern (Seq.index in_deg v)}
      v < n /\ Seq.index in_deg v > 0 ==>
        (forall (k: nat). {:pattern (Seq.index output k)}
          k < count ==> Seq.index output k <> v))
  = let aux (v: nat)
      : Lemma (requires v < n /\ Seq.index in_deg v > 0)
              (ensures forall (k: nat). k < count ==> Seq.index output k <> v)
    = lemma_positive_indeg_not_in_output adj n in_deg output count v;
      lemma_not_is_in_output_implies_forall output count v
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(* ================================================================
   Initialization Lemmas: count_remaining_preds at count=0
   At count=0, is_in_output is always false, so count_remaining_preds
   simply counts edges (predecessors) without any output filtering.
   ================================================================ *)

(* Base case: scanning 0 predecessors yields 0 *)
let lemma_crp_zero_base (adj: seq int) (n: nat) (output: seq int) (v: nat)
  : Lemma (count_remaining_preds adj n output 0 v 0 == 0)
  = ()

(* Step case: count_remaining_preds at count=0 decomposes into previous scan + edge check.
   At count=0, is_in_output is always false, simplifying the recurrence. *)
let lemma_crp_zero_step (adj: seq int) (n: nat) (output: seq int) (v: nat) (scan: nat)
  : Lemma
    (requires v < n /\ scan < n /\ Seq.length adj == n * n /\ Seq.length output >= 0)
    (ensures
      count_remaining_preds adj n output 0 v (scan + 1) ==
        count_remaining_preds adj n output 0 v scan +
          (if Seq.index adj (scan * n + v) <> 0 then 1 else 0))
  = // Unfold one step: scan+1 > 0, u = scan
    // is_in_output output 0 scan = false (count=0)
    // Condition simplifies to: scan < n && v < n && ... && adj[scan*n+v] <> 0
    assert (not (is_in_output output 0 scan));
    assert (scan * n + v < n * n)

(* At count=0, count_remaining_preds is independent of the output sequence *)
let rec lemma_crp_zero_output_independent
  (adj: seq int) (n: nat) (output1 output2: seq int) (v: nat) (scan: nat)
  : Lemma
    (ensures count_remaining_preds adj n output1 0 v scan ==
             count_remaining_preds adj n output2 0 v scan)
    (decreases scan)
  = if scan = 0 then ()
    else begin
      lemma_crp_zero_output_independent adj n output1 output2 v (scan - 1);
      assert (not (is_in_output output1 0 (scan - 1)));
      assert (not (is_in_output output2 0 (scan - 1)))
    end

(* ================================================================
   PREDECESSOR FINDING — Pure function for cycle construction
   ================================================================ *)

(* If count_remaining_preds > 0, find a concrete predecessor not in output *)
let rec find_non_output_predecessor
  (adj: seq int) (n: nat) (output: seq int) (count: nat) (v: nat) (scan: nat)
  : Pure nat
    (requires
      v < n /\ scan <= n /\ count <= Seq.length output /\ Seq.length adj == n * n /\
      count_remaining_preds adj n output count v scan > 0)
    (ensures fun u ->
      u < scan /\ u < n /\ u * n + v < n * n /\
      Seq.index adj (u * n + v) <> 0 /\
      not (is_in_output output count u))
    (decreases scan)
  = let u = scan - 1 in
    if u < n && v < n && Seq.length adj = n * n && u * n + v < Seq.length adj &&
       Seq.index adj (u * n + v) <> 0 && count <= Seq.length output &&
       not (is_in_output output count u)
    then u
    else find_non_output_predecessor adj n output count v (scan - 1)

(* Corollary at full scan *)
let find_non_output_predecessor_full
  (adj: seq int) (n: nat) (output: seq int) (count: nat) (v: nat)
  : Pure nat
    (requires
      v < n /\ count <= Seq.length output /\ Seq.length adj == n * n /\
      count_remaining_preds adj n output count v n > 0)
    (ensures fun u ->
      u < n /\ u * n + v < n * n /\
      Seq.index adj (u * n + v) <> 0 /\
      not (is_in_output output count u))
  = find_non_output_predecessor adj n output count v n

