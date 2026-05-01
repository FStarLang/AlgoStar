(** CLRS Chapter 22: Topological Sort — Lemma Interface
 * Signatures for Kahn's topological sort correctness.
 * Zero admits. *)
module CLRS.Ch22.TopologicalSort.Lemmas

open FStar.Seq

let strong_order_inv (adj: seq int) (n: nat) (output: seq int) (count: nat) : prop =
  count <= Seq.length output /\
  Seq.length adj == n * n /\
  (forall (j: nat). j < count ==>
    (let w = Seq.index output j in
     w >= 0 /\ w < n ==>
     (forall (u: nat). u < n /\ u * n + w < n * n /\ Seq.index adj (u * n + w) <> 0 ==>
       (exists (k: nat). k < j /\ Seq.index output k == u))))

val lemma_strong_order_extend 
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

val lemma_strong_order_base (adj: seq int) (n: nat) (output: seq int)
  : Lemma
    (requires Seq.length adj == n * n /\ 0 <= Seq.length output)
    (ensures strong_order_inv adj n output 0)

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

val lemma_queue_preds_dequeue (adj: seq int) (n: nat) (queue: seq FStar.SizeT.t) 
                               (qh qt: nat) (output: seq int) (count: nat)
  : Lemma
    (requires queue_preds_in_output_sz adj n queue qh qt output count /\ qh < qt)
    (ensures queue_preds_in_output_sz adj n queue (qh + 1) qt output count)

val lemma_queue_preds_extend_output
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

val lemma_queue_preds_enqueue
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

val lemma_queue_preds_no_enqueue
  (adj: seq int) (n: nat) (queue_old queue_new: seq FStar.SizeT.t) (qh qt: nat)
   (output: seq int) (count: nat) (write_pos: nat)
  : Lemma
    (requires
      queue_preds_in_output_sz adj n queue_old qh qt output count /\
      Seq.length queue_new == Seq.length queue_old /\
      (forall (qi: nat). qh <= qi /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi))
    (ensures queue_preds_in_output_sz adj n queue_new qh qt output count)

val lemma_queue_preds_transfer_and_extend
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

val initial_indeg_zero_no_preds (adj: seq int) (n: nat) (in_deg: seq int) (v: nat)
  : Lemma
    (requires 
      v < n /\ Seq.length adj == n * n /\ Seq.length in_deg >= n /\
      Seq.index in_deg v == 0 /\
      // in_deg[v] correctly counts predecessors (initial in-degrees)
      (forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==>
        Seq.index in_deg v > 0))
    (ensures
      forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==> false)

let rec is_in_output (output: seq int) (count: nat) (x: int) : Tot bool (decreases count) =
  if count = 0 then false
  else if count > Seq.length output then false
  else if Seq.index output (count - 1) = x then true
  else is_in_output output (count - 1) x

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

let indeg_correct (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat) : prop =
  Seq.length in_deg >= n /\ Seq.length adj == n * n /\ count <= Seq.length output /\
  (forall (v: nat). v < n ==> Seq.index in_deg v == count_remaining_preds adj n output count v n)

val lemma_zero_means_all_preds_output 
  (adj: seq int) (n: nat) (output: seq int) (count: nat) (v: nat) (scan: nat)
  : Lemma
    (requires
      v < n /\ Seq.length adj == n * n /\ count <= Seq.length output /\
      scan <= n /\ count_remaining_preds adj n output count v scan == 0)
    (ensures
      forall (u: nat). u < scan /\ u < n /\ u * n + v < Seq.length adj /\
        Seq.index adj (u * n + v) <> 0 ==> is_in_output output count u)

val lemma_zero_indeg_all_preds_output
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat) (v: nat)
  : Lemma
    (requires indeg_correct adj n in_deg output count /\ v < n /\ Seq.index in_deg v == 0)
    (ensures forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==>
      is_in_output output count u)

val lemma_is_in_output_exists (output: seq int) (count: nat) (x: nat)
  : Lemma
    (requires count <= Seq.length output /\ is_in_output output count x)
    (ensures exists (k: nat). k < count /\ Seq.index output k == x)

val lemma_not_in_output_from_forall (output: seq int) (count: nat) (x: int)
  : Lemma
    (requires count <= Seq.length output /\
      (forall (k: nat). k < count ==> Seq.index output k <> x))
    (ensures not (is_in_output output count x))

val lemma_not_is_in_output_implies_forall (output: seq int) (count: nat) (x: int)
  : Lemma
    (requires count <= Seq.length output /\ not (is_in_output output count x))
    (ensures forall (k: nat). k < count ==> Seq.index output k <> x)

val lemma_exists_to_is_in_output (output: seq int) (count: nat) (x: int)
  : Lemma
    (requires count <= Seq.length output /\
      (exists (k: nat). k < count /\ Seq.index output k == x))
    (ensures is_in_output output count x)

val lemma_zero_crp_from_all_preds (adj: seq int) (n: nat) (output: seq int) (count: nat)
                                       (w: nat) (scan: nat)
  : Lemma
    (requires
      w < n /\ Seq.length adj == n * n /\ count <= Seq.length output /\
      scan <= n /\
      (forall (u: nat). u < n /\ u * n + w < n * n /\ Seq.index adj (u * n + w) <> 0 ==>
        is_in_output output count u))
    (ensures count_remaining_preds adj n output count w scan == 0)

val lemma_queue_entry_zero_indeg
  (adj: seq int) (n: nat) (in_deg: seq int) (queue: seq FStar.SizeT.t)
  (output: seq int) (count: nat) (qh qt: nat) (qi: nat)
  : Lemma
    (requires
      queue_preds_in_output_sz adj n queue qh qt output count /\
      indeg_correct adj n in_deg output count /\
      qi >= qh /\ qi < qt)
    (ensures Seq.index in_deg (FStar.SizeT.v (Seq.index queue qi)) == 0)

val lemma_queue_entry_zero_indeg_forall
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

val lemma_zero_indeg_preds_exist
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat) (v: nat)
  : Lemma
    (requires indeg_correct adj n in_deg output count /\ v < n /\ Seq.index in_deg v == 0)
    (ensures forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==>
      (exists (k: nat). k < count /\ Seq.index output k == u))

val lemma_zero_indeg_preds_exist_forall
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat)
  : Lemma
    (requires indeg_correct adj n in_deg output count)
    (ensures forall (v: nat). {:pattern (Seq.index in_deg v)}
      v < n /\ Seq.index in_deg v == 0 ==>
        (forall (u: nat). u < n /\ u * n + v < n * n /\ Seq.index adj (u * n + v) <> 0 ==>
          (exists (k: nat). k < count /\ Seq.index output k == u)))

val lemma_is_in_output_extend (output: seq int) (count: nat) (x: nat) (pos: nat) (v: int)
  : Lemma
    (requires count <= Seq.length output /\ pos >= count /\ pos < Seq.length output /\ 
             is_in_output output count x)
    (ensures is_in_output (Seq.upd output pos v) count x)

val lemma_is_in_output_new (output: seq int) (count: nat) (u_val: int)
  : Lemma
    (requires count < Seq.length output)
    (ensures is_in_output (Seq.upd output count u_val) (count + 1) u_val)

val lemma_is_in_output_extend_neg
  (output: seq int) (count: nat) (x: int) (pos: nat) (v: int)
  : Lemma
    (requires count <= Seq.length output /\ pos >= count /\ pos < Seq.length output /\
             not (is_in_output output count x))
    (ensures not (is_in_output (Seq.upd output pos v) count x))

val lemma_not_in_output_upd_neq
  (output: seq int) (count: nat) (u_val: int) (x: int)
  : Lemma
    (requires count < Seq.length output /\ x <> u_val /\ not (is_in_output output count x))
    (ensures not (is_in_output (Seq.upd output count u_val) (count + 1) x))

val lemma_crp_extend
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

val lemma_indeg_transition
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

val lemma_exists_implies_is_in_output (output: seq int) (count: nat) (x: int) (k: nat)
  : Lemma
    (requires k < count /\ count <= Seq.length output /\ Seq.index output k == x)
    (ensures is_in_output output count x)

val lemma_is_in_output_monotone (output: seq int) (c1 c2: nat) (x: int)
  : Lemma
    (requires c1 <= c2 /\ c2 <= Seq.length output /\ is_in_output output c1 x)
    (ensures is_in_output output c2 x)

val lemma_crp_zero_when_all_preds_in_output
  (adj: seq int) (n: nat) (output: seq int) (count: nat) (v: nat) (scan: nat)
  : Lemma
    (requires
      v < n /\ scan <= n /\ count <= Seq.length output /\ Seq.length adj == n * n /\
      (forall (u: nat). u < scan /\ u < n /\ u * n + v < n * n /\
        Seq.index adj (u * n + v) <> 0 ==> is_in_output output count u))
    (ensures count_remaining_preds adj n output count v scan == 0)

val lemma_output_vert_zero_indeg
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat) (j: nat)
  : Lemma
    (requires
      strong_order_inv adj n output count /\
      indeg_correct adj n in_deg output count /\
      j < count /\ Seq.index output j >= 0 /\ Seq.index output j < n)
    (ensures Seq.index in_deg (Seq.index output j) == 0)

val lemma_positive_indeg_not_in_output
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat) (v: nat)
  : Lemma
    (requires
      strong_order_inv adj n output count /\
      indeg_correct adj n in_deg output count /\
      v < n /\ Seq.index in_deg v > 0 /\
      (forall (k: nat). k < count ==> Seq.index output k >= 0 /\ Seq.index output k < n))
    (ensures not (is_in_output output count v))

val lemma_positive_indeg_not_in_output_forall
  (adj: seq int) (n: nat) (in_deg: seq int) (output: seq int) (count: nat)
  : Lemma
    (requires
      strong_order_inv adj n output count /\
      indeg_correct adj n in_deg output count /\
      (forall (k: nat). k < count ==> Seq.index output k >= 0 /\ Seq.index output k < n))
    (ensures forall (v: nat). {:pattern (Seq.index in_deg v)}
      v < n /\ Seq.index in_deg v > 0 ==> not (is_in_output output count v))

val lemma_not_in_output_implies_forall_all
  (output: seq int) (count: nat)
  : Lemma
    (requires count <= Seq.length output)
    (ensures forall (v: nat).
      not (is_in_output output count v) ==>
        (forall (k: nat). k < count ==> Seq.index output k <> v))

val lemma_positive_indeg_implies_fresh_forall
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

val lemma_crp_zero_base (adj: seq int) (n: nat) (output: seq int) (v: nat)
  : Lemma (count_remaining_preds adj n output 0 v 0 == 0)

val lemma_crp_zero_step (adj: seq int) (n: nat) (output: seq int) (v: nat) (scan: nat)
  : Lemma
    (requires v < n /\ scan < n /\ Seq.length adj == n * n /\ Seq.length output >= 0)
    (ensures
      count_remaining_preds adj n output 0 v (scan + 1) ==
        count_remaining_preds adj n output 0 v scan +
          (if Seq.index adj (scan * n + v) <> 0 then 1 else 0))

val lemma_crp_zero_output_independent
  (adj: seq int) (n: nat) (output1 output2: seq int) (v: nat) (scan: nat)
  : Lemma
    (ensures count_remaining_preds adj n output1 0 v scan ==
             count_remaining_preds adj n output2 0 v scan)

val find_non_output_predecessor
  (adj: seq int) (n: nat) (output: seq int) (count: nat) (v: nat) (scan: nat)
  : Pure nat
    (requires
      v < n /\ scan <= n /\ count <= Seq.length output /\ Seq.length adj == n * n /\
      count_remaining_preds adj n output count v scan > 0)
    (ensures fun u ->
      u < scan /\ u < n /\ u * n + v < n * n /\
      Seq.index adj (u * n + v) <> 0 /\
      not (is_in_output output count u))

val find_non_output_predecessor_full
  (adj: seq int) (n: nat) (output: seq int) (count: nat) (v: nat)
  : Pure nat
    (requires
      v < n /\ count <= Seq.length output /\ Seq.length adj == n * n /\
      count_remaining_preds adj n output count v n > 0)
    (ensures fun u ->
      u < n /\ u * n + v < n * n /\
      Seq.index adj (u * n + v) <> 0 /\
      not (is_in_output output count u))

