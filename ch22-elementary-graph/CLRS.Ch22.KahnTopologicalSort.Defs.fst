module CLRS.Ch22.KahnTopologicalSort.Defs
open FStar.SizeT
open FStar.Mul
open CLRS.Ch22.TopologicalSort.Spec
open CLRS.Ch22.TopologicalSort.Lemmas
open CLRS.Ch22.TopologicalSort.Verified

module SZ = FStar.SizeT
module Seq = FStar.Seq

// Helper lemma: if u < n, v < n, and n*n fits, then u*n+v < n*n and fits
let lemma_index_in_bounds (u v n: nat)
  : Lemma
    (requires u < n /\ v < n /\ n > 0 /\ SZ.fits (n * n))
    (ensures u * n + v < n * n /\ SZ.fits (u * n) /\ SZ.fits (u * n + v))
  = ()

// Helper: Convert Seq.seq int to Seq.seq nat when all elements are >= 0
let seq_int_to_nat (s: Seq.seq int)
  : Pure (Seq.seq nat)
    (requires forall (i: nat). i < Seq.length s ==> Seq.index s i >= 0)
    (ensures fun r -> Seq.length r == Seq.length s /\
                      (forall (i: nat). i < Seq.length s ==> Seq.index r i == Seq.index s i))
  = let aux (i:nat{i < Seq.length s}) : nat = 
      let v = Seq.index s i in
      assert (v >= 0);
      v
    in
    Seq.init (Seq.length s) aux

(* ================================================================
   PREDICATES — Named abstractions for Kahn's algorithm invariants
   ================================================================ *)

(* Output elements in [0, count) are pairwise distinct *)
(* ================================================================
   PREDICATE LEMMAS
   ================================================================ *)

(* Base: partial_distinct holds vacuously at count 0 *)
let partial_distinct_base (output: Seq.seq int)
  : Lemma (requires Seq.length output >= 0)
          (ensures partial_distinct output 0)
  = ()

(* Extending partial_distinct: if new element is not in output[0..count),
   then output[0..count+1) is still distinct (after writing at position count) *)
let partial_distinct_extend
  (output_old output_new: Seq.seq int) (count: nat) (v: int)
  : Lemma
    (requires
      partial_distinct output_old count /\
      count < Seq.length output_new /\
      Seq.length output_new == Seq.length output_old /\
      Seq.index output_new count == v /\
      (forall (k: nat). k < count ==> Seq.index output_new k == Seq.index output_old k) /\
      (forall (k: nat). k < count ==> Seq.index output_old k <> v))
    (ensures partial_distinct output_new (count + 1))
  = ()

(* Extending partial_valid *)
let partial_valid_extend
  (output_old output_new: Seq.seq int) (count n: nat) (v: int)
  : Lemma
    (requires
      partial_valid output_old count n /\
      count < Seq.length output_new /\
      Seq.length output_new == Seq.length output_old /\
      Seq.index output_new count == v /\
      (forall (k: nat). k < count ==> Seq.index output_new k == Seq.index output_old k) /\
      v >= 0 /\ v < n)
    (ensures partial_valid output_new (count + 1) n)
  = ()

(* queue_fresh after dequeue: narrowing queue range preserves freshness *)
let queue_fresh_dequeue
  (output: Seq.seq int) (count: nat) (queue: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires queue_fresh output count queue qh qt /\ qh < qt)
    (ensures queue_fresh output count queue (qh + 1) qt)
  = ()

(* queue_fresh after extending output with the dequeued element:
   The dequeued element u is at queue[qh]. After adding u to output at position count,
   remaining queue entries in [qh+1, qt) must not be u (from queue_distinct)
   AND must not be in output[0..count) (from queue_fresh before dequeue). *)
#push-options "--z3rlimit 40"
let queue_fresh_extend_output
  (output_old output_new: Seq.seq int) (count: nat)
  (queue: Seq.seq SZ.t) (qh qt: nat) (u: int)
  : Lemma
    (requires
      queue_fresh output_old count queue (qh + 1) qt /\
      queue_distinct_sz queue (qh + 1) qt /\
      count < Seq.length output_new /\
      Seq.length output_new == Seq.length output_old /\
      Seq.index output_new count == u /\
      (forall (k: nat). k < count ==> Seq.index output_new k == Seq.index output_old k) /\
      // u is not equal to any remaining queue entry
      (forall (qi: nat). qi >= qh + 1 /\ qi < qt ==>
        SZ.v (Seq.index queue qi) <> u))
    (ensures queue_fresh output_new (count + 1) queue (qh + 1) qt)
  = ()
#pop-options

(* queue_fresh after enqueue: new entry w must not be in output[0..count) *)
let queue_fresh_enqueue
  (output: Seq.seq int) (count: nat)
  (queue_old queue_new: Seq.seq SZ.t) (qh qt: nat) (w: SZ.t)
  : Lemma
    (requires
      queue_fresh output count queue_old qh qt /\
      qt < Seq.length queue_new /\
      Seq.length queue_new == Seq.length queue_old /\
      Seq.index queue_new qt == w /\
      (forall (qi: nat). qi >= qh /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi) /\
      (forall (k: nat). k < count ==> Seq.index output k <> SZ.v w))
    (ensures queue_fresh output count queue_new qh (qt + 1))
  = ()

(* queue_fresh after no-enqueue (queue write outside active range) *)
let queue_fresh_no_enqueue
  (output: Seq.seq int) (count: nat)
  (queue_old queue_new: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires
      queue_fresh output count queue_old qh qt /\
      Seq.length queue_new == Seq.length queue_old /\
      (forall (qi: nat). qi >= qh /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi))
    (ensures queue_fresh output count queue_new qh qt)
  = ()

(* queue_distinct after enqueue: new entry w must differ from all existing entries *)
let queue_distinct_enqueue
  (queue_old queue_new: Seq.seq SZ.t) (qh qt: nat) (w: SZ.t)
  : Lemma
    (requires
      queue_distinct_sz queue_old qh qt /\
      qt < Seq.length queue_new /\
      Seq.length queue_new == Seq.length queue_old /\
      Seq.index queue_new qt == w /\
      (forall (qi: nat). qi >= qh /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi) /\
      (forall (qi: nat). qi >= qh /\ qi < qt ==> SZ.v (Seq.index queue_old qi) <> SZ.v w))
    (ensures queue_distinct_sz queue_new qh (qt + 1))
  = ()

(* queue_distinct after no-enqueue *)
let queue_distinct_no_enqueue
  (queue_old queue_new: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires
      queue_distinct_sz queue_old qh qt /\
      Seq.length queue_new == Seq.length queue_old /\
      (forall (qi: nat). qi >= qh /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi))
    (ensures queue_distinct_sz queue_new qh qt)
  = ()

(* queue_distinct after dequeue *)
let queue_distinct_dequeue
  (queue: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires queue_distinct_sz queue qh qt /\ qh < qt)
    (ensures queue_distinct_sz queue (qh + 1) qt)
  = ()

(* queue_valid_sz after enqueue *)
let queue_valid_enqueue
  (queue_old queue_new: Seq.seq SZ.t) (qh qt n: nat) (w: SZ.t)
  : Lemma
    (requires
      queue_valid_sz queue_old qh qt n /\
      qt < Seq.length queue_new /\
      Seq.length queue_new == Seq.length queue_old /\
      Seq.index queue_new qt == w /\
      (forall (qi: nat). qi >= qh /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi) /\
      SZ.v w < n)
    (ensures queue_valid_sz queue_new qh (qt + 1) n)
  = ()

(* queue_valid_sz after no-enqueue *)
let queue_valid_no_enqueue
  (queue_old queue_new: Seq.seq SZ.t) (qh qt n: nat)
  : Lemma
    (requires
      queue_valid_sz queue_old qh qt n /\
      Seq.length queue_new == Seq.length queue_old /\
      (forall (qi: nat). qi >= qh /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi))
    (ensures queue_valid_sz queue_new qh qt n)
  = ()

(* Derive not_in_output from queue_fresh *)
let queue_fresh_not_in_output
  (output: Seq.seq int) (count: nat) (queue: Seq.seq SZ.t) (qh qt: nat) (qi: nat)
  : Lemma
    (requires queue_fresh output count queue qh qt /\ qi >= qh /\ qi < qt)
    (ensures forall (k: nat). k < count ==> Seq.index output k <> SZ.v (Seq.index queue qi))
  = ()

(* Queue entry validity: all entries in [0, vqt) are < n *)
let queue_entries_valid_after_enqueue
  (squeue squeue': Seq.seq SZ.t) (vtail vtail': nat) (vv: SZ.t) (n: nat)
  : Lemma
    (requires
      queue_entries_valid squeue vtail n /\
      vtail' >= vtail /\
      vtail' <= vtail + 1 /\
      vtail' <= Seq.length squeue' /\
      Seq.length squeue' == Seq.length squeue /\
      (forall (i:nat). i < vtail ==> Seq.index squeue' i == Seq.index squeue i) /\
      (vtail' > vtail ==> Seq.index squeue' vtail == vv) /\
      SZ.v vv < n
    )
    (ensures queue_entries_valid squeue' vtail' n)
  = assert (vtail' <= Seq.length squeue');
    let aux (k:nat) : Lemma (requires k < vtail') (ensures k < Seq.length squeue' /\ SZ.v (Seq.index squeue' k) < n) =
      if k < vtail then (
        assert (k < Seq.length squeue);
        assert (Seq.index squeue' k == Seq.index squeue k)
      )
      else (
        assert (k == vtail);
        assert (Seq.index squeue' vtail == vv)
      )
    in
    Classical.forall_intro (Classical.move_requires aux)

(* ================================================================
   INITIALIZATION INVARIANTS — for Step 1 (compute in-degrees)
   ================================================================ *)

(* After processing rows [0, row) fully and columns [0, col) of row `row`,
   in_degree[j] == count_remaining_preds adj n output 0 j (row+1) for j < col,
   in_degree[j] == count_remaining_preds adj n output 0 j row    for j >= col. *)
[@@  "opaque_to_smt"]
let lemma_step1_inner_step
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (in_deg in_deg': Seq.seq int)
  (row col: nat)
  : Lemma
    (requires
      step1_inner_inv adj n output in_deg row col /\
      col < n /\ row < n /\
      Seq.length adj == n * n /\
      row * n + col < Seq.length adj /\
      Seq.length in_deg == n /\
      Seq.length in_deg' == n /\
      SZ.fits (n * n) /\
      // Only in_deg[col] might change
      (forall (k: nat). {:pattern (Seq.index in_deg' k)} k < n /\ k <> col ==>
        Seq.index in_deg' k == Seq.index in_deg k) /\
      // in_deg'[col] = in_deg[col] + (if edge then 1 else 0)
      Seq.index in_deg' col ==
        Seq.index in_deg col +
          (if Seq.index adj (row * n + col) <> 0 then 1 else 0))
    (ensures step1_inner_inv adj n output in_deg' row (col + 1))
  = reveal_opaque (`%step1_inner_inv) (step1_inner_inv adj n output in_deg row col);
    reveal_opaque (`%step1_inner_inv) (step1_inner_inv adj n output in_deg' row (col + 1));
    lemma_crp_zero_step adj n output col row

(* Outer loop: inner invariant at col=0 follows from outer invariant *)
let lemma_step1_outer_to_inner
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (in_deg: Seq.seq int)
  (row: nat)
  : Lemma
    (requires step1_outer_inv adj n output in_deg row /\ row < n)
    (ensures step1_inner_inv adj n output in_deg row 0)
  = reveal_opaque (`%step1_outer_inv) (step1_outer_inv adj n output in_deg row);
    reveal_opaque (`%step1_inner_inv) (step1_inner_inv adj n output in_deg row 0)

(* Inner loop completes: inner invariant at col=n implies outer invariant at row+1 *)
let lemma_step1_inner_to_outer
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (in_deg: Seq.seq int)
  (row: nat)
  : Lemma
    (requires step1_inner_inv adj n output in_deg row n)
    (ensures step1_outer_inv adj n output in_deg (row + 1))
  = reveal_opaque (`%step1_inner_inv) (step1_inner_inv adj n output in_deg row n);
    reveal_opaque (`%step1_outer_inv) (step1_outer_inv adj n output in_deg (row + 1))

(* Initial state: all zeros == crp at row 0 (no predecessors scanned) *)
let lemma_step1_initial
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (in_deg: Seq.seq int)
  : Lemma
    (requires
      n > 0 /\
      Seq.length adj == n * n /\ Seq.length in_deg == n /\ Seq.length output >= 0 /\
      (forall (j: nat). j < n ==> Seq.index in_deg j == 0))
    (ensures step1_outer_inv adj n output in_deg 0)
  = reveal_opaque (`%step1_outer_inv) (step1_outer_inv adj n output in_deg 0);
    let aux (j: nat) : Lemma (requires j < n)
                              (ensures count_remaining_preds adj n output 0 j 0 == 0) =
      lemma_crp_zero_base adj n output j
    in
    Classical.forall_intro (Classical.move_requires aux)

(* Step 1 complete: outer_inv at row=n gives indeg_correct at count=0 with any output *)
let lemma_step1_to_indeg_correct
  (adj: Seq.seq int) (n: nat) (ghost_out real_out: Seq.seq int) (in_deg: Seq.seq int)
  : Lemma
    (requires step1_outer_inv adj n ghost_out in_deg n /\ n > 0 /\
              Seq.length real_out >= n)
    (ensures indeg_correct adj n in_deg real_out 0)
  = reveal_opaque (`%step1_outer_inv) (step1_outer_inv adj n ghost_out in_deg n);
    // step1_outer_inv gives: in_deg[j] == crp adj n ghost_out 0 j n
    // We need: in_deg[j] == crp adj n real_out 0 j n
    // At count=0, crp is output-independent
    let aux (j: nat) : Lemma (requires j < n)
      (ensures count_remaining_preds adj n ghost_out 0 j n == count_remaining_preds adj n real_out 0 j n) =
      lemma_crp_zero_output_independent adj n ghost_out real_out j n
    in
    Classical.forall_intro (Classical.move_requires aux)

(* ================================================================
   STEP 2 LEMMAS — Queue initialization invariant maintenance
   ================================================================ *)

(* Initial: empty queue satisfies step2_queue_inv *)
let lemma_step2_initial
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue: Seq.seq SZ.t)
  : Lemma
    (requires n > 0 /\ Seq.length in_deg == n /\ Seq.length queue == n)
    (ensures step2_queue_inv adj n in_deg output queue 0 0)
  = reveal_opaque (`%step2_queue_inv) (step2_queue_inv adj n in_deg output queue 0 0)

(* Step 2 body: enqueue vertex vi if in_deg[vi] == 0, or skip *)
let lemma_step2_enqueue
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue queue': Seq.seq SZ.t) (vqt vi: nat)
  : Lemma
    (requires
      step2_queue_inv adj n in_deg output queue vqt vi /\
      vi < n /\ n > 0 /\ SZ.fits n /\
      Seq.length queue' == Seq.length queue /\
      Seq.length in_deg == n /\
      Seq.index in_deg vi == 0 /\
      vqt < Seq.length queue' /\
      Seq.index queue' vqt == SZ.uint_to_t vi /\
      (forall (k: nat). {:pattern (Seq.index queue' k)} k < vqt ==> Seq.index queue' k == Seq.index queue k))
    (ensures step2_queue_inv adj n in_deg output queue' (vqt + 1) (vi + 1))
  = reveal_opaque (`%step2_queue_inv) (step2_queue_inv adj n in_deg output queue vqt vi);
    reveal_opaque (`%step2_queue_inv) (step2_queue_inv adj n in_deg output queue' (vqt + 1) (vi + 1));
    assert (SZ.v (Seq.index queue' vqt) == vi);
    assert (vqt + 1 <= Seq.length queue');
    // For the quantifiers in step2_queue_inv:
    // 1. queue_distinct_sz queue' 0 (vqt+1): 
    //    - Old pairs (i,j < vqt): distinct from queue_distinct_sz queue 0 vqt
    //    - New+old pair (vqt, j<vqt): queue'[vqt]=vi, queue'[j]<vi (from step2_queue_inv invariant)
    // 2. All entries < vi+1: entries < vqt have values < vi < vi+1, entry at vqt has value vi < vi+1
    // 3. All entries have in_deg 0: entries < vqt from invariant, entry at vqt = vi has in_deg = 0 (given)
    ()

(* Step 2 body: skip vertex vi (in_deg != 0) *)
let lemma_step2_skip
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue queue': Seq.seq SZ.t) (vqt vi: nat)
  : Lemma
    (requires step2_queue_inv adj n in_deg output queue vqt vi /\ vi < n /\
              Seq.length queue' == Seq.length queue /\
              vqt <= Seq.length queue' /\
              (forall (k: nat). {:pattern (Seq.index queue' k)} k < vqt ==> Seq.index queue' k == Seq.index queue k))
    (ensures step2_queue_inv adj n in_deg output queue' vqt (vi + 1))
  = reveal_opaque (`%step2_queue_inv) (step2_queue_inv adj n in_deg output queue vqt vi);
    reveal_opaque (`%step2_queue_inv) (step2_queue_inv adj n in_deg output queue' vqt (vi + 1))

(* Unified Step 2 step: handles both enqueue (deg=0) and skip (deg!=0) *)
let lemma_step2_step
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue queue': Seq.seq SZ.t) (vqt new_vqt vi: nat)
  : Lemma
    (requires
      step2_queue_inv adj n in_deg output queue vqt vi /\
      vi < n /\ n > 0 /\ SZ.fits n /\
      Seq.length queue' == Seq.length queue /\
      Seq.length in_deg == n /\
      vqt < Seq.length queue' /\
      Seq.index queue' vqt == SZ.uint_to_t vi /\
      (forall (k: nat). {:pattern (Seq.index queue' k)} k < vqt ==> Seq.index queue' k == Seq.index queue k) /\
      (if Seq.index in_deg vi = 0 then new_vqt = vqt + 1 else new_vqt = vqt))
    (ensures step2_queue_inv adj n in_deg output queue' new_vqt (vi + 1))
  = if Seq.index in_deg vi = 0
    then lemma_step2_enqueue adj n in_deg output queue queue' vqt vi
    else lemma_step2_skip adj n in_deg output queue queue' vqt vi

(* Step 2 complete: step2_queue_inv → queue_distinct_sz *)
let lemma_step2_to_queue_distinct
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue: Seq.seq SZ.t) (vqt: nat)
  : Lemma
    (requires step2_queue_inv adj n in_deg output queue vqt n)
    (ensures queue_distinct_sz queue 0 vqt)
  = reveal_opaque (`%step2_queue_inv) (step2_queue_inv adj n in_deg output queue vqt n)

(* After Step 2 loop completes (vi=n), step2_queue_inv implies queue_entries_valid *)
let lemma_step2_to_entries_valid
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue: Seq.seq SZ.t) (vqt: nat)
  : Lemma
    (requires step2_queue_inv adj n in_deg output queue vqt n)
    (ensures queue_entries_valid queue vqt n)
  = reveal_opaque (`%step2_queue_inv) (step2_queue_inv adj n in_deg output queue vqt n)

(* Step 2 complete + indeg_correct → queue_preds_in_output_sz at count=0.
   Each queued vertex has in_degree == 0, and at count=0 this means no predecessors.
   The output parameter for queue_preds can differ from step2_queue_inv's output
   since at count=0, is_in_output is always false. *)
let lemma_step2_to_queue_preds
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (step2_out real_out: Seq.seq int)
  (queue: Seq.seq SZ.t) (vqt: nat)
  : Lemma
    (requires
      step2_queue_inv adj n in_deg step2_out queue vqt n /\
      indeg_correct adj n in_deg real_out 0 /\
      n > 0 /\ Seq.length real_out >= n)
    (ensures queue_preds_in_output_sz adj n queue 0 vqt real_out 0)
  = reveal_opaque (`%step2_queue_inv) (step2_queue_inv adj n in_deg step2_out queue vqt n);
    // step2_queue_inv gives: forall k < vqt. Seq.index in_deg (SZ.v (Seq.index queue k)) == 0
    // We need: for each k < vqt, all preds of queue[k] are in output[0..0)
    // Since in_deg[v] == 0 and indeg_correct, use lemma_zero_indeg_all_preds_output
    // which says: forall u < n. adj[u*n+v] <> 0 ==> is_in_output real_out 0 u
    // Since is_in_output output 0 u is always false, this means NO predecessors exist
    // Call the lemma for each vertex in queue
    let aux (v: nat) : Lemma
      (requires v < n /\ Seq.index in_deg v == 0)
      (ensures forall (j: nat). j < n /\ j * n + v < n * n /\
                Seq.index adj (j * n + v) <> 0 ==> is_in_output real_out 0 j)
      = lemma_zero_indeg_all_preds_output adj n in_deg real_out 0 v
    in
    Classical.forall_intro (Classical.move_requires aux)

(* ================================================================
   BUNDLED INVARIANT — opaque to SMT for performance
   ================================================================ *)

(* Bundled outer-loop correctness invariant.
   Marked opaque_to_smt so that the SMT solver sees it as atomic,
   preventing quantifier explosion from the 7 inner predicates. *)
[@@  "opaque_to_smt"]
let kahn_outer_inv_elim
  (adj: Seq.seq int) (n: nat)
  (sin_deg: Seq.seq int) (squeue: Seq.seq SZ.t) (soutput: Seq.seq int)
  (vqh vqt vout: nat)
  : Lemma
    (requires kahn_outer_inv adj n sin_deg squeue soutput vqh vqt vout)
    (ensures
      strong_order_inv adj n soutput vout /\
      partial_distinct soutput vout /\
      partial_valid soutput vout n /\
      queue_fresh soutput vout squeue vqh vqt /\
      queue_distinct_sz squeue vqh vqt /\
      queue_preds_in_output_sz adj n squeue vqh vqt soutput vout /\
      indeg_correct adj n sin_deg soutput vout)
  = reveal_opaque (`%kahn_outer_inv) (kahn_outer_inv adj n sin_deg squeue soutput vqh vqt vout)

(* Introduce kahn_outer_inv from individual predicates *)
let kahn_outer_inv_intro
  (adj: Seq.seq int) (n: nat)
  (sin_deg: Seq.seq int) (squeue: Seq.seq SZ.t) (soutput: Seq.seq int)
  (vqh vqt vout: nat)
  : Lemma
    (requires
      strong_order_inv adj n soutput vout /\
      partial_distinct soutput vout /\
      partial_valid soutput vout n /\
      queue_fresh soutput vout squeue vqh vqt /\
      queue_distinct_sz squeue vqh vqt /\
      queue_preds_in_output_sz adj n squeue vqh vqt soutput vout /\
      indeg_correct adj n sin_deg soutput vout)
    (ensures kahn_outer_inv adj n sin_deg squeue soutput vqh vqt vout)
  = reveal_opaque (`%kahn_outer_inv) (kahn_outer_inv adj n sin_deg squeue soutput vqh vqt vout)

(* ================================================================
   BRIDGE LEMMAS — Connect loop invariant predicates to postcondition
   ================================================================ *)

(* Bridge: partial_distinct at count=n → all_distinct for nat sequence *)
let lemma_partial_distinct_implies_all_distinct
  (soutput: Seq.seq int) (n: nat)
  : Lemma
    (requires
      partial_distinct soutput n /\
      Seq.length soutput == n /\
      (forall (i: nat). i < n ==> Seq.index soutput i >= 0))
    (ensures all_distinct (seq_int_to_nat soutput))
  = let r = seq_int_to_nat soutput in
    assert (Seq.length r == n);
    assert (forall (i: nat). i < n ==> Seq.index r i == Seq.index soutput i);
    // partial_distinct says: forall i j < n. i<>j ==> soutput[i] <> soutput[j]
    // Since r[i] == soutput[i] and r[j] == soutput[j], all_distinct r follows
    ()

(* Bridge: use theorem_kahns_algorithm_correct + seq_int_to_nat equivalence *)
let lemma_bridge_topological_order
  (adj: Seq.seq int) (n: nat) (soutput: Seq.seq int)
  : Lemma
    (requires
      n > 0 /\ Seq.length soutput == n /\ Seq.length adj == n * n /\
      strong_order_inv adj n soutput n /\
      all_distinct_int soutput /\
      all_valid_vertices_int soutput n /\
      (forall (i: nat). i < n ==> Seq.index soutput i >= 0))
    (ensures is_topological_order adj n (seq_int_to_nat soutput))
  = // Call the Verified module's theorem with the 2-arg seq_int_to_nat
    theorem_kahns_algorithm_correct adj n soutput;
    // theorem gives: is_topological_order adj n (Verified.seq_int_to_nat soutput n)
    // We need: is_topological_order adj n (local.seq_int_to_nat soutput)
    // Both produce sequences where index i == soutput[i], so they're Seq.equal
    let r1 = seq_int_to_nat soutput in    // local 1-arg version
    let r2 = CLRS.Ch22.TopologicalSort.Verified.seq_int_to_nat soutput n in  // 2-arg version
    assert (Seq.length r1 == n);
    assert (Seq.length r2 == n);
    assert (forall (i: nat). i < n ==> Seq.index r1 i == Seq.index soutput i);
    assert (forall (i: nat). i < n ==> Seq.index r2 i == Seq.index soutput i);
    assert (Seq.equal r1 r2)

(* Bridge: partial_distinct → all_distinct_int *)
let lemma_partial_distinct_implies_all_distinct_int
  (soutput: Seq.seq int) (n: nat)
  : Lemma
    (requires partial_distinct soutput n /\ Seq.length soutput == n)
    (ensures all_distinct_int soutput)
  = ()

(* Bridge: partial_valid → all_valid_vertices_int *)
let lemma_partial_valid_implies_all_valid_int
  (soutput: Seq.seq int) (n: nat)
  : Lemma
    (requires partial_valid soutput n n /\ Seq.length soutput == n)
    (ensures all_valid_vertices_int soutput n)
  = ()

(* Inner loop in-degree tracking: partial progress through neighbor scan *)
let inner_indeg_step
  (adj: Seq.seq int) (n: nat)
  (in_deg_pre in_deg_old in_deg_new: Seq.seq int) (u_val: int) (vv: nat)
  : Lemma
    (requires
      inner_indeg_partial adj n in_deg_pre in_deg_old u_val vv /\
      vv < n /\
      Seq.length in_deg_new == n /\
      (forall (k: nat). k < n /\ k <> vv ==> Seq.index in_deg_new k == Seq.index in_deg_old k) /\
      Seq.index in_deg_new vv ==
        Seq.index in_deg_old vv -
          (if u_val * n + vv < n * n && Seq.index adj (u_val * n + vv) <> 0 then 1 else 0))
    (ensures inner_indeg_partial adj n in_deg_pre in_deg_new u_val (vv + 1))
  = ()

(* At inner loop exit (vv == n), derive the full decrement property *)
let inner_indeg_complete
  (adj: Seq.seq int) (n: nat)
  (in_deg_pre in_deg_final: Seq.seq int) (u_val: int)
  : Lemma
    (requires inner_indeg_partial adj n in_deg_pre in_deg_final u_val n)
    (ensures
      forall (v: nat). v < n ==>
        Seq.index in_deg_final v == Seq.index in_deg_pre v -
          (if u_val * n + v < n * n && Seq.index adj (u_val * n + v) <> 0 then 1 else 0))
  = ()

(* ================================================================
   PROCESS_NEIGHBORS EXTRA INVARIANT — tracks queue predicates
   ================================================================ *)

(* Extra invariant for process_neighbors inner loop.
   Tracks: old entries preserved, new entries info, new entries distinct.
   Used to prove queue_fresh/distinct/preds after process_neighbors. *)
[@@  "opaque_to_smt"]
let pn_extra_inv_initial
  (sin_deg_start: Seq.seq int) (squeue_start: Seq.seq SZ.t) (vtail_start: nat) (n: nat)
  : Lemma
    (requires vtail_start <= Seq.length squeue_start /\ Seq.length sin_deg_start == n)
    (ensures pn_extra_inv sin_deg_start sin_deg_start squeue_start squeue_start vtail_start vtail_start n)
  = reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_start sin_deg_start squeue_start squeue_start vtail_start vtail_start n)

(* Maintenance: no enqueue case (vtail unchanged) *)
let pn_extra_inv_no_enqueue
  (sin_deg_start sin_deg_old sin_deg_new: Seq.seq int)
  (squeue_start squeue_old squeue_new: Seq.seq SZ.t)
  (vtail_start vtail: nat) (n: nat) (vv: nat)
  : Lemma
    (requires
      pn_extra_inv sin_deg_start sin_deg_old squeue_start squeue_old vtail_start vtail n /\
      vv < n /\
      vtail <= Seq.length squeue_new /\
      vtail_start <= Seq.length squeue_start /\
      Seq.length squeue_new == Seq.length squeue_old /\
      Seq.length sin_deg_old == n /\
      Seq.length sin_deg_new == n /\
      Seq.length sin_deg_start == n /\
      (forall (k: nat). k < vtail ==> Seq.index squeue_new k == Seq.index squeue_old k) /\
      (forall (k: nat). k < n /\ k <> vv ==> Seq.index sin_deg_new k == Seq.index sin_deg_old k) /\
      (forall (k: nat). k >= vtail_start /\ k < vtail ==>
        SZ.v (Seq.index squeue_old k) < vv))
    (ensures pn_extra_inv sin_deg_start sin_deg_new squeue_start squeue_new vtail_start vtail n)
  = reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_start sin_deg_old squeue_start squeue_old vtail_start vtail n);
    reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_start sin_deg_new squeue_start squeue_new vtail_start vtail n)

(* Maintenance: enqueue case (vtail advances by 1) *)
let pn_extra_inv_enqueue
  (sin_deg_start sin_deg_old sin_deg_new: Seq.seq int)
  (squeue_start squeue_old squeue_new: Seq.seq SZ.t)
  (vtail_start vtail: nat) (n: nat) (vv: nat)
  : Lemma
    (requires
      pn_extra_inv sin_deg_start sin_deg_old squeue_start squeue_old vtail_start vtail n /\
      vv < n /\
      vtail < Seq.length squeue_new /\
      vtail_start <= Seq.length squeue_start /\
      Seq.length squeue_new == Seq.length squeue_old /\
      Seq.length sin_deg_old == n /\
      Seq.length sin_deg_new == n /\ Seq.length sin_deg_start == n /\
      (forall (k: nat). k < vtail ==> Seq.index squeue_new k == Seq.index squeue_old k) /\
      SZ.v (Seq.index squeue_new vtail) == vv /\
      Seq.index sin_deg_start vv > 0 /\
      Seq.index sin_deg_new vv == 0 /\
      (forall (k: nat). k < n /\ k <> vv ==> Seq.index sin_deg_new k == Seq.index sin_deg_old k) /\
      (forall (k: nat). k >= vtail_start /\ k < vtail ==>
        SZ.v (Seq.index squeue_old k) < vv))
    (ensures pn_extra_inv sin_deg_start sin_deg_new squeue_start squeue_new vtail_start (vtail + 1) n)
  = reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_start sin_deg_old squeue_start squeue_old vtail_start vtail n);
    // Old new entries [vtail_start, vtail): vertex < vv hence <> vv, so sin_deg_new == sin_deg_old
    // New entry at vtail: vertex = vv, sin_deg_start vv > 0, sin_deg_new vv = 0
    // Pairwise distinct [vtail_start, vtail+1): old entries have vertex < vv, new entry has vertex vv
    assert (forall (k: nat). k >= vtail_start /\ k < vtail ==>
      SZ.v (Seq.index squeue_old k) < vv /\
      SZ.v (Seq.index squeue_old k) <> vv);
    assert (forall (k: nat). k >= vtail_start /\ k < vtail ==>
      Seq.index sin_deg_new (SZ.v (Seq.index squeue_old k)) ==
      Seq.index sin_deg_old (SZ.v (Seq.index squeue_old k)));
    reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_start sin_deg_new squeue_start squeue_new vtail_start (vtail + 1) n)

(* Unified step lemma: handles both enqueue and no-enqueue after maybe_enqueue *)
let pn_extra_inv_step
  (sin_deg_start sin_deg_old sin_deg_new: Seq.seq int)
  (squeue_start squeue_old squeue_new: Seq.seq SZ.t)
  (vtail_start vtail_old vtail_new: nat) (n: nat) (vv: nat)
  : Lemma
    (requires
      pn_extra_inv sin_deg_start sin_deg_old squeue_start squeue_old vtail_start vtail_old n /\
      vv < n /\
      vtail_new >= vtail_old /\
      vtail_new <= vtail_old + 1 /\
      vtail_new <= Seq.length squeue_new /\
      vtail_start <= Seq.length squeue_start /\
      Seq.length squeue_new == Seq.length squeue_old /\
      Seq.length sin_deg_old == n /\
      Seq.length sin_deg_new == n /\ Seq.length sin_deg_start == n /\
      (forall (k: nat). k < vtail_old ==> Seq.index squeue_new k == Seq.index squeue_old k) /\
      (forall (k: nat). k < n /\ k <> vv ==> Seq.index sin_deg_new k == Seq.index sin_deg_old k) /\
      (forall (k: nat). k >= vtail_start /\ k < vtail_old ==>
        SZ.v (Seq.index squeue_old k) < vv) /\
      // If enqueue: new entry at vtail_old is vv with proper conditions
      (vtail_new == vtail_old + 1 ==>
        (SZ.v (Seq.index squeue_new vtail_old) == vv /\
         Seq.index sin_deg_start vv > 0 /\
         Seq.index sin_deg_new vv == 0)))
    (ensures pn_extra_inv sin_deg_start sin_deg_new squeue_start squeue_new vtail_start vtail_new n)
  = if vtail_new = vtail_old then
      pn_extra_inv_no_enqueue sin_deg_start sin_deg_old sin_deg_new
        squeue_start squeue_old squeue_new vtail_start vtail_old n vv
    else (
      pn_extra_inv_enqueue sin_deg_start sin_deg_old sin_deg_new
        squeue_start squeue_old squeue_new vtail_start vtail_old n vv
    )

(* Opaque predicate: queue entries in [vtail_start, vtail_cur) have vertex < vv.
   This is needed as a precondition for pn_extra_inv_step. *)
let pn_entries_below_initial
  (squeue: Seq.seq SZ.t) (vtail_start: nat)
  : Lemma
    (requires vtail_start <= Seq.length squeue)
    (ensures pn_entries_below squeue vtail_start vtail_start 0)
  = reveal_opaque (`%pn_entries_below) (pn_entries_below squeue vtail_start vtail_start 0)

let pn_entries_below_step
  (squeue_old squeue_new: Seq.seq SZ.t)
  (vtail_start vtail_old vtail_new vv: nat)
  : Lemma
    (requires
      pn_entries_below squeue_old vtail_start vtail_old vv /\
      vtail_new >= vtail_old /\
      vtail_new <= vtail_old + 1 /\
      vtail_new <= Seq.length squeue_new /\
      Seq.length squeue_new == Seq.length squeue_old /\
      (forall (k:nat). k < vtail_old ==> Seq.index squeue_new k == Seq.index squeue_old k) /\
      (vtail_new == vtail_old + 1 ==> SZ.v (Seq.index squeue_new vtail_old) == vv))
    (ensures pn_entries_below squeue_new vtail_start vtail_new (vv + 1))
  = reveal_opaque (`%pn_entries_below) (pn_entries_below squeue_old vtail_start vtail_old vv);
    reveal_opaque (`%pn_entries_below) (pn_entries_below squeue_new vtail_start vtail_new (vv + 1))

(* Eliminate pn_entries_below to get the raw forall *)
let pn_entries_below_elim
  (squeue: Seq.seq SZ.t) (vtail_start vtail_cur vv: nat)
  : Lemma
    (requires pn_entries_below squeue vtail_start vtail_cur vv)
    (ensures
      vtail_start <= vtail_cur /\
      vtail_cur <= Seq.length squeue /\
      (forall (k:nat). k >= vtail_start /\ k < vtail_cur ==> SZ.v (Seq.index squeue k) < vv))
  = reveal_opaque (`%pn_entries_below) (pn_entries_below squeue vtail_start vtail_cur vv)

(* Combined step lemma: does inner_indeg_step + pn_entries_below_step + pn_extra_inv_step
   in one F* lemma. This avoids Pulse VC elaboration issues with multiple lemma calls. *)
let pn_combined_step
  (adj: Seq.seq int) (n: nat)
  (sin_degree sin_deg_cur sin_deg_new: Seq.seq int)
  (squeue_start squeue_cur squeue_new: Seq.seq SZ.t)
  (vtail_start vtail_cur vtail_new: nat) (u vv: nat)
  : Lemma
    (requires
      inner_indeg_partial adj n sin_degree sin_deg_cur u vv /\
      pn_extra_inv sin_degree sin_deg_cur squeue_start squeue_cur vtail_start vtail_cur n /\
      pn_entries_below squeue_cur vtail_start vtail_cur vv /\
      vv < n /\ u < n /\
      vtail_new >= vtail_cur /\ vtail_new <= vtail_cur + 1 /\ vtail_new <= n /\
      Seq.length adj == n * n /\
      Seq.length sin_deg_cur == n /\ Seq.length sin_deg_new == n /\ Seq.length sin_degree == n /\
      Seq.length squeue_cur == n /\ Seq.length squeue_new == n /\
      vtail_start <= Seq.length squeue_start /\
      // Queue frame
      (forall (k:nat). k < vtail_cur ==> Seq.index squeue_new k == Seq.index squeue_cur k) /\
      // Indeg frame
      (forall (k:nat). {:pattern (Seq.index sin_deg_new k)}
        k < n /\ k <> vv ==> Seq.index sin_deg_new k == Seq.index sin_deg_cur k) /\
      // Indeg at vv
      Seq.index sin_deg_new vv ==
        Seq.index sin_deg_cur vv -
          (if u * n + vv < n * n && Seq.index adj (u * n + vv) <> 0 then 1 else 0) /\
      // Enqueue info
      (vtail_new == vtail_cur + 1 ==>
        (SZ.v (Seq.index squeue_new vtail_cur) == vv /\
         Seq.index sin_deg_new vv == 0 /\
         Seq.index sin_deg_cur vv > 0)))
    (ensures
      inner_indeg_partial adj n sin_degree sin_deg_new u (vv + 1) /\
      pn_extra_inv sin_degree sin_deg_new squeue_start squeue_new vtail_start vtail_new n /\
      pn_entries_below squeue_new vtail_start vtail_new (vv + 1))
  = inner_indeg_step adj n sin_degree sin_deg_cur sin_deg_new u vv;
    pn_entries_below_step squeue_cur squeue_new vtail_start vtail_cur vtail_new vv;
    pn_entries_below_elim squeue_cur vtail_start vtail_cur vv;
    // sin_deg_cur[vv] == sin_degree[vv] from inner_indeg_partial (vv not yet processed)
    assert (Seq.index sin_deg_cur vv == Seq.index sin_degree vv);
    // If enqueue: sin_deg_new[vv] == 0 means sin_deg_cur[vv] == 1, so sin_degree[vv] > 0
    pn_extra_inv_step sin_degree sin_deg_cur sin_deg_new
      squeue_start squeue_cur squeue_new
      vtail_start vtail_cur vtail_new n vv

(* ================================================================
   BRIDGE LEMMAS: Derive queue properties from pn_extra_inv
   After process_neighbors, we have pn_extra_inv for new entries [vqt, vtail_post)
   and existing queue properties for old entries [qh+1, vqt).
   These lemmas combine them into properties for the full range [qh+1, vtail_post).
   ================================================================ *)

(* Extraction lemmas: reveal pn_extra_inv in isolation to get specific facts.
   This avoids flooding the SMT context with all pn_extra_inv quantifiers. *)

let lemma_pn_extract_old_preserved
  (sin_deg_pre sin_deg_post: Seq.seq int) (squeue_pre squeue_post: Seq.seq SZ.t)
  (vqt vtail_post: nat) (n: nat) (qi: nat)
  : Lemma
    (requires pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
              qi < vqt /\ vqt <= Seq.length squeue_post /\ vqt <= Seq.length squeue_pre)
    (ensures Seq.index squeue_post qi == Seq.index squeue_pre qi)
  = reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n)

(* Forall version: old entries preserved — reveal_opaque gives us the forall directly *)
let lemma_pn_extract_old_forall
  (sin_deg_pre sin_deg_post: Seq.seq int) (squeue_pre squeue_post: Seq.seq SZ.t)
  (vqt vtail_post qh: nat) (n: nat)
  : Lemma
    (requires pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
              qh <= vqt /\ vqt <= Seq.length squeue_post /\ vqt <= Seq.length squeue_pre)
    (ensures forall (qi: nat). {:pattern (Seq.index squeue_post qi)}
      qh <= qi /\ qi < vqt ==> Seq.index squeue_post qi == Seq.index squeue_pre qi)
  = reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n)

let lemma_pn_extract_new_entry
  (sin_deg_pre sin_deg_post: Seq.seq int) (squeue_pre squeue_post: Seq.seq SZ.t)
  (vqt vtail_post: nat) (n: nat) (qi: nat)
  : Lemma
    (requires pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
              qi >= vqt /\ qi < vtail_post /\ vtail_post <= Seq.length squeue_post /\
              Seq.length sin_deg_pre == n /\ Seq.length sin_deg_post == n)
    (ensures (let v = SZ.v (Seq.index squeue_post qi) in
              v < n /\ Seq.index sin_deg_pre v > 0 /\ Seq.index sin_deg_post v == 0))
  = reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n)

(* Forall version: new entries properties — reveal_opaque gives the forall directly *)
let lemma_pn_extract_new_forall
  (sin_deg_pre sin_deg_post: Seq.seq int) (squeue_pre squeue_post: Seq.seq SZ.t)
  (vqt vtail_post: nat) (n: nat)
  : Lemma
    (requires pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
              vtail_post <= Seq.length squeue_post /\
              Seq.length sin_deg_pre == n /\ Seq.length sin_deg_post == n)
    (ensures forall (qi: nat). {:pattern (Seq.index squeue_post qi)}
      vqt <= qi /\ qi < vtail_post ==>
        (let v = SZ.v (Seq.index squeue_post qi) in
         v < n /\ Seq.index sin_deg_pre v > 0 /\ Seq.index sin_deg_post v == 0))
  = reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n)

let lemma_pn_extract_new_distinct
  (sin_deg_pre sin_deg_post: Seq.seq int) (squeue_pre squeue_post: Seq.seq SZ.t)
  (vqt vtail_post: nat) (n: nat) (i j: nat)
  : Lemma
    (requires pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
              i >= vqt /\ i < vtail_post /\ j >= vqt /\ j < vtail_post /\ i <> j /\
              vtail_post <= Seq.length squeue_post)
    (ensures SZ.v (Seq.index squeue_post i) <> SZ.v (Seq.index squeue_post j))
  = reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n)

(* Forall version: new entries pairwise distinct — reveal_opaque gives the forall directly *)
let lemma_pn_extract_new_distinct_forall
  (sin_deg_pre sin_deg_post: Seq.seq int) (squeue_pre squeue_post: Seq.seq SZ.t)
  (vqt vtail_post: nat) (n: nat)
  : Lemma
    (requires pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
              vtail_post <= Seq.length squeue_post)
    (ensures forall (i j: nat). {:pattern (Seq.index squeue_post i); (Seq.index squeue_post j)}
      i >= vqt /\ i < vtail_post /\ j >= vqt /\ j < vtail_post /\ i <> j ==>
        SZ.v (Seq.index squeue_post i) <> SZ.v (Seq.index squeue_post j))
  = reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n)

(* Combined bridge: derive all three queue properties from pn_extra_inv.
   Uses reveal_opaque + forall-lifted lemmas — no nested forall_intro with Seq.index.
   Key insight: nested functions with Seq.index in ensures fail well-formedness checks
   when the enclosing context has quantifiers. Solution: reveal_opaque gives us the
   quantified facts directly, and forall-lifted lemmas chain the reasoning. *)

(* Transfer-and-extend for queue_fresh: old entries via preservation, new entries via provided forall *)
let lemma_queue_fresh_transfer_and_extend
  (output: Seq.seq int) (count: nat)
  (queue_old queue_new: Seq.seq SZ.t) (qh qt_old qt_new: nat)
  : Lemma
    (requires
      queue_fresh output count queue_old qh qt_old /\
      qt_old <= qt_new /\ qt_new <= Seq.length queue_new /\
      (forall (qi: nat). {:pattern (Seq.index queue_new qi)}
        qh <= qi /\ qi < qt_old ==> Seq.index queue_new qi == Seq.index queue_old qi) /\
      (forall (qi: nat). {:pattern (Seq.index queue_new qi)}
        qt_old <= qi /\ qi < qt_new ==>
          (forall (k: nat). {:pattern (Seq.index output k)}
            k < count ==> Seq.index output k <> SZ.v (Seq.index queue_new qi))))
    (ensures queue_fresh output count queue_new qh qt_new)
  = ()

(* Transfer-and-extend for queue_distinct: old-old via preservation, new-new + old-new provided *)
let lemma_queue_distinct_transfer_and_extend
  (queue_old queue_new: Seq.seq SZ.t) (qh qt_old qt_new: nat)
  : Lemma
    (requires
      queue_distinct_sz queue_old qh qt_old /\
      qt_old <= qt_new /\ qt_new <= Seq.length queue_new /\
      // Old entries preserved
      (forall (qi: nat). {:pattern (Seq.index queue_new qi)}
        qh <= qi /\ qi < qt_old ==> Seq.index queue_new qi == Seq.index queue_old qi) /\
      // New entries pairwise distinct
      (forall (i j: nat). {:pattern (Seq.index queue_new i); (Seq.index queue_new j)}
        i >= qt_old /\ i < qt_new /\ j >= qt_old /\ j < qt_new /\ i <> j ==>
          SZ.v (Seq.index queue_new i) <> SZ.v (Seq.index queue_new j)) /\
      // Old-new cross distinct
      (forall (i j: nat). {:pattern (Seq.index queue_new i); (Seq.index queue_new j)}
        i >= qh /\ i < qt_old /\ j >= qt_old /\ j < qt_new ==>
          SZ.v (Seq.index queue_new i) <> SZ.v (Seq.index queue_new j)))
    (ensures queue_distinct_sz queue_new qh qt_new)
  = ()

(* Prove old-new cross distinct from indeg facts:
   old entries have indeg 0, new entries have indeg > 0 → different vertices.
   NOTE: bounds must precede foralls for Seq.index well-formedness *)
#push-options "--z3rlimit 50"
let lemma_old_new_cross_distinct
  (sin_deg: Seq.seq int)
  (queue_old queue_new: Seq.seq SZ.t)
  (qh qt_old qt_new n: nat)
  : Lemma
    (requires
      qt_old <= qt_new /\
      qt_old <= Seq.length queue_old /\
      qt_new <= Seq.length queue_new /\
      Seq.length sin_deg == n /\
      // Old entries preserved
      (forall (qi: nat). {:pattern (Seq.index queue_new qi)}
        qh <= qi /\ qi < qt_old ==> Seq.index queue_new qi == Seq.index queue_old qi) /\
      // Old entries have indeg 0
      (forall (qi: nat). {:pattern (Seq.index queue_old qi)}
        qh <= qi /\ qi < qt_old ==>
          SZ.v (Seq.index queue_old qi) < n /\
          Seq.index sin_deg (SZ.v (Seq.index queue_old qi)) == 0) /\
      // New entries have indeg > 0
      (forall (qi: nat). {:pattern (Seq.index queue_new qi)}
        qt_old <= qi /\ qi < qt_new ==>
          SZ.v (Seq.index queue_new qi) < n /\
          Seq.index sin_deg (SZ.v (Seq.index queue_new qi)) > 0))
    (ensures
      forall (i j: nat). {:pattern (Seq.index queue_new i); (Seq.index queue_new j)}
        i >= qh /\ i < qt_old /\ j >= qt_old /\ j < qt_new ==>
          SZ.v (Seq.index queue_new i) <> SZ.v (Seq.index queue_new j))
  = ()
#pop-options

(* Bridge new entries from output_pre to output_post via Seq.upd.
   Key: combines pn_extract_new (sin_deg > 0) + positive_indeg_implies_fresh (fresh against output_pre)
   + Seq.upd (output_post differs only at vout) + sin_deg[u]=0 vs sin_deg[v]>0 (u <> v)
   NOTE: bounds must precede foralls for Seq.index well-formedness *)
#push-options "--z3rlimit 50"
let lemma_new_entries_fresh_after_upd
  (sin_deg: Seq.seq int) (queue: Seq.seq SZ.t)
  (output_old output_new: Seq.seq int)
  (qt_old qt_new vout u n: nat)
  : Lemma
    (requires
      qt_new <= Seq.length queue /\
      Seq.length sin_deg == n /\
      (vout + 1) <= Seq.length output_new /\
      vout <= Seq.length output_old /\
      u < n /\
      Seq.index sin_deg u == 0 /\
      Seq.index output_new vout == u /\
      (forall (k: nat). {:pattern (Seq.index output_new k)}
        k < vout ==> Seq.index output_new k == Seq.index output_old k) /\
      (forall (qi: nat). {:pattern (Seq.index queue qi)}
        qt_old <= qi /\ qi < qt_new ==>
          SZ.v (Seq.index queue qi) < n /\
          Seq.index sin_deg (SZ.v (Seq.index queue qi)) > 0) /\
      (forall (v: nat). {:pattern (Seq.index sin_deg v)}
        v < n /\ Seq.index sin_deg v > 0 ==>
          (forall (k: nat). {:pattern (Seq.index output_old k)}
            k < vout ==> Seq.index output_old k <> v)))
    (ensures
      forall (qi: nat). {:pattern (Seq.index queue qi)}
        qt_old <= qi /\ qi < qt_new ==>
          (forall (k: nat). {:pattern (Seq.index output_new k)}
            k < (vout + 1) ==> Seq.index output_new k <> SZ.v (Seq.index queue qi)))
  = ()
#pop-options

(* Sub-lemma 1: queue_preds — reveal_opaque + zero_indeg_preds_exist_forall *)
#push-options "--z3rlimit 50"
let lemma_bridge_preds
  (adj: Seq.seq int) (n: nat)
  (sin_deg_pre sin_deg_post: Seq.seq int)
  (squeue_pre squeue_post: Seq.seq SZ.t)
  (soutput_post: Seq.seq int)
  (qh_plus_1 vqt vtail_post vout: nat)
  : Lemma
    (requires
      queue_preds_in_output_sz adj n squeue_pre qh_plus_1 vqt soutput_post (vout + 1) /\
      pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
      indeg_correct adj n sin_deg_post soutput_post (vout + 1) /\
      qh_plus_1 <= vqt /\ vqt <= vtail_post /\
      vtail_post <= Seq.length squeue_post /\
      vqt <= Seq.length squeue_pre /\
      Seq.length sin_deg_pre == n /\ Seq.length sin_deg_post == n /\
      Seq.length adj == n * n /\
      (vout + 1) <= Seq.length soutput_post)
    (ensures
      queue_preds_in_output_sz adj n squeue_post qh_plus_1 vtail_post soutput_post (vout + 1))
  = // Reveal pn_extra_inv → gives old-preserved + new-entry foralls
    reveal_opaque (`%pn_extra_inv) (pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n);
    // For new entries: indeg 0 → all preds in output
    lemma_zero_indeg_preds_exist_forall adj n sin_deg_post soutput_post (vout + 1);
    // SMT chains: old entries transfer from squeue_pre, new entries from indeg
    lemma_queue_preds_transfer_and_extend adj n squeue_pre squeue_post qh_plus_1 vqt vtail_post
      soutput_post (vout + 1)
#pop-options

(* Sub-lemma 2: queue_fresh — chain extraction + combined fresh + Seq.upd bridge + transfer *)
#push-options "--z3rlimit 100"
let lemma_bridge_fresh
  (adj: Seq.seq int) (n: nat)
  (sin_deg_pre sin_deg_post: Seq.seq int)
  (squeue_pre squeue_post: Seq.seq SZ.t)
  (soutput_pre soutput_post: Seq.seq int)
  (qh_plus_1 vqt vtail_post vout: nat) (u: nat)
  : Lemma
    (requires
      queue_fresh soutput_post (vout + 1) squeue_pre qh_plus_1 vqt /\
      pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
      indeg_correct adj n sin_deg_pre soutput_pre vout /\
      strong_order_inv adj n soutput_pre vout /\
      partial_valid soutput_pre vout n /\
      u < n /\ vout < Seq.length soutput_pre /\
      soutput_post == Seq.upd soutput_pre vout u /\
      Seq.index sin_deg_pre u == 0 /\
      qh_plus_1 <= vqt /\ vqt <= vtail_post /\
      vtail_post <= Seq.length squeue_post /\
      vqt <= Seq.length squeue_pre /\
      Seq.length sin_deg_pre == n /\ Seq.length sin_deg_post == n /\
      (vout + 1) <= Seq.length soutput_post /\
      Seq.length soutput_post == Seq.length soutput_pre /\
      Seq.length adj == n * n)
    (ensures
      queue_fresh soutput_post (vout + 1) squeue_post qh_plus_1 vtail_post)
  = // Step 1: old entries preserved in squeue_post
    lemma_pn_extract_old_forall sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post qh_plus_1 n;
    // Step 2: new entries have sin_deg_pre > 0
    lemma_pn_extract_new_forall sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n;
    // Step 3: positive in_deg → fresh against soutput_pre (combined, no chaining needed)
    lemma_positive_indeg_implies_fresh_forall adj n sin_deg_pre soutput_pre vout;
    // Step 4: bridge new entries from output_pre to output_post via Seq.upd
    lemma_new_entries_fresh_after_upd sin_deg_pre squeue_post soutput_pre soutput_post
      vqt vtail_post vout u n;
    // Step 5: transfer_and_extend combines old (from precondition) + new (from step 4)
    lemma_queue_fresh_transfer_and_extend soutput_post (vout + 1) squeue_pre squeue_post
      qh_plus_1 vqt vtail_post
#pop-options

(* Sub-lemma 3: queue_distinct — extraction foralls + zero_indeg_forall + cross_distinct + transfer *)
#push-options "--z3rlimit 100"
let lemma_bridge_distinct
  (adj: Seq.seq int) (n: nat)
  (sin_deg_pre sin_deg_post: Seq.seq int)
  (squeue_pre squeue_post: Seq.seq SZ.t)
  (soutput_pre: Seq.seq int)
  (qh_plus_1 vqt vtail_post vout: nat)
  : Lemma
    (requires
      queue_distinct_sz squeue_pre qh_plus_1 vqt /\
      pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
      queue_preds_in_output_sz adj n squeue_pre qh_plus_1 vqt soutput_pre vout /\
      indeg_correct adj n sin_deg_pre soutput_pre vout /\
      qh_plus_1 <= vqt /\ vqt <= vtail_post /\
      vtail_post <= Seq.length squeue_post /\
      vqt <= Seq.length squeue_pre /\
      Seq.length sin_deg_pre == n /\ Seq.length sin_deg_post == n /\
      Seq.length adj == n * n)
    (ensures
      queue_distinct_sz squeue_post qh_plus_1 vtail_post)
  = // Step 1: old entries preserved
    lemma_pn_extract_old_forall sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post qh_plus_1 n;
    // Step 2: new entries pairwise distinct
    lemma_pn_extract_new_distinct_forall sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n;
    // Step 3: new entries have sin_deg_pre > 0
    lemma_pn_extract_new_forall sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n;
    // Step 4: old entries have sin_deg_pre == 0
    lemma_queue_entry_zero_indeg_forall adj n sin_deg_pre squeue_pre soutput_pre vout qh_plus_1 vqt;
    // Step 5: old-new cross distinct (old has indeg 0, new has indeg > 0)
    lemma_old_new_cross_distinct sin_deg_pre squeue_pre squeue_post qh_plus_1 vqt vtail_post n;
    // Step 6: transfer_and_extend combines old-old, new-new, old-new
    lemma_queue_distinct_transfer_and_extend squeue_pre squeue_post qh_plus_1 vqt vtail_post
#pop-options

(* Combined bridge: calls all three sub-lemmas *)
let lemma_bridge_queue_through_pn
  (adj: Seq.seq int) (n: nat)
  (sin_deg_pre sin_deg_post: Seq.seq int)
  (squeue_pre squeue_post: Seq.seq SZ.t)
  (soutput_pre soutput_post: Seq.seq int)
  (qh_plus_1 vqt vtail_post vout: nat) (u: nat)
  : Lemma
    (requires
      queue_preds_in_output_sz adj n squeue_pre qh_plus_1 vqt soutput_post (vout + 1) /\
      queue_fresh soutput_post (vout + 1) squeue_pre qh_plus_1 vqt /\
      queue_distinct_sz squeue_pre qh_plus_1 vqt /\
      pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
      indeg_correct adj n sin_deg_pre soutput_pre vout /\
      indeg_correct adj n sin_deg_post soutput_post (vout + 1) /\
      strong_order_inv adj n soutput_pre vout /\
      partial_valid soutput_pre vout n /\
      u < n /\ vout < Seq.length soutput_pre /\
      soutput_post == Seq.upd soutput_pre vout u /\
      Seq.length sin_deg_pre == n /\
      Seq.length sin_deg_post == n /\
      Seq.index sin_deg_pre u == 0 /\
      queue_preds_in_output_sz adj n squeue_pre qh_plus_1 vqt soutput_pre vout /\
      qh_plus_1 <= vqt /\ vqt <= vtail_post /\
      vtail_post <= Seq.length squeue_post /\
      Seq.length squeue_post == Seq.length squeue_pre /\
      vqt <= Seq.length squeue_pre /\
      (vout + 1) <= Seq.length soutput_post /\
      Seq.length soutput_post == Seq.length soutput_pre /\
      Seq.length adj == n * n /\
      Seq.length sin_deg_pre == n /\
      Seq.length sin_deg_post == n)
    (ensures
      queue_preds_in_output_sz adj n squeue_post qh_plus_1 vtail_post soutput_post (vout + 1) /\
      queue_fresh soutput_post (vout + 1) squeue_post qh_plus_1 vtail_post /\
      queue_distinct_sz squeue_post qh_plus_1 vtail_post)
  = lemma_bridge_preds adj n sin_deg_pre sin_deg_post squeue_pre squeue_post soutput_post
      qh_plus_1 vqt vtail_post vout;
    lemma_bridge_fresh adj n sin_deg_pre sin_deg_post squeue_pre squeue_post soutput_pre soutput_post
      qh_plus_1 vqt vtail_post vout u;
    lemma_bridge_distinct adj n sin_deg_pre sin_deg_post squeue_pre squeue_post soutput_pre
      qh_plus_1 vqt vtail_post vout

(* ================================================================
   DAG COMPLETENESS — Proves count == n when all zero-indeg are in output
   ================================================================ *)

(* is_in_output implies count_occurrences >= 1 *)
let rec lemma_is_in_output_implies_count (output: Seq.seq int) (count: nat) (x: int)
  : Lemma
    (requires count <= Seq.length output /\ is_in_output output count x)
    (ensures count_occurrences output count x >= 1)
    (decreases count)
  = if count = 0 then ()
    else if Seq.index output (count - 1) = x then ()
    else lemma_is_in_output_implies_count output (count - 1) x

(* Pigeonhole for find_missing_vertex: if all n vertices are in output[0..count)
   with count < n and output is partial_distinct, contradiction. *)
let lemma_pigeonhole_missing (output: Seq.seq int) (count n: nat)
  : Lemma
    (requires
      count < n /\ n > 0 /\ Seq.length output >= count /\
      partial_distinct output count /\ partial_valid output count n /\
      (forall (v: nat). v < n ==> is_in_output output count v))
    (ensures False)
  = let aux (v: nat) : Lemma (requires v < n) (ensures count_occurrences output count v >= 1) =
      lemma_is_in_output_implies_count output count v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    lemma_pigeonhole_count_occurrences output count n

(* Find vertex not in output, given count < n *)
let rec find_missing_vertex
  (output: Seq.seq int) (count n: nat) (v: nat)
  : Pure nat
    (requires
      v <= n /\ count < n /\ Seq.length output >= count /\ n > 0 /\
      partial_distinct output count /\ partial_valid output count n /\
      (forall (u: nat). u < v /\ u < n ==> is_in_output output count u))
    (ensures fun u -> u < n /\ not (is_in_output output count u))
    (decreases (n - v))
  = if v >= n then begin
      lemma_pigeonhole_missing output count n;
      0 (* unreachable - lemma proves False *)
    end
    else if is_in_output output count v then
      find_missing_vertex output count n (v + 1)
    else v

(* Main DAG completeness lemma *)
let lemma_dag_completeness
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int) (count: nat)
  : Lemma
    (requires
      n > 0 /\ count <= n /\ Seq.length output == n /\ Seq.length adj == n * n /\
      Seq.length in_deg >= n /\
      ~(has_cycle adj n) /\
      indeg_correct adj n in_deg output count /\
      partial_distinct output count /\
      partial_valid output count n /\
      strong_order_inv adj n output count /\
      (forall (v: nat). v < n /\ Seq.index in_deg v == 0 ==> is_in_output output count v))
    (ensures count >= n)
  = if count >= n then ()
    else begin
      let aux (w: nat)
        : Lemma (requires w < n /\ not (is_in_output output count w))
                (ensures count_remaining_preds adj n output count w n > 0)
        = ()
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      let v0 = find_missing_vertex output count n 0 in
      lemma_non_output_implies_cycle adj n output count v0;
      ()
    end

(* ================================================================
   ZERO_INDEG_ACCOUNTED — Loop invariant for DAG completeness
   Every vertex with in_deg == 0 is either in output or in the active queue.
   ================================================================ *)

(* Check if v is in queue[qh..qt) *)
let zero_indeg_accounted_elim
  (in_deg: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat)
  (queue: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires zero_indeg_accounted in_deg n output count queue qh qt)
    (ensures
      Seq.length in_deg >= n /\ count <= Seq.length output /\
      qh <= qt /\ qt <= Seq.length queue /\
      (forall (v: nat). v < n /\ Seq.index in_deg v == 0 ==>
        is_in_output output count v \/ is_in_queue_sz queue qh qt v))
  = reveal_opaque (`%zero_indeg_accounted) (zero_indeg_accounted in_deg n output count queue qh qt)

let zero_indeg_accounted_intro
  (in_deg: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat)
  (queue: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires
      Seq.length in_deg >= n /\ count <= Seq.length output /\
      qh <= qt /\ qt <= Seq.length queue /\
      (forall (v: nat). v < n /\ Seq.index in_deg v == 0 ==>
        is_in_output output count v \/ is_in_queue_sz queue qh qt v))
    (ensures zero_indeg_accounted in_deg n output count queue qh qt)
  = reveal_opaque (`%zero_indeg_accounted) (zero_indeg_accounted in_deg n output count queue qh qt)

(* At exit (qh == qt): zero_indeg_accounted → all zero-indeg in output *)
let zero_indeg_accounted_at_exit
  (in_deg: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat)
  (queue: Seq.seq SZ.t) (qh: nat)
  : Lemma
    (requires zero_indeg_accounted in_deg n output count queue qh qh)
    (ensures
      Seq.length in_deg >= n /\
      (forall (v: nat). v < n /\ Seq.index in_deg v == 0 ==> is_in_output output count v))
  = reveal_opaque (`%zero_indeg_accounted) (zero_indeg_accounted in_deg n output count queue qh qh)

(* is_in_queue after dequeue: if v was in [qh, qt) and v != queue[qh], then v in [qh+1, qt) *)
let rec lemma_is_in_queue_dequeue
  (queue: Seq.seq SZ.t) (qh qt: nat) (v: nat)
  : Lemma
    (requires qh < qt /\ qt <= Seq.length queue /\ is_in_queue_sz queue qh qt v /\ SZ.v (Seq.index queue qh) <> v)
    (ensures is_in_queue_sz queue (qh + 1) qt v)
    (decreases (qt - qh))
  = if qh >= qt then ()
    else if SZ.v (Seq.index queue qh) = v then ()
    else ()

(* is_in_queue monotone in range: [qh, qt) ⊂ [qh, qt') for qt' >= qt *)
let rec lemma_is_in_queue_extend
  (queue: Seq.seq SZ.t) (qh qt qt': nat) (v: nat)
  : Lemma
    (requires qh <= qt /\ qt <= qt' /\ qt' <= Seq.length queue /\ is_in_queue_sz queue qh qt v)
    (ensures is_in_queue_sz queue qh qt' v)
    (decreases (qt - qh))
  = if qh >= qt then ()
    else if SZ.v (Seq.index queue qh) = v then ()
    else lemma_is_in_queue_extend queue (qh + 1) qt qt' v

(* is_in_output monotone in count *)
let rec lemma_is_in_output_monotone_local
  (output: Seq.seq int) (c1 c2: nat) (v: int)
  : Lemma
    (requires c1 <= c2 /\ c2 <= Seq.length output /\ is_in_output output c1 v)
    (ensures is_in_output output c2 v)
    (decreases c2)
  = if c1 = c2 then ()
    else if Seq.index output (c2 - 1) = v then ()
    else lemma_is_in_output_monotone_local output c1 (c2 - 1) v

(* is_in_queue preserved when old entries are preserved *)
let rec lemma_is_in_queue_preserved
  (queue_old queue_new: Seq.seq SZ.t) (qh qt: nat) (v: nat)
  : Lemma
    (requires is_in_queue_sz queue_old qh qt v /\ qh <= qt /\ qt <= Seq.length queue_old /\
      qt <= Seq.length queue_new /\
      (forall (k: nat). k >= qh /\ k < qt ==> Seq.index queue_new k == Seq.index queue_old k))
    (ensures is_in_queue_sz queue_new qh qt v)
    (decreases (qt - qh))
  = if qh >= qt then ()
    else if SZ.v (Seq.index queue_old qh) = v then ()
    else lemma_is_in_queue_preserved queue_old queue_new (qh + 1) qt v

(* After enqueue at position qt: is_in_queue for the new entry *)
let lemma_is_in_queue_enqueue
  (queue: Seq.seq SZ.t) (qh qt: nat) (v: nat)
  : Lemma
    (requires qh <= qt /\ qt < Seq.length queue /\ SZ.v (Seq.index queue qt) == v)
    (ensures is_in_queue_sz queue qh (qt + 1) v)
  = if qh >= qt + 1 then ()
    else if SZ.v (Seq.index queue qh) = v then ()
    else begin
      // v is at position qt, which is in [qh, qt+1)
      let rec aux (p: nat)
        : Lemma (requires p <= qt /\ p >= qh)
                (ensures is_in_queue_sz queue p (qt + 1) v)
                (decreases (qt + 1 - p))
        = if p >= qt + 1 then ()
          else if SZ.v (Seq.index queue p) = v then ()
          else aux (p + 1)
      in
      aux qh
    end

(* is_in_queue monotone in start: shrinking qh expands the search range *)
let rec lemma_is_in_queue_weaken_start
  (queue: Seq.seq SZ.t) (qh qh' qt: nat) (v: nat)
  : Lemma
    (requires qh <= qh' /\ qh' <= qt /\ qt <= Seq.length queue /\ is_in_queue_sz queue qh' qt v)
    (ensures is_in_queue_sz queue qh qt v)
    (decreases (qh' - qh))
  = if qh >= qh' then ()
    else if SZ.v (Seq.index queue qh) = v then ()
    else lemma_is_in_queue_weaken_start queue (qh + 1) qh' qt v

(* Maintenance of zero_indeg_accounted after dequeue + output extend + process_neighbors.
   Key argument:
   - Vertices with in_deg_post == 0 that had in_deg_pre == 0: still in output or queue (preserved)
   - Vertices with in_deg_post == 0 that had in_deg_pre > 0: newly enqueued by process_neighbors
   Uses pn_extra_inv to identify newly enqueued vertices. *)
let lemma_zero_indeg_accounted_after_pn
  (adj: Seq.seq int) (n: nat)
  (in_deg_pre in_deg_post: Seq.seq int) (output_post: Seq.seq int) (count_post: nat)
  (queue_pre queue_post: Seq.seq SZ.t) (qh_post vqt vtail_post: nat)
  : Lemma
    (requires
      // Previous zero_indeg_accounted (after dequeue + output extend, before pn)
      zero_indeg_accounted in_deg_pre n output_post count_post queue_pre qh_post vqt /\
      // pn_extra_inv: old entries preserved, new entries characterized
      pn_extra_inv in_deg_pre in_deg_post queue_pre queue_post vqt vtail_post n /\
      // pn completeness: every v whose in_deg dropped from nonzero to 0 was enqueued
      (forall (v: nat). v < n /\ Seq.index in_deg_pre v <> 0 /\ Seq.index in_deg_post v == 0 ==>
        is_in_queue_sz queue_post vqt vtail_post v) /\
      // Bounds
      qh_post <= vqt /\ vqt <= vtail_post /\ vtail_post <= Seq.length queue_post /\
      vqt <= Seq.length queue_pre /\
      Seq.length in_deg_pre == n /\ Seq.length in_deg_post == n /\
      count_post <= Seq.length output_post)
    (ensures
      zero_indeg_accounted in_deg_post n output_post count_post queue_post qh_post vtail_post)
  = reveal_opaque (`%zero_indeg_accounted) (zero_indeg_accounted in_deg_pre n output_post count_post queue_pre qh_post vqt);
    reveal_opaque (`%pn_extra_inv) (pn_extra_inv in_deg_pre in_deg_post queue_pre queue_post vqt vtail_post n);
    // For each v < n with in_deg_post[v] == 0:
    let aux (v: nat)
      : Lemma (requires v < n /\ Seq.index in_deg_post v == 0)
              (ensures is_in_output output_post count_post v \/ is_in_queue_sz queue_post qh_post vtail_post v)
      = if Seq.index in_deg_pre v = 0 then begin
          // Case A: in_deg was already 0 → v in output or queue_pre[qh_post, vqt)
          assert (is_in_output output_post count_post v \/ is_in_queue_sz queue_pre qh_post vqt v);
          if is_in_output output_post count_post v then ()
          else begin
            // v in queue_pre[qh_post, vqt) → v in queue_post[qh_post, vqt) (old entries preserved)
            lemma_is_in_queue_preserved queue_pre queue_post qh_post vqt v;
            // queue_post[qh_post, vqt) ⊂ queue_post[qh_post, vtail_post)
            lemma_is_in_queue_extend queue_post qh_post vqt vtail_post v
          end
        end
        else begin
          // Case B: in_deg_pre[v] <> 0, in_deg_post[v] == 0 → newly enqueued
          // pn_completeness gives: v is in queue_post[vqt, vtail_post)
          assert (is_in_queue_sz queue_post vqt vtail_post v);
          // Expand search range: [vqt, vtail_post) ⊂ [qh_post, vtail_post) since qh_post <= vqt
          lemma_is_in_queue_weaken_start queue_post qh_post vqt vtail_post v
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    reveal_opaque (`%zero_indeg_accounted) (zero_indeg_accounted in_deg_post n output_post count_post queue_post qh_post vtail_post)


(* Combined lemma: after process_neighbors, re-establish kahn_outer_inv.
   Combines inner_indeg_complete + indeg_transition + bridge_queue_through_pn + kahn_outer_inv_intro.
   This avoids generating a single huge VC in the Pulse loop body. *)
#push-options "--z3rlimit 400"
let lemma_post_process_neighbors
  (adj: Seq.seq int) (n: nat)
  (sin_deg_pre sin_deg_post: Seq.seq int)
  (squeue_pre squeue_post: Seq.seq SZ.t)
  (soutput_pre soutput_post: Seq.seq int)
  (vqh vqt vtail_post vout: nat) (u: nat)
  : Lemma
    (requires
      u < n /\ vout < n /\ vqh < vqt /\ vqt <= n /\
      Seq.length adj == n * n /\ SZ.fits (n * n) /\
      Seq.length sin_deg_pre == n /\ Seq.length sin_deg_post == n /\
      Seq.length squeue_pre == n /\ Seq.length squeue_post == n /\
      Seq.length soutput_pre == n /\ Seq.length soutput_post == n /\
      vout == vqh /\
      soutput_post == Seq.upd soutput_pre vout u /\
      u == SZ.v (Seq.index squeue_pre vqh) /\
      // kahn_outer_inv was revealed before dequeue
      indeg_correct adj n sin_deg_pre soutput_pre vout /\
      strong_order_inv adj n soutput_pre vout /\
      strong_order_inv adj n soutput_post (vout + 1) /\
      partial_distinct soutput_post (vout + 1) /\
      partial_valid soutput_pre vout n /\
      partial_valid soutput_post (vout + 1) n /\
      queue_preds_in_output_sz adj n squeue_pre (vqh + 1) vqt soutput_pre vout /\
      queue_preds_in_output_sz adj n squeue_pre (vqh + 1) vqt soutput_post (vout + 1) /\
      queue_fresh soutput_post (vout + 1) squeue_pre (vqh + 1) vqt /\
      queue_distinct_sz squeue_pre (vqh + 1) vqt /\
      Seq.index sin_deg_pre u == 0 /\
      not (is_in_output soutput_pre vout u) /\
      // process_neighbors postconditions
      inner_indeg_partial adj n sin_deg_pre sin_deg_post u n /\
      pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
      vtail_post >= vqt /\ vtail_post <= n /\
      queue_entries_valid squeue_post vtail_post n)
    (ensures
      kahn_outer_inv adj n sin_deg_post squeue_post soutput_post (vqh + 1) vtail_post (vout + 1))
  = inner_indeg_complete adj n sin_deg_pre sin_deg_post u;
    lemma_indeg_transition adj n sin_deg_pre sin_deg_post soutput_pre vout u;
    lemma_bridge_queue_through_pn adj n sin_deg_pre sin_deg_post squeue_pre squeue_post
      soutput_pre soutput_post (vqh + 1) vqt vtail_post vout u;
    kahn_outer_inv_intro adj n sin_deg_post squeue_post soutput_post
      (vqh + 1) vtail_post (vout + 1)
#pop-options
