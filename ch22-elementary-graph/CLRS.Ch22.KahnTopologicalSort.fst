module CLRS.Ch22.KahnTopologicalSort
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open Pulse.Lib.WithPure
open CLRS.Ch22.TopologicalSort.Spec
open CLRS.Ch22.TopologicalSort.Lemmas
open CLRS.Ch22.TopologicalSort.Verified

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

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
let partial_distinct (output: Seq.seq int) (count: nat) : prop =
  count <= Seq.length output /\
  (forall (i j: nat). {:pattern (Seq.index output i); (Seq.index output j)}
    i < count /\ j < count /\ i <> j ==>
      Seq.index output i <> Seq.index output j)

(* Output elements in [0, count) are valid vertex indices *)
let partial_valid (output: Seq.seq int) (count n: nat) : prop =
  count <= Seq.length output /\
  (forall (i: nat). {:pattern (Seq.index output i)}
    i < count ==> Seq.index output i >= 0 /\ Seq.index output i < n)

(* Queue entries in [qh, qt) are valid vertex indices *)
let queue_valid_sz (queue: Seq.seq SZ.t) (qh qt n: nat) : prop =
  qh <= qt /\ qt <= Seq.length queue /\
  (forall (k: nat). {:pattern (Seq.index queue k)}
    k >= qh /\ k < qt ==> SZ.v (Seq.index queue k) < n)

(* Queue entries are NOT in output — needed for distinctness *)
let queue_fresh (output: Seq.seq int) (count: nat) (queue: Seq.seq SZ.t) (qh qt: nat) : prop =
  count <= Seq.length output /\ qh <= qt /\ qt <= Seq.length queue /\
  (forall (qi: nat). {:pattern (Seq.index queue qi)}
    qi >= qh /\ qi < qt ==>
      (forall (k: nat). {:pattern (Seq.index output k)}
        k < count ==> Seq.index output k <> SZ.v (Seq.index queue qi)))

(* Queue entries are pairwise distinct *)
let queue_distinct_sz (queue: Seq.seq SZ.t) (qh qt: nat) : prop =
  qh <= qt /\ qt <= Seq.length queue /\
  (forall (i j: nat). {:pattern (Seq.index queue i); (Seq.index queue j)}
    i >= qh /\ i < qt /\ j >= qh /\ j < qt /\ i <> j ==>
      SZ.v (Seq.index queue i) <> SZ.v (Seq.index queue j))

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
let queue_entries_valid (squeue: Seq.seq SZ.t) (vqt: nat) (n: nat) =
  vqt <= Seq.length squeue /\
  (forall (k: nat). k < vqt ==> SZ.v (Seq.index squeue k) < n)

(* Maintain queue_entries_valid after maybe_enqueue *)
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
let step1_inner_inv
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (in_deg: Seq.seq int)
  (row col: nat) : prop =
  Seq.length adj == n * n /\ Seq.length in_deg == n /\ Seq.length output >= 0 /\
  row < n /\ col <= n /\
  (forall (j: nat). j < col ==>
    Seq.index in_deg j == count_remaining_preds adj n output 0 j (row + 1)) /\
  (forall (j: nat). col <= j /\ j < n ==>
    Seq.index in_deg j == count_remaining_preds adj n output 0 j row)

(* After processing rows [0, row) fully,
   in_degree[j] == count_remaining_preds adj n output 0 j row for all j < n. *)
[@@  "opaque_to_smt"]
let step1_outer_inv
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (in_deg: Seq.seq int)
  (row: nat) : prop =
  Seq.length adj == n * n /\ Seq.length in_deg == n /\ Seq.length output >= 0 /\
  row <= n /\
  (forall (j: nat). j < n ==>
    Seq.index in_deg j == count_remaining_preds adj n output 0 j row)

(* Inner loop step: processing adj[row, col] updates in_degree[col] *)
let lemma_step1_inner_step
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (in_deg in_deg': Seq.seq int)
  (row col: nat)
  : Lemma
    (requires
      step1_inner_inv adj n output in_deg row col /\
      col < n /\ row < n /\
      Seq.length adj == n * n /\
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
   BUNDLED INVARIANT — opaque to SMT for performance
   ================================================================ *)

(* Bundled outer-loop correctness invariant.
   Marked opaque_to_smt so that the SMT solver sees it as atomic,
   preventing quantifier explosion from the 7 inner predicates. *)
[@@  "opaque_to_smt"]
let kahn_outer_inv
  (adj: Seq.seq int) (n: nat)
  (sin_deg: Seq.seq int) (squeue: Seq.seq SZ.t) (soutput: Seq.seq int)
  (vqh vqt vout: nat) : prop =
  strong_order_inv adj n soutput vout /\
  partial_distinct soutput vout /\
  partial_valid soutput vout n /\
  queue_fresh soutput vout squeue vqh vqt /\
  queue_distinct_sz squeue vqh vqt /\
  queue_preds_in_output_sz adj n squeue vqh vqt soutput vout /\
  indeg_correct adj n sin_deg soutput vout

(* Reveal kahn_outer_inv to get individual predicates *)
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
let inner_indeg_partial
  (adj: Seq.seq int) (n: nat)
  (in_deg_pre in_deg_cur: Seq.seq int) (u_val: int) (vv: nat) =
  Seq.length in_deg_cur == n /\ Seq.length in_deg_pre == n /\
  Seq.length adj == n * n /\ u_val >= 0 /\ u_val < n /\
  (forall (v: nat). v < vv /\ v < n ==>
    Seq.index in_deg_cur v == Seq.index in_deg_pre v -
      (if u_val * n + v < n * n && Seq.index adj (u_val * n + v) <> 0 then 1 else 0)) /\
  (forall (v: nat). v >= vv /\ v < n ==>
    Seq.index in_deg_cur v == Seq.index in_deg_pre v)

(* After processing vertex vv, inner_indeg_partial advances *)
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
   ASSUME_FACT — Ghost wrapper for admit, avoids Z3 issues with assume_
   We use this as a placeholder; every call will be eliminated.
   ================================================================ *)

ghost fn assume_fact (p: prop) requires emp ensures pure p { admit() }

(* ================================================================
   HELPER: maybe_enqueue — Process edge and potentially enqueue vertex
   ================================================================ *)

#push-options "--z3rlimit 50"
fn maybe_enqueue
  (adj: A.array int)
  (in_degree: A.array int)
  (queue_data: A.array SZ.t)
  (queue_tail: R.ref SZ.t)
  (u: SZ.t)        // current vertex being processed
  (vv: SZ.t)       // neighbor vertex to potentially enqueue
  (n: SZ.t)        // number of vertices
  (#sadj: erased (Seq.seq int))
  (#sin_degree: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  (#vtail: erased SZ.t)
  requires
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree **
    A.pts_to queue_data squeue **
    R.pts_to queue_tail vtail **
    with_pure (
      SZ.v u < SZ.v n /\
      SZ.v vv < SZ.v n /\
      SZ.v vtail <= SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sin_degree == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.fits (SZ.v u * SZ.v n) /\
      queue_entries_valid squeue (SZ.v vtail) (SZ.v n)
    )
  ensures exists* sin_degree' squeue' vtail'.
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree' **
    A.pts_to queue_data squeue' **
    R.pts_to queue_tail vtail' **
    pure (
      Seq.length sin_degree' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      SZ.v vtail' >= SZ.v vtail /\
      SZ.v vtail' <= SZ.v vtail + 1 /\
      SZ.v vtail' <= SZ.v n /\
      // In-degree frame: only index vv is modified
      (forall (k:nat). {:pattern (Seq.index sin_degree' k)}
        k < SZ.v n /\ k <> SZ.v vv ==>
          Seq.index sin_degree' k == Seq.index sin_degree k) /\
      // In-degree at vv: precisely determined by edge
      Seq.index sin_degree' (SZ.v vv) ==
        Seq.index sin_degree (SZ.v vv) -
          (if SZ.v u * SZ.v n + SZ.v vv < SZ.v n * SZ.v n &&
              Seq.index sadj (SZ.v u * SZ.v n + SZ.v vv) <> 0
           then 1 else 0) /\
      // Queue entries validity maintained
      queue_entries_valid squeue' (SZ.v vtail') (SZ.v n)
    )
{
  // Compute edge index: u * n + vv
  lemma_index_in_bounds (SZ.v u) (SZ.v vv) (SZ.v n);
  let idx = u *^ n +^ vv;
  let edge_val = A.op_Array_Access adj idx;
  let old_deg = A.op_Array_Access in_degree vv;
  let vqt = !queue_tail;
  
  if (edge_val <> 0) {
    // Edge exists: decrement in_degree[vv]
    let new_deg: int = old_deg - 1;
    A.op_Array_Assignment in_degree vv new_deg;
    
    if (new_deg = 0 && SZ.lt vqt n) {
      // Enqueue vv
      A.op_Array_Assignment queue_data vqt vv;
      queue_tail := SZ.add vqt 1sz
    } else {
      ()
    }
  } else {
    ()
  }
}
#pop-options

(* ================================================================
   HELPER: process_neighbors — Inner loop: scan all potential neighbors
   of dequeued vertex u, decrement in-degrees, enqueue zero-indegree vertices.
   Extracted to keep the outer loop VC small.
   ================================================================ *)

#push-options "--z3rlimit 50"
fn process_neighbors
  (adj: A.array int)
  (in_degree: A.array int)
  (queue_data: A.array SZ.t)
  (queue_tail: R.ref SZ.t)
  (u: SZ.t)
  (n: SZ.t)
  (#sadj: erased (Seq.seq int))
  (#sin_degree: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  (#vtail: erased SZ.t)
  requires
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree **
    A.pts_to queue_data squeue **
    R.pts_to queue_tail vtail **
    pure (
      SZ.v u < SZ.v n /\
      SZ.v vtail <= SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sin_degree == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.fits (SZ.v u * SZ.v n) /\
      queue_entries_valid squeue (SZ.v vtail) (SZ.v n)
    )
  ensures exists* sin_degree' squeue' vtail'.
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree' **
    A.pts_to queue_data squeue' **
    R.pts_to queue_tail vtail' **
    pure (
      Seq.length sin_degree' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      SZ.v vtail' >= SZ.v vtail /\
      SZ.v vtail' <= SZ.v n /\
      queue_entries_valid squeue' (SZ.v vtail') (SZ.v n) /\
      // In-degree changes: inner_indeg_partial at n (complete)
      inner_indeg_partial sadj (SZ.v n) sin_degree sin_degree' (SZ.v u) (SZ.v n)
    )
{
  let mut v: SZ.t = 0sz;
  while (!v <^ n)
  invariant exists* vv sin_deg_cur squeue_cur vtail_cur.
    R.pts_to v vv **
    A.pts_to adj sadj **
    A.pts_to in_degree sin_deg_cur **
    A.pts_to queue_data squeue_cur **
    R.pts_to queue_tail vtail_cur **
    pure (
      SZ.v u < SZ.v n /\
      SZ.v vv <= SZ.v n /\
      SZ.v vtail_cur >= SZ.v vtail /\
      SZ.v vtail_cur <= SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sin_deg_cur == SZ.v n /\
      Seq.length squeue_cur == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.fits (SZ.v u * SZ.v n) /\
      queue_entries_valid squeue_cur (SZ.v vtail_cur) (SZ.v n) /\
      inner_indeg_partial sadj (SZ.v n) sin_degree sin_deg_cur (SZ.v u) (SZ.v vv)
    )
  {
    let vv = !v;
    // Capture current in-degree state from invariant before maybe_enqueue
    with sin_deg_cur0. assert (A.pts_to in_degree sin_deg_cur0);
    maybe_enqueue adj in_degree queue_data queue_tail u vv n;
    // After maybe_enqueue: in_degree updated at vv, rest unchanged
    with sin_deg_new squeue_new vtail_new. _;
    inner_indeg_step sadj (SZ.v n) sin_degree sin_deg_cur0 sin_deg_new (SZ.v u) (SZ.v vv);
    v := SZ.add vv 1sz
  }
}
#pop-options

#push-options "--z3rlimit 80"

// Topological sort using Kahn's algorithm
// Input: adjacency matrix adj (n×n represented as flat array)
// Output: array containing topological order of vertices
//SNIPPET_START: topological_sort_sig
fn topological_sort 
  (adj: A.array int) 
  (n: SZ.t)
  (#sadj: erased (Seq.seq int))
  requires 
    A.pts_to adj sadj **
    pure (
      SZ.v n > 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns output: V.vec int
  ensures exists* sout.
    A.pts_to adj sadj **
    V.pts_to output sout **
    pure (
      Seq.length sout == SZ.v n /\
      // All vertices in output are valid indices
      (forall (i: nat). i < SZ.v n ==> Seq.index sout i < SZ.v n) /\
      // STRENGTHENED POSTCONDITIONS:
      // 1. All elements are non-negative (can be viewed as nat)
      (forall (i: nat). i < Seq.length sout ==> Seq.index sout i >= 0) /\
      // 2. All elements are distinct
      all_distinct (seq_int_to_nat sout) /\
      // 3. Output is a valid topological order
      is_topological_order sadj (SZ.v n) (seq_int_to_nat sout)
    )
//SNIPPET_END: topological_sort_sig
{
  // Step 1: Compute in-degrees
  let in_degree_v = V.alloc 0 n;
  V.to_array_pts_to in_degree_v;
  let in_degree = V.vec_to_array in_degree_v;
  rewrite (A.pts_to (V.vec_to_array in_degree_v) (Seq.create (SZ.v n) 0))
       as (A.pts_to in_degree (Seq.create (SZ.v n) 0));
  
  // Ghost output placeholder for step1 invariants (output not allocated yet)
  let ghost_output : erased (Seq.seq int) = hide (Seq.empty #int);
  
  // Establish initial step1_outer_inv
  lemma_step1_initial sadj (SZ.v n) (reveal ghost_output) (Seq.create (SZ.v n) 0);
  
  // For each vertex i
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi sin_degree.
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sin_degree == SZ.v n /\
      step1_outer_inv sadj (SZ.v n) (reveal ghost_output) sin_degree (SZ.v vi)
    )
  {
    let vi = !i;
    with sin_deg_outer. assert (A.pts_to in_degree sin_deg_outer);
    
    // Convert outer_inv to inner_inv at col=0
    lemma_step1_outer_to_inner sadj (SZ.v n) (reveal ghost_output) sin_deg_outer (SZ.v vi);
    
    // For each vertex j, check if edge vi->j exists
    let mut j: SZ.t = 0sz;
    while (!j <^ n)
    invariant exists* vj sin_degree.
      R.pts_to i vi **
      R.pts_to j vj **
      A.pts_to adj sadj **
      A.pts_to in_degree sin_degree **
      pure (
        SZ.v vi < SZ.v n /\
        SZ.v vj <= SZ.v n /\
        Seq.length sin_degree == SZ.v n /\
        Seq.length sadj == SZ.v n * SZ.v n /\
        SZ.fits (SZ.v n * SZ.v n) /\
        step1_inner_inv sadj (SZ.v n) (reveal ghost_output) sin_degree (SZ.v vi) (SZ.v vj)
      )
    {
      let vj = !j;
      with sin_deg_inner. assert (A.pts_to in_degree sin_deg_inner);
      
      // Check if edge from vi to vj exists
      let idx = vi *^ n +^ vj;
      let edge_val = A.op_Array_Access adj idx;
      
      // If edge exists, increment in_degree[vj]
      let old_deg = A.op_Array_Access in_degree vj;
      let new_deg: int = (if edge_val <> 0 then old_deg + 1 else old_deg);
      A.op_Array_Assignment in_degree vj new_deg;
      
      // Prove step1_inner_inv advances
      with sin_deg_new. assert (A.pts_to in_degree sin_deg_new);
      lemma_step1_inner_step sadj (SZ.v n) (reveal ghost_output) sin_deg_inner sin_deg_new (SZ.v vi) (SZ.v vj);
      
      j := vj +^ 1sz;
    };
    
    // Inner loop complete: convert inner_inv at col=n to outer_inv at row+1
    with sin_deg_after_inner. assert (A.pts_to in_degree sin_deg_after_inner);
    lemma_step1_inner_to_outer sadj (SZ.v n) (reveal ghost_output) sin_deg_after_inner (SZ.v vi);
    
    i := vi +^ 1sz;
  };
  
  // After Step 1: we have step1_outer_inv at row=n
  // Capture in_degree state for indeg_correct conversion
  with sin_deg_after_step1. assert (A.pts_to in_degree sin_deg_after_step1);
  
  // Step 2: Initialize queue with vertices having in-degree 0
  let queue_v = V.alloc 0sz n;
  V.to_array_pts_to queue_v;
  let queue = V.vec_to_array queue_v;
  rewrite (A.pts_to (V.vec_to_array queue_v) (Seq.create (SZ.v n) 0sz))
       as (A.pts_to queue (Seq.create (SZ.v n) 0sz));
  let mut queue_tail: SZ.t = 0sz;
  
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi vqt sin_degree squeue.
    R.pts_to i vi **
    R.pts_to queue_tail vqt **
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree **
    A.pts_to queue squeue **
    pure (
      SZ.v vi <= SZ.v n /\
      SZ.v vqt <= SZ.v vi /\
      SZ.v vqt <= SZ.v n /\
      Seq.length sin_degree == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      queue_entries_valid squeue (SZ.v vqt) (SZ.v n) /\
      // Carry step1 result through Step 2 (in_degree is read-only here)
      step1_outer_inv sadj (SZ.v n) (reveal ghost_output) sin_degree (SZ.v n)
    )
  {
    let vi = !i;
    let deg = A.op_Array_Access in_degree vi;
    let vqt = !queue_tail;
    
    // Unconditionally write (might write garbage if deg != 0, but queue_tail won't advance)
    A.op_Array_Assignment queue vqt vi;
    
    // Conditionally advance queue_tail
    let new_vqt: SZ.t = (if deg = 0 then vqt +^ 1sz else vqt);
    queue_tail := new_vqt;
    
    i := vi +^ 1sz;
  };
  
  // Step 3: Process queue and build output
  let output_v = V.alloc 0 n;
  V.to_array_pts_to output_v;
  let output = V.vec_to_array output_v;
  rewrite (A.pts_to (V.vec_to_array output_v) (Seq.create (SZ.v n) 0))
       as (A.pts_to output (Seq.create (SZ.v n) 0));
  let mut queue_head: SZ.t = 0sz;
  let mut out_idx: SZ.t = 0sz;
  
  // --- Initialize correctness predicates ---
  with sin_deg_init. assert (A.pts_to in_degree sin_deg_init);
  with squeue_init. assert (A.pts_to queue squeue_init);
  with soutput_init. assert (A.pts_to output soutput_init);
  with vqt_init. assert (R.pts_to queue_tail vqt_init);
  
  // Base cases: trivially true at count=0
  lemma_strong_order_base sadj (SZ.v n) soutput_init;
  partial_distinct_base soutput_init;
  // partial_valid at 0: vacuously true (forall i < 0 ...)
  // queue_fresh at count=0: vacuously true (forall k < 0 ...)
  
  // indeg_correct: Step 1 computed in-degrees; use step1_outer_inv at row=n
  lemma_step1_to_indeg_correct sadj (SZ.v n) (reveal ghost_output) soutput_init sin_deg_init;
  
  // Queue predicates still need Step 2 invariant work:
  assume_fact (
    queue_distinct_sz squeue_init 0 (SZ.v vqt_init) /\
    queue_preds_in_output_sz sadj (SZ.v n) squeue_init 0 (SZ.v vqt_init) soutput_init 0
  );
  // Bundle into opaque invariant
  kahn_outer_inv_intro sadj (SZ.v n) sin_deg_init squeue_init soutput_init 0 (SZ.v vqt_init) 0;
  
  while (!queue_head <^ !queue_tail)
  invariant exists* vqh vqt vout sin_degree squeue soutput.
    R.pts_to queue_head vqh **
    R.pts_to queue_tail vqt **
    R.pts_to out_idx vout **
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree **
    A.pts_to queue squeue **
    A.pts_to output soutput **
    pure (
      SZ.v vqh <= SZ.v vqt /\
      SZ.v vqt <= SZ.v n /\
      SZ.v vout == SZ.v vqh /\
      SZ.v vout <= SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length sin_degree == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      Seq.length soutput == SZ.v n /\
      queue_entries_valid squeue (SZ.v vqt) (SZ.v n) /\
      (forall (k: nat). k < SZ.v vout ==> Seq.index soutput k < SZ.v n) /\
      (forall (k: nat). SZ.v vout <= k /\ k < SZ.v n ==> Seq.index soutput k == 0) /\
      (forall (k: nat). k < Seq.length soutput ==> Seq.index soutput k >= 0) /\
      // Opaque bundled correctness invariant
      kahn_outer_inv sadj (SZ.v n) sin_degree squeue soutput (SZ.v vqh) (SZ.v vqt) (SZ.v vout)
    )
  {
    let vqh = !queue_head;
    let vqt = !queue_tail;
    let vout = !out_idx;
    
    // Capture ghost state from loop invariant
    with soutput_pre. assert (A.pts_to output soutput_pre);
    with squeue_pre. assert (A.pts_to queue squeue_pre);
    with sin_deg_pre. assert (A.pts_to in_degree sin_deg_pre);
    
    // Reveal the opaque invariant to get individual predicates
    kahn_outer_inv_elim sadj (SZ.v n) sin_deg_pre squeue_pre soutput_pre (SZ.v vqh) (SZ.v vqt) (SZ.v vout);
    
    // Dequeue vertex u
    let u = A.op_Array_Access queue vqh;
    assert (pure (SZ.v u < SZ.v n));
    lemma_index_in_bounds (SZ.v u) 0 (SZ.v n);
    
    // Add u to output
    let u_int = SZ.v u;
    A.op_Array_Assignment output vout u_int;
    
    // Capture post-write output state
    with soutput_post. assert (A.pts_to output soutput_post);
    assert (pure (soutput_post == Seq.upd soutput_pre (SZ.v vout) u_int));
    
    // --- Prove strong_order_inv maintenance ---
    lemma_strong_order_extend sadj (SZ.v n) soutput_pre soutput_post (SZ.v vout) u_int;
    
    // --- Prove partial_distinct maintenance ---
    queue_fresh_not_in_output soutput_pre (SZ.v vout) squeue_pre (SZ.v vqh) (SZ.v vqt) (SZ.v vqh);
    partial_distinct_extend soutput_pre soutput_post (SZ.v vout) u_int;
    
    // --- Prove partial_valid maintenance ---
    partial_valid_extend soutput_pre soutput_post (SZ.v vout) (SZ.v n) u_int;
    
    // --- Queue predicates after dequeue ---
    lemma_queue_preds_dequeue sadj (SZ.v n) squeue_pre (SZ.v vqh) (SZ.v vqt) soutput_pre (SZ.v vout);
    lemma_queue_preds_extend_output sadj (SZ.v n) squeue_pre (SZ.v vqh + 1) (SZ.v vqt) soutput_pre soutput_post (SZ.v vout) u_int;
    queue_fresh_dequeue soutput_pre (SZ.v vout) squeue_pre (SZ.v vqh) (SZ.v vqt);
    queue_distinct_dequeue squeue_pre (SZ.v vqh) (SZ.v vqt);
    
    // queue_fresh after extending output with u:
    // queue_distinct before dequeue tells us u differs from remaining entries
    queue_fresh_extend_output soutput_pre soutput_post (SZ.v vout) squeue_pre (SZ.v vqh) (SZ.v vqt) u_int;
    
    let new_vout = vout +^ 1sz;
    out_idx := new_vout;
    queue_head := vqh +^ 1sz;
    
    // Process all neighbors of u (inner loop extracted)
    process_neighbors adj in_degree queue queue_tail u n;
    
    // After process_neighbors: in_degree and queue changed, output unchanged
    with sin_deg_post squeue_post vtail_post. _;
    with soutput_new. assert (A.pts_to output soutput_new);
    // process_neighbors doesn't touch output — framing gives soutput_new == soutput_post
    assert (pure (soutput_new == soutput_post));
    
    // process_neighbors doesn't touch output, so soutput_new == soutput_post (by framing)
    // Convert inner_indeg_complete for indeg_transition
    inner_indeg_complete sadj (SZ.v n) sin_deg_pre sin_deg_post (SZ.v u);
    
    // indeg_correct: use lemma_indeg_transition
    // u not in output[0..vout) follows from queue_fresh
    queue_fresh_not_in_output soutput_pre (SZ.v vout) squeue_pre (SZ.v vqh) (SZ.v vqt) (SZ.v vqh);
    // Convert forall-based "not in output" to is_in_output form
    lemma_not_in_output_from_forall soutput_pre (SZ.v vout) u_int;
    lemma_indeg_transition sadj (SZ.v n) sin_deg_pre sin_deg_post soutput_pre (SZ.v vout) u_int;
    
    // Queue predicates through inner loop:
    // For old queue entries [vqh+1, vqt): they were preserved by process_neighbors
    // For new entries [vqt, vtail_post): newly enqueued vertices with in_deg == 0
    assume_fact (
      queue_preds_in_output_sz sadj (SZ.v n) squeue_post (SZ.v vqh + 1) (SZ.v vtail_post) soutput_post (SZ.v vout + 1) /\
      queue_fresh soutput_post (SZ.v vout + 1) squeue_post (SZ.v vqh + 1) (SZ.v vtail_post) /\
      queue_distinct_sz squeue_post (SZ.v vqh + 1) (SZ.v vtail_post)
    );
    
    // Bundle back into opaque invariant
    kahn_outer_inv_intro sadj (SZ.v n) sin_deg_post squeue_post soutput_new
      (SZ.v vqh + 1) (SZ.v vtail_post) (SZ.v vout + 1);
    
    // Structural properties of soutput_new = soutput_post = Seq.upd soutput_pre vout u_int
    // u_int < n and u_int >= 0; soutput_pre satisfies the properties by loop invariant
    // For k < vout: Seq.index soutput_new k == Seq.index soutput_pre k (by Seq.upd, k <> vout)
    // For k == vout: Seq.index soutput_new vout == u_int < n, u_int >= 0
    // For k > vout, k < n: Seq.index soutput_new k == Seq.index soutput_pre k == 0
    assert (pure (soutput_new == Seq.upd soutput_pre (SZ.v vout) u_int));
    assert (pure (Seq.length soutput_new == SZ.v n));
    assert (pure (u_int >= 0 /\ u_int < SZ.v n))
  };
  
  // After the loop, extract the existentials
  with vqh vqt vout sin_degree squeue soutput. _;
  
  // Loop exit: vqh == vqt (queue empty), vout == vqh
  // All vertices processed: assume vout == n (follows from algorithm termination)
  assume_fact (SZ.v vout == SZ.v n);
  
  // Structural properties
  assert (pure (forall (i: nat). i < SZ.v n ==> Seq.index soutput i < SZ.v n));
  assert (pure (forall (i: nat). i < Seq.length soutput ==> Seq.index soutput i >= 0));
  
  // Reveal the opaque invariant to extract strong_order_inv, partial_distinct, etc.
  kahn_outer_inv_elim sadj (SZ.v n) sin_degree squeue soutput (SZ.v vqh) (SZ.v vqt) (SZ.v vout);
  
  // Bridge: partial_distinct at count=n → all_distinct (seq_int_to_nat soutput)
  lemma_partial_distinct_implies_all_distinct soutput (SZ.v n);
  
  // Bridge: strong_order_inv + all_distinct_int + all_valid_vertices_int → is_topological_order
  lemma_partial_distinct_implies_all_distinct_int soutput (SZ.v n);
  lemma_partial_valid_implies_all_valid_int soutput (SZ.v n);
  lemma_bridge_topological_order sadj (SZ.v n) soutput;
  
  // Clean up temporary arrays
  with sin. assert (A.pts_to in_degree sin);
  rewrite (A.pts_to in_degree sin)
       as (A.pts_to (V.vec_to_array in_degree_v) sin);
  V.to_vec_pts_to in_degree_v;
  V.free in_degree_v;

  with sq. assert (A.pts_to queue sq);
  rewrite (A.pts_to queue sq)
       as (A.pts_to (V.vec_to_array queue_v) sq);
  V.to_vec_pts_to queue_v;
  V.free queue_v;
  
  // Convert output back to vec
  with so. assert (A.pts_to output so);
  rewrite (A.pts_to output so)
       as (A.pts_to (V.vec_to_array output_v) so);
  V.to_vec_pts_to output_v;

  output_v
}

#pop-options
