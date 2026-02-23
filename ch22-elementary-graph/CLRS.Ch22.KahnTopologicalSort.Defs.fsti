module CLRS.Ch22.KahnTopologicalSort.Defs
open FStar.SizeT
open FStar.Mul
open CLRS.Ch22.TopologicalSort.Spec
open CLRS.Ch22.TopologicalSort.Lemmas
open CLRS.Ch22.TopologicalSort.Verified

module SZ = FStar.SizeT
module Seq = FStar.Seq

#set-options "--z3rlimit 100"

// Helper lemma: if u < n, v < n, and n*n fits, then u*n+v < n*n and fits
val lemma_index_in_bounds (u v n: nat)
  : Lemma
    (requires u < n /\ v < n /\ n > 0 /\ SZ.fits (n * n))
    (ensures u * n + v < n * n /\ SZ.fits (u * n) /\ SZ.fits (u * n + v))

val seq_int_to_nat (s: Seq.seq int)
  : Pure (Seq.seq nat)
    (requires forall (i: nat). i < Seq.length s ==> Seq.index s i >= 0)
    (ensures fun r -> Seq.length r == Seq.length s /\
                      (forall (i: nat). i < Seq.length s ==> Seq.index r i == Seq.index s i))

(* ================================================================
   PREDICATES — Named abstractions for Kahn's algorithm invariants
   ================================================================ *)

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

(* Step 2 invariant: queue entries are all < vi and have in_degree 0 *)

let rec is_in_queue_sz (queue: Seq.seq SZ.t) (qh qt: nat) (v: nat) : Tot bool (decreases (qt - qh)) =
  if qh >= qt then false
  else if qh >= Seq.length queue then false
  else if SZ.v (Seq.index queue qh) = v then true
  else is_in_queue_sz queue (qh + 1) qt v

(* zero_indeg_accounted: every vertex with in_deg == 0 is in output or active queue *)
let zero_indeg_accounted
  (in_deg: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat)
  (queue: Seq.seq SZ.t) (qh qt: nat) : prop =
  Seq.length in_deg >= n /\ count <= Seq.length output /\ qh <= qt /\ qt <= Seq.length queue /\
  (forall (v: nat). {:pattern (Seq.index in_deg v)}
    v < n /\ Seq.index in_deg v == 0 ==>
      is_in_output output count v \/ is_in_queue_sz queue qh qt v)

let step2_queue_inv
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue: Seq.seq SZ.t) (vqt vi: nat) : prop =
  vqt <= vi /\ vi <= n /\
  vqt <= Seq.length queue /\
  Seq.length in_deg == n /\
  queue_distinct_sz queue 0 vqt /\
  // All entries are < vi (since we only enqueue vertices we've scanned)
  (forall (k: nat). {:pattern (Seq.index queue k)} k < vqt ==> SZ.v (Seq.index queue k) < vi) /\
  // All entries have in_degree 0
  (forall (k: nat). {:pattern (Seq.index queue k)} k < vqt ==> Seq.index in_deg (SZ.v (Seq.index queue k)) == 0) /\
  // Completeness: every zero-indeg vertex scanned so far is in the queue
  (forall (v: nat). v < vi /\ Seq.index in_deg v == 0 ==> is_in_queue_sz queue 0 vqt v)


(* ================================================================
   PREDICATE LEMMAS
   ================================================================ *)

val partial_distinct_base (output: Seq.seq int)
  : Lemma (requires Seq.length output >= 0)
          (ensures partial_distinct output 0)

val partial_distinct_extend
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

val partial_valid_extend
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

val queue_fresh_dequeue
  (output: Seq.seq int) (count: nat) (queue: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires queue_fresh output count queue qh qt /\ qh < qt)
    (ensures queue_fresh output count queue (qh + 1) qt)

#push-options "--z3rlimit 40"
val queue_fresh_extend_output
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

#pop-options

val queue_fresh_enqueue
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

val queue_fresh_no_enqueue
  (output: Seq.seq int) (count: nat)
  (queue_old queue_new: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires
      queue_fresh output count queue_old qh qt /\
      Seq.length queue_new == Seq.length queue_old /\
      (forall (qi: nat). qi >= qh /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi))
    (ensures queue_fresh output count queue_new qh qt)

val queue_distinct_enqueue
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

val queue_distinct_no_enqueue
  (queue_old queue_new: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires
      queue_distinct_sz queue_old qh qt /\
      Seq.length queue_new == Seq.length queue_old /\
      (forall (qi: nat). qi >= qh /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi))
    (ensures queue_distinct_sz queue_new qh qt)

val queue_distinct_dequeue
  (queue: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires queue_distinct_sz queue qh qt /\ qh < qt)
    (ensures queue_distinct_sz queue (qh + 1) qt)

val queue_valid_enqueue
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

val queue_valid_no_enqueue
  (queue_old queue_new: Seq.seq SZ.t) (qh qt n: nat)
  : Lemma
    (requires
      queue_valid_sz queue_old qh qt n /\
      Seq.length queue_new == Seq.length queue_old /\
      (forall (qi: nat). qi >= qh /\ qi < qt ==> Seq.index queue_new qi == Seq.index queue_old qi))
    (ensures queue_valid_sz queue_new qh qt n)

val queue_fresh_not_in_output
  (output: Seq.seq int) (count: nat) (queue: Seq.seq SZ.t) (qh qt: nat) (qi: nat)
  : Lemma
    (requires queue_fresh output count queue qh qt /\ qi >= qh /\ qi < qt)
    (ensures forall (k: nat). k < count ==> Seq.index output k <> SZ.v (Seq.index queue qi))

let queue_entries_valid (squeue: Seq.seq SZ.t) (vqt: nat) (n: nat) =
  vqt <= Seq.length squeue /\
  (forall (k: nat). k < vqt ==> SZ.v (Seq.index squeue k) < n)

(* Maintain queue_entries_valid after maybe_enqueue *)

val queue_entries_valid_after_enqueue
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

(* ================================================================
   INITIALIZATION INVARIANTS — for Step 1 (compute in-degrees)
   ================================================================ *)

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

let step1_outer_inv
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (in_deg: Seq.seq int)
  (row: nat) : prop =
  Seq.length adj == n * n /\ Seq.length in_deg == n /\ Seq.length output >= 0 /\
  row <= n /\
  (forall (j: nat). j < n ==>
    Seq.index in_deg j == count_remaining_preds adj n output 0 j row)

(* Inner loop step: processing adj[row, col] updates in_degree[col] *)

val lemma_step1_inner_step
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

val lemma_step1_outer_to_inner
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (in_deg: Seq.seq int)
  (row: nat)
  : Lemma
    (requires step1_outer_inv adj n output in_deg row /\ row < n)
    (ensures step1_inner_inv adj n output in_deg row 0)

val lemma_step1_inner_to_outer
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (in_deg: Seq.seq int)
  (row: nat)
  : Lemma
    (requires step1_inner_inv adj n output in_deg row n)
    (ensures step1_outer_inv adj n output in_deg (row + 1))

val lemma_step1_initial
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (in_deg: Seq.seq int)
  : Lemma
    (requires
      n > 0 /\
      Seq.length adj == n * n /\ Seq.length in_deg == n /\ Seq.length output >= 0 /\
      (forall (j: nat). j < n ==> Seq.index in_deg j == 0))
    (ensures step1_outer_inv adj n output in_deg 0)

val lemma_step1_to_indeg_correct
  (adj: Seq.seq int) (n: nat) (ghost_out real_out: Seq.seq int) (in_deg: Seq.seq int)
  : Lemma
    (requires step1_outer_inv adj n ghost_out in_deg n /\ n > 0 /\
              Seq.length real_out >= n)
    (ensures indeg_correct adj n in_deg real_out 0)

(* ================================================================
   STEP 2 LEMMAS — Queue initialization invariant maintenance
   ================================================================ *)

val lemma_step2_initial
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue: Seq.seq SZ.t)
  : Lemma
    (requires n > 0 /\ Seq.length in_deg == n /\ Seq.length queue == n)
    (ensures step2_queue_inv adj n in_deg output queue 0 0)

val lemma_step2_enqueue
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

val lemma_step2_skip
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue queue': Seq.seq SZ.t) (vqt vi: nat)
  : Lemma
    (requires step2_queue_inv adj n in_deg output queue vqt vi /\ vi < n /\
              Seq.index in_deg vi <> 0 /\
              Seq.length queue' == Seq.length queue /\
              vqt <= Seq.length queue' /\
              (forall (k: nat). {:pattern (Seq.index queue' k)} k < vqt ==> Seq.index queue' k == Seq.index queue k))
    (ensures step2_queue_inv adj n in_deg output queue' vqt (vi + 1))

val lemma_step2_step
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

val lemma_step2_to_queue_distinct
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue: Seq.seq SZ.t) (vqt: nat)
  : Lemma
    (requires step2_queue_inv adj n in_deg output queue vqt n)
    (ensures queue_distinct_sz queue 0 vqt)

val lemma_step2_to_entries_valid
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue: Seq.seq SZ.t) (vqt: nat)
  : Lemma
    (requires step2_queue_inv adj n in_deg output queue vqt n)
    (ensures queue_entries_valid queue vqt n)

val lemma_step2_to_queue_preds
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (step2_out real_out: Seq.seq int)
  (queue: Seq.seq SZ.t) (vqt: nat)
  : Lemma
    (requires
      step2_queue_inv adj n in_deg step2_out queue vqt n /\
      indeg_correct adj n in_deg real_out 0 /\
      n > 0 /\ Seq.length real_out >= n)
    (ensures queue_preds_in_output_sz adj n queue 0 vqt real_out 0)

(* All queue entries [0..qt) have zero in-degree under sin_deg *)
let queue_entries_zero_indeg
  (sin_deg: Seq.seq int) (squeue: Seq.seq SZ.t) (qt: nat) : prop =
  qt <= Seq.length squeue /\
  Seq.length sin_deg > 0 /\
  (forall (k: nat). k < qt ==>
    SZ.v (Seq.index squeue k) < Seq.length sin_deg /\
    Seq.index sin_deg (SZ.v (Seq.index squeue k)) == 0)

val lemma_step2_to_queue_entries_zero_indeg
  (adj: Seq.seq int) (n: nat) (in_deg: Seq.seq int) (output: Seq.seq int)
  (queue: Seq.seq SZ.t) (vqt: nat)
  : Lemma
    (requires step2_queue_inv adj n in_deg output queue vqt n /\ n > 0)
    (ensures queue_entries_zero_indeg in_deg queue vqt)

val lemma_step2_to_zero_indeg_accounted
  (in_deg: Seq.seq int) (n: nat) (output: Seq.seq int)
  (queue: Seq.seq SZ.t) (vqt: nat)
  : Lemma
    (requires
      Seq.length in_deg == n /\ n > 0 /\
      Seq.length output >= n /\
      vqt <= Seq.length queue /\
      (forall (v: nat). v < n /\ Seq.index in_deg v == 0 ==> is_in_queue_sz queue 0 vqt v))
    (ensures zero_indeg_accounted in_deg n output 0 queue 0 vqt)

(* ================================================================
   BUNDLED INVARIANT — opaque to SMT for performance
   ================================================================ *)

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

val kahn_outer_inv_elim
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

val kahn_outer_inv_intro
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

(* ================================================================
   BRIDGE LEMMAS — Connect loop invariant predicates to postcondition
   ================================================================ *)

val lemma_partial_distinct_implies_all_distinct
  (soutput: Seq.seq int) (n: nat)
  : Lemma
    (requires
      partial_distinct soutput n /\
      Seq.length soutput == n /\
      (forall (i: nat). i < n ==> Seq.index soutput i >= 0))
    (ensures all_distinct (seq_int_to_nat soutput))

val lemma_bridge_topological_order
  (adj: Seq.seq int) (n: nat) (soutput: Seq.seq int)
  : Lemma
    (requires
      n > 0 /\ Seq.length soutput == n /\ Seq.length adj == n * n /\
      strong_order_inv adj n soutput n /\
      all_distinct_int soutput /\
      all_valid_vertices_int soutput n /\
      (forall (i: nat). i < n ==> Seq.index soutput i >= 0))
    (ensures is_topological_order adj n (seq_int_to_nat soutput))

val lemma_partial_distinct_implies_all_distinct_int
  (soutput: Seq.seq int) (n: nat)
  : Lemma
    (requires partial_distinct soutput n /\ Seq.length soutput == n)
    (ensures all_distinct_int soutput)

val lemma_partial_valid_implies_all_valid_int
  (soutput: Seq.seq int) (n: nat)
  : Lemma
    (requires partial_valid soutput n n /\ Seq.length soutput == n)
    (ensures all_valid_vertices_int soutput n)

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

val inner_indeg_step
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

val inner_indeg_complete
  (adj: Seq.seq int) (n: nat)
  (in_deg_pre in_deg_final: Seq.seq int) (u_val: int)
  : Lemma
    (requires inner_indeg_partial adj n in_deg_pre in_deg_final u_val n)
    (ensures
      forall (v: nat). v < n ==>
        Seq.index in_deg_final v == Seq.index in_deg_pre v -
          (if u_val * n + v < n * n && Seq.index adj (u_val * n + v) <> 0 then 1 else 0))

(* ================================================================
   PROCESS_NEIGHBORS EXTRA INVARIANT — tracks queue predicates
   ================================================================ *)

let pn_extra_inv
  (sin_deg_start sin_deg_cur: Seq.seq int)
  (squeue_start squeue_cur: Seq.seq SZ.t)
  (vtail_start vtail_cur: nat) (n: nat) : prop =
  vtail_start <= vtail_cur /\
  vtail_cur <= Seq.length squeue_cur /\
  vtail_start <= Seq.length squeue_start /\
  Seq.length sin_deg_start == n /\
  Seq.length sin_deg_cur == n /\
  // Old entries preserved
  (forall (k: nat). {:pattern (Seq.index squeue_cur k)}
    k < vtail_start ==> Seq.index squeue_cur k == Seq.index squeue_start k) /\
  // New entries: vertex < n, had positive in_deg before, have in_deg 0 now
  (forall (k: nat). {:pattern (Seq.index squeue_cur k)}
    k >= vtail_start /\ k < vtail_cur ==>
      (let v = SZ.v (Seq.index squeue_cur k) in
       v < n /\
       Seq.index sin_deg_start v > 0 /\
       Seq.index sin_deg_cur v == 0)) /\
  // New entries pairwise distinct
  (forall (i j: nat). {:pattern (Seq.index squeue_cur i); (Seq.index squeue_cur j)}
    i >= vtail_start /\ i < vtail_cur /\ j >= vtail_start /\ j < vtail_cur /\ i <> j ==>
      SZ.v (Seq.index squeue_cur i) <> SZ.v (Seq.index squeue_cur j))

(* Initial: empty range, trivially true *)

val pn_extra_inv_initial
  (sin_deg_start: Seq.seq int) (squeue_start: Seq.seq SZ.t) (vtail_start: nat) (n: nat)
  : Lemma
    (requires vtail_start <= Seq.length squeue_start /\ Seq.length sin_deg_start == n)
    (ensures pn_extra_inv sin_deg_start sin_deg_start squeue_start squeue_start vtail_start vtail_start n)

val pn_extra_inv_no_enqueue
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

val pn_extra_inv_enqueue
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

val pn_extra_inv_step
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

let pn_entries_below
  (squeue: Seq.seq SZ.t) (vtail_start vtail_cur vv: nat) : prop =
  vtail_start <= vtail_cur /\
  vtail_cur <= Seq.length squeue /\
  (forall (k:nat). {:pattern (Seq.index squeue k)}
    k >= vtail_start /\ k < vtail_cur ==> SZ.v (Seq.index squeue k) < vv)


val pn_entries_below_initial
  (squeue: Seq.seq SZ.t) (vtail_start: nat)
  : Lemma
    (requires vtail_start <= Seq.length squeue)
    (ensures pn_entries_below squeue vtail_start vtail_start 0)

val pn_entries_below_step
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

val pn_entries_below_elim
  (squeue: Seq.seq SZ.t) (vtail_start vtail_cur vv: nat)
  : Lemma
    (requires pn_entries_below squeue vtail_start vtail_cur vv)
    (ensures
      vtail_start <= vtail_cur /\
      vtail_cur <= Seq.length squeue /\
      (forall (k:nat). k >= vtail_start /\ k < vtail_cur ==> SZ.v (Seq.index squeue k) < vv))

(* pn_enqueue_complete: every vertex < vv whose in_deg dropped from nonzero to 0 is enqueued *)
let pn_enqueue_complete
  (sin_deg_start sin_deg_cur: Seq.seq int)
  (squeue_cur: Seq.seq SZ.t)
  (vtail_start vtail_cur: nat) (n vv: nat) : prop =
  vv <= n /\
  vtail_start <= vtail_cur /\ vtail_cur <= Seq.length squeue_cur /\
  Seq.length sin_deg_start == n /\ Seq.length sin_deg_cur == n /\
  (forall (v: nat). v < vv /\ v < n /\ Seq.index sin_deg_start v <> 0 /\ Seq.index sin_deg_cur v == 0 ==>
    (exists (k: nat). k >= vtail_start /\ k < vtail_cur /\ SZ.v (Seq.index squeue_cur k) == v))

val pn_enqueue_complete_initial
  (sin_deg_start: Seq.seq int) (squeue: Seq.seq SZ.t) (vtail_start: nat) (n: nat)
  : Lemma
    (requires vtail_start <= Seq.length squeue /\ Seq.length sin_deg_start == n)
    (ensures pn_enqueue_complete sin_deg_start sin_deg_start squeue vtail_start vtail_start n 0)

val pn_enqueue_complete_step
  (sin_deg_start sin_deg_cur sin_deg_new: Seq.seq int)
  (squeue_cur squeue_new: Seq.seq SZ.t)
  (vtail_start vtail_cur vtail_new: nat) (n vv: nat)
  : Lemma
    (requires
      pn_enqueue_complete sin_deg_start sin_deg_cur squeue_cur vtail_start vtail_cur n vv /\
      vv < n /\
      vtail_new >= vtail_cur /\ vtail_new <= vtail_cur + 1 /\
      vtail_new <= Seq.length squeue_new /\
      Seq.length squeue_new == Seq.length squeue_cur /\
      Seq.length sin_deg_new == n /\ Seq.length sin_deg_start == n /\
      (forall (k: nat). k < vtail_cur ==> Seq.index squeue_new k == Seq.index squeue_cur k) /\
      (forall (k: nat). k < n /\ k <> vv ==> Seq.index sin_deg_new k == Seq.index sin_deg_cur k) /\
      // If enqueue: vv was enqueued at position vtail_cur
      (vtail_new == vtail_cur + 1 ==>
        (SZ.v (Seq.index squeue_new vtail_cur) == vv /\
         Seq.index sin_deg_start vv <> 0 /\
         Seq.index sin_deg_new vv == 0)) /\
      // Key fact from inner_indeg_partial: vv hasn't been processed yet
      Seq.index sin_deg_cur vv == Seq.index sin_deg_start vv /\
      // No-enqueue + nonzero start in_deg means in_deg didn't drop to 0
      (vtail_new == vtail_cur /\ Seq.index sin_deg_start vv <> 0 ==> Seq.index sin_deg_new vv <> 0))
    (ensures pn_enqueue_complete sin_deg_start sin_deg_new squeue_new vtail_start vtail_new n (vv + 1))

val lemma_vtail_lt_n (squeue: Seq.seq SZ.t) (vtail n vv: nat)
  : Lemma
    (requires vtail <= n /\ n <= Seq.length squeue /\ vv < n /\
      (forall (i j: nat). i < vtail /\ j < vtail /\ i <> j ==>
        SZ.v (Seq.index squeue i) <> SZ.v (Seq.index squeue j)) /\
      (forall (k:nat). k < vtail ==> SZ.v (Seq.index squeue k) < n) /\
      (forall (k:nat). k < vtail ==> SZ.v (Seq.index squeue k) <> vv))
    (ensures vtail < n)

val pn_combined_step
  (adj: Seq.seq int) (n: nat)
  (sin_degree sin_deg_cur sin_deg_new: Seq.seq int)
  (squeue_start squeue_cur squeue_new: Seq.seq SZ.t)
  (vtail_start vtail_cur vtail_new: nat) (u vv: nat)
  : Lemma
    (requires
      inner_indeg_partial adj n sin_degree sin_deg_cur u vv /\
      pn_extra_inv sin_degree sin_deg_cur squeue_start squeue_cur vtail_start vtail_cur n /\
      pn_entries_below squeue_cur vtail_start vtail_cur vv /\
      pn_enqueue_complete sin_degree sin_deg_cur squeue_cur vtail_start vtail_cur n vv /\
      queue_entries_zero_indeg sin_degree squeue_cur vtail_start /\
      queue_entries_valid squeue_cur vtail_cur n /\
      queue_distinct_sz squeue_cur 0 vtail_cur /\
      (forall (k:nat). k < n ==> Seq.index sin_degree k >= 0) /\
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
         Seq.index sin_deg_cur vv > 0)) /\
      // Converse: if in_deg dropped to 0 from positive and queue not full, enqueue happened
      (Seq.index sin_deg_new vv == 0 /\ Seq.index sin_deg_cur vv > 0 /\ vtail_cur < n ==>
        vtail_new == vtail_cur + 1))
    (ensures
      inner_indeg_partial adj n sin_degree sin_deg_new u (vv + 1) /\
      pn_extra_inv sin_degree sin_deg_new squeue_start squeue_new vtail_start vtail_new n /\
      pn_entries_below squeue_new vtail_start vtail_new (vv + 1) /\
      pn_enqueue_complete sin_degree sin_deg_new squeue_new vtail_start vtail_new n (vv + 1) /\
      queue_distinct_sz squeue_new 0 vtail_new)

(* ================================================================
   BRIDGE LEMMAS: Derive queue properties from pn_extra_inv
   After process_neighbors, we have pn_extra_inv for new entries [vqt, vtail_post)
   and existing queue properties for old entries [qh+1, vqt).
   These lemmas combine them into properties for the full range [qh+1, vtail_post).
   ================================================================ *)


val lemma_pn_extract_old_preserved
  (sin_deg_pre sin_deg_post: Seq.seq int) (squeue_pre squeue_post: Seq.seq SZ.t)
  (vqt vtail_post: nat) (n: nat) (qi: nat)
  : Lemma
    (requires pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
              qi < vqt /\ vqt <= Seq.length squeue_post /\ vqt <= Seq.length squeue_pre)
    (ensures Seq.index squeue_post qi == Seq.index squeue_pre qi)

val lemma_pn_extract_old_forall
  (sin_deg_pre sin_deg_post: Seq.seq int) (squeue_pre squeue_post: Seq.seq SZ.t)
  (vqt vtail_post qh: nat) (n: nat)
  : Lemma
    (requires pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
              qh <= vqt /\ vqt <= Seq.length squeue_post /\ vqt <= Seq.length squeue_pre)
    (ensures forall (qi: nat). {:pattern (Seq.index squeue_post qi)}
      qh <= qi /\ qi < vqt ==> Seq.index squeue_post qi == Seq.index squeue_pre qi)

val lemma_pn_extract_new_entry
  (sin_deg_pre sin_deg_post: Seq.seq int) (squeue_pre squeue_post: Seq.seq SZ.t)
  (vqt vtail_post: nat) (n: nat) (qi: nat)
  : Lemma
    (requires pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
              qi >= vqt /\ qi < vtail_post /\ vtail_post <= Seq.length squeue_post /\
              Seq.length sin_deg_pre == n /\ Seq.length sin_deg_post == n)
    (ensures (let v = SZ.v (Seq.index squeue_post qi) in
              v < n /\ Seq.index sin_deg_pre v > 0 /\ Seq.index sin_deg_post v == 0))

val lemma_pn_extract_new_forall
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

val lemma_pn_extract_new_distinct
  (sin_deg_pre sin_deg_post: Seq.seq int) (squeue_pre squeue_post: Seq.seq SZ.t)
  (vqt vtail_post: nat) (n: nat) (i j: nat)
  : Lemma
    (requires pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
              i >= vqt /\ i < vtail_post /\ j >= vqt /\ j < vtail_post /\ i <> j /\
              vtail_post <= Seq.length squeue_post)
    (ensures SZ.v (Seq.index squeue_post i) <> SZ.v (Seq.index squeue_post j))

val lemma_pn_extract_new_distinct_forall
  (sin_deg_pre sin_deg_post: Seq.seq int) (squeue_pre squeue_post: Seq.seq SZ.t)
  (vqt vtail_post: nat) (n: nat)
  : Lemma
    (requires pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
              vtail_post <= Seq.length squeue_post)
    (ensures forall (i j: nat). {:pattern (Seq.index squeue_post i); (Seq.index squeue_post j)}
      i >= vqt /\ i < vtail_post /\ j >= vqt /\ j < vtail_post /\ i <> j ==>
        SZ.v (Seq.index squeue_post i) <> SZ.v (Seq.index squeue_post j))

val lemma_queue_fresh_transfer_and_extend
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

val lemma_queue_distinct_transfer_and_extend
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

#push-options "--z3rlimit 50"
val lemma_old_new_cross_distinct
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

#pop-options

#push-options "--z3rlimit 50"
val lemma_new_entries_fresh_after_upd
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

#pop-options

#push-options "--z3rlimit 50"
val lemma_bridge_preds
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

#pop-options

#push-options "--z3rlimit 100"
val lemma_bridge_fresh
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

#pop-options

#push-options "--z3rlimit 100"
val lemma_bridge_distinct
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

#pop-options

val lemma_bridge_queue_through_pn
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

(* ================================================================
   DAG COMPLETENESS — Proves count == n when all zero-indeg are in output
   ================================================================ *)

val find_missing_vertex
  (output: Seq.seq int) (count n: nat) (v: nat)
  : Pure nat
    (requires
      v <= n /\ count < n /\ Seq.length output >= count /\ n > 0 /\
      partial_distinct output count /\ partial_valid output count n /\
      (forall (u: nat). u < v /\ u < n ==> is_in_output output count u))
    (ensures fun u -> u < n /\ not (is_in_output output count u))

val lemma_dag_completeness
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

(* ================================================================
   ZERO_INDEG_ACCOUNTED — Loop invariant for DAG completeness
   Every vertex with in_deg == 0 is either in output or in the active queue.
   ================================================================ *)


val zero_indeg_accounted_elim
  (in_deg: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat)
  (queue: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires zero_indeg_accounted in_deg n output count queue qh qt)
    (ensures
      Seq.length in_deg >= n /\ count <= Seq.length output /\
      qh <= qt /\ qt <= Seq.length queue /\
      (forall (v: nat). v < n /\ Seq.index in_deg v == 0 ==>
        is_in_output output count v \/ is_in_queue_sz queue qh qt v))

val zero_indeg_accounted_intro
  (in_deg: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat)
  (queue: Seq.seq SZ.t) (qh qt: nat)
  : Lemma
    (requires
      Seq.length in_deg >= n /\ count <= Seq.length output /\
      qh <= qt /\ qt <= Seq.length queue /\
      (forall (v: nat). v < n /\ Seq.index in_deg v == 0 ==>
        is_in_output output count v \/ is_in_queue_sz queue qh qt v))
    (ensures zero_indeg_accounted in_deg n output count queue qh qt)

val zero_indeg_accounted_at_exit
  (in_deg: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat)
  (queue: Seq.seq SZ.t) (qh: nat)
  : Lemma
    (requires zero_indeg_accounted in_deg n output count queue qh qh)
    (ensures
      Seq.length in_deg >= n /\
      (forall (v: nat). v < n /\ Seq.index in_deg v == 0 ==> is_in_output output count v))


val lemma_is_in_queue_dequeue
  (queue: Seq.seq SZ.t) (qh qt: nat) (v: nat)
  : Lemma
    (requires qh < qt /\ qt <= Seq.length queue /\ is_in_queue_sz queue qh qt v /\ SZ.v (Seq.index queue qh) <> v)
    (ensures is_in_queue_sz queue (qh + 1) qt v)

val lemma_is_in_queue_extend
  (queue: Seq.seq SZ.t) (qh qt qt': nat) (v: nat)
  : Lemma
    (requires qh <= qt /\ qt <= qt' /\ qt' <= Seq.length queue /\ is_in_queue_sz queue qh qt v)
    (ensures is_in_queue_sz queue qh qt' v)

val lemma_is_in_output_monotone_local
  (output: Seq.seq int) (c1 c2: nat) (v: int)
  : Lemma
    (requires c1 <= c2 /\ c2 <= Seq.length output /\ is_in_output output c1 v)
    (ensures is_in_output output c2 v)

(* After dequeue u from queue and add u to output:
   u moves from queue[qh] to output[count]. *)
val lemma_zero_indeg_accounted_dequeue_extend
  (in_deg: Seq.seq int) (n: nat)
  (output_pre output_post: Seq.seq int) (count: nat)
  (queue: Seq.seq SZ.t) (qh qt: nat) (u: int)
  : Lemma
    (requires
      zero_indeg_accounted in_deg n output_pre count queue qh qt /\
      qh < qt /\ qt <= Seq.length queue /\
      count < Seq.length output_post /\ Seq.length output_post == Seq.length output_pre /\
      output_post == Seq.upd output_pre count u /\
      u == SZ.v (Seq.index queue qh) /\
      n > 0)
    (ensures
      zero_indeg_accounted in_deg n output_post (count + 1) queue (qh + 1) qt)

val lemma_is_in_queue_preserved
  (queue_old queue_new: Seq.seq SZ.t) (qh qt: nat) (v: nat)
  : Lemma
    (requires is_in_queue_sz queue_old qh qt v /\ qh <= qt /\ qt <= Seq.length queue_old /\
      qt <= Seq.length queue_new /\
      (forall (k: nat). k >= qh /\ k < qt ==> Seq.index queue_new k == Seq.index queue_old k))
    (ensures is_in_queue_sz queue_new qh qt v)

val lemma_is_in_queue_enqueue
  (queue: Seq.seq SZ.t) (qh qt: nat) (v: nat)
  : Lemma
    (requires qh <= qt /\ qt < Seq.length queue /\ SZ.v (Seq.index queue qt) == v)
    (ensures is_in_queue_sz queue qh (qt + 1) v)

val lemma_is_in_queue_weaken_start
  (queue: Seq.seq SZ.t) (qh qh' qt: nat) (v: nat)
  : Lemma
    (requires qh <= qh' /\ qh' <= qt /\ qt <= Seq.length queue /\ is_in_queue_sz queue qh' qt v)
    (ensures is_in_queue_sz queue qh qt v)

val lemma_is_in_queue_witness
  (queue: Seq.seq SZ.t) (qh qt k: nat) (v: nat)
  : Lemma
    (requires qh <= k /\ k < qt /\ qt <= Seq.length queue /\ SZ.v (Seq.index queue k) == v)
    (ensures is_in_queue_sz queue qh qt v)

val lemma_pn_enqueue_complete_to_is_in_queue
  (sin_deg_start sin_deg_post: Seq.seq int) (squeue_post: Seq.seq SZ.t)
  (vtail_start vtail_post: nat) (n: nat)
  : Lemma
    (requires pn_enqueue_complete sin_deg_start sin_deg_post squeue_post vtail_start vtail_post n n)
    (ensures
      forall (v: nat). v < n /\ Seq.index sin_deg_start v <> 0 /\ Seq.index sin_deg_post v == 0 ==>
        is_in_queue_sz squeue_post vtail_start vtail_post v)

val lemma_zero_indeg_accounted_after_pn
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


val lemma_post_process_neighbors
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
      inner_indeg_partial adj n sin_deg_pre sin_deg_post u n /\
      pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n /\
      vtail_post >= vqt /\ vtail_post <= n /\
      queue_entries_valid squeue_post vtail_post n)
    (ensures
      kahn_outer_inv adj n sin_deg_post squeue_post soutput_post (vqh + 1) vtail_post (vout + 1))

(* queue_entries_zero_indeg maintenance after process_neighbors.
   Old entries [0, vqt) had sin_deg == 0. Since u not in output, u can't be a predecessor
   of any zero-indeg vertex, so pn doesn't decrement their in-degrees.
   New entries [vqt, vtail_post) have sin_deg_post == 0 from pn_extra_inv. *)
val lemma_queue_entries_zero_indeg_after_pn
  (adj: Seq.seq int) (n: nat)
  (sin_deg_pre sin_deg_post: Seq.seq int) (output: Seq.seq int) (count: nat)
  (squeue_pre squeue_post: Seq.seq SZ.t) (vqt vtail_post: nat) (u: nat)
  : Lemma
    (requires
      n > 0 /\ u < n /\
      Seq.length adj == n * n /\
      Seq.length sin_deg_pre == n /\ Seq.length sin_deg_post == n /\
      Seq.length squeue_pre == n /\ Seq.length squeue_post == n /\
      count <= Seq.length output /\
      vqt <= vtail_post /\ vtail_post <= n /\
      queue_entries_zero_indeg sin_deg_pre squeue_pre vqt /\
      indeg_correct adj n sin_deg_pre output count /\
      not (is_in_output output count u) /\
      inner_indeg_partial adj n sin_deg_pre sin_deg_post u n /\
      pn_extra_inv sin_deg_pre sin_deg_post squeue_pre squeue_post vqt vtail_post n)
    (ensures queue_entries_zero_indeg sin_deg_post squeue_post vtail_post)

(* sin_deg nonneg: derivable from indeg_correct + partial_distinct + partial_valid *)
val lemma_indeg_nonneg
  (adj: Seq.seq int) (n: nat) (sin_deg: Seq.seq int) (output: Seq.seq int) (count: nat)
  : Lemma
    (requires
      indeg_correct adj n sin_deg output count /\
      partial_distinct output count /\
      partial_valid output count n /\
      n > 0)
    (ensures forall (v: nat). v < n ==> Seq.index sin_deg v >= 0)
