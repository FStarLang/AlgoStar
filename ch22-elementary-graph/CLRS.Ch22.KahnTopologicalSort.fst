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

open CLRS.Ch22.KahnTopologicalSort.Defs

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec
module ML = FStar.Math.Lemmas

(* ================================================================
   GHOST TICK — for complexity tracking
   ================================================================ *)

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

(* ================================================================
   COMPLEXITY ARITHMETIC LEMMA
   ================================================================ *)

let lemma_topsort_complexity_bound (n i j: nat)
  : Lemma (requires n >= 1 /\ i < n /\ j <= n)
          (ensures i * n + j <= n * n)
  = ML.lemma_mult_le_right n i (n - 1);
    assert (i * n <= (n - 1) * n);
    assert ((n - 1) * n + n == n * n);
    assert (i * n + j <= (n - 1) * n + n)

(* ================================================================
   HELPER: maybe_enqueue — Process edge and potentially enqueue vertex
   ================================================================ *)

#push-options "--z3rlimit 10"
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
      queue_entries_valid squeue' (SZ.v vtail') (SZ.v n) /\
      // Queue frame: entries below old tail preserved
      (forall (k:nat). k < SZ.v vtail ==>
        Seq.index squeue' k == Seq.index squeue k) /\
      // If enqueue happened: new entry is vv and in-degree reached 0, old in-degree was positive
      (SZ.v vtail' == SZ.v vtail + 1 ==>
        (SZ.v (Seq.index squeue' (SZ.v vtail)) == SZ.v vv /\
         Seq.index sin_degree' (SZ.v vv) == 0 /\
         Seq.index sin_degree (SZ.v vv) > 0)) /\
      // Converse: if in-degree dropped to 0 from positive and queue not full, enqueue happened
      (Seq.index sin_degree' (SZ.v vv) == 0 /\ Seq.index sin_degree (SZ.v vv) > 0 /\ SZ.v vtail < SZ.v n ==>
        SZ.v vtail' == SZ.v vtail + 1)
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

(* Ghost wrapper: performs one step of the inner loop.
   Avoids Pulse VC closure issue with multiple with-captures in loops. *)
#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
fn pn_loop_step
  (adj: A.array int) (in_degree: A.array int)
  (queue_data: A.array SZ.t) (queue_tail: R.ref SZ.t)
  (u vv n vtail_start_val: SZ.t)
  (sin_degree_init: erased (Seq.seq int))
  (squeue_init: erased (Seq.seq SZ.t))
  (#sadj: erased (Seq.seq int))
  (#sin_deg_cur: erased (Seq.seq int))
  (#squeue_cur: erased (Seq.seq SZ.t))
  (#vtail_cur: erased SZ.t)
  requires
    A.pts_to adj sadj **
    A.pts_to in_degree sin_deg_cur **
    A.pts_to queue_data squeue_cur **
    R.pts_to queue_tail vtail_cur **
    pure (
      SZ.v u < SZ.v n /\
      SZ.v vv < SZ.v n /\
      SZ.v vtail_cur <= SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sin_deg_cur == SZ.v n /\
      Seq.length squeue_cur == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.fits (SZ.v u * SZ.v n) /\
      queue_entries_valid squeue_cur (SZ.v vtail_cur) (SZ.v n) /\
      inner_indeg_partial sadj (SZ.v n) sin_degree_init sin_deg_cur (SZ.v u) (SZ.v vv) /\
      pn_extra_inv sin_degree_init sin_deg_cur squeue_init squeue_cur (SZ.v vtail_start_val) (SZ.v vtail_cur) (SZ.v n) /\
      pn_entries_below squeue_cur (SZ.v vtail_start_val) (SZ.v vtail_cur) (SZ.v vv) /\
      pn_enqueue_complete sin_degree_init sin_deg_cur squeue_cur (SZ.v vtail_start_val) (SZ.v vtail_cur) (SZ.v n) (SZ.v vv) /\
      queue_entries_zero_indeg sin_degree_init squeue_cur (SZ.v vtail_start_val) /\
      queue_distinct_sz squeue_cur 0 (SZ.v vtail_cur) /\
      (forall (k:nat). k < SZ.v n ==> Seq.index sin_degree_init k >= 0) /\
      SZ.v vtail_start_val <= Seq.length squeue_init /\
      Seq.length squeue_init == SZ.v n
    )
  ensures exists* sin_deg_new squeue_new vtail_new.
    A.pts_to adj sadj **
    A.pts_to in_degree sin_deg_new **
    A.pts_to queue_data squeue_new **
    R.pts_to queue_tail vtail_new **
    pure (
      SZ.v vtail_new >= SZ.v vtail_cur /\
      SZ.v vtail_new <= SZ.v n /\
      Seq.length sin_deg_new == SZ.v n /\
      Seq.length squeue_new == SZ.v n /\
      queue_entries_valid squeue_new (SZ.v vtail_new) (SZ.v n) /\
      inner_indeg_partial sadj (SZ.v n) sin_degree_init sin_deg_new (SZ.v u) (SZ.v vv + 1) /\
      pn_extra_inv sin_degree_init sin_deg_new squeue_init squeue_new (SZ.v vtail_start_val) (SZ.v vtail_new) (SZ.v n) /\
      pn_entries_below squeue_new (SZ.v vtail_start_val) (SZ.v vtail_new) (SZ.v vv + 1) /\
      pn_enqueue_complete sin_degree_init sin_deg_new squeue_new (SZ.v vtail_start_val) (SZ.v vtail_new) (SZ.v n) (SZ.v vv + 1) /\
      queue_distinct_sz squeue_new 0 (SZ.v vtail_new)
    )
{
  with sin_deg_cur0. assert (A.pts_to in_degree sin_deg_cur0);
  with squeue_cur0. assert (A.pts_to queue_data squeue_cur0);
  let vtail_before = !queue_tail;
  
  maybe_enqueue adj in_degree queue_data queue_tail u vv n;
  with sin_deg_new squeue_new vtail_new. _;
  
  let vtail_after = !queue_tail;

  // Combined F* step: inner_indeg + entries_below + pn_extra_inv
  pn_combined_step sadj (SZ.v n)
    sin_degree_init sin_deg_cur0 sin_deg_new
    squeue_init squeue_cur0 squeue_new
    (SZ.v vtail_start_val) (SZ.v vtail_before) (SZ.v vtail_after) (SZ.v u) (SZ.v vv);

  // Help postcondition: connect vtail_before/after to vtail_cur
  assert (pure (SZ.v vtail_after >= SZ.v vtail_cur));
  assert (pure (SZ.v vtail_after <= SZ.v n));
  assert (pure (queue_entries_valid squeue_new (SZ.v vtail_after) (SZ.v n)))
}
#pop-options

(* ================================================================
   HELPER: process_neighbors — Inner loop: scan all potential neighbors
   of dequeued vertex u, decrement in-degrees, enqueue zero-indegree vertices.
   Extracted to keep the outer loop VC small.
   ================================================================ *)

#push-options "--z3rlimit 10"
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
      queue_entries_valid squeue (SZ.v vtail) (SZ.v n) /\
      queue_entries_zero_indeg sin_degree squeue (SZ.v vtail) /\
      queue_distinct_sz squeue 0 (SZ.v vtail) /\
      (forall (k:nat). k < SZ.v n ==> Seq.index sin_degree k >= 0)
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
      inner_indeg_partial sadj (SZ.v n) sin_degree sin_degree' (SZ.v u) (SZ.v n) /\
      pn_extra_inv sin_degree sin_degree' squeue squeue' (SZ.v vtail) (SZ.v vtail') (SZ.v n) /\
      pn_enqueue_complete sin_degree sin_degree' squeue' (SZ.v vtail) (SZ.v vtail') (SZ.v n) (SZ.v n) /\
      queue_distinct_sz squeue' 0 (SZ.v vtail')
    )
{
  // Read initial vtail as concrete value for pn_loop_step
  let vtail_init = !queue_tail;
  
  // Establish initial predicates
  pn_extra_inv_initial sin_degree squeue (SZ.v vtail_init) (SZ.v n);
  pn_entries_below_initial squeue (SZ.v vtail_init);
  pn_enqueue_complete_initial sin_degree squeue (SZ.v vtail_init) (SZ.v n);
  
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
      SZ.v vtail_cur >= SZ.v vtail_init /\
      SZ.v vtail_cur <= SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sin_deg_cur == SZ.v n /\
      Seq.length squeue_cur == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.fits (SZ.v u * SZ.v n) /\
      queue_entries_valid squeue_cur (SZ.v vtail_cur) (SZ.v n) /\
      inner_indeg_partial sadj (SZ.v n) sin_degree sin_deg_cur (SZ.v u) (SZ.v vv) /\
      pn_extra_inv sin_degree sin_deg_cur squeue squeue_cur (SZ.v vtail_init) (SZ.v vtail_cur) (SZ.v n) /\
      pn_entries_below squeue_cur (SZ.v vtail_init) (SZ.v vtail_cur) (SZ.v vv) /\
      pn_enqueue_complete sin_degree sin_deg_cur squeue_cur (SZ.v vtail_init) (SZ.v vtail_cur) (SZ.v n) (SZ.v vv) /\
      queue_entries_zero_indeg sin_degree squeue_cur (SZ.v vtail_init) /\
      queue_distinct_sz squeue_cur 0 (SZ.v vtail_cur) /\
      (forall (k:nat). k < SZ.v n ==> Seq.index sin_degree k >= 0) /\
      SZ.v vtail_init <= Seq.length squeue /\
      Seq.length squeue == SZ.v n
    )
  decreases (SZ.v n - SZ.v !v)
  {
    let vv = !v;
    
    pn_loop_step adj in_degree queue_data queue_tail u vv n vtail_init sin_degree squeue;
    
    v := SZ.add vv 1sz
  }
}
#pop-options

#push-options "--z3rlimit 10 --split_queries always --ifuel 2"
// Input: adjacency matrix adj (n×n represented as flat array)
// Output: array containing topological order of vertices
//SNIPPET_START: topological_sort_sig
fn topological_sort 
  (adj: A.array int) 
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#c0: erased nat)
  requires 
    A.pts_to adj sadj **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      ~(has_cycle sadj (SZ.v n))
    )
  returns output: V.vec int
  ensures exists* sout (cf: nat).
    A.pts_to adj sadj **
    V.pts_to output sout **
    GR.pts_to ctr cf **
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
      is_topological_order sadj (SZ.v n) (seq_int_to_nat sout) /\
      // Complexity: at most n² ticks
      cf >= reveal c0 /\
      cf - reveal c0 <= SZ.v n * SZ.v n
    )
//SNIPPET_END: topological_sort_sig
{
  // Step 1: Compute in-degrees
  // Ticks are placed in the inner loop of the n×n adjacency scan.
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
  invariant exists* vi sin_degree (vc: nat).
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sin_degree == SZ.v n /\
      step1_outer_inv sadj (SZ.v n) (reveal ghost_output) sin_degree (SZ.v vi) /\
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi * SZ.v n
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    with sin_deg_outer. assert (A.pts_to in_degree sin_deg_outer);
    
    // Convert outer_inv to inner_inv at col=0
    lemma_step1_outer_to_inner sadj (SZ.v n) (reveal ghost_output) sin_deg_outer (SZ.v vi);
    
    // For each vertex j, check if edge vi->j exists
    let mut j: SZ.t = 0sz;
    while (!j <^ n)
    invariant exists* vj sin_degree (vc2: nat).
      R.pts_to i vi **
      R.pts_to j vj **
      A.pts_to adj sadj **
      A.pts_to in_degree sin_degree **
      GR.pts_to ctr vc2 **
      pure (
        SZ.v vi < SZ.v n /\
        SZ.v vj <= SZ.v n /\
        Seq.length sin_degree == SZ.v n /\
        Seq.length sadj == SZ.v n * SZ.v n /\
        SZ.fits (SZ.v n * SZ.v n) /\
        step1_inner_inv sadj (SZ.v n) (reveal ghost_output) sin_degree (SZ.v vi) (SZ.v vj) /\
        vc2 >= reveal c0 /\
        vc2 - reveal c0 == SZ.v vi * SZ.v n + SZ.v vj
      )
    decreases (SZ.v n - SZ.v !j)
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
      FStar.Math.Lemmas.nat_times_nat_is_nat (SZ.v vi) (SZ.v n);
      assert (pure (SZ.v vi * SZ.v n + SZ.v vj < Seq.length sadj));
      lemma_step1_inner_step sadj (SZ.v n) (reveal ghost_output) sin_deg_inner sin_deg_new (SZ.v vi) (SZ.v vj);
      
      // Tick: one unit of work per adjacency check
      tick ctr;
      
      j := vj +^ 1sz;
    };
    
    // Inner loop complete: convert inner_inv at col=n to outer_inv at row+1
    with sin_deg_after_inner. assert (A.pts_to in_degree sin_deg_after_inner);
    lemma_step1_inner_to_outer sadj (SZ.v n) (reveal ghost_output) sin_deg_after_inner (SZ.v vi);
    
    // Tick count: vi*n + n == (vi+1)*n
    with vc_mid. assert (GR.pts_to ctr vc_mid);
    assert (pure (reveal vc_mid - reveal c0 == SZ.v vi * SZ.v n + SZ.v n));
    assert (pure (SZ.v vi * SZ.v n + SZ.v n == (SZ.v vi + 1) * SZ.v n));
    
    i := vi +^ 1sz;
  };
  
  // After Step 1: n*n ticks have been charged during the adjacency scan
  // Capture in_degree state for indeg_correct conversion
  with sin_deg_after_step1. assert (A.pts_to in_degree sin_deg_after_step1);
  
  // Step 2: Initialize queue with vertices having in-degree 0
  let queue_v = V.alloc 0sz n;
  V.to_array_pts_to queue_v;
  let queue = V.vec_to_array queue_v;
  rewrite (A.pts_to (V.vec_to_array queue_v) (Seq.create (SZ.v n) 0sz))
       as (A.pts_to queue (Seq.create (SZ.v n) 0sz));
  let mut queue_tail: SZ.t = 0sz;
  
  // Establish step2 initial invariant
  lemma_step2_initial sadj (SZ.v n) sin_deg_after_step1 (reveal ghost_output) (Seq.create (SZ.v n) 0sz);
  
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi vqt squeue (vc: nat).
    R.pts_to i vi **
    R.pts_to queue_tail vqt **
    A.pts_to adj sadj **
    A.pts_to queue squeue **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      SZ.v vqt <= SZ.v vi /\
      SZ.v vqt <= SZ.v n /\
      Seq.length squeue == SZ.v n /\
      // Step 2 queue invariant (includes queue_distinct, entries < vi, entries have indeg 0)
      step2_queue_inv sadj (SZ.v n) sin_deg_after_step1 (reveal ghost_output) squeue (SZ.v vqt) (SZ.v vi) /\
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v n * SZ.v n
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    let vqt = !queue_tail;
    with squeue_pre. assert (A.pts_to queue squeue_pre);
    
    // Read in_degree[vi] (in_degree is framed — not in invariant)
    let deg = A.op_Array_Access in_degree vi;
    
    // Unconditionally write queue[vqt] = vi
    A.op_Array_Assignment queue vqt vi;
    with squeue_post. assert (A.pts_to queue squeue_post);
    
    // Conditionally advance queue_tail
    let new_vqt: SZ.t = (if deg = 0 then vqt +^ 1sz else vqt);
    queue_tail := new_vqt;
    
    // Step 2 invariant maintenance — single unified lemma
    lemma_step2_step sadj (SZ.v n) sin_deg_after_step1 (reveal ghost_output)
      squeue_pre squeue_post (SZ.v vqt) (SZ.v new_vqt) (SZ.v vi);
    
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
  
  // Queue distinct + queue preds + queue entries valid from Step 2 invariant
  lemma_step2_to_queue_distinct sadj (SZ.v n) sin_deg_init (reveal ghost_output) squeue_init (SZ.v vqt_init);
  lemma_step2_to_entries_valid sadj (SZ.v n) sin_deg_init (reveal ghost_output) squeue_init (SZ.v vqt_init);
  lemma_step2_to_queue_preds sadj (SZ.v n) sin_deg_init (reveal ghost_output) soutput_init squeue_init (SZ.v vqt_init);
  // Bundle into opaque invariant
  kahn_outer_inv_intro sadj (SZ.v n) sin_deg_init squeue_init soutput_init 0 (SZ.v vqt_init) 0;
  
  // Extra invariants for DAG completeness
  lemma_step2_to_queue_entries_zero_indeg sadj (SZ.v n) sin_deg_init (reveal ghost_output) squeue_init (SZ.v vqt_init);
  // zero_indeg_accounted: from step2 completeness (all zero-indeg vertices in queue)
  // step2_queue_inv at vi=n gives: forall v < n. in_deg[v] == 0 ==> is_in_queue_sz queue 0 vqt v
  lemma_step2_to_zero_indeg_accounted sin_deg_init (SZ.v n) soutput_init squeue_init (SZ.v vqt_init);
  
  while (!queue_head <^ !queue_tail)
  invariant exists* vqh vqt vout sin_degree squeue soutput (vc: nat).
    R.pts_to queue_head vqh **
    R.pts_to queue_tail vqt **
    R.pts_to out_idx vout **
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree **
    A.pts_to queue squeue **
    A.pts_to output soutput **
    GR.pts_to ctr vc **
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
      kahn_outer_inv sadj (SZ.v n) sin_degree squeue soutput (SZ.v vqh) (SZ.v vqt) (SZ.v vout) /\
      // Extra invariants for DAG completeness
      queue_entries_zero_indeg sin_degree squeue (SZ.v vqt) /\
      queue_distinct_sz squeue 0 (SZ.v vqt) /\
      zero_indeg_accounted sin_degree (SZ.v n) soutput (SZ.v vout) squeue (SZ.v vqh) (SZ.v vqt) /\
      ~(has_cycle sadj (SZ.v n)) /\
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v n * SZ.v n
    )
  decreases (SZ.v n - SZ.v !queue_head)
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
    // u not in output[0..vout) follows from queue_fresh
    queue_fresh_not_in_output soutput_pre (SZ.v vout) squeue_pre (SZ.v vqh) (SZ.v vqt) (SZ.v vqh);
    lemma_not_in_output_from_forall soutput_pre (SZ.v vout) u_int;
    
    // Combined post-process_neighbors: re-establish kahn_outer_inv
    lemma_post_process_neighbors sadj (SZ.v n) sin_deg_pre sin_deg_post squeue_pre squeue_post
      soutput_pre soutput_post (SZ.v vqh) (SZ.v vqt) (SZ.v vtail_post) (SZ.v vout) u_int;
    
    // Structural properties of soutput_new = soutput_post = Seq.upd soutput_pre vout u_int
    // u_int < n and u_int >= 0; soutput_pre satisfies the properties by loop invariant
    // For k < vout: Seq.index soutput_new k == Seq.index soutput_pre k (by Seq.upd, k <> vout)
    // For k == vout: Seq.index soutput_new vout == u_int < n, u_int >= 0
    // For k > vout, k < n: Seq.index soutput_new k == Seq.index soutput_pre k == 0
    assert (pure (soutput_new == Seq.upd soutput_pre (SZ.v vout) u_int));
    assert (pure (Seq.length soutput_new == SZ.v n));
    assert (pure (u_int >= 0 /\ u_int < SZ.v n));
    
    // --- Maintain extra invariants for DAG completeness ---
    
    // queue_entries_zero_indeg: maintained after pn
    lemma_queue_entries_zero_indeg_after_pn sadj (SZ.v n)
      sin_deg_pre sin_deg_post soutput_pre (SZ.v vout)
      squeue_pre squeue_post (SZ.v vqt) (SZ.v vtail_post) u_int;
    
    // queue_distinct_sz squeue_post 0 vtail_post: from process_neighbors postcondition
    // (already available)
    
    // zero_indeg_accounted: need intermediate + after pn
    // Convert pn_enqueue_complete to is_in_queue_sz
    lemma_pn_enqueue_complete_to_is_in_queue
      sin_deg_pre sin_deg_post squeue_post (SZ.v vqt) (SZ.v vtail_post) (SZ.v n);
    
    // Establish intermediate zero_indeg_accounted (after dequeue+output extend, before pn)
    // From old: zero_indeg_accounted sin_deg_pre n soutput_pre vout squeue_pre vqh vqt
    // After: zero_indeg_accounted sin_deg_pre n soutput_post (vout+1) squeue_pre (vqh+1) vqt
    // u moved from queue to output, others preserved
    lemma_zero_indeg_accounted_dequeue_extend
      sin_deg_pre (SZ.v n) soutput_pre soutput_post (SZ.v vout)
      squeue_pre (SZ.v vqh) (SZ.v vqt) u_int;
    
    // Now apply lemma_zero_indeg_accounted_after_pn
    lemma_zero_indeg_accounted_after_pn sadj (SZ.v n)
      sin_deg_pre sin_deg_post soutput_post (SZ.v vout + 1)
      squeue_pre squeue_post (SZ.v vqh + 1) (SZ.v vqt) (SZ.v vtail_post);

    // Help Z3 re-establish quantified output-sequence properties
    assert (pure (forall (k: nat). k < SZ.v new_vout ==> Seq.index soutput_new k < SZ.v n));
    assert (pure (forall (k: nat). SZ.v new_vout <= k /\ k < SZ.v n ==> Seq.index soutput_new k == 0));
    assert (pure (forall (k: nat). k < Seq.length soutput_new ==> Seq.index soutput_new k >= 0))
  };
  
  // After the loop, extract the existentials
  with _b vqh vqt vout sin_degree squeue soutput vc_final. _;
  
  // Loop exit: vqh == vqt (queue empty), vout == vqh
  // Prove vout == n using DAG completeness
  
  // Reveal the opaque invariant to extract strong_order_inv, partial_distinct, etc.
  kahn_outer_inv_elim sadj (SZ.v n) sin_degree squeue soutput (SZ.v vqh) (SZ.v vqt) (SZ.v vout);
  
  // zero_indeg_accounted at exit (empty queue: qh == qt)
  // gives: all zero-indeg vertices are in output
  zero_indeg_accounted_at_exit sin_degree (SZ.v n) soutput (SZ.v vout) squeue (SZ.v vqh);
  
  // lemma_dag_completeness: no cycles + all zero-indeg in output → vout >= n
  lemma_dag_completeness sadj (SZ.v n) sin_degree soutput (SZ.v vout);
  
  // vout <= n (from loop invariant) + vout >= n → vout == n
  assert (pure (SZ.v vout == SZ.v n));
  
  // Structural properties
  assert (pure (forall (i: nat). i < SZ.v n ==> Seq.index soutput i < SZ.v n));
  assert (pure (forall (i: nat). i < Seq.length soutput ==> Seq.index soutput i >= 0));
  
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
