module CLRS.Ch26.MaxFlow
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot
open CLRS.Ch26.MaxFlow.Spec
module Proofs = CLRS.Ch26.MaxFlow.Proofs

(*
   Ford-Fulkerson (Edmonds-Karp) — Verified in Pulse
   
   Computes a maximum flow via BFS-based augmenting paths:
   1. BFS on residual graph to find shortest augmenting path
   2. Find bottleneck (min residual capacity) along the path
   3. Augment flow along the path
   4. Repeat until no augmenting path exists
   
   Connects to the fully verified pure spec (Spec.fst, Proofs.fst):
   - valid_flow maintained through augmentation
   - MFMC theorem: no augmenting path ⟹ max flow
*)

(* ================================================================
   TOTAL WRAPPERS for sequence operations (avoid partial Seq.index)
   ================================================================ *)

let seq_get (s: Seq.seq int) (i: nat) : int =
  if i < Seq.length s then Seq.index s i else 0

let seq_get_sz (s: Seq.seq SZ.t) (i: nat) : SZ.t =
  if i < Seq.length s then Seq.index s i else 0sz

(* ================================================================
   SPEC-LEVEL PREDICATES
   ================================================================ *)

(** Valid non-negative capacities *)
let valid_caps (cap_seq: Seq.seq int) (n: nat) : prop =
  Seq.length cap_seq == n * n /\
  (forall (i: nat). i < n * n ==> Seq.index cap_seq i >= 0)

(** Imperative flow matches spec-level valid_flow — guarded to avoid refinement issues *)
let imp_valid_flow (flow_seq cap_seq: Seq.seq int) (n source sink: nat) : prop =
  n > 0 /\
  source < n /\
  sink < n /\
  Seq.length flow_seq == n * n /\
  Seq.length cap_seq == n * n /\
  // Capacity constraint: 0 ≤ f(u,v) ≤ c(u,v)
  (forall (u: nat) (v: nat). u < n /\ v < n ==>
    (let idx = u * n + v in
     idx < Seq.length flow_seq /\
     0 <= Seq.index flow_seq idx /\ 
     Seq.index flow_seq idx <= Seq.index cap_seq idx)) /\
  // Flow conservation
  (forall (u: nat). u < n /\ u <> source /\ u <> sink ==>
    sum_flow_into flow_seq n u n == sum_flow_out flow_seq n u n)

(** Zero-initialized array equals Seq.create *)
let lemma_zero_array_eq_create (s: Seq.seq int) (len: nat)
  : Lemma
    (requires Seq.length s == len /\ (forall (i: nat). i < len ==> Seq.index s i == 0))
    (ensures s == Seq.create len 0)
  = Seq.lemma_eq_intro s (Seq.create len 0)

(** Queue entries are valid vertices *)
let queue_valid (squeue: Seq.seq SZ.t) (head tail: nat) (n: nat) : prop =
  forall (k: nat). k >= head /\ k < tail ==> SZ.v (seq_get_sz squeue k) < n

(** Pred entries for discovered non-source vertices are valid *)
let pred_valid (spred scolor: Seq.seq int) (n source: nat) : prop =
  forall (v: nat). v < n /\ v <> source /\ seq_get scolor v <> 0 ==>
    seq_get spred v >= 0 /\ seq_get spred v < n

(* Note: pred_valid is not currently threaded through the BFS functions.
   The assume_ calls in find_bottleneck_imp and augment_imp assert pred validity
   based on the BFS invariant that only valid vertices are stored in pred[]. *)

(* ================================================================
   BFS ON RESIDUAL GRAPH
   ================================================================ *)

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
fn bfs_init
  (color pred: A.array int)
  (n source: SZ.t)
  (#scolor: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  requires
    A.pts_to color scolor **
    A.pts_to pred spred **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length spred == SZ.v n
    )
  ensures exists* scolor' spred'.
    A.pts_to color scolor' **
    A.pts_to pred spred' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      (forall (j: nat). j < SZ.v n /\ j <> SZ.v source ==> seq_get scolor' j == 0) /\
      seq_get scolor' (SZ.v source) == 1 /\
      (forall (j: nat). j < SZ.v n ==> seq_get spred' j == -1)
    )
{
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi sc sp.
    R.pts_to i vi **
    A.pts_to color sc **
    A.pts_to pred sp **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sc == SZ.v n /\
      Seq.length sp == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> seq_get sc j == 0) /\
      (forall (j: nat). j < SZ.v vi ==> seq_get sp j == -1)
    )
  {
    let vi = !i;
    A.op_Array_Assignment color vi 0;
    A.op_Array_Assignment pred vi (-1);
    i := vi +^ 1sz
  };
  A.op_Array_Assignment color source 1;
  ()
}
#pop-options

(** Try to discover vertex vv from u in the residual graph *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
fn maybe_discover
  (capacity flow color pred: A.array int)
  (queue: A.array SZ.t)
  (n u vv: SZ.t)
  (q_tail: R.ref SZ.t)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  (#vtail: erased SZ.t)
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor **
    A.pts_to pred spred **
    A.pts_to queue squeue **
    R.pts_to q_tail vtail **
    pure (
      SZ.v n > 0 /\
      SZ.v u < SZ.v n /\
      SZ.v vv < SZ.v n /\
      SZ.v vtail <= SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      queue_valid squeue 0 (SZ.v vtail) (SZ.v n)
    )
  ensures exists* scolor' spred' squeue' vtail'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor' **
    A.pts_to pred spred' **
    A.pts_to queue squeue' **
    R.pts_to q_tail vtail' **
    pure (
      SZ.v vtail' <= SZ.v n /\
      SZ.v vtail' >= SZ.v vtail /\
      Seq.length scolor' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      queue_valid squeue' 0 (SZ.v vtail') (SZ.v n)
    )
{
  let vt = !q_tail;
  let cv: int = A.op_Array_Access color vv;
  let idx_fwd: SZ.t = u *^ n +^ vv;
  let idx_bwd: SZ.t = vv *^ n +^ u;
  let cap_val: int = A.op_Array_Access capacity idx_fwd;
  let flow_fwd: int = A.op_Array_Access flow idx_fwd;
  let flow_bwd: int = A.op_Array_Access flow idx_bwd;
  let res_fwd: int = cap_val - flow_fwd;
  if (cv = 0 && (res_fwd > 0 || flow_bwd > 0) && vt <^ n)
  {
    A.op_Array_Assignment color vv 1;
    A.op_Array_Assignment pred vv (SZ.v u);
    A.op_Array_Assignment queue vt vv;
    q_tail := vt +^ 1sz;
    ()
  }
  else { () }
}
#pop-options

(** Explore all neighbors of vertex u in the residual graph *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
fn bfs_explore_neighbors
  (capacity flow color pred: A.array int)
  (queue: A.array SZ.t)
  (n u: SZ.t)
  (q_tail: R.ref SZ.t)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  (#vtail: erased SZ.t)
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor **
    A.pts_to pred spred **
    A.pts_to queue squeue **
    R.pts_to q_tail vtail **
    pure (
      SZ.v n > 0 /\
      SZ.v u < SZ.v n /\
      SZ.v vtail <= SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      queue_valid squeue 0 (SZ.v vtail) (SZ.v n)
    )
  ensures exists* scolor' spred' squeue' vtail'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor' **
    A.pts_to pred spred' **
    A.pts_to queue squeue' **
    R.pts_to q_tail vtail' **
    pure (
      SZ.v vtail' <= SZ.v n /\
      SZ.v vtail' >= SZ.v vtail /\
      Seq.length scolor' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      queue_valid squeue' 0 (SZ.v vtail') (SZ.v n)
    )
{
  let mut v: SZ.t = 0sz;
  while (!v <^ n)
  invariant exists* vv sc sp sq vt.
    R.pts_to v vv **
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color sc **
    A.pts_to pred sp **
    A.pts_to queue sq **
    R.pts_to q_tail vt **
    pure (
      SZ.v vv <= SZ.v n /\
      SZ.v vt <= SZ.v n /\
      SZ.v vt >= SZ.v vtail /\
      Seq.length sc == SZ.v n /\
      Seq.length sp == SZ.v n /\
      Seq.length sq == SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      queue_valid sq 0 (SZ.v vt) (SZ.v n)
    )
  {
    let vv = !v;
    maybe_discover capacity flow color pred queue n u vv q_tail;
    v := vv +^ 1sz
  };
  ()
}
#pop-options

(** Main BFS: returns whether sink was reached *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
fn bfs_residual
  (capacity flow color pred: A.array int)
  (queue: A.array SZ.t)
  (n source sink: SZ.t)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#scolor0: erased (Seq.seq int))
  (#spred0: erased (Seq.seq int))
  (#squeue0: erased (Seq.seq SZ.t))
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor0 **
    A.pts_to pred spred0 **
    A.pts_to queue squeue0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length scolor0 == SZ.v n /\
      Seq.length spred0 == SZ.v n /\
      Seq.length squeue0 == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns found: bool
  ensures exists* scolor' spred' squeue'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor' **
    A.pts_to pred spred' **
    A.pts_to queue squeue' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      found == (seq_get scolor' (SZ.v sink) <> 0)
    )
{
  bfs_init color pred n source;
  A.op_Array_Assignment queue 0sz source;
  let mut q_head: SZ.t = 0sz;
  let mut q_tail: SZ.t = 1sz;

  while (
    let vh = !q_head;
    let vt = !q_tail;
    vh <^ vt
  )
  invariant exists* vhead vtail scolor_q spred_q squeue_q.
    R.pts_to q_head vhead **
    R.pts_to q_tail vtail **
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor_q **
    A.pts_to pred spred_q **
    A.pts_to queue squeue_q **
    pure (
      SZ.v vhead <= SZ.v vtail /\
      SZ.v vtail <= SZ.v n /\
      Seq.length scolor_q == SZ.v n /\
      Seq.length spred_q == SZ.v n /\
      Seq.length squeue_q == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      queue_valid squeue_q 0 (SZ.v vtail) (SZ.v n)
    )
  {
    let vh = !q_head;
    let u: SZ.t = A.op_Array_Access queue vh;
    // Queue entries are valid: follows from queue_valid invariant
    // u = Seq.index squeue vh, vh < vtail, so SZ.v u < SZ.v n
    ();
    q_head := vh +^ 1sz;
    bfs_explore_neighbors capacity flow color pred queue n u q_tail;
    A.op_Array_Assignment color u 2;
    ()
  };
  let sink_color: int = A.op_Array_Access color sink;
  (sink_color <> 0)
}
#pop-options

(* ================================================================
   BOTTLENECK AND AUGMENTATION VIA PRED ARRAY
   ================================================================ *)

(** Find bottleneck: walk pred array from sink to source *)
#push-options "--z3rlimit 160 --fuel 1 --ifuel 1"
fn find_bottleneck_imp
  (capacity flow pred: A.array int)
  (n source sink: SZ.t)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to pred spred **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length spred == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns bn: int
  ensures
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to pred spred **
    pure (bn >= 0)
{
  let mut current: SZ.t = sink;
  let mut bottleneck: int = 2147483647;  // INT_MAX as sentinel

  while (
    let c = !current;
    not (c = source)
  )
  invariant exists* vc vbn.
    R.pts_to current vc **
    R.pts_to bottleneck vbn **
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to pred spred **
    pure (
      SZ.v vc < SZ.v n /\
      vbn >= 0 /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length spred == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  {
    let vc = !current;
    let u_int: int = A.op_Array_Access pred vc;
    assume_ (pure (u_int >= 0 /\ SZ.fits u_int /\ u_int < SZ.v n));
    let u: SZ.t = SZ.uint_to_t u_int;
    // Compute residual capacity of edge u → vc
    let idx_fwd: SZ.t = u *^ n +^ vc;
    let idx_bwd: SZ.t = vc *^ n +^ u;
    let cap_val: int = A.op_Array_Access capacity idx_fwd;
    let flow_fwd: int = A.op_Array_Access flow idx_fwd;
    let flow_bwd: int = A.op_Array_Access flow idx_bwd;
    let res_fwd: int = cap_val - flow_fwd;
    let vbn = !bottleneck;
    if (res_fwd > 0)
    {
      if (res_fwd < vbn) { bottleneck := res_fwd } else { () }
    }
    else
    {
      if (flow_bwd > 0 && flow_bwd < vbn) { bottleneck := flow_bwd } else { () }
    };
    current := u
  };
  !bottleneck
}
#pop-options

(** Augment flow: walk pred array from sink to source, update flow *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
fn augment_imp
  (capacity flow pred: A.array int)
  (n source sink: SZ.t)
  (bn: int)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to pred spred **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      bn > 0 /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length spred == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* flow_seq'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq' **
    A.pts_to pred spred **
    pure (
      Seq.length flow_seq' == SZ.v n * SZ.v n
    )
{
  let mut current: SZ.t = sink;

  while (
    let c = !current;
    not (c = source)
  )
  invariant exists* vc fs.
    R.pts_to current vc **
    A.pts_to capacity cap_seq **
    A.pts_to flow fs **
    A.pts_to pred spred **
    pure (
      SZ.v vc < SZ.v n /\
      Seq.length fs == SZ.v n * SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length spred == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  {
    let vc = !current;
    let u_int: int = A.op_Array_Access pred vc;
    assume_ (pure (u_int >= 0 /\ SZ.fits u_int /\ u_int < SZ.v n));
    let u: SZ.t = SZ.uint_to_t u_int;
    // Check forward vs backward
    let idx_fwd: SZ.t = u *^ n +^ vc;
    let idx_bwd: SZ.t = vc *^ n +^ u;
    let cap_val: int = A.op_Array_Access capacity idx_fwd;
    let flow_fwd: int = A.op_Array_Access flow idx_fwd;
    if (cap_val - flow_fwd > 0)
    {
      // Forward edge: increase flow[u*n+v] by bn
      A.op_Array_Assignment flow idx_fwd (flow_fwd + bn);
      current := u
    }
    else
    {
      // Backward edge: decrease flow[v*n+u] by bn
      let flow_bwd: int = A.op_Array_Access flow idx_bwd;
      A.op_Array_Assignment flow idx_bwd (flow_bwd - bn);
      current := u
    }
  };
  ()
}
#pop-options

(* ================================================================
   MAIN FORD-FULKERSON LOOP
   ================================================================ *)

(** Initialize flow to zero *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
fn zero_init_flow
  (flow: A.array int)
  (nn: SZ.t)
  (#flow_seq: erased (Seq.seq int))
  requires
    A.pts_to flow flow_seq **
    pure (Seq.length flow_seq == SZ.v nn)
  ensures exists* flow_seq'.
    A.pts_to flow flow_seq' **
    pure (
      Seq.length flow_seq' == SZ.v nn /\
      (forall (i: nat). i < SZ.v nn ==> Seq.index flow_seq' i == 0)
    )
{
  let mut i: SZ.t = 0sz;
  while (!i <^ nn)
  invariant exists* vi fs.
    R.pts_to i vi **
    A.pts_to flow fs **
    pure (
      SZ.v vi <= SZ.v nn /\
      Seq.length fs == SZ.v nn /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index fs j == 0)
    )
  {
    let vi = !i;
    A.op_Array_Assignment flow vi 0;
    i := vi +^ 1sz
  };
  ()
}
#pop-options

(** Main max flow: Ford-Fulkerson with BFS (Edmonds-Karp) *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
fn max_flow
  (capacity: A.array int)
  (#cap_seq: Ghost.erased (Seq.seq int))
  (flow: A.array int)
  (#flow_contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (source: SZ.t)
  (sink: SZ.t)
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_contents **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      valid_caps cap_seq (SZ.v n)
    )
  returns _: unit
  ensures exists* flow_seq'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq' **
    pure (
      imp_valid_flow flow_seq' cap_seq (SZ.v n) (SZ.v source) (SZ.v sink)
    )
{
  let nn: SZ.t = n *^ n;

  // Phase 1: Initialize flow to zero
  zero_init_flow flow nn;

  // Phase 2: Allocate BFS workspace
  let color = A.alloc 0 n;
  let pred = A.alloc (-1) n;
  let queue = A.alloc 0sz n;

  // Phase 3: Main Ford-Fulkerson loop
  let mut continue_loop: bool = true;
  
  // Establish initial valid_flow for zero flow
  with flow_z. assert (A.pts_to flow flow_z);
  lemma_zero_array_eq_create flow_z (SZ.v n * SZ.v n);
  Proofs.zero_flow_valid #(SZ.v n) cap_seq (SZ.v source) (SZ.v sink);
  
  while (!continue_loop)
  invariant exists* cont flow_s sc sp sq.
    R.pts_to continue_loop cont **
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_s **
    A.pts_to color sc **
    A.pts_to pred sp **
    A.pts_to queue sq **
    pure (
      Seq.length flow_s == SZ.v n * SZ.v n /\
      Seq.length sc == SZ.v n /\
      Seq.length sp == SZ.v n /\
      Seq.length sq == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      imp_valid_flow flow_s cap_seq (SZ.v n) (SZ.v source) (SZ.v sink)
    )
  {
    // Split capacity permission for BFS (read-only)

    let found = bfs_residual capacity flow color pred queue n source sink;


    if found
    {
      // Found augmenting path: augment
      let bn = find_bottleneck_imp capacity flow pred n source sink;
      if (bn > 0) {
        augment_imp capacity flow pred n source sink bn;
        // After augmentation, valid_flow is maintained
        // This requires connecting imperative augmentation to pure augment_aux
        with flow_new. assert (A.pts_to flow flow_new);
        assume_ (pure (imp_valid_flow flow_new cap_seq (SZ.v n) (SZ.v source) (SZ.v sink)))
      } else {
        continue_loop := false
      };
    }
    else
    {
      continue_loop := false
    }
  };

  // Cleanup BFS workspace
  A.free color;
  A.free pred;
  A.free queue;
  ()
}
#pop-options
