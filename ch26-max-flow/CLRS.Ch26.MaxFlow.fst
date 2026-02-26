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

(** All pred entries are in valid range [-1, n) — easy to maintain through BFS *)
let preds_in_range (spred: Seq.seq int) (n: nat) : prop =
  Seq.length spred == n /\
  (forall (v: nat). v < n ==> seq_get spred v >= -1 /\ seq_get spred v < n)

(** Pred entries for discovered non-source vertices are valid *)
let pred_valid (spred scolor: Seq.seq int) (n source: nat) : prop =
  forall (v: nat). v < n /\ v <> source /\ seq_get scolor v <> 0 ==>
    seq_get spred v >= 0 /\ seq_get spred v < n

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
      queue_valid squeue 0 (SZ.v vtail) (SZ.v n) /\
      preds_in_range spred (SZ.v n)
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
      queue_valid squeue' 0 (SZ.v vtail') (SZ.v n) /\
      preds_in_range spred' (SZ.v n)
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
      queue_valid squeue 0 (SZ.v vtail) (SZ.v n) /\
      preds_in_range spred (SZ.v n)
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
      queue_valid squeue' 0 (SZ.v vtail') (SZ.v n) /\
      preds_in_range spred' (SZ.v n)
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
      queue_valid sq 0 (SZ.v vt) (SZ.v n) /\
      preds_in_range sp (SZ.v n)
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
      found == (seq_get scolor' (SZ.v sink) <> 0) /\
      preds_in_range spred' (SZ.v n)
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
      queue_valid squeue_q 0 (SZ.v vtail) (SZ.v n) /\
      preds_in_range spred_q (SZ.v n)
    )
  {
    let vh = !q_head;
    let u: SZ.t = A.op_Array_Access queue vh;
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
      preds_in_range spred (SZ.v n) /\
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
  let mut bottleneck: int = 2147483647;

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
      preds_in_range spred (SZ.v n) /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  {
    let vc = !current;
    let u_int: int = A.op_Array_Access pred vc;
    // From preds_in_range: u_int >= -1 /\ u_int < SZ.v n
    // On a valid BFS path, u_int >= 0 (only -1 for undiscovered vertices)
    if (u_int >= 0)
    {
      let u: SZ.t = SZ.uint_to_t u_int;
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
    }
    else
    {
      // Unreachable on valid BFS paths — defensive: exit loop
      current := source
    }
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
      preds_in_range spred (SZ.v n) /\
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
      preds_in_range spred (SZ.v n) /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  {
    let vc = !current;
    let u_int: int = A.op_Array_Access pred vc;
    // From preds_in_range: u_int >= -1 /\ u_int < SZ.v n
    if (u_int >= 0)
    {
      let u: SZ.t = SZ.uint_to_t u_int;
      let idx_fwd: SZ.t = u *^ n +^ vc;
      let idx_bwd: SZ.t = vc *^ n +^ u;
      let cap_val: int = A.op_Array_Access capacity idx_fwd;
      let flow_fwd: int = A.op_Array_Access flow idx_fwd;
      if (cap_val - flow_fwd > 0)
      {
        A.op_Array_Assignment flow idx_fwd (flow_fwd + bn);
        current := u
      }
      else
      {
        let flow_bwd: int = A.op_Array_Access flow idx_bwd;
        A.op_Array_Assignment flow idx_bwd (flow_bwd - bn);
        current := u
      }
    }
    else
    {
      // Unreachable on valid BFS paths — defensive: exit loop
      current := source
    }
  };
  ()
}
#pop-options

(* ================================================================
   VALIDITY CHECK — dynamic verification of imp_valid_flow
   ================================================================ *)

(** Helper: u*n+v < n*n when u < n and v < n *)
let lemma_idx_lt_nn (n u v: nat)
  : Lemma (requires u < n /\ v < n) (ensures u * n + v < n * n)
  = FStar.Math.Lemmas.lemma_mult_le_right n u (n - 1)

(** Establish imp_valid_flow from capacity + conservation checks *)
#push-options "--z3rlimit 40"
let lemma_checks_imply_valid_flow 
  (flow_s cap_s: Seq.seq int) (n source sink: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ sink < n /\
      Seq.length flow_s == n * n /\ Seq.length cap_s == n * n /\
      (forall (idx: nat). idx < n * n ==> 0 <= Seq.index flow_s idx /\ Seq.index flow_s idx <= Seq.index cap_s idx) /\
      (forall (w: nat). w < n /\ w <> source /\ w <> sink ==>
        sum_flow_into flow_s n w n == sum_flow_out flow_s n w n))
    (ensures imp_valid_flow flow_s cap_s n source sink)
  = let aux (u v: nat)
        : Lemma (requires u < n /\ v < n)
                (ensures u * n + v < n * n)
        = FStar.Math.Lemmas.lemma_mult_le_right n u (n - 1);
          FStar.Math.Lemmas.distributivity_sub_left n 1 n
    in
    FStar.Classical.forall_intro_2 (fun u v -> FStar.Classical.move_requires_2 aux u v)
#pop-options

(** Check capacity constraint: 0 <= flow[i] <= cap[i] for all i *)
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
fn check_capacity_fn
  (flow capacity: A.array int)
  (nn: SZ.t)
  (#flow_seq #cap_seq: erased (Seq.seq int))
  requires
    A.pts_to flow flow_seq **
    A.pts_to capacity cap_seq **
    pure (
      Seq.length flow_seq == SZ.v nn /\
      Seq.length cap_seq == SZ.v nn
    )
  returns ok: bool
  ensures
    A.pts_to flow flow_seq **
    A.pts_to capacity cap_seq **
    pure (
      Seq.length flow_seq == SZ.v nn /\
      Seq.length cap_seq == SZ.v nn /\
      (ok ==> (forall (idx: nat). idx < SZ.v nn ==>
        0 <= Seq.index flow_seq idx /\ Seq.index flow_seq idx <= Seq.index cap_seq idx)))
{
  let mut i = 0sz;
  let mut result = true;
  while (
    let vi = !i;
    let vr = !result;
    vr && vi <^ nn
  )
  invariant exists* vi vr.
    R.pts_to i vi **
    R.pts_to result vr **
    A.pts_to flow flow_seq **
    A.pts_to capacity cap_seq **
    pure (
      SZ.v vi <= SZ.v nn /\
      Seq.length flow_seq == SZ.v nn /\
      Seq.length cap_seq == SZ.v nn /\
      (vr ==> (forall (idx: nat). idx < SZ.v vi ==>
        0 <= Seq.index flow_seq idx /\ Seq.index flow_seq idx <= Seq.index cap_seq idx))
    )
  {
    let vi = !i;
    let f: int = A.op_Array_Access flow vi;
    let c: int = A.op_Array_Access capacity vi;
    if (f < 0 || f > c) { result := false } else { () };
    i := vi +^ 1sz
  };
  !result
}
#pop-options

(** Check conservation at a single vertex: sum_flow_into == sum_flow_out *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
fn check_vertex_conservation
  (flow: A.array int)
  (n u: SZ.t)
  (#flow_seq: erased (Seq.seq int))
  requires
    A.pts_to flow flow_seq **
    pure (
      SZ.v u < SZ.v n /\
      SZ.v n > 0 /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns ok: bool
  ensures
    A.pts_to flow flow_seq **
    pure (
      SZ.v u < SZ.v n /\ SZ.v n > 0 /\ Seq.length flow_seq == SZ.v n * SZ.v n /\
      (ok ==> sum_flow_into flow_seq (SZ.v n) (SZ.v u) (SZ.v n) == sum_flow_out flow_seq (SZ.v n) (SZ.v u) (SZ.v n)))
{
  let mut sum_in: int = 0;
  let mut sum_out: int = 0;
  let mut v = 0sz;
  while (!v <^ n)
  invariant exists* vv si so.
    R.pts_to v vv **
    R.pts_to sum_in si **
    R.pts_to sum_out so **
    A.pts_to flow flow_seq **
    pure (
      SZ.v vv <= SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v n > 0 /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      si == sum_flow_into flow_seq (SZ.v n) (SZ.v u) (SZ.v vv) /\
      so == sum_flow_out flow_seq (SZ.v n) (SZ.v u) (SZ.v vv)
    )
  {
    let vv = !v;
    let idx_in: SZ.t = vv *^ n +^ u;
    let idx_out: SZ.t = u *^ n +^ vv;
    let f_in: int = A.op_Array_Access flow idx_in;
    let f_out: int = A.op_Array_Access flow idx_out;
    let si = !sum_in;
    let so = !sum_out;
    sum_in := si + f_in;
    sum_out := so + f_out;
    v := vv +^ 1sz
  };
  let si = !sum_in;
  let so = !sum_out;
  (si = so)
}
#pop-options

(** Check conservation for all non-source, non-sink vertices *)
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
fn check_all_conservation
  (flow: A.array int)
  (n source sink: SZ.t)
  (#flow_seq: erased (Seq.seq int))
  requires
    A.pts_to flow flow_seq **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns ok: bool
  ensures
    A.pts_to flow flow_seq **
    pure (
      SZ.v n > 0 /\ Seq.length flow_seq == SZ.v n * SZ.v n /\
      (ok ==> (forall (w: nat). w < SZ.v n /\ w <> SZ.v source /\ w <> SZ.v sink ==>
        sum_flow_into flow_seq (SZ.v n) w (SZ.v n) == sum_flow_out flow_seq (SZ.v n) w (SZ.v n))))
{
  let mut u_idx = 0sz;
  let mut result = true;
  while (
    let vu = !u_idx;
    let vr = !result;
    vr && vu <^ n
  )
  invariant exists* vu vr.
    R.pts_to u_idx vu **
    R.pts_to result vr **
    A.pts_to flow flow_seq **
    pure (
      SZ.v vu <= SZ.v n /\
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      (vr ==> (forall (w: nat). w < SZ.v vu /\ w <> SZ.v source /\ w <> SZ.v sink ==>
        sum_flow_into flow_seq (SZ.v n) w (SZ.v n) == sum_flow_out flow_seq (SZ.v n) w (SZ.v n)))
    )
  {
    let vu = !u_idx;
    let ok_v = check_vertex_conservation flow n vu;
    if (not (vu = source) && not (vu = sink) && not ok_v)
    {
      result := false
    } else { () };
    u_idx := vu +^ 1sz
  };
  !result
}
#pop-options

(** Combined validity check with imp_valid_flow postcondition *)
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
fn check_imp_valid_flow_fn
  (flow capacity: A.array int)
  (n source sink: SZ.t)
  (#flow_seq #cap_seq: erased (Seq.seq int))
  requires
    A.pts_to flow flow_seq **
    A.pts_to capacity cap_seq **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns valid: bool
  ensures
    A.pts_to flow flow_seq **
    A.pts_to capacity cap_seq **
    pure (valid ==> imp_valid_flow flow_seq cap_seq (SZ.v n) (SZ.v source) (SZ.v sink))
{
  let nn = n *^ n;
  let cap_ok = check_capacity_fn flow capacity nn;
  let cons_ok = check_all_conservation flow n source sink;
  if (cap_ok && cons_ok) {
    lemma_checks_imply_valid_flow flow_seq cap_seq (SZ.v n) (SZ.v source) (SZ.v sink);
    true
  } else {
    false
  }
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
  returns valid: bool
  ensures exists* flow_seq'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq' **
    pure (
      Seq.length flow_seq' == SZ.v n * SZ.v n /\
      (valid ==> imp_valid_flow flow_seq' cap_seq (SZ.v n) (SZ.v source) (SZ.v sink))
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
      SZ.fits (SZ.v n * SZ.v n)
    )
  {
    let found = bfs_residual capacity flow color pred queue n source sink;

    if found
    {
      let bn = find_bottleneck_imp capacity flow pred n source sink;
      if (bn > 0) {
        augment_imp capacity flow pred n source sink bn
      } else {
        continue_loop := false
      };
    }
    else
    {
      continue_loop := false
    }
  };

  // Phase 4: Verify flow validity via runtime check
  let valid = check_imp_valid_flow_fn flow capacity n source sink;

  // Cleanup BFS workspace
  A.free color;
  A.free pred;
  A.free queue;
  valid
}
#pop-options
