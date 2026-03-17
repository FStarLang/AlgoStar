module CLRS.Ch26.MaxFlow.ImplTest
(* Spec validation test for CLRS Ch26 Max Flow (Edmonds-Karp).

   Source: Methodology adapted from the intent-formalization repository:
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/

   This test validates that the postcondition of max_flow is precise enough
   to uniquely determine the flow values for concrete instances.

   Test case: 2-vertex single-edge network
   - n=2, source=0, sink=1
   - cap[0→1]=7, all other capacities=0
   - Expected: flow[0→1]=7, flow_value=7 *)

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch26.MaxFlow.Spec
open CLRS.Ch26.MaxFlow.Impl
open CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

(* ================================================================
   Pure helper lemmas for postcondition completeness
   ================================================================ *)

#push-options "--z3rlimit 100 --fuel 4 --ifuel 2"

(* Helper to instantiate the universally quantified no_augmenting_path
   with a specific concrete path. *)
let instantiate_no_aug_path
  (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (sink: nat{sink < n})
  (path: list nat)
  : Lemma
    (requires
      no_augmenting_path #n cap flow source sink /\
      Cons? path /\ L.hd path = source /\ L.last path = sink /\
      (forall (v: nat). L.mem v path ==> v < n))
    (ensures bottleneck cap flow n path <= 0)
= ()

(* Completeness lemma for 2-vertex single-edge network.

   Network: n=2, s=0, t=1, cap[0→1]=7, all other capacities=0.

   Proves: valid_flow + no_augmenting_path uniquely determine:
     flow[0→1] = 7, flow[0→0] = 0, flow[1→0] = 0, flow[1→1] = 0

   Proof:
   1. valid_flow capacity constraints at zero-cap edges force those flows to 0
   2. no_augmenting_path for path [0;1] gives bottleneck([0;1]) <= 0
   3. Unfolding bottleneck: if 7 - flow[0,1] > 0 then bottleneck > 0, contradiction
   4. So flow[0,1] >= 7, combined with flow[0,1] <= 7 (capacity), gives flow[0,1] = 7 *)
let single_edge_completeness (flow_seq cap_seq: Seq.seq int)
  : Lemma
    (requires
      Seq.length flow_seq == 4 /\ Seq.length cap_seq == 4 /\
      valid_flow #2 flow_seq cap_seq 0 1 /\
      no_augmenting_path #2 cap_seq flow_seq 0 1 /\
      Seq.index cap_seq 0 == 0 /\
      Seq.index cap_seq 1 == 7 /\
      Seq.index cap_seq 2 == 0 /\
      Seq.index cap_seq 3 == 0)
    (ensures
      get flow_seq 2 0 1 == 7 /\
      get flow_seq 2 0 0 == 0 /\
      get flow_seq 2 1 0 == 0 /\
      get flow_seq 2 1 1 == 0)
= instantiate_no_aug_path #2 cap_seq flow_seq 0 1 [0; 1]

(* Flow value for the single-edge network: |f| = 7 *)
let single_edge_flow_value (flow_seq cap_seq: Seq.seq int)
  : Lemma
    (requires
      Seq.length flow_seq == 4 /\ Seq.length cap_seq == 4 /\
      valid_flow #2 flow_seq cap_seq 0 1 /\
      no_augmenting_path #2 cap_seq flow_seq 0 1 /\
      Seq.index cap_seq 0 == 0 /\
      Seq.index cap_seq 1 == 7 /\
      Seq.index cap_seq 2 == 0 /\
      Seq.index cap_seq 3 == 0)
    (ensures flow_value flow_seq 2 0 == 7)
= single_edge_completeness flow_seq cap_seq

(* MFMC theorem applied: flow_value = cut_capacity for some cut *)
let single_edge_mfmc (flow_seq cap_seq: Seq.seq int)
  : Lemma
    (requires
      Seq.length flow_seq == 4 /\ Seq.length cap_seq == 4 /\
      valid_flow #2 flow_seq cap_seq 0 1 /\
      no_augmenting_path #2 cap_seq flow_seq 0 1 /\
      Seq.index cap_seq 0 == 0 /\
      Seq.index cap_seq 1 == 7 /\
      Seq.index cap_seq 2 == 0 /\
      Seq.index cap_seq 3 == 0)
    (ensures
      (exists (s_set: nat -> bool).
        is_st_cut s_set 2 0 1 /\
        flow_value flow_seq 2 0 == cut_capacity #2 cap_seq s_set))
= max_flow_min_cut_theorem #2 cap_seq flow_seq 0 1

#pop-options

(* ================================================================
   Disconnected graph lemmas
   ================================================================ *)

#push-options "--z3rlimit 100 --fuel 4 --ifuel 2"

(* Completeness lemma for disconnected 2-vertex network.
   Network: n=2, s=0, t=1, all capacities=0.
   Proves: valid_flow + no_augmenting_path uniquely determine all flows = 0. *)
let disconnected_completeness (flow_seq cap_seq: Seq.seq int)
  : Lemma
    (requires
      Seq.length flow_seq == 4 /\ Seq.length cap_seq == 4 /\
      valid_flow #2 flow_seq cap_seq 0 1 /\
      Seq.index cap_seq 0 == 0 /\
      Seq.index cap_seq 1 == 0 /\
      Seq.index cap_seq 2 == 0 /\
      Seq.index cap_seq 3 == 0)
    (ensures
      get flow_seq 2 0 0 == 0 /\
      get flow_seq 2 0 1 == 0 /\
      get flow_seq 2 1 0 == 0 /\
      get flow_seq 2 1 1 == 0)
= ()

(* Flow value for disconnected network: |f| = 0 *)
let disconnected_flow_value (flow_seq cap_seq: Seq.seq int)
  : Lemma
    (requires
      Seq.length flow_seq == 4 /\ Seq.length cap_seq == 4 /\
      valid_flow #2 flow_seq cap_seq 0 1 /\
      Seq.index cap_seq 0 == 0 /\
      Seq.index cap_seq 1 == 0 /\
      Seq.index cap_seq 2 == 0 /\
      Seq.index cap_seq 3 == 0)
    (ensures flow_value flow_seq 2 0 == 0)
= disconnected_completeness flow_seq cap_seq

#pop-options

(* ================================================================
   Pulse test functions
   ================================================================ *)

#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"

```pulse
(* Completeness test: 2-vertex single-edge network.
   s=0, t=1, cap[0→1]=7, all other capacities=0.

   Validates:
   1. Precondition satisfiable: valid_caps established via check + intro
   2. Postcondition complete: proves flow[0→1] = 7, all other flows = 0
   3. Flow value correct: |f| = 7
   4. MFMC applicable: flow_value = min-cut capacity *)
fn test_max_flow_completeness ()
  requires emp
  returns _: unit
  ensures emp
{
  let n : SZ.t = 2sz;
  let nn : SZ.t = n *^ n;

  // Allocate capacity matrix (2×2 = 4 elements, all zeros)
  let cv = V.alloc 0 nn;
  V.to_array_pts_to cv;
  let capacity = V.vec_to_array cv;
  with sc. assert (A.pts_to (V.vec_to_array cv) sc);
  rewrite (A.pts_to (V.vec_to_array cv) sc) as (A.pts_to capacity sc);

  // Allocate flow matrix (2×2 = 4 elements, all zeros)
  let fv = V.alloc 0 nn;
  V.to_array_pts_to fv;
  let flow = V.vec_to_array fv;
  with sf. assert (A.pts_to (V.vec_to_array fv) sf);
  rewrite (A.pts_to (V.vec_to_array fv) sf) as (A.pts_to flow sf);

  // Set capacity: single edge 0→1 with capacity 7
  // Index 1 in 2×2 flat matrix = position (0,1) = edge 0→1
  A.op_Array_Assignment capacity 1sz 7;

  // Bind updated capacity ghost sequence
  with cap_seq. assert (A.pts_to capacity cap_seq);

  // Establish valid_caps via runtime check + intro lemma (no assume_)
  let caps_ok = check_valid_caps_fn capacity nn;
  if caps_ok {
    valid_caps_intro cap_seq (SZ.v n);

    // ========== CALL MAX_FLOW ==========
    let flow_val = max_flow capacity flow n 0sz 1sz;

    // ========== POSTCONDITION VALIDATION ==========
    // Bind flow result
    with flow_seq. assert (A.pts_to flow flow_seq);

    // Bridge: imp_valid_flow → Spec.valid_flow
    imp_valid_flow_implies_valid_flow flow_seq cap_seq 2 0 1;

    // Completeness: postcondition determines exact flow values
    single_edge_completeness flow_seq cap_seq;

    // Read back all flow values and verify against expected
    let f00 = flow.(0sz);
    let f01 = flow.(1sz);
    let f10 = flow.(2sz);
    let f11 = flow.(3sz);

    // These assertions prove the postcondition uniquely determines the output
    assert (pure (f01 == 7));  // flow[0→1] = 7 (max flow on the single edge)
    assert (pure (f00 == 0));  // flow[0→0] = 0 (self-loop, cap=0)
    assert (pure (f10 == 0));  // flow[1→0] = 0 (reverse edge, cap=0)
    assert (pure (f11 == 0));  // flow[1→1] = 0 (self-loop, cap=0)

    // Verify return value equals expected flow value
    single_edge_flow_value flow_seq cap_seq;
    lemma_imp_flow_value_eq flow_seq 2 0;
    assert (pure (flow_val == 7));

    // Verify MFMC theorem is applicable: flow_value = min-cut capacity
    single_edge_mfmc flow_seq cap_seq;

    // Cleanup
    with sc2. assert (A.pts_to capacity sc2);
    rewrite (A.pts_to capacity sc2) as (A.pts_to (V.vec_to_array cv) sc2);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf2. assert (A.pts_to flow sf2);
    rewrite (A.pts_to flow sf2) as (A.pts_to (V.vec_to_array fv) sf2);
    V.to_vec_pts_to fv;
    V.free fv;
  } else {
    // Unreachable: capacities [0;7;0;0] are non-negative
    with sc2. assert (A.pts_to capacity sc2);
    rewrite (A.pts_to capacity sc2) as (A.pts_to (V.vec_to_array cv) sc2);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf2. assert (A.pts_to flow sf2);
    rewrite (A.pts_to flow sf2) as (A.pts_to (V.vec_to_array fv) sf2);
    V.to_vec_pts_to fv;
    V.free fv;
  }
}
```

#pop-options

(* ================================================================
   Pulse test: Disconnected graph (flow_value = 0)
   ================================================================ *)

#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"

```pulse
(* Completeness test: 2-vertex disconnected network.
   s=0, t=1, all capacities=0.

   Validates:
   1. Precondition satisfiable: valid_caps for all-zero capacities
   2. Postcondition complete: proves all flow values = 0
   3. Return value correct: fv = 0
   4. Flow value correct: |f| = 0 *)
fn test_max_flow_disconnected_completeness ()
  requires emp
  returns _: unit
  ensures emp
{
  let n : SZ.t = 2sz;
  let nn : SZ.t = n *^ n;

  // Allocate capacity matrix (2×2 = 4 elements, all zeros)
  let cv = V.alloc 0 nn;
  V.to_array_pts_to cv;
  let capacity = V.vec_to_array cv;
  with sc. assert (A.pts_to (V.vec_to_array cv) sc);
  rewrite (A.pts_to (V.vec_to_array cv) sc) as (A.pts_to capacity sc);

  // Allocate flow matrix (2×2 = 4 elements, all zeros)
  let fv = V.alloc 0 nn;
  V.to_array_pts_to fv;
  let flow = V.vec_to_array fv;
  with sf. assert (A.pts_to (V.vec_to_array fv) sf);
  rewrite (A.pts_to (V.vec_to_array fv) sf) as (A.pts_to flow sf);

  // No edges — all capacities remain 0
  with cap_seq. assert (A.pts_to capacity cap_seq);

  // Establish valid_caps via runtime check + intro lemma
  let caps_ok = check_valid_caps_fn capacity nn;
  if caps_ok {
    valid_caps_intro cap_seq (SZ.v n);

    // ========== CALL MAX_FLOW ==========
    let flow_val = max_flow capacity flow n 0sz 1sz;

    // ========== POSTCONDITION VALIDATION ==========
    with flow_seq. assert (A.pts_to flow flow_seq);

    // Bridge: imp_valid_flow → Spec.valid_flow
    imp_valid_flow_implies_valid_flow flow_seq cap_seq 2 0 1;

    // Completeness: all-zero capacities force all flows to 0
    disconnected_completeness flow_seq cap_seq;

    // Read back all flow values and verify
    let f00 = flow.(0sz);
    let f01 = flow.(1sz);
    let f10 = flow.(2sz);
    let f11 = flow.(3sz);

    assert (pure (f00 == 0));
    assert (pure (f01 == 0));
    assert (pure (f10 == 0));
    assert (pure (f11 == 0));

    // Verify return value equals expected flow value (0)
    disconnected_flow_value flow_seq cap_seq;
    lemma_imp_flow_value_eq flow_seq 2 0;
    assert (pure (flow_val == 0));

    // Cleanup
    with sc2. assert (A.pts_to capacity sc2);
    rewrite (A.pts_to capacity sc2) as (A.pts_to (V.vec_to_array cv) sc2);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf2. assert (A.pts_to flow sf2);
    rewrite (A.pts_to flow sf2) as (A.pts_to (V.vec_to_array fv) sf2);
    V.to_vec_pts_to fv;
    V.free fv;
  } else {
    // Unreachable: all-zero capacities are non-negative
    with sc2. assert (A.pts_to capacity sc2);
    rewrite (A.pts_to capacity sc2) as (A.pts_to (V.vec_to_array cv) sc2);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf2. assert (A.pts_to flow sf2);
    rewrite (A.pts_to flow sf2) as (A.pts_to (V.vec_to_array fv) sf2);
    V.to_vec_pts_to fv;
    V.free fv;
  }
}
```

#pop-options
