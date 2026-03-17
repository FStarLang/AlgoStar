module CLRS.Ch26.MaxFlow.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch26.MaxFlow.Spec

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq

(*
   Public interface for the Ford-Fulkerson (Edmonds-Karp) implementation.
   
   Provides:
   - valid_caps: precondition for non-negative capacities
   - imp_valid_flow: postcondition for valid flow in flat array representation
   - check_valid_caps_fn: runtime capacity validation
   - max_flow: main entry point computing maximum flow
*)

(** Maximum signed integer constant used as bottleneck sentinel *)
val int_max : int

(** Total wrapper for sequence indexing (returns 0 if out-of-bounds) *)
val seq_get (s: Seq.seq int) (i: nat) : int

(** Total wrapper for SizeT sequence indexing *)
val seq_get_sz (s: Seq.seq SZ.t) (i: nat) : SZ.t

(** Valid non-negative capacities *)
val valid_caps (cap_seq: Seq.seq int) (n: nat) : prop

(** Imperative flow validity: capacity constraints + flow conservation *)
val imp_valid_flow (flow_seq cap_seq: Seq.seq int) (n source sink: nat) : prop

(** Total wrapper for flow_value — avoids refinement types in Pulse ensures clauses *)
val imp_flow_value (s: Seq.seq int) (n source: nat) : int

(** imp_flow_value agrees with flow_value when constraints hold *)
val lemma_imp_flow_value_eq (s: Seq.seq int) (n source: nat)
  : Lemma
    (requires n > 0 /\ source < n /\ Seq.length s == n * n)
    (ensures imp_flow_value s n source == flow_value s n source)

//SNIPPET_START: imp_valid_flow_bridge
(** Bridge lemma: imp_valid_flow implies Spec.valid_flow.
    Allows callers to use the MFMC theorem with the result of max_flow. *)
val imp_valid_flow_implies_valid_flow (flow_seq cap_seq: Seq.seq int) (n source sink: nat)
  : Lemma
    (requires imp_valid_flow flow_seq cap_seq n source sink)
    (ensures
      n > 0 /\ source < n /\ sink < n /\
      Seq.length flow_seq == n * n /\ Seq.length cap_seq == n * n /\
      valid_flow #n flow_seq cap_seq source sink)
//SNIPPET_END: imp_valid_flow_bridge

(** Introduction lemma for valid_caps: allows callers to establish valid_caps
    from its constituent parts (needed since valid_caps is abstract). *)
val valid_caps_intro (cap_seq: Seq.seq int) (n: nat)
  : Lemma
    (requires Seq.length cap_seq == n * n /\ (forall (i: nat). i < n * n ==> Seq.index cap_seq i >= 0))
    (ensures valid_caps cap_seq n)

(** Runtime check for valid capacities *)
fn check_valid_caps_fn
  (capacity: A.array int)
  (nn: SZ.t)
  (#cap_seq: erased (Seq.seq int))
  requires
    A.pts_to capacity cap_seq **
    pure (Seq.length cap_seq == SZ.v nn)
  returns ok: bool
  ensures
    A.pts_to capacity cap_seq **
    pure (
      Seq.length cap_seq == SZ.v nn /\
      (ok ==> (forall (i: nat). i < SZ.v nn ==> Seq.index cap_seq i >= 0)))

(** Compute maximum flow using Edmonds-Karp (BFS-based Ford-Fulkerson).
    
    Parameters:
    - capacity: n×n flat capacity matrix (read-only)
    - flow: n×n flat flow matrix (output, overwritten)
    - n: number of vertices
    - source, sink: source and sink vertex indices
    
    Termination: proved without fuel. Each augmentation increases flow_value by ≥1,
    bounded by cap_sum = Σ cap[source][v]. Loop terminates in at most cap_sum + 1 iterations.
    
    Returns: the maximum flow value (== imp_flow_value of the result flow matrix).
    
    Postcondition:
    - imp_valid_flow on the resulting flow array
    - no_augmenting_path: no residual source→sink path exists (max flow achieved)
    - fv == imp_flow_value: return value equals the flow value of the result
    - fv >= 0: flow value is non-negative
    - Combined with bridge lemma → enables the MFMC theorem *)
//SNIPPET_START: max_flow_sig
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
  returns fv: int
  ensures exists* flow_seq'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq' **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq' == SZ.v n * SZ.v n /\
      imp_valid_flow flow_seq' cap_seq (SZ.v n) (SZ.v source) (SZ.v sink) /\
      no_augmenting_path #(SZ.v n) cap_seq flow_seq' (SZ.v source) (SZ.v sink) /\
      fv == imp_flow_value flow_seq' (SZ.v n) (SZ.v source) /\
      fv >= 0
    )
//SNIPPET_END: max_flow_sig
