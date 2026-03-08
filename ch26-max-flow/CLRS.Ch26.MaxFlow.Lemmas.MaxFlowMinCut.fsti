module CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut

open FStar.Mul
open FStar.List.Tot
open CLRS.Ch26.MaxFlow.Spec

module Seq = FStar.Seq
module L = FStar.List.Tot

(*
   Interface for the Max-Flow Min-Cut Theorem (CLRS Theorem 26.6).
   
   All proofs are complete with zero admits.
   
   Key results:
   - CLRS Lemma 26.4: |f| = net flow across any cut
   - CLRS Corollary 26.5: Weak duality |f| ≤ c(S,T)
   - CLRS Theorem 26.6: Max-flow min-cut (strong duality)
*)

(** CLRS Lemma 26.4: Flow value equals net flow across any s-t cut *)
val lemma_flow_value_eq_net_flow
  (#n: nat) (flow: flow_matrix n) (cap: capacity_matrix n)
  (source: nat{source < n}) (sink: nat{sink < n}) (s_set: nat -> bool)
  : Lemma
    (requires valid_flow flow cap source sink /\ is_st_cut s_set n source sink)
    (ensures flow_value flow n source == net_flow_across_cut flow s_set)

(** CLRS Corollary 26.5: Weak duality — |f| ≤ c(S,T) for any valid flow and s-t cut *)
val weak_duality (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                  (source: nat{source < n}) (sink: nat{sink < n})
                  (s_set: nat -> bool)
  : Lemma
    (requires valid_flow flow cap source sink /\
              is_st_cut s_set n source sink)
    (ensures flow_value flow n source <= cut_capacity cap s_set)

(** CLRS Theorem 26.6: Max-flow min-cut theorem.
    When no augmenting path exists in the residual graph,
//SNIPPET_START: max_flow_min_cut
    the flow value equals the capacity of some cut (strong duality). *)
val max_flow_min_cut_theorem (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                              (source: nat{source < n}) (sink: nat{sink < n})
  : Lemma
    (requires
      valid_flow flow cap source sink /\
      no_augmenting_path cap flow source sink)
    (ensures
      (exists (s_set: nat -> bool).
        is_st_cut s_set n source sink /\
        flow_value flow n source == cut_capacity cap s_set))
//SNIPPET_END: max_flow_min_cut
