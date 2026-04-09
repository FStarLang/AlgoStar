(*
   Kadane C Bridge Lemmas — connecting c2pulse array model to F* spec

   Provides:
   - to_int_seq: convert c2pulse ghost seq (option Int32.t) to Seq.seq int
   - max_subarray_spec_c: max_subarray_spec over c2pulse representation
   - kadane_spec_c: kadane_spec over c2pulse representation

   Used by Kadane.c via _include_pulse to tighten the C postcondition
   to match CLRS.Ch04.MaxSubarray.Kadane.fsti.

   NO admits. NO assumes.
*)

module CLRS.Ch04.Kadane.C.BridgeLemmas

open FStar.Seq
open CLRS.Ch04.MaxSubarray.Spec
module Seq = FStar.Seq

// Convert c2pulse ghost sequence (option Int32.t) to plain int sequence
let to_int_seq (s: Seq.seq (option Int32.t)) : Tot (Seq.seq int) =
  Seq.init (Seq.length s) (fun i ->
    match Seq.index s i with
    | Some v -> Int32.v v
    | None -> 0)

// Max subarray spec applied to c2pulse array representation
let max_subarray_spec_c (s: Seq.seq (option Int32.t)) : Tot int =
  max_subarray_spec (to_int_seq s)

// Kadane spec applied to c2pulse array representation
let kadane_spec_c (s: Seq.seq (option Int32.t)) (i: nat) (cur best: int)
  : Pure int (requires i <= Seq.length s) (ensures fun _ -> True) =
  kadane_spec (to_int_seq s) i cur best

// Bridge: element access through to_int_seq matches Int32.v of option value
let bridge_element (s: Seq.seq (option Int32.t)) (i: nat)
  : Lemma (requires i < Seq.length s /\ Some? (Seq.index s i))
          (ensures Seq.index (to_int_seq s) i == Int32.v (Some?.v (Seq.index s i)))
  = ()
