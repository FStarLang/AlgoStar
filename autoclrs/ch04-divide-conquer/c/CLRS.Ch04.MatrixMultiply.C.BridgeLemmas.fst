(*
   Matrix Multiply C Bridge Lemmas — connecting c2pulse array model to F* spec

   Provides:
   - to_int_seq: convert c2pulse ghost seq (option Int32.t) to Seq.seq int
   - dot_product_spec_c: dot_product_spec over c2pulse representation
   - mat_mul_correct_c: mat_mul_correct over c2pulse representation
   - mat_mul_partial_ij_c: mat_mul_partial_ij over c2pulse representation

   Used by MatrixMultiply.c via _include_pulse to prove functional correctness
   matching CLRS.Ch04.MatrixMultiply.Impl.fsti.

   NO admits. NO assumes.
*)

module CLRS.Ch04.MatrixMultiply.C.BridgeLemmas

open FStar.Seq
open FStar.Mul
open CLRS.Ch04.MatrixMultiply.Spec
module Seq = FStar.Seq

// Convert c2pulse ghost sequence (option Int32.t) to plain int sequence
let to_int_seq (s: Seq.seq (option Int32.t)) : Tot (Seq.seq int) =
  Seq.init (Seq.length s) (fun i ->
    match Seq.index s i with
    | Some v -> Int32.v v
    | None -> 0)

// Length preservation
let to_int_seq_length (s: Seq.seq (option Int32.t))
  : Lemma (Seq.length (to_int_seq s) == Seq.length s)
  = ()

// Element access bridge
let to_int_seq_index (s: Seq.seq (option Int32.t)) (i: nat)
  : Lemma (requires i < Seq.length s /\ Some? (Seq.index s i))
          (ensures Seq.index (to_int_seq s) i == Int32.v (Some?.v (Seq.index s i)))
  = ()

// dot_product_spec over c2pulse representation
let dot_product_spec_c (sa sb: Seq.seq (option Int32.t)) (n i j limit: nat) : Tot int =
  dot_product_spec (to_int_seq sa) (to_int_seq sb) n i j limit

// Step lemma: unfolds dot_product_spec_c by one recursive step.
// SMT pattern triggers automatically during k-loop invariant proof.
let dot_product_spec_c_step (sa sb: Seq.seq (option Int32.t)) (n i j limit: nat)
  : Lemma
    (requires
      limit > 0 /\ limit <= n /\ i < n /\ j < n /\ n > 0 /\
      Seq.length sa == n * n /\ Seq.length sb == n * n /\
      Some? (Seq.index sa (flat_index n i (limit - 1))) /\
      Some? (Seq.index sb (flat_index n (limit - 1) j)))
    (ensures
      dot_product_spec_c sa sb n i j limit ==
      dot_product_spec_c sa sb n i j (limit - 1) +
      Int32.v (Some?.v (Seq.index sa (flat_index n i (limit - 1)))) *
      Int32.v (Some?.v (Seq.index sb (flat_index n (limit - 1) j))))
    [SMTPat (dot_product_spec_c sa sb n i j limit)]
  = to_int_seq_length sa;
    to_int_seq_length sb;
    to_int_seq_index sa (flat_index n i (limit - 1));
    to_int_seq_index sb (flat_index n (limit - 1) j)

// mat_mul_correct over c2pulse representation
let mat_mul_correct_c (sa sb sc: Seq.seq (option Int32.t)) (n: nat) : prop =
  mat_mul_correct (to_int_seq sa) (to_int_seq sb) (to_int_seq sc) n

// mat_mul_partial_ij over c2pulse representation
let mat_mul_partial_ij_c (sa sb sc: Seq.seq (option Int32.t)) (n ri cj: nat) : prop =
  mat_mul_partial_ij (to_int_seq sa) (to_int_seq sb) (to_int_seq sc) n ri cj
