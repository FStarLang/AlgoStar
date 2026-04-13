(*
   Interface for Matrix Multiply C Bridge Lemmas.

   Hides the definitions of dot_product_spec_c and helper functions
   from downstream modules (especially MatrixMultiply.fst) to prevent
   Z3 from unrolling recursive definitions and polluting the SMT context.

   Only the base case, step lemma, and type signatures are exported.
*)

module CLRS.Ch04.MatrixMultiply.C.BridgeLemmas

open FStar.Seq
open FStar.Mul
open CLRS.Ch04.MatrixMultiply.Spec
module Seq = FStar.Seq

// Convert c2pulse ghost sequence (option Int32.t) to plain int sequence
val to_int_seq (s: Seq.seq (option Int32.t)) : Tot (Seq.seq int)

// Length preservation
val to_int_seq_length (s: Seq.seq (option Int32.t))
  : Lemma (Seq.length (to_int_seq s) == Seq.length s)
    [SMTPat (Seq.length (to_int_seq s))]

// Element access bridge
val to_int_seq_index (s: Seq.seq (option Int32.t)) (i: nat)
  : Lemma (requires i < Seq.length s /\ Some? (Seq.index s i))
          (ensures Seq.length (to_int_seq s) == Seq.length s /\
                   Seq.index (to_int_seq s) i == Int32.v (Some?.v (Seq.index s i)))

// dot_product_spec over c2pulse representation
val dot_product_spec_c (sa sb: Seq.seq (option Int32.t)) (n i j limit: nat) : Tot int

// Base case: dot product with limit 0 is 0
val dot_product_spec_c_base (sa sb: Seq.seq (option Int32.t)) (n i j: nat)
  : Lemma (dot_product_spec_c sa sb n i j 0 == 0)
    [SMTPat (dot_product_spec_c sa sb n i j 0)]

// Step lemma: unfolds dot_product_spec_c by one recursive step.
val dot_product_spec_c_step (sa sb: Seq.seq (option Int32.t)) (n i j limit: nat)
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

// mat_mul_correct over c2pulse representation
val mat_mul_correct_c (sa sb sc: Seq.seq (option Int32.t)) (n: nat) : prop

// mat_mul_partial_ij over c2pulse representation
val mat_mul_partial_ij_c (sa sb sc: Seq.seq (option Int32.t)) (n ri cj: nat) : prop

// ── Bridge lemmas for matrix multiply functional correctness ─────
val to_int_seq_upd (s: Seq.seq (option Int32.t)) (idx: nat) (v: Int32.t)
  : Lemma
    (requires idx < Seq.length s)
    (ensures Seq.equal (to_int_seq (Seq.upd s idx (Some v)))
                       (Seq.upd (to_int_seq s) idx (Int32.v v)))
    [SMTPat (to_int_seq (Seq.upd s idx (Some v)))]

// mat_mul_partial_ij_c: base case (0, 0) is trivially true
val mat_mul_partial_ij_c_base (sa sb sc: Seq.seq (option Int32.t)) (n: nat)
  : Lemma
    (requires Seq.length sc == n * n)
    (ensures mat_mul_partial_ij_c sa sb sc n 0 0)
    [SMTPat (mat_mul_partial_ij_c sa sb sc n 0 0)]

// Update lemma: after writing the correct dot product at (ri,cj), advance to (ri, cj+1)
val mat_mul_partial_ij_c_update
    (sa sb sc: Seq.seq (option Int32.t)) (n ri cj: nat) (v: Int32.t)
  : Lemma
    (requires
      mat_mul_partial_ij_c sa sb sc n ri cj /\
      ri < n /\ cj < n /\ n > 0 /\
      Seq.length sc == n * n /\
      id #int (Int32.v v) == dot_product_spec_c sa sb n ri cj n)
    (ensures
      mat_mul_partial_ij_c sa sb (Seq.upd sc (flat_index n ri cj) (Some v)) n ri (cj + 1))

// Row advance: after completing row ri (all n columns), advance to (ri+1, 0)
val mat_mul_partial_ij_c_row_advance
    (sa sb sc: Seq.seq (option Int32.t)) (n ri: nat)
  : Lemma
    (requires mat_mul_partial_ij_c sa sb sc n ri n /\ ri < n /\ n > 0)
    (ensures mat_mul_partial_ij_c sa sb sc n (ri + 1) 0)

// Complete: after all rows done, full correctness holds
val mat_mul_partial_ij_c_complete
    (sa sb sc: Seq.seq (option Int32.t)) (n: nat)
  : Lemma
    (requires mat_mul_partial_ij_c sa sb sc n n 0 /\ n > 0)
    (ensures mat_mul_correct_c sa sb sc n)
    [SMTPat (mat_mul_partial_ij_c sa sb sc n n 0)]
