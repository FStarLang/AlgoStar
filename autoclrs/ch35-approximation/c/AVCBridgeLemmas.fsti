module AVCBridgeLemmas

(**
 * Bridge lemmas connecting c2pulse's option Int32.t representation
 * (used by AVCHelper) to the pure int representation (used by
 * CLRS.Ch35.VertexCover.Spec).
 *
 * Enables expressing Spec-level postconditions for the C implementation.
 *)

open FStar.Mul
module Seq = FStar.Seq
module Spec = CLRS.Ch35.VertexCover.Spec

(** Convert an option Int32.t sequence to an int sequence.
    Some x  ↦  Int32.v x
    None    ↦  0 *)
val to_int_seq (s: Seq.seq (option Int32.t)) : Seq.seq int

val to_int_seq_length (s: Seq.seq (option Int32.t))
  : Lemma (ensures Seq.length (to_int_seq s) = Seq.length s)
          [SMTPat (Seq.length (to_int_seq s))]

val to_int_seq_index (s: Seq.seq (option Int32.t)) (i: nat)
  : Lemma (requires i < Seq.length s)
          (ensures Seq.index (to_int_seq s) i = AVCHelper.seq_val s i)
          [SMTPat (Seq.index (to_int_seq s) i)]

(** Bridge: outer_inv_pure at loop exit implies Spec.is_cover *)
val outer_inv_implies_is_cover
  (sa sc: Seq.seq (option Int32.t)) (n: nat)
  : Lemma (requires AVCHelper.outer_inv_pure sa sc n n)
          (ensures Spec.is_cover (to_int_seq sa) (to_int_seq sc) n n 0)

(** Bridge: AVCHelper.binary implies binary on int sequence *)
val binary_implies_binary_int
  (sc: Seq.seq (option Int32.t)) (n: nat)
  : Lemma (requires AVCHelper.binary sc n /\ Seq.length sc = n)
          (ensures forall (i: nat). i < n ==>
            (Seq.index (to_int_seq sc) i = 0 \/ Seq.index (to_int_seq sc) i = 1))

(** Combined bridge: outer_inv_pure ⟹ Spec-level properties *)
val bridge_full
  (sa sc: Seq.seq (option Int32.t)) (n: nat)
  : Lemma (requires AVCHelper.outer_inv_pure sa sc n n)
          (ensures (
            let s_adj = to_int_seq sa in
            let s_cover = to_int_seq sc in
            Spec.is_cover s_adj s_cover n n 0 /\
            (forall (i: nat). i < n ==>
              (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
            (exists (opt: nat). Spec.min_vertex_cover_size s_adj n opt)))
