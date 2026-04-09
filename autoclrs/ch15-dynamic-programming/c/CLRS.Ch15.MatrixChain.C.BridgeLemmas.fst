module CLRS.Ch15.MatrixChain.C.BridgeLemmas

open FStar.Seq
module I32 = FStar.Int32

open CLRS.Ch15.MatrixChain.Spec

let to_int_seq (s: seq (option I32.t)) : seq int =
  Seq.init (Seq.length s) (fun i ->
    match Seq.index s i with
    | Some x -> I32.v x
    | None -> 0)

let to_int_seq_length (s: seq (option I32.t))
  : Lemma (ensures Seq.length (to_int_seq s) = Seq.length s)
          [SMTPat (Seq.length (to_int_seq s))]
  = ()

let to_int_seq_index (s: seq (option I32.t)) (i: nat)
  : Lemma (requires i < Seq.length s /\ Some? (Seq.index s i))
          (ensures Seq.index (to_int_seq s) i == I32.v (Some?.v (Seq.index s i)))
          [SMTPat (Seq.index (to_int_seq s) i)]
  = ()
