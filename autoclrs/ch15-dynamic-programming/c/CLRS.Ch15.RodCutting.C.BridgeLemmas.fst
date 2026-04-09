module CLRS.Ch15.RodCutting.C.BridgeLemmas

open FStar.Seq
module I32 = FStar.Int32

open CLRS.Ch15.RodCutting.Spec

let to_nat_seq (s: seq (option I32.t)) : seq nat =
  Seq.init (Seq.length s) (fun i -> (
    match Seq.index s i with
    | Some x -> let v = I32.v x in if v >= 0 then v else 0
    | None -> 0
  ) <: nat)

let to_nat_seq_length (s: seq (option I32.t))
  : Lemma (ensures Seq.length (to_nat_seq s) = Seq.length s)
          [SMTPat (Seq.length (to_nat_seq s))]
  = ()

let to_nat_seq_index (s: seq (option I32.t)) (i: nat)
  : Lemma (requires i < Seq.length s /\ Some? (Seq.index s i) /\ I32.v (Some?.v (Seq.index s i)) >= 0)
          (ensures Seq.index (to_nat_seq s) i == (let v = I32.v (Some?.v (Seq.index s i)) in if v >= 0 then v else 0))
          [SMTPat (Seq.index (to_nat_seq s) i)]
  = ()
