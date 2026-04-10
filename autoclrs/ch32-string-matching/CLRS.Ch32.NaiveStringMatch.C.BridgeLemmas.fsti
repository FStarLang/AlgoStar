module CLRS.Ch32.NaiveStringMatch.C.BridgeLemmas
open CLRS.Ch32.NaiveStringMatch.Spec
module Seq = FStar.Seq
module SizeT = FStar.SizeT

let unwrap_val (o: option Int32.t) : Int32.t =
  match o with | Some v -> v | None -> 0l

let unwrap_seq (s: Seq.seq (option Int32.t)) (n: nat{n <= Seq.length s})
  : Tot (Seq.seq Int32.t) =
  Seq.init n (fun (i: nat{i < n}) -> unwrap_val (Seq.index s i))

val match_connection
    (vt: Seq.seq (option Int32.t))
    (vp: Seq.seq (option Int32.t))
    (n: nat) (m: nat) (s: nat) (j: nat)
    (all_match: int)
  : Lemma
    (requires
      m > 0 /\ s + m <= n /\ j <= m /\
      n <= Seq.length vt /\ m <= Seq.length vp /\
      SizeT.fits m /\
      (all_match = 0 \/ all_match = 1) /\
      (forall (i: nat). i < Seq.length vt ==> Some? (Seq.index vt i)) /\
      (forall (i: nat). i < Seq.length vp ==> Some? (Seq.index vp i)) /\
      (forall (k: SizeT.t). SizeT.v k < j ==>
        (Seq.index vt (s + SizeT.v k) = Seq.index vp (SizeT.v k))) /\
      (all_match = 0 ==> s + j < Seq.length vt ==> j < Seq.length vp ==>
        Seq.index vt (s + j) <> Seq.index vp j) /\
      (not (j < m && all_match = 1)))
    (ensures (j = m) = matches_at_dec (unwrap_seq vt n) (unwrap_seq vp m) s)
