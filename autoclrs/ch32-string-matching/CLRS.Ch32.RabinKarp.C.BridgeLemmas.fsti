module CLRS.Ch32.RabinKarp.C.BridgeLemmas
open CLRS.Ch32.RabinKarp.Spec
module Seq = FStar.Seq
module SizeT = FStar.SizeT

/// Convert option Int32.t to nat (defaulting negative/None to 0)
let unwrap_nat_val (o: option Int32.t) : nat =
  match o with | Some v -> if Int32.v v >= 0 then Int32.v v else 0 | None -> 0

/// Convert a prefix of an option Int32.t sequence to a nat sequence
let unwrap_nat_seq (s: Seq.seq (option Int32.t)) (n: nat{n <= Seq.length s})
  : Tot (Seq.seq nat) =
  Seq.init n (fun (i: nat{i < n}) -> unwrap_nat_val (Seq.index s i))

/// Counting function using RabinKarp.Spec.matches_at_dec
let rec count_matches_up_to (text pattern: Seq.seq nat) (limit: nat)
  : Tot nat (decreases limit) =
  if limit = 0 then 0
  else count_matches_up_to text pattern (limit - 1) +
       (if matches_at_dec text pattern (limit - 1) then 1 else 0)

val count_matches_up_to_unfold (text pattern: Seq.seq nat) (limit: nat)
  : Lemma (requires limit > 0)
          (ensures count_matches_up_to text pattern limit ==
                   count_matches_up_to text pattern (limit - 1) +
                   (if matches_at_dec text pattern (limit - 1) then 1 else 0))

val count_matches_up_to_bounded (text pattern: Seq.seq nat) (limit: nat)
  : Lemma (ensures count_matches_up_to text pattern limit <= limit)

/// Bridge lemma: connects array-level option equality to spec-level matches_at_dec
val match_connection
    (vt: Seq.seq (option Int32.t))
    (vp: Seq.seq (option Int32.t))
    (n: nat) (m: nat) (s: nat) (j: nat)
    (all_match: int)
  : Lemma
    (requires
      m > 0 /\ s + m <= n /\ j <= m /\
      n <= Seq.length vt /\ m <= Seq.length vp /\
      SizeT.fits n /\
      (all_match = 0 \/ all_match = 1) /\
      (forall (i: nat). i < Seq.length vt ==> Some? (Seq.index vt i)) /\
      (forall (i: nat). i < Seq.length vp ==> Some? (Seq.index vp i)) /\
      (forall (k: SizeT.t). SizeT.v k < n ==>
        Int32.v (Some?.v (Seq.index vt (SizeT.v k))) >= 0) /\
      (forall (k: SizeT.t). SizeT.v k < m ==>
        Int32.v (Some?.v (Seq.index vp (SizeT.v k))) >= 0) /\
      (forall (k: SizeT.t). SizeT.v k < j ==>
        (Seq.index vt (s + SizeT.v k) = Seq.index vp (SizeT.v k))) /\
      (all_match = 0 ==> s + j < Seq.length vt ==> j < Seq.length vp ==>
        Seq.index vt (s + j) <> Seq.index vp j) /\
      (not (j < m && all_match = 1)))
    (ensures (j = m) = matches_at_dec (unwrap_nat_seq vt n) (unwrap_nat_seq vp m) s)
