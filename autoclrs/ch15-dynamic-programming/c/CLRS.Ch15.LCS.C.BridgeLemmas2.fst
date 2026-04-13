module CLRS.Ch15.LCS.C.BridgeLemmas2

open FStar.Seq
open CLRS.Ch15.LCS.Spec

(* Bridge: lcs_length result is bounded by m and n.
   Used to establish tight upper bounds on the C implementation result. *)
let lcs_result_upper_bound (x y: seq int) (m n: nat)
  : Lemma
      (requires m == Seq.length x /\ n == Seq.length y)
      (ensures lcs_length x y m n <= m /\ lcs_length x y m n <= n)
  = lcs_length_upper_bound x y m n
