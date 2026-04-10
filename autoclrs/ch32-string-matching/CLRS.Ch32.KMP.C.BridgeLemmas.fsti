module CLRS.Ch32.KMP.C.BridgeLemmas
open CLRS.Ch32.KMP.PureDefs
open CLRS.Ch32.KMP.Spec
module Seq = FStar.Seq
module SizeT = FStar.SizeT

/// Safe int-to-nat coercion (equals x when x >= 0)
let to_nat (x: int) : nat = if x >= 0 then x else 0

/// Convert option Int32 to int (for c2pulse option-array bridge)
let unwrap_int_val (o: option Int32.t) : int =
  match o with | Some v -> Int32.v v | None -> 0

/// Convert option-array ghost sequence to int sequence
let unwrap_int_seq (s: Seq.seq (option Int32.t)) (n: nat{n <= Seq.length s})
  : Tot (Seq.seq int) =
  Seq.init n (fun (i: nat{i < n}) -> unwrap_int_val (Seq.index s i))

/// follow_fail unfolds one step when k > 0 and pattern[k] != c
val follow_fail_step (pattern pi: Seq.seq int) (k: nat) (c: int)
  : Lemma
    (requires pi_max pattern pi /\ k > 0 /\ k < Seq.length pattern /\
              Seq.index pattern k <> c)
    (ensures follow_fail pattern pi k c ==
             follow_fail pattern pi (Seq.index pi (k - 1)) c)

/// is_max_prefix_below base case: at position 0, q=0 is the max prefix
val is_max_prefix_below_init (text pattern: Seq.seq int) (n m: nat)
  : Lemma
    (requires m > 0 /\ n >= m /\
              Seq.length text == n /\ Seq.length pattern == m)
    (ensures is_max_prefix_below text pattern 0 0)

/// Connect C loop operations to kmp_step_result.
/// After inner failure-chain loop exits:
///   q_final = 0 \/ pattern[q_final] = c  (from break/exit condition)
///   follow_fail pattern pi q_init c == follow_fail pattern pi q_final c
val kmp_extend_connection (pattern pi: Seq.seq int) (q_init q_final: nat)
  (c: int) (m: nat)
  : Lemma
    (requires m > 0 /\ m == Seq.length pattern /\ m == Seq.length pi /\
              pi_max pattern pi /\
              q_init < m /\ q_final < m /\ q_final <= q_init /\
              follow_fail pattern pi q_init c ==
                follow_fail pattern pi q_final c /\
              (q_final = 0 \/ Seq.index pattern q_final = c))
    (ensures
      (let q_extend =
        if Seq.index pattern q_final = c then q_final + 1
        else q_final in
       q_extend == kmp_step_result pattern pi q_init c m))

/// Bridge option-level Seq.index to int-level unwrap_int_seq index
val unwrap_seq_index_lemma (s: Seq.seq (option Int32.t)) (m q: nat)
  : Lemma (requires q < m /\ m <= Seq.length s)
          (ensures Seq.index (unwrap_int_seq s m) q == unwrap_int_val (Seq.index s q))

/// count_before at n-m+1 equals count_matches_spec
val count_finish (vt vp: Seq.seq (option Int32.t)) (n m: nat)
  : Lemma
    (requires n >= m /\ m > 0 /\
              n <= Seq.length vt /\ m <= Seq.length vp)
    (ensures
      count_before (unwrap_int_seq vt n) (unwrap_int_seq vp m) (n - m + 1) ==
      count_matches_spec (unwrap_int_seq vt n) (unwrap_int_seq vp m) n m)
