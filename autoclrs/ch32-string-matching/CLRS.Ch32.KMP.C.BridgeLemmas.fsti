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

/// ---- compute_prefix bridge lemmas ----

module Bridge = CLRS.Ch32.KMP.Bridge

/// Partial pi maximality for int sequences (mirrors Bridge.pi_max_sz_up_to).
/// Marked opaque_to_smt so that Z3 never sees the internal quantifiers in
/// generated Pulse VCs, preventing trigger cascading.
[@@ "opaque_to_smt"]
let pi_max_up_to_int (pattern: Seq.seq int) (pi: Seq.seq int) (bound: nat) : prop =
  bound <= Seq.length pattern /\
  Seq.length pi >= Seq.length pattern /\
  Seq.length pattern > 0 /\
  (forall (q: nat). q < bound ==> Seq.index pi q >= 0) /\
  (forall (q: nat). q < bound ==>
    is_prefix_suffix #int pattern q (Seq.index pi q)) /\
  (forall (q: nat) (k: nat). q < bound /\ is_prefix_suffix #int pattern q k ==>
    k <= Seq.index pi q)

/// Base case: pi[0] = 0 implies maximality for bound = 1
val maximality_base_int (pattern pi: Seq.seq int)
  : Lemma (requires Seq.length pattern > 0 /\ Seq.length pi >= Seq.length pattern /\
                    Seq.index pi 0 == 0)
          (ensures pi_max_up_to_int pattern pi 1)

/// Extract validity at a specific position from opaque pi_max_up_to_int
val pi_max_instantiate_int (pattern pi: Seq.seq int) (bound: nat) (r: nat)
  : Lemma (requires pi_max_up_to_int pattern pi bound /\ r < bound /\
                    bound <= Seq.length pattern /\ Seq.length pi >= Seq.length pattern)
          (ensures Seq.index pi r >= 0 /\ is_prefix_suffix #int pattern r (Seq.index pi r))

/// Extract maximality at a specific (r, k) from opaque pi_max_up_to_int
val pi_max_max_at_int (pattern pi: Seq.seq int) (bound: nat) (r: nat) (k: nat)
  : Lemma (requires pi_max_up_to_int pattern pi bound /\ r < bound /\
                    bound <= Seq.length pattern /\ Seq.length pi >= Seq.length pattern /\
                    is_prefix_suffix #int pattern r k)
          (ensures k <= Seq.index pi r)

/// Init inner loop mismatch invariant
val inner_init_int (pattern pi: Seq.seq int)
    (q: nat{0 < q /\ q < Seq.length pattern}) (k: nat)
  : Lemma (requires pi_max_up_to_int pattern pi q /\
                    Seq.length pi >= Seq.length pattern /\
                    k == Seq.index pi (q - 1))
          (ensures Bridge.all_ps_above_mismatch #int pattern q k)

/// Inner step: extend mismatch when following failure link
val inner_step_int (pattern pi: Seq.seq int)
    (q: nat{0 < q /\ q < Seq.length pattern}) (k: nat) (k_new: nat)
  : Lemma
    (requires pi_max_up_to_int pattern pi q /\
             Seq.length pi >= Seq.length pattern /\
             k > 0 /\ k <= q - 1 /\ k < Seq.length pattern /\
             is_prefix_suffix #int pattern (q - 1) k /\
             Seq.index pattern k <> Seq.index pattern q /\
             Bridge.all_ps_above_mismatch #int pattern q k /\
             k_new == Seq.index pi (k - 1) /\
             is_prefix_suffix #int pattern (k - 1) k_new)
    (ensures Bridge.all_ps_above_mismatch #int pattern q k_new /\
             is_prefix_suffix #int pattern (q - 1) k_new)

/// Bridge: option-level sequence update to int-level
val unwrap_seq_update (s: Seq.seq (option Int32.t)) (m q: nat) (v: Int32.t)
  : Lemma (requires q < m /\ m <= Seq.length s)
          (ensures
            (forall (r: nat). r < m /\ r <> q ==>
              Seq.index (unwrap_int_seq (Seq.upd s q (Some v)) m) r ==
              Seq.index (unwrap_int_seq s m) r) /\
            Seq.index (unwrap_int_seq (Seq.upd s q (Some v)) m) q == Int32.v v)

/// Extend maximality from q to q+1 after writing pi[q]
val extend_maximality_int (pattern pi_old pi_new: Seq.seq int)
    (q: nat{0 < q /\ q < Seq.length pattern}) (k_final: nat) (chars_match: bool)
  : Lemma
    (requires pi_max_up_to_int pattern pi_old q /\
             Seq.length pi_old >= Seq.length pattern /\
             Seq.length pi_new >= Seq.length pattern /\
             (forall (r: nat). r < q ==> Seq.index pi_new r == Seq.index pi_old r) /\
             is_prefix_suffix #int pattern (q - 1) k_final /\
             k_final < Seq.length pattern /\
             Bridge.all_ps_above_mismatch #int pattern q k_final /\
             (chars_match ==> Seq.index pattern k_final == Seq.index pattern q) /\
             (not chars_match ==> (k_final == 0 /\ Seq.index pattern k_final <> Seq.index pattern q)) /\
             Seq.index pi_new q == (if chars_match then k_final + 1 else k_final))
    (ensures pi_max_up_to_int pattern pi_new (q + 1))

/// Convert full-bound partial to full pi_max
val up_to_full_int (pattern pi: Seq.seq int)
  : Lemma (requires pi_max_up_to_int pattern pi (Seq.length pattern) /\
                    Seq.length pi == Seq.length pattern)
          (ensures pi_max pattern pi)
