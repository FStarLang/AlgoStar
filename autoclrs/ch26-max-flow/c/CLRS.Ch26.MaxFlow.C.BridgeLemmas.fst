module CLRS.Ch26.MaxFlow.C.BridgeLemmas

(*
   Bridge lemmas connecting the c2pulse-generated Max_flow module
   to the pure CLRS.Ch26.MaxFlow.Spec definitions.

   The c2pulse array model uses Seq.seq (option Int32.t) while
   the Spec module uses Seq.seq int with get/set helpers.
   This module provides:
   1. seq_val / seq_val_sz: extract int/nat from option sequences
   2. c_valid_flow / c_flow_value: Spec predicates phrased over c2pulse seqs
   3. all_nonneg_caps: capacity validity in c2pulse representation
   4. c_no_augmenting_path: no augmenting path in c2pulse representation
*)

module Seq = FStar.Seq
open FStar.Mul
open CLRS.Ch26.MaxFlow.Spec

(** Extract int value from c2pulse option-Int32 sequence (total, default 0) *)
let seq_val (s: Seq.seq (option Int32.t)) (i: nat) : int =
  if i < Seq.length s
  then match Seq.index s i with
       | Some x -> Int32.v x
       | None -> 0
  else 0

(** Extract nat value from c2pulse option-SizeT sequence (total, default 0) *)
let seq_val_sz (s: Seq.seq (option SizeT.t)) (i: nat) : nat =
  if i < Seq.length s
  then match Seq.index s i with
       | Some x -> SizeT.v x
       | None -> 0
  else 0

(** Convert c2pulse option sequence to plain int sequence *)
let rec to_int_seq (s: Seq.seq (option Int32.t)) (i: nat)
  : Tot (Seq.seq int) (decreases (Seq.length s - i))
  = if i >= Seq.length s then Seq.empty
    else
      let v = match Seq.index s i with
              | Some x -> Int32.v x
              | None -> 0 in
      Seq.cons v (to_int_seq s (i + 1))

let to_int_seq_full (s: Seq.seq (option Int32.t)) : Seq.seq int =
  to_int_seq s 0

(** Length of converted sequence equals original *)
let rec lemma_to_int_seq_length (s: Seq.seq (option Int32.t)) (i: nat)
  : Lemma (ensures Seq.length (to_int_seq s i) ==
             (if i >= Seq.length s then 0 else Seq.length s - i))
          (decreases (Seq.length s - i))
  = if i >= Seq.length s then ()
    else lemma_to_int_seq_length s (i + 1)

let lemma_to_int_seq_full_length (s: Seq.seq (option Int32.t))
  : Lemma (ensures Seq.length (to_int_seq_full s) == Seq.length s)
  = lemma_to_int_seq_length s 0

(** Index into converted sequence equals seq_val *)
let rec lemma_to_int_seq_index (s: Seq.seq (option Int32.t)) (i: nat) (j: nat)
  : Lemma (requires i + j < Seq.length s)
          (ensures (lemma_to_int_seq_length s i;
                    Seq.index (to_int_seq s i) j == seq_val s (i + j)))
          (decreases j)
  = lemma_to_int_seq_length s i;
    if j = 0 then ()
    else lemma_to_int_seq_index s (i + 1) (j - 1)

(** Capacity constraint in c2pulse representation:
    0 ≤ flow[u*n+v] ≤ cap[u*n+v] for all u,v < n *)
let c_capacity_constraint
    (flow_s cap_s: Seq.seq (option Int32.t))
    (n: nat) : prop =
  Seq.length flow_s == n * n /\
  Seq.length cap_s == n * n /\
  (forall (u v: nat). u < n /\ v < n ==>
    0 <= seq_val flow_s (u * n + v) /\
    seq_val flow_s (u * n + v) <= seq_val cap_s (u * n + v))

(** Sum of flow into vertex v from vertices 0..k-1 (c2pulse version) *)
let rec c_sum_flow_into (flow_s: Seq.seq (option Int32.t))
    (n: nat{Seq.length flow_s == n * n}) (v: nat{v < n}) (k: nat)
  : Tot int (decreases k)
  = if k = 0 then 0
    else if k - 1 < n then seq_val flow_s ((k - 1) * n + v) + c_sum_flow_into flow_s n v (k - 1)
    else c_sum_flow_into flow_s n v (k - 1)

(** Sum of flow out of vertex v to vertices 0..k-1 (c2pulse version) *)
let rec c_sum_flow_out (flow_s: Seq.seq (option Int32.t))
    (n: nat{Seq.length flow_s == n * n}) (v: nat{v < n}) (k: nat)
  : Tot int (decreases k)
  = if k = 0 then 0
    else if k - 1 < n then seq_val flow_s (v * n + (k - 1)) + c_sum_flow_out flow_s n v (k - 1)
    else c_sum_flow_out flow_s n v (k - 1)

(** Flow conservation in c2pulse representation *)
let c_flow_conservation
    (flow_s: Seq.seq (option Int32.t))
    (n source sink: nat) : prop =
  n > 0 /\ source < n /\ sink < n /\
  Seq.length flow_s == n * n /\
  (forall (u: nat). u < n /\ u <> source /\ u <> sink ==>
    c_sum_flow_into flow_s n u n == c_sum_flow_out flow_s n u n)

(** Valid flow in c2pulse representation *)
let c_valid_flow
    (flow_s cap_s: Seq.seq (option Int32.t))
    (n source sink: nat) : prop =
  c_capacity_constraint flow_s cap_s n /\
  c_flow_conservation flow_s n source sink

(** Flow value in c2pulse representation *)
let c_flow_value (flow_s: Seq.seq (option Int32.t))
    (n: nat{n > 0 /\ Seq.length flow_s == n * n})
    (source: nat{source < n}) : int =
  c_sum_flow_out flow_s n source n - c_sum_flow_into flow_s n source n

(** All capacities are non-negative *)
let all_nonneg_caps (cap_s: Seq.seq (option Int32.t)) (n: nat) : prop =
  Seq.length cap_s == n * n /\
  (forall (i: nat). i < n * n ==> seq_val cap_s i >= 0)

(** Nonlinear arithmetic: a*n + b < n*n when a < n /\ b < n *)
let index_bound (a b n: nat)
  : Lemma (requires a < n /\ b < n)
          (ensures a * n + b < n * n)
  = FStar.Math.Lemmas.lemma_mult_le_right n a (n - 1);
    FStar.Math.Lemmas.distributivity_sub_left n 1 n

(** Combined index bound + SizeT fits for flat matrix access *)
let index_fits (a b n: nat)
  : Lemma (requires a < n /\ b < n /\ SizeT.fits (n * n))
          (ensures a * n + b < n * n /\
                   SizeT.fits (a * n + b) /\
                   SizeT.fits (a * n))
  = index_bound a b n;
    SizeT.fits_lte (a * n + b) (n * n);
    SizeT.fits_lte (a * n) (n * n)

(** ================================================================
    MAX_CAP bound and Int32 overflow safety lemmas
    ================================================================ *)

(** Maximum capacity value for Int32-safe computation.
    46340^2 = 2147395600 < 2^31 - 1 = 2147483647 *)
let max_cap : nat = 46340

let max_cap_squared_fits ()
  : Lemma (max_cap * max_cap < pow2 31)
  = assert_norm (46340 * 46340 < pow2 31)

(** Subtraction of non-negative Int32 values fits in Int32.
    If 0 <= a <= Int32.max and 0 <= b <= Int32.max then a - b fits. *)
let nonneg_sub_fits (a b: int)
  : Lemma (requires 0 <= a /\ a <= 2147483647 /\ 0 <= b /\ b <= 2147483647)
          (ensures FStar.Int.fits (a - b) 32)
  = ()

(** Product of two bounded values: their sum and difference fit in Int32 *)
let bounded_product_fits (a b: int)
  : Lemma (requires 0 <= a /\ a <= max_cap /\ 0 <= b /\ b <= max_cap)
          (ensures FStar.Int.fits (a + b) 32 /\
                   FStar.Int.fits (a - b) 32)
  = max_cap_squared_fits ();
    assert_norm (max_cap < pow2 31 - 1);
    assert_norm (-(pow2 31) < -(max_cap))

(** dist + 1 fits in Int32 when dist <= 46338 *)
let dist_plus_one_fits (d: int)
  : Lemma (requires d >= -1 /\ d <= 46338)
          (ensures FStar.Int.fits (d + 1) 32)
  = assert_norm (46339 < pow2 31 - 1);
    assert_norm (-(pow2 31) < 0)

(** flow + bn fits in Int32 when both bounded by max_cap *)
let flow_plus_bn_fits (f bn: int)
  : Lemma (requires 0 <= f /\ f <= max_cap /\ 0 < bn /\ bn <= max_cap)
          (ensures FStar.Int.fits (f + bn) 32)
  = max_cap_squared_fits ();
    assert_norm (2 * max_cap < pow2 31 - 1)

(** flow - bn fits in Int32 when both bounded by max_cap *)
let flow_minus_bn_fits (f bn: int)
  : Lemma (requires 0 <= f /\ f <= max_cap /\ 0 < bn /\ bn <= max_cap)
          (ensures FStar.Int.fits (f - bn) 32)
  = assert_norm (-(pow2 31) <= -(max_cap))

(** Both flow+bn and flow-bn fit when all values in [0, max_cap].
    Can be called unconditionally before conditionally writing. *)
let flow_update_fits (f bn: int)
  : Lemma (requires 0 <= f /\ f <= max_cap /\ 0 <= bn /\ bn <= max_cap)
          (ensures FStar.Int.fits (f + bn) 32 /\
                   FStar.Int.fits (f - bn) 32)
  = max_cap_squared_fits ();
    assert_norm (2 * max_cap < pow2 31 - 1);
    assert_norm (-(pow2 31) <= -(max_cap))

(** Flow value accumulator fits in Int32.
    After v iterations, |fv| <= v * max_cap.
    fv + flow_out and fv + flow_out - flow_in also fit. *)
let fv_accumulator_fits (fv: int) (flow_out flow_in: int) (v n: nat)
  : Lemma (requires
             n <= max_cap /\
             0 <= flow_out /\ flow_out <= max_cap /\
             0 <= flow_in /\ flow_in <= max_cap /\
             v < n /\
             -(v * max_cap) <= fv /\ fv <= v * max_cap)
          (ensures
             FStar.Int.fits (fv + flow_out) 32 /\
             FStar.Int.fits (fv + flow_out - flow_in) 32 /\
             -((v + 1) * max_cap) <= fv + flow_out - flow_in /\
             fv + flow_out - flow_in <= (v + 1) * max_cap)
  = max_cap_squared_fits ();
    assert (fv + flow_out <= v * max_cap + max_cap);
    assert (v * max_cap + max_cap == (v + 1) * max_cap);
    assert ((v + 1) * max_cap <= n * max_cap);
    FStar.Math.Lemmas.lemma_mult_le_right max_cap n max_cap;
    FStar.Math.Lemmas.lemma_mult_le_left max_cap n max_cap;
    assert (n * max_cap <= max_cap * max_cap);
    assert (max_cap * max_cap < pow2 31 - 1);
    assert_norm (-(pow2 31) <= -(max_cap * max_cap));
    assert (fv + flow_out - flow_in >= -(v * max_cap) - max_cap);
    assert (-(v * max_cap) - max_cap == -((v + 1) * max_cap));
    assert (-((v + 1) * max_cap) >= -(max_cap * max_cap))
