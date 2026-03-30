(*
   Interface for digit-based counting sort lemmas.
   Exposes only the definitions and lemma signatures used by Impl.fst.
*)

module CLRS.Ch08.CountingSort.DigitSortLemmas

open FStar.Seq
module Seq = FStar.Seq
module B = CLRS.Ch08.RadixSort.Base
module Stab = CLRS.Ch08.RadixSort.Stability

(* ========== Digit counting functions ========== *)

val digit_count_le (s: Seq.seq nat) (v: int) (d: nat) (base: nat) : Tot nat

val digit_count (s: Seq.seq nat) (v: nat) (d base: nat) : Tot nat

(* ========== Phase 2: digit counting predicates ========== *)

let digit_counts_match_prefix (sc: Seq.seq int) (sa: Seq.seq nat)
                               (d base: nat) (progress: nat) : prop =
  Seq.length sc == base /\ base > 0 /\
  progress <= Seq.length sa /\
  (forall (v: nat). v < base ==>
    Seq.index sc v == digit_count (Seq.slice sa 0 progress) v d base)

let digit_counts_match (sc: Seq.seq int) (sa: Seq.seq nat) (d base: nat) : prop =
  digit_counts_match_prefix sc sa d base (Seq.length sa)

val digit_counts_match_prefix_zero (sc: Seq.seq int) (sa: Seq.seq nat) (d base: nat)
  : Lemma (requires
      Seq.length sc == base /\ base > 0 /\
      Seq.length sa > 0 /\
      (forall (v: nat). v < base ==> Seq.index sc v == 0))
    (ensures digit_counts_match_prefix sc sa d base 0)

val digit_count_phase_step
  (sa: Seq.seq nat) (sc sc': Seq.seq int) (j: nat) (d base: nat) (key: nat)
  : Lemma (requires
      digit_counts_match_prefix sc sa d base j /\
      j < Seq.length sa /\ base > 0 /\
      key == B.digit (Seq.index sa j) d base /\ key < base /\
      Seq.length sc' == base /\
      (forall (v: nat). v < base /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key + 1)
    (ensures digit_counts_match_prefix sc' sa d base (j + 1))

(* ========== Phase 3: prefix sums ========== *)

let digit_prefix_sum_inv (sc: Seq.seq int) (sa: Seq.seq nat)
                          (d base: nat) (progress: nat) : prop =
  Seq.length sc == base /\ base > 0 /\
  progress >= 1 /\ progress <= base /\
  (forall (v: nat). v < progress ==> Seq.index sc v == digit_count_le sa v d base) /\
  (forall (v: nat). v >= progress /\ v < base ==>
    Seq.index sc v == digit_count (Seq.slice sa 0 (Seq.length sa)) v d base)

val digit_prefix_sum_init (sc: Seq.seq int) (sa: Seq.seq nat) (d base: nat)
  : Lemma (requires digit_counts_match sc sa d base /\ base > 0)
          (ensures digit_prefix_sum_inv sc sa d base 1)

val digit_prefix_sum_step (sc sc': Seq.seq int) (sa: Seq.seq nat) (d base: nat) (i: nat)
  : Lemma (requires digit_prefix_sum_inv sc sa d base i /\
                    i >= 1 /\ i < base /\
                    Seq.length sc' == base /\
                    (forall (v: nat). v < base /\ v <> i ==> Seq.index sc' v == Seq.index sc v) /\
                    Seq.index sc' i == Seq.index sc i + Seq.index sc (i - 1))
          (ensures digit_prefix_sum_inv sc' sa d base (i + 1))

val digit_prefix_sum_complete (sc: Seq.seq int) (sa: Seq.seq nat) (d base: nat)
  : Lemma (requires digit_prefix_sum_inv sc sa d base base)
          (ensures (forall (v: nat). v < base ==> Seq.index sc v == digit_count_le sa v d base) /\
                   Seq.index sc (base - 1) == Seq.length sa)

(* ========== Phase 4 tracking invariants (abstract) ========== *)

val phase4_c_inv (sc: Seq.seq int) (sa: Seq.seq nat) (d base n remaining: nat) : prop

val phase4_b_inv (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n: nat) : prop

val phase4_content_inv (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n remaining: nat) : prop

(* ========== Phase 4 init ========== *)

val phase4_c_inv_init (sc: Seq.seq int) (sa: Seq.seq nat) (d base: nat)
  : Lemma (requires
      Seq.length sc == base /\ base > 0 /\ Seq.length sa > 0 /\
      (forall (v: nat). v < base ==> Seq.index sc v == digit_count_le sa v d base))
    (ensures phase4_c_inv sc sa d base (Seq.length sa) (Seq.length sa))

val phase4_b_inv_init (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base: nat)
  : Lemma (requires
      Seq.length sc == base /\ base > 0 /\ Seq.length sa > 0 /\
      Seq.length sb == Seq.length sa /\
      (forall (v: nat). v < base ==> Seq.index sc v == digit_count_le sa v d base))
    (ensures phase4_b_inv sc sa sb d base (Seq.length sa))

val phase4_content_inv_init (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base: nat)
  : Lemma (requires
      Seq.length sc == base /\ base > 0 /\ Seq.length sa > 0 /\
      Seq.length sb == Seq.length sa /\
      (forall (v: nat). v < base ==> Seq.index sc v == digit_count_le sa v d base))
    (ensures phase4_content_inv sc sa sb d base (Seq.length sa) (Seq.length sa))

(* ========== Phase 4 step ========== *)

val phase4_pos_bounds (sc: Seq.seq int) (sa: Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base)
    (ensures Seq.index sc key >= 1 /\ Seq.index sc key <= n)

val phase4_c_step (sc sc': Seq.seq int) (sa: Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\
      (forall (v: nat). v < base /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key - 1)
    (ensures phase4_c_inv sc' sa d base n (remaining - 1))

val phase4_b_step (sc sc': Seq.seq int) (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      phase4_b_inv sc sa sb d base n /\
      Seq.length sb == n /\
      remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\ Seq.length sb' == n /\
      (forall (v: nat). v < base /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key - 1 /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' (Seq.index sc key - 1) == Seq.index sa (remaining - 1))
    (ensures phase4_b_inv sc' sa sb' d base n)

val phase4_content_step (sc sc': Seq.seq int) (sa sb sb': Seq.seq nat) (d base n remaining: nat) (key: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n remaining /\
      Seq.length sa == n /\ Seq.length sc == base /\ remaining <= n /\
      phase4_content_inv sc sa sb d base n remaining /\
      Seq.length sb == n /\
      remaining > 0 /\ key < base /\
      key == B.digit (Seq.index sa (remaining - 1)) d base /\
      Seq.length sc' == base /\ Seq.length sb' == n /\
      (forall (v: nat). v < base /\ v <> key ==> Seq.index sc' v == Seq.index sc v) /\
      Seq.index sc' key == Seq.index sc key - 1 /\
      Seq.index sc key >= 1 /\ Seq.index sc key <= n /\
      (forall (p: nat). p < n /\ p <> Seq.index sc key - 1 ==> Seq.index sb' p == Seq.index sb p) /\
      Seq.index sb' (Seq.index sc key - 1) == Seq.index sa (remaining - 1))
    (ensures phase4_content_inv sc' sa sb' d base n (remaining - 1))

(* ========== Phase 4 final ========== *)

val phase4_final_is_stable (sc: Seq.seq int) (sa sb: Seq.seq nat) (d base n: nat)
  : Lemma (requires
      phase4_c_inv sc sa d base n 0 /\
      phase4_b_inv sc sa sb d base n /\
      phase4_content_inv sc sa sb d base n 0 /\
      Seq.length sa == n /\ n > 0 /\ Seq.length sb == n /\ base >= 2 /\ Seq.length sc == base)
    (ensures Stab.is_stable_sort_on_digit sa sb d base)

(* ========== Empty case ========== *)

val empty_is_stable_on_digit (s1 s2: Seq.seq nat) (d base: nat)
  : Lemma (requires Seq.length s1 == 0 /\ Seq.length s2 == 0 /\ base >= 2)
          (ensures Stab.is_stable_sort_on_digit s1 s2 d base)
