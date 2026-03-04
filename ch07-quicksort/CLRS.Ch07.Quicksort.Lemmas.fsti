(*
   CLRS Chapter 7: Quicksort — Lemma Signatures

   Interface for correctness and complexity lemmas used by quicksort:
   - Bounds lemmas (seq_min, seq_max)
   - Permutation composition for 3-way splits
   - Sorted append for combining sorted halves
   - Recursive complexity bound
*)
module CLRS.Ch07.Quicksort.Lemmas

open CLRS.Ch07.Partition.Spec
open CLRS.Ch07.Quicksort.Spec
open CLRS.Common.SortSpec
module Seq = FStar.Seq

val lemma_seq_min_is_min (s: Seq.seq int) (i: nat{i < Seq.length s})
  : Lemma (ensures seq_min s <= Seq.index s i)

val lemma_seq_max_is_max (s: Seq.seq int) (i: nat{i < Seq.length s})
  : Lemma (ensures Seq.index s i <= seq_max s)

val lemma_between_bounds_from_min_max (s: Seq.seq int)
  : Lemma (ensures between_bounds s (seq_min s) (seq_max s))

val lemma_min_le_max (s: Seq.seq int)
  : Lemma (requires Seq.length s > 0)
          (ensures seq_min s <= seq_max s)

val append_permutations_3 (s1 s2 s3 s1' s3': Seq.seq int)
  : Lemma
    (requires permutation s1 s1' /\ permutation s3 s3')
    (ensures permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')))

val append_permutations_3_squash (s1 s2 s3 s1' s3': Seq.seq int)
  (_ : squash (permutation s1 s1' /\ permutation s3 s3'))
  : squash (permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')))

val lemma_sorted_append
  (s1 s2 : Seq.seq int)
  (l1 r1 l2 r2 : int)
  : Lemma
    (requires sorted s1 /\ between_bounds s1 l1 r1 /\
              sorted s2 /\ between_bounds s2 l2 r2 /\
              r1 >= l1 /\ r2 >= l2 /\
              r1 <= l2)
    (ensures sorted (Seq.append s1 s2) /\ between_bounds (Seq.append s1 s2) l1 r2)

val lemma_sorted_append_squash
  (s1 s2 : Seq.seq int)
  (l1 r1 l2 r2 : int)
    (_ : squash (sorted s1 /\ between_bounds s1 l1 r1 /\
              sorted s2 /\ between_bounds s2 l2 r2 /\
              r1 >= l1 /\ r2 >= l2 /\
              r1 <= l2))
    : squash (sorted (Seq.append s1 s2) /\ between_bounds (Seq.append s1 s2) l1 r2)

val lemma_quicksort_complexity_bound (n n_left n_right: nat) (c_partition: nat)
  : Lemma
    (requires
      n > 0 /\
      n_left + 1 + n_right == n /\
      c_partition == n - 1)
    (ensures
      c_partition + op_Multiply n_left (n_left - 1) / 2 + op_Multiply n_right (n_right - 1) / 2
      <= op_Multiply n (n - 1) / 2)
