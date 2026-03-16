(*
   Bucket Sort — Lemma Interface (CLRS §8.4)

   Public signatures for bucket sort correctness:
   - Insertion sort correctness and permutation preservation
   - Inter-bucket ordering (bucket_index_monotone, bucket_index_strict)
   - Sorted concatenation of buckets
   - Length preservation through bucket distribution
   - Main bucket_sort function

   NO admits. NO assumes.
*)

module CLRS.Ch08.BucketSort.Lemmas

open FStar.List.Tot
open CLRS.Ch08.BucketSort.Spec
module List = FStar.List.Tot

(* ========== Min/Max Lemmas ========== *)

val list_min_from_bound (xs: list int) (current_min: int)
  : Lemma (ensures list_min_from xs current_min <= current_min)

val list_max_from_bound (xs: list int) (current_max: int)
  : Lemma (ensures list_max_from xs current_max >= current_max)

val list_min_from_le_all (xs: list int) (current_min: int)
  : Lemma (ensures (let result = list_min_from xs current_min in
                   result <= current_min /\
                   (forall y. List.mem y xs ==> result <= y)))

val list_max_from_ge_all (xs: list int) (current_max: int)
  : Lemma (ensures (let result = list_max_from xs current_max in
                   result >= current_max /\
                   (forall y. List.mem y xs ==> result >= y)))

val min_max_equal_implies_all_equal (xs: list int{Cons? xs})
  : Lemma (requires list_min xs == list_max xs)
          (ensures (forall x. List.mem x xs ==> x == list_min xs))

(* ========== Insertion Sort Correctness ========== *)

val insert_count (x: int) (xs: list int{sorted xs}) (y: int)
  : Lemma (ensures List.count y (insert x xs) == List.count y (x :: xs))

val insertion_sort_count (xs: list int) (y: int)
  : Lemma (ensures List.count y (insertion_sort xs) == List.count y xs)

val insert_maintains_sorted (x: int) (xs: list int)
  : Lemma (requires sorted xs)
          (ensures sorted (insert x xs))

val insertion_sort_correct (xs: list int)
  : Lemma (ensures sorted (insertion_sort xs))

val all_equal_sorted (xs: list int) (v: int)
  : Lemma (requires forall (x: int). List.mem x xs ==> x == v)
          (ensures sorted xs)

(* ========== Sorted Concatenation (must precede bucket_index in .fst order) ========== *)

val append_sorted_with_ordering (xs ys: list int)
  : Lemma (requires sorted xs /\ sorted ys /\
                     (forall (x y: int). List.mem x xs /\ List.mem y ys ==> x <= y))
          (ensures sorted (List.append xs ys))

(* ========== Length Preservation ========== *)

val concat_all_length (buckets: list (list int))
  : Lemma (ensures List.length (concat_all buckets) == sum_lengths buckets)

(* ========== Inter-bucket Ordering ========== *)

val bucket_index_bound (v min_val max_val: int) (k: pos)
  : Lemma (ensures bucket_index v min_val max_val k < k)

val bucket_index_monotone (v1 v2 min_val max_val: int) (k: pos)
  : Lemma (requires min_val < max_val /\ min_val <= v1 /\ v1 < max_val /\
                     min_val <= v2 /\ v2 < max_val /\ v1 <= v2)
          (ensures bucket_index v1 min_val max_val k <= bucket_index v2 min_val max_val k)

val bucket_index_strict (v1 v2 min_val max_val: int) (k: pos)
  : Lemma (requires min_val < max_val /\ min_val <= v1 /\ v1 < max_val /\
                     min_val <= v2 /\ v2 < max_val /\
                     bucket_index v1 min_val max_val k < bucket_index v2 min_val max_val k)
          (ensures v1 < v2)

val filter_all_length (xs: list int) (k: pos) (min_val max_val: int)
  : Lemma (requires min_val < max_val /\
                    (forall x. List.mem x xs ==> min_val <= x /\ x < max_val))
          (ensures sum_filter_lengths xs 0 k min_val max_val == List.length xs)

(* ========== Sorted Bucket Concatenation ========== *)

val concat_sorted_ordered
  (buckets: list (list int)) (min_val max_val: int) (k: pos) (offset: nat)
  : Lemma
    (requires
      min_val < max_val /\
      all_sorted buckets /\
      buckets_correct buckets min_val max_val k offset)
    (ensures sorted (concat_all buckets) /\
             (forall (x: int). List.mem x (concat_all buckets) ==>
               min_val <= x /\ x < max_val /\ bucket_index x min_val max_val k >= offset))

(* ========== Permutation ========== *)

val sort_all_buckets_count (buckets: list (list int)) (x: int)
  : Lemma (ensures List.count x (concat_all (sort_all_buckets buckets)) ==
           List.count x (concat_all buckets))

val create_all_buckets_perm
  (xs: list int) (curr: nat) (k: pos) (min_val max_val: int) (x: int)
  : Lemma
    (requires curr <= k /\ min_val < max_val /\
             (forall y. List.mem y xs ==> min_val <= y /\ y < max_val))
    (ensures List.count x (concat_all (create_all_buckets xs curr k min_val max_val)) ==
             (if min_val <= x && x < max_val && bucket_index x min_val max_val k >= curr
              then List.count x xs else 0))

(* ========== Main Algorithm ========== *)

//SNIPPET_START: bucket_sort_sig
val bucket_sort (xs: list int) (k: pos)
  : Pure (list int)
    (requires True)
    (ensures fun ys -> sorted ys /\ List.length ys == List.length xs /\ is_permutation xs ys)
//SNIPPET_END: bucket_sort_sig
