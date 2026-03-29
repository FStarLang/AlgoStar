(*
   Bucket Sort — Correctness lemmas and main algorithm (CLRS §8.4)

   Proofs of insertion sort correctness, inter-bucket ordering,
   length preservation, sorted concatenation, and permutation.
   The main bucket_sort function is here because its body calls lemmas.

   NO admits. NO assumes.
*)

module CLRS.Ch08.BucketSort.Lemmas

open FStar.List.Tot
open FStar.Math.Lemmas
open CLRS.Ch08.BucketSort.Spec
module List = FStar.List.Tot

(* ========== Min/Max Lemmas ========== *)

let rec list_min_from_bound (xs: list int) (current_min: int)
  : Lemma (ensures list_min_from xs current_min <= current_min)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_min_from_bound xs' (if x < current_min then x else current_min)

let rec list_max_from_bound (xs: list int) (current_max: int)
  : Lemma (ensures list_max_from xs current_max >= current_max)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_max_from_bound xs' (if x > current_max then x else current_max)

let rec list_min_from_le_all (xs: list int) (current_min: int)
  : Lemma (ensures (let result = list_min_from xs current_min in
                   result <= current_min /\
                   (forall y. List.mem y xs ==> result <= y)))
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_min_from_le_all xs' (if x < current_min then x else current_min)

let rec list_max_from_ge_all (xs: list int) (current_max: int)
  : Lemma (ensures (let result = list_max_from xs current_max in
                   result >= current_max /\
                   (forall y. List.mem y xs ==> result >= y)))
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_max_from_ge_all xs' (if x > current_max then x else current_max)

let rec list_min_from_ge_bound (xs: list int) (bound: int)
  : Lemma (requires forall y. List.mem y xs ==> y >= bound)
          (ensures list_min_from xs bound >= bound)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_min_from_ge_bound xs' (if x < bound then x else bound)

let rec list_max_from_le_bound (xs: list int) (bound: int)
  : Lemma (requires forall y. List.mem y xs ==> y <= bound)
          (ensures list_max_from xs bound <= bound)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_max_from_le_bound xs' (if x > bound then x else bound)

let min_max_equal_implies_all_equal (xs: list int{Cons? xs})
  : Lemma (requires list_min xs == list_max xs)
          (ensures (forall x. List.mem x xs ==> x == list_min xs))
  = let hd = Cons?.hd xs in
    let tl = Cons?.tl xs in
    list_min_from_le_all tl hd;
    list_max_from_ge_all tl hd;
    ()

(* ========== Insertion Sort Correctness ========== *)

let rec insert_count (x: int) (xs: list int{sorted xs}) (y: int)
  : Lemma (ensures List.count y (insert x xs) == List.count y (x :: xs))
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: t -> if x <= h then () else insert_count x t y

let rec insertion_sort_count (xs: list int) (y: int)
  : Lemma (ensures List.count y (insertion_sort xs) == List.count y xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: t -> 
      insertion_sort_count t y;
      insert_count h (insertion_sort t) y

let rec insert_maintains_sorted (x: int) (xs: list int)
  : Lemma (requires sorted xs)
          (ensures sorted (insert x xs))
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: t -> if x <= h then () else insert_maintains_sorted x t

let rec insertion_sort_correct (xs: list int)
  : Lemma (ensures sorted (insertion_sort xs))
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: t -> 
      insertion_sort_correct t;
      insert_maintains_sorted h (insertion_sort t)

let rec all_equal_sorted (xs: list int) (v: int)
  : Lemma (requires forall (x: int). List.mem x xs ==> x == v)
          (ensures sorted xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | [_] -> ()
    | _ :: x2 :: rest -> all_equal_sorted (x2 :: rest) v

//SNIPPET_START: append_sorted_disjoint
let rec append_sorted_disjoint (xs ys: list int) (mid: int)
  : Lemma (requires sorted xs /\ sorted ys /\
                     (forall (x: int). List.mem x xs ==> x < mid) /\
                     (forall (y: int). List.mem y ys ==> y >= mid))
          (ensures sorted (List.append xs ys))
          (decreases xs)
  = match xs with
    | [] -> ()
    | [x] -> ()
    | x1 :: x2 :: rest -> append_sorted_disjoint (x2 :: rest) ys mid
//SNIPPET_END: append_sorted_disjoint

let rec append_sorted_with_ordering (xs ys: list int)
  : Lemma (requires sorted xs /\ sorted ys /\
                     (forall (x y: int). List.mem x xs /\ List.mem y ys ==> x <= y))
          (ensures sorted (List.append xs ys))
          (decreases xs)
  = match xs with
    | [] -> ()
    | [_] -> ()
    | _ :: xs' -> append_sorted_with_ordering xs' ys

let rec concat_all_length (buckets: list (list int))
  : Lemma (ensures List.length (concat_all buckets) == sum_lengths buckets)
          (decreases buckets)
  = match buckets with
    | [] -> ()
    | b :: bs -> 
      concat_all_length bs;
      List.append_length b (concat_all bs)

let rec sort_all_buckets_preserves_lengths (buckets: list (list int))
  : Lemma (ensures List.length (sort_all_buckets buckets) == List.length buckets /\
                   (forall (i: nat). i < List.length buckets ==>
                     List.length (List.index (sort_all_buckets buckets) i) ==
                     List.length (List.index buckets i)))
          (decreases buckets)
  = match buckets with
    | [] -> ()
    | _ :: bs -> sort_all_buckets_preserves_lengths bs

let rec sort_all_buckets_sorted (buckets: list (list int))
  : Lemma (ensures forall (i: nat). i < List.length (sort_all_buckets buckets) ==>
                   sorted (List.index (sort_all_buckets buckets) i))
          (decreases buckets)
  = match buckets with
    | [] -> ()
    | b :: bs -> 
      insertion_sort_correct b;
      sort_all_buckets_sorted bs

(* ========== Inter-bucket Ordering ========== *)

let bucket_index_bound (v min_val max_val: int) (k: pos)
  : Lemma (ensures bucket_index v min_val max_val k < k)
  = ()

#push-options "--z3rlimit 40"
let bucket_index_monotone (v1 v2 min_val max_val: int) (k: pos)
  : Lemma (requires min_val < max_val /\ min_val <= v1 /\ v1 < max_val /\
                     min_val <= v2 /\ v2 < max_val /\ v1 <= v2)
          (ensures bucket_index v1 min_val max_val k <= bucket_index v2 min_val max_val k)
  = let range_size = max_val - min_val in
    let bucket_size = if range_size / k = 0 then 1 else range_size / k in
    lemma_div_le (v1 - min_val) (v2 - min_val) bucket_size
#pop-options

let bucket_index_strict (v1 v2 min_val max_val: int) (k: pos)
  : Lemma (requires min_val < max_val /\ min_val <= v1 /\ v1 < max_val /\
                     min_val <= v2 /\ v2 < max_val /\
                     bucket_index v1 min_val max_val k < bucket_index v2 min_val max_val k)
          (ensures v1 < v2)
  = if v2 <= v1 then bucket_index_monotone v2 v1 min_val max_val k else ()

let rec filter_bucket_correct (xs: list int) (i: nat) (min_val max_val: int) (k: pos) (x: int)
  : Lemma (requires List.mem x (filter_bucket xs i min_val max_val k))
          (ensures min_val <= x /\ x < max_val /\ bucket_index x min_val max_val k = i)
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: t ->
      if min_val <= h && h < max_val && bucket_index h min_val max_val k = i
      then (if h = x then () else filter_bucket_correct t i min_val max_val k x)
      else filter_bucket_correct t i min_val max_val k x

(* ========== Length Preservation ========== *)

let rec sum_filter_eq_sum_lengths (xs: list int) (curr: nat) (k: pos) (min_val max_val: int)
  : Lemma (requires curr <= k)
          (ensures sum_filter_lengths xs curr k min_val max_val ==
                   sum_lengths (create_all_buckets xs curr k min_val max_val))
          (decreases k - curr)
  = if curr >= k then ()
    else sum_filter_eq_sum_lengths xs (curr + 1) k min_val max_val

let rec sum_filter_lengths_nil (curr: nat) (k: pos) (min_val max_val: int)
  : Lemma (requires curr <= k)
          (ensures sum_filter_lengths [] curr k min_val max_val == 0)
          (decreases k - curr)
  = if curr >= k then ()
    else sum_filter_lengths_nil (curr + 1) k min_val max_val

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec sum_filter_lengths_cons (h: int) (t: list int) (curr: nat) (k: pos) (min_val max_val: int)
  : Lemma 
    (requires curr <= k /\ min_val <= h /\ h < max_val /\ min_val < max_val)
    (ensures (let j = bucket_index h min_val max_val k in
              sum_filter_lengths (h :: t) curr k min_val max_val ==
              sum_filter_lengths t curr k min_val max_val + (if j >= curr then 1 else 0)))
    (decreases k - curr)
  = if curr >= k then ()
    else (
      sum_filter_lengths_cons h t (curr + 1) k min_val max_val;
      ()
    )
#pop-options

let rec filter_all_length (xs: list int) (k: pos) (min_val max_val: int)
  : Lemma (requires min_val < max_val /\
                    (forall x. List.mem x xs ==> min_val <= x /\ x < max_val))
          (ensures sum_filter_lengths xs 0 k min_val max_val == List.length xs)
          (decreases xs)
  = match xs with
    | [] -> sum_filter_lengths_nil 0 k min_val max_val
    | h :: t ->
      filter_all_length t k min_val max_val;
      sum_filter_lengths_cons h t 0 k min_val max_val;
      bucket_index_bound h min_val max_val k

let rec sort_all_buckets_preserves_sum (buckets: list (list int))
  : Lemma (ensures sum_lengths (sort_all_buckets buckets) == sum_lengths buckets)
          (decreases buckets)
  = match buckets with
    | [] -> ()
    | _ :: bs -> sort_all_buckets_preserves_sum bs

(* ========== Sorted Concatenation ========== *)

let rec insertion_sort_mem (xs: list int) (x: int)
  : Lemma (ensures (List.mem x (insertion_sort xs) <==> List.mem x xs))
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: t -> insertion_sort_mem t x

let rec sort_all_buckets_mem (buckets: list (list int)) (i: nat) (x: int)
  : Lemma (requires i < List.length buckets)
          (ensures i < List.length (sort_all_buckets buckets) /\
                   (List.mem x (List.index (sort_all_buckets buckets) i) <==>
                    List.mem x (List.index buckets i)))
          (decreases buckets)
  = match buckets with
    | [] -> ()
    | b :: bs ->
      if i = 0 then insertion_sort_mem b x
      else sort_all_buckets_mem bs (i - 1) x

let rec create_all_buckets_correct
  (xs: list int) (curr: nat) (k: pos) (min_val max_val: int)
  : Lemma 
    (requires curr <= k /\ min_val < max_val)
    (ensures buckets_correct (create_all_buckets xs curr k min_val max_val) min_val max_val k curr)
    (decreases k - curr)
  = if curr >= k then ()
    else (
      create_all_buckets_correct xs (curr + 1) k min_val max_val;
      let aux (x: int) 
        : Lemma (requires List.mem x (filter_bucket xs curr min_val max_val k))
                (ensures min_val <= x /\ x < max_val /\ bucket_index x min_val max_val k = curr)
        = filter_bucket_correct xs curr min_val max_val k x
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    )

let rec sort_all_buckets_correct
  (buckets: list (list int)) (min_val max_val: int) (k: pos) (offset: nat)
  : Lemma 
    (requires buckets_correct buckets min_val max_val k offset)
    (ensures buckets_correct (sort_all_buckets buckets) min_val max_val k offset)
    (decreases buckets)
  = match buckets with
    | [] -> ()
    | b :: bs ->
      sort_all_buckets_correct bs min_val max_val k (offset + 1);
      let aux (x: int)
        : Lemma (requires List.mem x (insertion_sort b))
                (ensures min_val <= x /\ x < max_val /\ bucket_index x min_val max_val k = offset)
        = insertion_sort_mem b x
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let rec sort_all_buckets_all_sorted (buckets: list (list int))
  : Lemma (ensures all_sorted (sort_all_buckets buckets))
          (decreases buckets)
  = match buckets with
    | [] -> ()
    | b :: bs ->
      insertion_sort_correct b;
      sort_all_buckets_all_sorted bs

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec concat_sorted_ordered 
  (buckets: list (list int)) (min_val max_val: int) (k: pos) (offset: nat)
  : Lemma 
    (requires 
      min_val < max_val /\
      all_sorted buckets /\
      buckets_correct buckets min_val max_val k offset)
    (ensures sorted (concat_all buckets) /\
             (forall (x: int). List.mem x (concat_all buckets) ==>
               min_val <= x /\ x < max_val /\ bucket_index x min_val max_val k >= offset))
    (decreases buckets)
  = match buckets with
    | [] -> ()
    | b :: bs ->
      concat_sorted_ordered bs min_val max_val k (offset + 1);
      let lemma_ord (x: int)
        : Lemma (requires List.mem x b)
                (ensures forall y. List.mem y (concat_all bs) ==> x <= y)
        = let inner (y: int)
            : Lemma (requires List.mem y (concat_all bs)) (ensures x <= y)
            = bucket_index_strict x y min_val max_val k
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires inner)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires lemma_ord);
      append_sorted_with_ordering b (concat_all bs);
      let mem_lemma (x: int) 
        : Lemma (requires List.mem x (concat_all (b :: bs)))
                (ensures min_val <= x /\ x < max_val /\ bucket_index x min_val max_val k >= offset)
        = List.append_mem b (concat_all bs) x
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires mem_lemma)
#pop-options

(* ========== Permutation Proof ========== *)

let rec filter_bucket_count (xs: list int) (i: nat) (min_val max_val: int) (k: pos) (x: int)
  : Lemma (ensures List.count x (filter_bucket xs i min_val max_val k) ==
           (if min_val <= x && x < max_val && bucket_index x min_val max_val k = i 
            then List.count x xs else 0))
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: t -> filter_bucket_count t i min_val max_val k x

let rec sort_all_buckets_count (buckets: list (list int)) (x: int)
  : Lemma (ensures List.count x (concat_all (sort_all_buckets buckets)) == 
           List.count x (concat_all buckets))
          (decreases buckets)
  = match buckets with
    | [] -> ()
    | b :: bs ->
      sort_all_buckets_count bs x;
      insertion_sort_count b x;
      List.append_count b (concat_all bs) x;
      List.append_count (insertion_sort b) (concat_all (sort_all_buckets bs)) x

#push-options "--z3rlimit 40"
let rec create_all_buckets_perm 
  (xs: list int) (curr: nat) (k: pos) (min_val max_val: int) (x: int)
  : Lemma 
    (requires curr <= k /\ min_val < max_val /\
             (forall y. List.mem y xs ==> min_val <= y /\ y < max_val))
    (ensures List.count x (concat_all (create_all_buckets xs curr k min_val max_val)) ==
             (if min_val <= x && x < max_val && bucket_index x min_val max_val k >= curr 
              then List.count x xs else 0))
    (decreases k - curr)
  = if curr >= k then ()
    else (
      create_all_buckets_perm xs (curr + 1) k min_val max_val x;
      filter_bucket_count xs curr min_val max_val k x;
      List.append_count 
        (filter_bucket xs curr min_val max_val k) 
        (concat_all (create_all_buckets xs (curr + 1) k min_val max_val)) x
    )
#pop-options

(* ========== Main Algorithm ========== *)

//SNIPPET_START: bucket_sort_sig
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries always"
let bucket_sort (xs: list int) (k: pos)
  : Pure (list int)
    (requires True)
    (ensures fun ys -> sorted ys /\ List.length ys == List.length xs /\ is_permutation xs ys)
//SNIPPET_END: bucket_sort_sig
  = match xs with
    | [] -> []
    | _ ->
    let min_val = list_min xs in
    let max_val = list_max xs in
    
    if min_val = max_val then (
      min_max_equal_implies_all_equal xs;
      all_equal_sorted xs min_val;
      xs
    ) else (
      let buckets = create_all_buckets xs 0 k min_val (max_val + 1) in
      let sorted_buckets = sort_all_buckets buckets in
      
      sort_all_buckets_sorted buckets;
      sort_all_buckets_preserves_lengths buckets;
      concat_all_length sorted_buckets;
      
      sort_all_buckets_preserves_sum buckets;
      sum_filter_eq_sum_lengths xs 0 k min_val (max_val + 1);
      list_min_from_le_all (Cons?.tl xs) (Cons?.hd xs);
      list_max_from_ge_all (Cons?.tl xs) (Cons?.hd xs);
      filter_all_length xs k min_val (max_val + 1);
      
      create_all_buckets_correct xs 0 k min_val (max_val + 1);
      sort_all_buckets_correct buckets min_val (max_val + 1) k 0;
      sort_all_buckets_all_sorted buckets;
      concat_sorted_ordered sorted_buckets min_val (max_val + 1) k 0;
      
      let perm_aux (y: int) : Lemma (List.count y (concat_all sorted_buckets) == List.count y xs) =
        create_all_buckets_perm xs 0 k min_val (max_val + 1) y;
        sort_all_buckets_count buckets y;
        if not (min_val <= y && y < max_val + 1) then
          List.mem_count xs y
        else ()
      in
      FStar.Classical.forall_intro perm_aux;
      
      concat_all sorted_buckets
    )
#pop-options
