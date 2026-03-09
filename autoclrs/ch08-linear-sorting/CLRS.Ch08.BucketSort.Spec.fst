(*
   Bucket Sort — Pure F* specification (CLRS §8.4)

   Core definitions: sorted and in_range predicates, insertion sort,
   bucket distribution functions, and helper functions for min/max.

   NO admits. NO assumes.
*)

module CLRS.Ch08.BucketSort.Spec

open FStar.List.Tot
open FStar.Math.Lemmas
module List = FStar.List.Tot

(* ========== Basic Predicates ========== *)

//SNIPPET_START: bucket_sort_sorted
let rec sorted (xs: list int) : prop =
  match xs with
  | [] -> True
  | [x] -> True
  | x :: y :: rest -> x <= y /\ sorted (y :: rest)
//SNIPPET_END: bucket_sort_sorted

let rec in_range (xs: list int) (lb ub: int) : prop =
  match xs with
  | [] -> True
  | x :: rest -> lb <= x /\ x < ub /\ in_range rest lb ub

(* ========== Insertion Sort ========== *)

let rec sorted_cons_mem (h: int) (t: list int) (y: int)
  : Lemma (requires sorted (h :: t) /\ List.mem y t)
          (ensures h <= y)
          (decreases t)
  = match t with
    | [] -> ()
    | z :: zs -> if z = y then () else sorted_cons_mem h zs y

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let rec insert (x: int) (xs: list int{sorted xs}) 
  : Tot (ys:list int{sorted ys /\ List.length ys == List.length xs + 1 /\
                      (forall y. List.mem y ys <==> (y = x \/ List.mem y xs))})
    (decreases xs)
  = match xs with
    | [] -> [x]
    | h :: t -> 
      if x <= h then x :: xs
      else (
        let r = insert x t in
        let (z :: r_tail) = r in
        if z <> x && List.mem z t then sorted_cons_mem h t z
        else ();
        h :: r
      )
#pop-options

let rec insertion_sort (xs: list int)
  : Tot (ys:list int{sorted ys /\ List.length ys == List.length xs})
    (decreases xs)
  = match xs with
    | [] -> []
    | h :: t -> insert h (insertion_sort t)

(* ========== Bucket Distribution Functions ========== *)

let bucket_index (v min_val max_val: int) (k: pos) : nat =
  if max_val <= min_val || v < min_val || v >= max_val then 0
  else
    let range_size = max_val - min_val in
    let bucket_size = if range_size / k = 0 then 1 else range_size / k in
    let bi = (v - min_val) / bucket_size in
    if bi >= k then k - 1 else bi

let rec filter_bucket (xs: list int) (i: nat) (min_val max_val: int) (k: pos)
  : Tot (list int) (decreases xs)
  = match xs with
    | [] -> []
    | x :: xs' ->
      if min_val <= x && x < max_val && bucket_index x min_val max_val k = i
      then x :: filter_bucket xs' i min_val max_val k
      else filter_bucket xs' i min_val max_val k

let rec create_all_buckets (xs: list int) (curr_bucket: nat) (k: pos) (min_val max_val: int)
  : Pure (list (list int))
    (requires curr_bucket <= k)
    (ensures fun _ -> True)
    (decreases k - curr_bucket)
  = if curr_bucket >= k then []
    else filter_bucket xs curr_bucket min_val max_val k :: 
         create_all_buckets xs (curr_bucket + 1) k min_val max_val

let rec sort_all_buckets (buckets: list (list int))
  : Tot (list (list int)) (decreases buckets)
  = match buckets with
    | [] -> []
    | b :: bs -> insertion_sort b :: sort_all_buckets bs

let rec concat_all (buckets: list (list int))
  : Tot (list int) (decreases buckets)
  = match buckets with
    | [] -> []
    | b :: bs -> List.append b (concat_all bs)

(* ========== Min/Max Helper Functions ========== *)

let rec list_min_from (xs: list int) (current_min: int)
  : Tot int (decreases xs)
  = match xs with
    | [] -> current_min
    | x :: xs' -> list_min_from xs' (if x < current_min then x else current_min)

let list_min (xs: list int{Cons? xs}) : int =
  list_min_from (Cons?.tl xs) (Cons?.hd xs)

let rec list_max_from (xs: list int) (current_max: int)
  : Tot int (decreases xs)
  = match xs with
    | [] -> current_max
    | x :: xs' -> list_max_from xs' (if x > current_max then x else current_max)

let list_max (xs: list int{Cons? xs}) : int =
  list_max_from (Cons?.tl xs) (Cons?.hd xs)

(* ========== Auxiliary Definitions ========== *)

let rec sum_lengths (buckets: list (list int)) : nat =
  match buckets with
  | [] -> 0
  | b :: bs -> List.length b + sum_lengths bs

let rec sum_filter_lengths (xs: list int) (curr: nat) (k: pos) (min_val max_val: int)
  : Pure nat (requires curr <= k) (ensures fun _ -> True) (decreases k - curr)
  = if curr >= k then 0
    else List.length (filter_bucket xs curr min_val max_val k) 
         + sum_filter_lengths xs (curr + 1) k min_val max_val

let is_permutation (xs ys: list int) : prop =
  forall x. List.count x xs == List.count x ys

let rec buckets_correct (buckets: list (list int)) (min_val max_val: int) (k: pos) (offset: nat) : prop =
  match buckets with
  | [] -> True
  | b :: bs ->
    (forall x. List.mem x b ==> min_val <= x /\ x < max_val /\ bucket_index x min_val max_val k = offset) /\
    buckets_correct bs min_val max_val k (offset + 1)

let rec all_sorted (buckets: list (list int)) : prop =
  match buckets with
  | [] -> True
  | b :: bs -> sorted b /\ all_sorted bs
