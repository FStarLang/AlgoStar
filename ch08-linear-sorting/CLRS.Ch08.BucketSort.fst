(*
   Bucket Sort - Pure F* verified implementation  
   
   This implements CLRS Bucket Sort (Section 8.4) for integer lists.
   
   Algorithm:
   1. Find min/max to determine range
   2. Divide range into k buckets
   3. Distribute elements into buckets based on values
   4. Sort each bucket using insertion sort
   5. Concatenate all sorted buckets
   
   Key Correctness Insight (CLRS): 
   If buckets cover non-overlapping ranges and each is sorted,
   then concatenation produces a sorted result.
   
   Proven Properties:
   - Insertion sort correctness (sorts and preserves length)
   - Single-element lists are sorted
   - Lists with all equal elements are sorted
   - Appending two sorted lists with disjoint ranges yields sorted list
   - Bucket index monotonicity and inter-bucket value ordering
   - Buckets partition the input (length preservation)
   - Full bucket sort correctness: sorted output with same length as input
   
   Complexity: O(n + k) average case when input uniformly distributed
               O(n²) worst case when all elements in one bucket
*)

module CLRS.Ch08.BucketSort

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

/// Predicate: all elements in list are within [lb, ub)
let rec in_range (xs: list int) (lb ub: int) : prop =
  match xs with
  | [] -> True
  | x :: xs' -> lb <= x /\ x < ub /\ in_range xs' lb ub

(* ========== Insertion Sort ========== *)

/// Lemma: if sorted list starts with h and y is in the tail, then h <= y
let rec sorted_cons_mem (h: int) (t: list int) (y: int)
  : Lemma (requires sorted (h :: t) /\ List.mem y t)
          (ensures h <= y)
          (decreases t)
  = match t with
    | [] -> ()
    | z :: zs -> if z = y then () else sorted_cons_mem h zs y

/// Insert element into sorted list, maintaining sortedness
/// Key property: result contains exactly the same elements as x :: xs
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
        // z is in r, so z = x \/ mem z t (from IH on insert)
        // If z = x: h <= x since x > h. Wait, x > h means h < x, so h <= z = x. ✓
        // If mem z t: sorted (h::t) gives h <= z via sorted_cons_mem. ✓
        if z <> x && List.mem z t then sorted_cons_mem h t z
        else (); // z = x, and h < x (since not (x <= h))
        h :: r
      )
#pop-options

/// Insertion sort: sort list by repeated insertion
let rec insertion_sort (xs: list int)
  : Tot (ys:list int{sorted ys /\ List.length ys == List.length xs})
    (decreases xs)
  = match xs with
    | [] -> []
    | h :: t -> insert h (insertion_sort t)

(* ========== Bucket Distribution Functions ========== *)

/// Determine which bucket (0..k-1) a value belongs to
/// Values are distributed based on their position in [min_val, max_val)
let bucket_index (v min_val max_val: int) (k: pos) : nat =
  if max_val <= min_val || v < min_val || v >= max_val then 0
  else
    let range_size = max_val - min_val in
    let bucket_size = if range_size / k = 0 then 1 else range_size / k in
    let bi = (v - min_val) / bucket_size in
    if bi >= k then k - 1 else bi  // Clamp to valid range

/// Extract all elements that belong to bucket i
let rec filter_bucket (xs: list int) (i: nat) (min_val max_val: int) (k: pos)
  : Tot (list int) (decreases xs)
  = match xs with
    | [] -> []
    | x :: xs' ->
      if min_val <= x && x < max_val && bucket_index x min_val max_val k = i
      then x :: filter_bucket xs' i min_val max_val k
      else filter_bucket xs' i min_val max_val k

/// Create all k buckets by filtering input for each bucket index
let rec create_all_buckets (xs: list int) (curr_bucket: nat) (k: pos) (min_val max_val: int)
  : Pure (list (list int))
    (requires curr_bucket <= k)
    (ensures fun _ -> True)
    (decreases k - curr_bucket)
  = if curr_bucket >= k then []
    else filter_bucket xs curr_bucket min_val max_val k :: 
         create_all_buckets xs (curr_bucket + 1) k min_val max_val

/// Sort each bucket using insertion sort
let rec sort_all_buckets (buckets: list (list int))
  : Tot (list (list int)) (decreases buckets)
  = match buckets with
    | [] -> []
    | b :: bs -> insertion_sort b :: sort_all_buckets bs

/// Concatenate all buckets into a single list
let rec concat_all (buckets: list (list int))
  : Tot (list int) (decreases buckets)
  = match buckets with
    | [] -> []
    | b :: bs -> List.append b (concat_all bs)

(* ========== Helper Functions ========== *)

/// Find minimum value in a non-empty list
let rec list_min_from (xs: list int) (current_min: int)
  : Tot int (decreases xs)
  = match xs with
    | [] -> current_min
    | x :: xs' -> list_min_from xs' (if x < current_min then x else current_min)

let list_min (xs: list int{Cons? xs}) : int =
  list_min_from (Cons?.tl xs) (Cons?.hd xs)

/// Find maximum value in a non-empty list
let rec list_max_from (xs: list int) (current_max: int)
  : Tot int (decreases xs)
  = match xs with
    | [] -> current_max
    | x :: xs' -> list_max_from xs' (if x > current_max then x else current_max)

let list_max (xs: list int{Cons? xs}) : int =
  list_max_from (Cons?.tl xs) (Cons?.hd xs)

(* ========== Correctness Lemmas ========== *)

/// Lemma: list_min_from returns a value <= current_min
let rec list_min_from_bound (xs: list int) (current_min: int)
  : Lemma (ensures list_min_from xs current_min <= current_min)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_min_from_bound xs' (if x < current_min then x else current_min)

/// Lemma: list_max_from returns a value >= current_max
let rec list_max_from_bound (xs: list int) (current_max: int)
  : Lemma (ensures list_max_from xs current_max >= current_max)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_max_from_bound xs' (if x > current_max then x else current_max)

/// Lemma: list_min_from is <= all elements and <= current_min
let rec list_min_from_le_all (xs: list int) (current_min: int)
  : Lemma (ensures (let result = list_min_from xs current_min in
                   result <= current_min /\
                   (forall y. List.mem y xs ==> result <= y)))
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_min_from_le_all xs' (if x < current_min then x else current_min)

/// Lemma: list_max_from is >= all elements and >= current_max
let rec list_max_from_ge_all (xs: list int) (current_max: int)
  : Lemma (ensures (let result = list_max_from xs current_max in
                   result >= current_max /\
                   (forall y. List.mem y xs ==> result >= y)))
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_max_from_ge_all xs' (if x > current_max then x else current_max)

/// Lemma: list_min_from when all elements >= bound
let rec list_min_from_ge_bound (xs: list int) (bound: int)
  : Lemma (requires forall y. List.mem y xs ==> y >= bound)
          (ensures list_min_from xs bound >= bound)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_min_from_ge_bound xs' (if x < bound then x else bound)

/// Lemma: list_max_from when all elements <= bound
let rec list_max_from_le_bound (xs: list int) (bound: int)
  : Lemma (requires forall y. List.mem y xs ==> y <= bound)
          (ensures list_max_from xs bound <= bound)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> list_max_from_le_bound xs' (if x > bound then x else bound)

/// Lemma: when min = max, all elements are equal to that value
let min_max_equal_implies_all_equal (xs: list int{Cons? xs})
  : Lemma (requires list_min xs == list_max xs)
          (ensures (forall x. List.mem x xs ==> x == list_min xs))
  = let hd = Cons?.hd xs in
    let tl = Cons?.tl xs in
    let min_val = list_min xs in
    // list_min <= all elements (from definition)
    list_min_from_le_all tl hd;
    // list_max >= all elements (from definition) 
    list_max_from_ge_all tl hd;
    // Since min = max and min <= all <= max, all elements = min = max
    ()

/// Lemma: insertion maintains sortedness
let rec insert_maintains_sorted (x: int) (xs: list int)
  : Lemma (requires sorted xs)
          (ensures sorted (insert x xs))
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: t -> if x <= h then () else insert_maintains_sorted x t

/// Lemma: insertion sort produces sorted output
let rec insertion_sort_correct (xs: list int)
  : Lemma (ensures sorted (insertion_sort xs))
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: t -> 
      insertion_sort_correct t;
      insert_maintains_sorted h (insertion_sort t)

/// Lemma: if all elements equal, list is sorted
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

/// Lemma: A weaker version - appending sorted lists where all elements of first <= all of second
let rec append_sorted_with_ordering (xs ys: list int)
  : Lemma (requires sorted xs /\ sorted ys /\
                     (forall (x y: int). List.mem x xs /\ List.mem y ys ==> x <= y))
          (ensures sorted (List.append xs ys))
          (decreases xs)
  = match xs with
    | [] -> ()
    | [_] -> ()
    | _ :: xs' -> append_sorted_with_ordering xs' ys

/// Helper: sum of lengths
let rec sum_lengths (buckets: list (list int)) : nat =
  match buckets with 
  | [] -> 0 
  | b :: bs -> List.length b + sum_lengths bs

/// Lemma: concat_all preserves total length (sum of individual lengths)
let rec concat_all_length (buckets: list (list int))
  : Lemma (ensures List.length (concat_all buckets) == sum_lengths buckets)
          (decreases buckets)
  = match buckets with
    | [] -> ()
    | b :: bs -> 
      concat_all_length bs;
      List.append_length b (concat_all bs)

/// Lemma: sort_all_buckets preserves length of bucket list and each bucket
let rec sort_all_buckets_preserves_lengths (buckets: list (list int))
  : Lemma (ensures List.length (sort_all_buckets buckets) == List.length buckets /\
                   (forall (i: nat). i < List.length buckets ==>
                     List.length (List.index (sort_all_buckets buckets) i) ==
                     List.length (List.index buckets i)))
          (decreases buckets)
  = match buckets with
    | [] -> ()
    | _ :: bs -> sort_all_buckets_preserves_lengths bs

/// Lemma: sort_all_buckets produces sorted buckets
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

/// bucket_index always returns a value in [0, k)
let bucket_index_bound (v min_val max_val: int) (k: pos)
  : Lemma (ensures bucket_index v min_val max_val k < k)
  = ()

/// bucket_index is monotone: v1 <= v2 implies bucket_index v1 <= bucket_index v2
#push-options "--z3rlimit 40"
let bucket_index_monotone (v1 v2 min_val max_val: int) (k: pos)
  : Lemma (requires min_val < max_val /\ min_val <= v1 /\ v1 < max_val /\
                     min_val <= v2 /\ v2 < max_val /\ v1 <= v2)
          (ensures bucket_index v1 min_val max_val k <= bucket_index v2 min_val max_val k)
  = let range_size = max_val - min_val in
    let bucket_size = if range_size / k = 0 then 1 else range_size / k in
    lemma_div_le (v1 - min_val) (v2 - min_val) bucket_size
#pop-options

/// Contrapositive: different bucket indices imply strict value ordering
let bucket_index_strict (v1 v2 min_val max_val: int) (k: pos)
  : Lemma (requires min_val < max_val /\ min_val <= v1 /\ v1 < max_val /\
                     min_val <= v2 /\ v2 < max_val /\
                     bucket_index v1 min_val max_val k < bucket_index v2 min_val max_val k)
          (ensures v1 < v2)
  = if v2 <= v1 then bucket_index_monotone v2 v1 min_val max_val k else ()

/// Elements in filter_bucket have correct bucket_index
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

/// Sum of filter_bucket lengths from curr to k-1
let rec sum_filter_lengths (xs: list int) (curr: nat) (k: pos) (min_val max_val: int)
  : Pure nat (requires curr <= k) (ensures fun _ -> True) (decreases k - curr)
  = if curr >= k then 0
    else List.length (filter_bucket xs curr min_val max_val k) +
         sum_filter_lengths xs (curr + 1) k min_val max_val

/// sum_filter_lengths equals sum_lengths of create_all_buckets
let rec sum_filter_eq_sum_lengths (xs: list int) (curr: nat) (k: pos) (min_val max_val: int)
  : Lemma (requires curr <= k)
          (ensures sum_filter_lengths xs curr k min_val max_val ==
                   sum_lengths (create_all_buckets xs curr k min_val max_val))
          (decreases k - curr)
  = if curr >= k then ()
    else sum_filter_eq_sum_lengths xs (curr + 1) k min_val max_val

/// sum_filter_lengths of empty list is 0
let rec sum_filter_lengths_nil (curr: nat) (k: pos) (min_val max_val: int)
  : Lemma (requires curr <= k)
          (ensures sum_filter_lengths [] curr k min_val max_val == 0)
          (decreases k - curr)
  = if curr >= k then ()
    else sum_filter_lengths_nil (curr + 1) k min_val max_val

/// Key lemma: adding an in-range element h increases sum by exactly 1
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
      let j = bucket_index h min_val max_val k in
      // filter_bucket (h::t) curr: if h matches curr, length increases by 1; otherwise same as for t
      // IH gives sum from curr+1 for (h::t) = sum from curr+1 for t + (if j >= curr+1 then 1 else 0)
      // When j = curr: filter adds 1 at curr, IH adds 0 from curr+1 onwards. Total: +1
      // When j <> curr: filter adds 0 at curr, (j>=curr iff j>=curr+1). Total: same as IH
      ()
    )
#pop-options

/// Main length theorem: sum of all filter_bucket lengths = length of input
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

/// sort_all_buckets preserves sum_lengths
let rec sort_all_buckets_preserves_sum (buckets: list (list int))
  : Lemma (ensures sum_lengths (sort_all_buckets buckets) == sum_lengths buckets)
          (decreases buckets)
  = match buckets with
    | [] -> ()
    | _ :: bs -> sort_all_buckets_preserves_sum bs

(* ========== Sorted Concatenation ========== *)

/// insertion_sort preserves membership
let rec insertion_sort_mem (xs: list int) (x: int)
  : Lemma (ensures (List.mem x (insertion_sort xs) <==> List.mem x xs))
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: t -> insertion_sort_mem t x

/// sort_all_buckets preserves membership within each bucket
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

/// Recursive predicate: each bucket contains elements with correct bucket_index
let rec buckets_correct (buckets: list (list int)) (min_val max_val: int) (k: pos) (offset: nat) : prop =
  match buckets with
  | [] -> True
  | b :: bs ->
    (forall x. List.mem x b ==> min_val <= x /\ x < max_val /\ bucket_index x min_val max_val k = offset) /\
    buckets_correct bs min_val max_val k (offset + 1)

/// Recursive predicate: all buckets are sorted
let rec all_sorted (buckets: list (list int)) : prop =
  match buckets with
  | [] -> True
  | b :: bs -> sorted b /\ all_sorted bs

/// create_all_buckets produces correctly-indexed buckets
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

/// sort_all_buckets preserves the buckets_correct predicate
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

/// sort_all_buckets produces all_sorted buckets
let rec sort_all_buckets_all_sorted (buckets: list (list int))
  : Lemma (ensures all_sorted (sort_all_buckets buckets))
          (decreases buckets)
  = match buckets with
    | [] -> ()
    | b :: bs ->
      insertion_sort_correct b;
      sort_all_buckets_all_sorted bs

/// Sortedness of concat_all when buckets have inter-bucket ordering
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
      // Establish ordering: every element of b <= every element of concat_all bs
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
      // Establish membership property for the full concat
      let mem_lemma (x: int) 
        : Lemma (requires List.mem x (concat_all (b :: bs)))
                (ensures min_val <= x /\ x < max_val /\ bucket_index x min_val max_val k >= offset)
        = List.append_mem b (concat_all bs) x
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires mem_lemma)
#pop-options

(* ========== Main Algorithm ========== *)

//SNIPPET_START: bucket_sort_sig
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let bucket_sort (xs: list int) (k: pos)
  : Pure (list int)
    (requires Cons? xs)
    (ensures fun ys -> sorted ys /\ List.length ys == List.length xs)
//SNIPPET_END: bucket_sort_sig
  = let min_val = list_min xs in
    let max_val = list_max xs in
    
    // Special case: all elements equal
    if min_val = max_val then (
      min_max_equal_implies_all_equal xs;
      all_equal_sorted xs min_val;
      xs
    ) else (
      // Step 1: Create k buckets over range [min_val, max_val + 1)
      let buckets = create_all_buckets xs 0 k min_val (max_val + 1) in
      
      // Step 2: Sort each bucket
      let sorted_buckets = sort_all_buckets buckets in
      
      // Establish key properties
      sort_all_buckets_sorted buckets;
      sort_all_buckets_preserves_lengths buckets;
      concat_all_length sorted_buckets;
      
      // Step 3: Concatenate all sorted buckets
      
      // Prove length preservation:
      // sum_lengths sorted_buckets == sum_lengths buckets == sum_filter_lengths == length xs
      sort_all_buckets_preserves_sum buckets;
      sum_filter_eq_sum_lengths xs 0 k min_val (max_val + 1);
      list_min_from_le_all (Cons?.tl xs) (Cons?.hd xs);
      list_max_from_ge_all (Cons?.tl xs) (Cons?.hd xs);
      filter_all_length xs k min_val (max_val + 1);
      
      // Prove sortedness:
      // 1. create_all_buckets has correct bucket indices
      create_all_buckets_correct xs 0 k min_val (max_val + 1);
      // 2. sort_all_buckets preserves the correctness predicate
      sort_all_buckets_correct buckets min_val (max_val + 1) k 0;
      // 3. sort_all_buckets produces all_sorted buckets
      sort_all_buckets_all_sorted buckets;
      // 4. concat sorted_buckets is sorted
      concat_sorted_ordered sorted_buckets min_val (max_val + 1) k 0;
      
      concat_all sorted_buckets
    )
#pop-options

(* ========== Complexity Analysis ========== *)

/// Cost model for bucket sort
type cost = nat

let bucket_sort_cost (n k: pos) : cost =
  n +                       // Step 1: Distribute n elements into buckets
  op_Multiply n n / k +     // Step 2: Sort buckets (O(n²/k) average case)
  n                         // Step 3: Concatenate buckets

//SNIPPET_START: bucket_sort_linear_cost
let bucket_sort_linear_cost (n: pos)
  : Lemma (bucket_sort_cost n n <= op_Multiply 3 n)
  = ()
//SNIPPET_END: bucket_sort_linear_cost

/// Analysis:
/// - Best/Average case (uniform distribution): Θ(n + k)
///   * Each bucket has ~n/k elements
///   * Sorting k buckets of size n/k: k * O((n/k)²) = O(n²/k)
///   * When k = Θ(n), total cost is Θ(n)
/// 
/// - Worst case: Θ(n²)
///   * All elements go to one bucket
///   * Reduces to insertion sort on n elements

(*
   SUMMARY OF VERIFICATION STATUS:
   
   ✓ PROVEN:
   - Insertion sort correctness (sortedness + length preservation)
   - All-equal-elements case is sorted
   - Disjoint sorted sequences can be concatenated to stay sorted (key insight)
   - Bucket index monotonicity (v1 <= v2 implies bucket_index v1 <= bucket_index v2)
   - Inter-bucket ordering (different bucket indices imply strict value ordering)
   - Filter bucket correctness (elements have correct bucket_index)
   - Length preservation (sum of filter_bucket lengths = input length)
   - Sort preserves bucket correctness and membership
   - Concatenation of sorted, inter-bucket-ordered buckets is sorted
   - Main bucket sort correctness: output is sorted and same length as input
   - Complexity analysis structure
*)
