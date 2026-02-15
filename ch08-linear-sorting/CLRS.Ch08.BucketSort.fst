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
   
   Partial Proof (with documented admits):
   - Main algorithm structure is correct
   - Component functions preserve length
   - Concatenation strategy matches CLRS
   
   Complexity: O(n + k) average case when input uniformly distributed
               O(n²) worst case when all elements in one bucket
*)

module CLRS.Ch08.BucketSort

open FStar.List.Tot
open FStar.Math.Lemmas
module List = FStar.List.Tot

(* ========== Basic Predicates ========== *)

/// Predicate: list is sorted in non-decreasing order
let rec sorted (xs: list int) : prop =
  match xs with
  | [] -> True
  | [x] -> True
  | x :: y :: rest -> x <= y /\ sorted (y :: rest)

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

/// Lemma: appending two sorted lists with disjoint ranges is sorted
/// This is the KEY INSIGHT of bucket sort
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

(* ========== Main Algorithm ========== *)

/// Main Bucket Sort Algorithm
/// Sorts input list using k buckets
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let bucket_sort (xs: list int) (k: pos)
  : Pure (list int)
    (requires Cons? xs)
    (ensures fun ys -> sorted ys /\ List.length ys == List.length xs)
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
      // The proof requires showing:
      //  1. Each sorted_bucket is sorted (done by sort_all_buckets_sorted)
      //  2. Elements in bucket i <= elements in bucket j for i < j (by bucket_index monotonicity)
      //  3. Buckets partition the input (permutation - length preservation)
      
      admit(); // Remaining: show concat_all sorted_buckets is sorted and has correct length
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

/// Theorem: When k = n, bucket sort achieves O(n) cost
let bucket_sort_linear_cost (n: pos)
  : Lemma (bucket_sort_cost n n <= op_Multiply 3 n)
  = ()

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
   - Complexity analysis structure
   
   ⚠ ADMITTED (with clear proof obligation):
   - Main bucket sort correctness requires proving:
     1. filter_bucket only returns elements in correct range
     2. create_all_buckets produces non-overlapping buckets
     3. Bucket ranges are ordered (bucket i < bucket i+1)
     4. concat_all can apply append_sorted_disjoint transitively
     5. Buckets form a permutation of input
   
   The admit() represents these structural properties about buckets.
   The core algorithmic insight (append_sorted_disjoint) is proven.
*)
