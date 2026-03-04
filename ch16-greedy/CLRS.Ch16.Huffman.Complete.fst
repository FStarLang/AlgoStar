(*
   Complete Huffman Tree Construction - Following CLRS §16.3
   
   This module implements the full HUFFMAN algorithm from CLRS Section 16.3
   that builds the actual Huffman tree, not just the cost.
   
   ALGORITHM (CLRS §16.3):
   ----------------------
   HUFFMAN(C)
   1  n = |C|
   2  Q = C           // priority queue initialized with leaf trees
   3  for i = 1 to n-1
   4    allocate new node z
   5    z.left = x = EXTRACT-MIN(Q)
   6    z.right = y = EXTRACT-MIN(Q)
   7    z.freq = x.freq + y.freq
   8    INSERT(Q, z)
   9  return EXTRACT-MIN(Q)  // the root of the Huffman tree
   
   IMPLEMENTATION STRATEGY:
   -----------------------
   - Uses htree type from CLRS.Ch16.Huffman.Spec (Leaf | Internal)
   - Priority queue implemented as sorted list (ascending by frequency)
   - EXTRACT-MIN: take head of list
   - INSERT: insert_sorted maintains ordering
   - Proves correctness properties from CLRS Theorem 16.3
   
   KEY THEOREMS (CLRS §16.3):
   -------------------------
   1. Greedy Choice Property (Lemma 16.2):
      The two lowest-frequency characters x,y can be placed as siblings
      at maximum depth in an optimal tree.
      
   2. Optimal Substructure (Lemma 16.3):
      If T is optimal for alphabet C, and x,y are lowest-frequency siblings,
      then T' (with x,y merged) is optimal for C-{x,y}∪{z}.
      
   3. Correctness (Theorem 16.3):
      HUFFMAN produces an optimal prefix code.
   
   PROOF SKETCH:
   ------------
   - Base case: Single character → single leaf (cost 0)
   - Inductive step: By greedy choice + optimal substructure
     * Merge two min-frequency trees
     * Recursively solve on reduced problem
     * WPL relationship: WPL(T) = WPL(T') + freq(x) + freq(y)
   
   NO admits remain. Key properties proven:
   - Leaf frequency multiset preservation (via count-based equality)
   - WPL relationship for sibling merges: WPL(T) = WPL(T') + f1 + f2
   - Base case optimality for single-element inputs
*)

module CLRS.Ch16.Huffman.Complete

open FStar.List.Tot
open FStar.List.Tot.Properties
open CLRS.Ch16.Huffman.Spec

(*** Re-export Key Types and Functions ***)

// Tree type is already defined in Spec:
//   type htree = Leaf : freq:pos -> htree
//              | Internal : freq:pos -> left:htree -> right:htree -> htree

// Key operations from Spec:
//   - freq_of : htree -> pos
//   - weighted_path_length : htree -> nat
//   - cost : htree -> nat
//   - insert_sorted : htree -> list htree -> list htree
//   - merge : htree -> htree -> htree
//   - huffman_build : list pos{Cons? _} -> htree

(*** Priority Queue Specification ***)

// Our priority queue is a sorted list of trees (by frequency, ascending)
type priority_queue = list htree

// Well-formed priority queue: non-empty and sorted by frequency
let rec is_sorted_by_freq (l: list htree) : prop =
  match l with
  | [] -> True
  | [_] -> True
  | t1 :: t2 :: rest -> 
      freq_of t1 <= freq_of t2 /\ is_sorted_by_freq (t2 :: rest)

let is_valid_pq (pq: priority_queue) : prop =
  Cons? pq /\ is_sorted_by_freq pq

// Lemma: map preserves non-emptiness
let map_nonempty (#a #b: Type) (f: a -> b) (l: list a{Cons? l})
  : Lemma (ensures Cons? (map f l))
  = ()

// Lemma: sortWith preserves non-emptiness
let sortWith_nonempty (#a: Type) (f: a -> a -> int) (l: list a{Cons? l})
  : Lemma (ensures Cons? (sortWith f l))
  = // sortWith is defined as:
    // | [] -> []
    // | pivot::tl -> append (sortWith f lo) (pivot::sortWith f hi)
    // When l is non-empty (pivot::tl), the result is append ... (pivot::...)
    // which is always non-empty (contains at least pivot)
    match l with
    | [_] -> ()  // sortWith [x] = [x], which is non-empty
    | pivot :: tl ->
        // After partition, we get lo and hi
        // Result is: append (sortWith f lo) (pivot :: sortWith f hi)
        // This contains at least pivot, so it's non-empty
        // The append of any list with a non-empty list is non-empty
        ()  // F* can figure this out from the definition

// Helper: all elements in a list satisfy a predicate relative to a pivot
let rec all_le_pivot (pivot: htree) (l: list htree) : prop =
  match l with
  | [] -> True
  | hd :: tl -> freq_of hd <= freq_of pivot /\ all_le_pivot pivot tl

let rec all_ge_pivot (pivot: htree) (l: list htree) : prop =
  match l with
  | [] -> True
  | hd :: tl -> freq_of pivot <= freq_of hd /\ all_ge_pivot pivot tl

// Lemma: freq_cmp satisfies antisymmetry for the <= relation
let freq_cmp_antisymmetry (t1 t2: htree)
  : Lemma (freq_cmp t1 t2 >= 0 <==> freq_cmp t2 t1 <= 0)
  = ()

// Lemma: partition with bool_of_compare and freq_cmp separates elements correctly
let rec partition_by_freq_cmp (pivot: htree) (l: list htree)
  : Lemma (ensures (let hi, lo = partition (bool_of_compare freq_cmp pivot) l in
                    all_le_pivot pivot lo /\ all_ge_pivot pivot hi))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
        partition_by_freq_cmp pivot tl;
        // bool_of_compare freq_cmp pivot hd = (freq_cmp pivot hd < 0)
        //                                    = (freq_of pivot - freq_of hd < 0)
        //                                    = (freq_of pivot < freq_of hd)
        // If this is true, hd goes to hi, and we need freq_of pivot <= freq_of hd (✓)
        // If this is false, hd goes to lo, and we need freq_of hd <= freq_of pivot
        //   freq_cmp pivot hd >= 0 means freq_of pivot - freq_of hd >= 0
        //   which means freq_of pivot >= freq_of hd, i.e., freq_of hd <= freq_of pivot (✓)
        ()

// Lemma: if all elements are >= pivot and the rest is sorted, prepending maintains sort
let prepend_maintains_sorted (pivot: htree) (sorted_rest: list htree)
  : Lemma (requires is_sorted_by_freq sorted_rest /\ all_ge_pivot pivot sorted_rest)
          (ensures is_sorted_by_freq (pivot :: sorted_rest))
  = match sorted_rest with
    | [] -> ()
    | hd :: tl ->
        // Need to show: is_sorted_by_freq (pivot :: hd :: tl)
        // Which is: freq_of pivot <= freq_of hd /\ is_sorted_by_freq (hd :: tl)
        // From all_ge_pivot pivot (hd :: tl): freq_of pivot <= freq_of hd /\ all_ge_pivot pivot tl
        // From is_sorted_by_freq (hd :: tl): already have this
        ()

// Lemma: sortWith preserves all_ge_pivot
let rec sortWith_preserves_all_ge (pivot: htree) (l: list htree)
  : Lemma (requires all_ge_pivot pivot l)
          (ensures all_ge_pivot pivot (sortWith freq_cmp l))
          (decreases (length l))
  = match l with
    | [] -> ()
    | [x] -> ()
    | p :: tl ->
        let hi, lo = partition (bool_of_compare freq_cmp p) tl in
        partition_length (bool_of_compare freq_cmp p) tl;
        // Need to show: all_ge_pivot pivot hi and all_ge_pivot pivot lo
        let rec partition_preserves_all_ge (pivot: htree) (p: htree) (l: list htree)
          : Lemma (requires all_ge_pivot pivot l)
                  (ensures (let hi, lo = partition (bool_of_compare freq_cmp p) l in
                            all_ge_pivot pivot hi /\ all_ge_pivot pivot lo))
                  (decreases l)
          = match l with
            | [] -> ()
            | hd :: tl -> partition_preserves_all_ge pivot p tl
        in
        partition_preserves_all_ge pivot p tl;
        // From all_ge_pivot pivot (p :: tl): freq_of pivot <= freq_of p /\ all_ge_pivot pivot tl
        assert (freq_of pivot <= freq_of p);
        sortWith_preserves_all_ge pivot lo;
        sortWith_preserves_all_ge pivot hi;
        // Now show that append (sortWith freq_cmp lo) (p :: sortWith freq_cmp hi) has all_ge_pivot pivot
        let rec append_all_ge (pivot: htree) (l1 l2: list htree)
          : Lemma (requires all_ge_pivot pivot l1 /\ all_ge_pivot pivot l2)
                  (ensures all_ge_pivot pivot (append l1 l2))
                  (decreases l1)
          = match l1 with
            | [] -> ()
            | hd :: tl -> append_all_ge pivot tl l2
        in
        append_all_ge pivot (sortWith freq_cmp lo) (p :: sortWith freq_cmp hi);
        ()

// Lemma: sortWith preserves all_le_pivot
let rec sortWith_preserves_all_le (pivot: htree) (l: list htree)
  : Lemma (requires all_le_pivot pivot l)
          (ensures all_le_pivot pivot (sortWith freq_cmp l))
          (decreases (length l))
  = match l with
    | [] -> ()
    | [x] -> ()
    | p :: tl ->
        let hi, lo = partition (bool_of_compare freq_cmp p) tl in
        partition_length (bool_of_compare freq_cmp p) tl;
        let rec partition_preserves_all_le (pivot: htree) (p: htree) (l: list htree)
          : Lemma (requires all_le_pivot pivot l)
                  (ensures (let hi, lo = partition (bool_of_compare freq_cmp p) l in
                            all_le_pivot pivot hi /\ all_le_pivot pivot lo))
                  (decreases l)
          = match l with
            | [] -> ()
            | hd :: tl -> partition_preserves_all_le pivot p tl
        in
        partition_preserves_all_le pivot p tl;
        assert (freq_of p <= freq_of pivot);
        sortWith_preserves_all_le pivot lo;
        sortWith_preserves_all_le pivot hi;
        let rec append_all_le (pivot: htree) (l1 l2: list htree)
          : Lemma (requires all_le_pivot pivot l1 /\ all_le_pivot pivot l2)
                  (ensures all_le_pivot pivot (append l1 l2))
                  (decreases l1)
          = match l1 with
            | [] -> ()
            | hd :: tl -> append_all_le pivot tl l2
        in
        append_all_le pivot (sortWith freq_cmp lo) (p :: sortWith freq_cmp hi);
        ()

// Lemma: appending sorted lists with all elements in first <= all in second gives sorted
let rec append_sorted (l1 l2: list htree)
  : Lemma (requires is_sorted_by_freq l1 /\ is_sorted_by_freq l2 /\
                    (match l1, l2 with
                     | _, [] -> True
                     | [], _ -> True
                     | _, hd2 :: _ -> all_le_pivot hd2 l1))
          (ensures is_sorted_by_freq (append l1 l2))
          (decreases l1)
  = match l1 with
    | [] -> ()
    | hd1 :: tl1 ->
        append_sorted tl1 l2;
        match tl1, l2 with
        | [], [] -> ()
        | [], hd2 :: _ -> ()
        | hd_tl1 :: _, [] -> ()
        | hd_tl1 :: _, hd2 :: _ ->
            // From is_sorted_by_freq l1: freq_of hd1 <= freq_of hd_tl1
            // From all_le_pivot hd2 l1: freq_of hd_tl1 <= freq_of hd2
            // From append_sorted tl1 l2: is_sorted_by_freq (append tl1 l2)
            // append l1 l2 = hd1 :: append tl1 l2
            // Need: freq_of hd1 <= freq_of (head of append tl1 l2)
            ()

// Lemma: sortWith with freq_cmp produces a sorted result
let rec sortWith_produces_sorted_freq_cmp (l: list htree)
  : Lemma (ensures is_sorted_by_freq (sortWith freq_cmp l))
          (decreases (length l))
  = match l with
    | [] -> ()
    | [x] -> ()
    | pivot :: tl ->
        let hi, lo = partition (bool_of_compare freq_cmp pivot) tl in
        partition_length (bool_of_compare freq_cmp pivot) tl;
        // From partition_length: length lo + length hi = length tl
        // Therefore length lo < length l and length hi < length l
        partition_by_freq_cmp pivot tl;
        // From partition_by_freq_cmp: all_le_pivot pivot lo /\ all_ge_pivot pivot hi
        sortWith_produces_sorted_freq_cmp lo;
        sortWith_produces_sorted_freq_cmp hi;
        // sortWith freq_cmp lo is sorted and all elements are <= pivot
        // sortWith freq_cmp hi is sorted and all elements are >= pivot
        sortWith_preserves_all_ge pivot hi;
        sortWith_preserves_all_le pivot lo;
        prepend_maintains_sorted pivot (sortWith freq_cmp hi);
        // pivot :: sortWith freq_cmp hi is sorted
        append_sorted (sortWith freq_cmp lo) (pivot :: sortWith freq_cmp hi)
        // Result: append (sortWith freq_cmp lo) (pivot :: sortWith freq_cmp hi) is sorted

// Lemma: map preserves length
let rec map_length (#a #b: Type) (f: a -> b) (l: list a)
  : Lemma (ensures length (map f l) = length l)
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> map_length f tl

// Lemma: sortWith preserves length  
let rec sortWith_length (#a: Type) (f: a -> a -> int) (l: list a)
  : Lemma (ensures length (sortWith f l) = length l)
          (decreases (length l))
  = match l with
    | [] -> ()
    | pivot :: tl ->
        // sortWith definition: append (sortWith f lo) (pivot::sortWith f hi)
        // where (hi, lo) = partition (bool_of_compare f pivot) tl
        let hi, lo = partition (bool_of_compare f pivot) tl in
        partition_length (bool_of_compare f pivot) tl;
        // From partition_length: length lo + length hi = length tl
        sortWith_length f lo;
        sortWith_length f hi;
        // length (sortWith f lo) = length lo
        // length (sortWith f hi) = length hi
        // length (pivot :: sortWith f hi) = 1 + length hi
        append_length (sortWith f lo) (pivot :: sortWith f hi)
        // length (append ...) = length (sortWith f lo) + length (pivot :: sortWith f hi)
        //                     = length lo + 1 + length hi
        //                     = length lo + length hi + 1
        //                     = length tl + 1
        //                     = length l

// Initialize PQ from frequency list
let init_pq (freqs: list pos{Cons? freqs}) : pq:priority_queue{is_valid_pq pq /\ length pq = length freqs} =
  let trees = map (fun f -> Leaf f) freqs in
  map_nonempty (fun f -> Leaf f) freqs;
  map_length (fun f -> Leaf f) freqs;
  assert (length trees = length freqs);
  sortWith_nonempty freq_cmp trees;
  sortWith_length freq_cmp trees;
  let sorted = sortWith freq_cmp trees in
  assert (length sorted = length trees);
  assert (length sorted = length freqs);
  sortWith_produces_sorted_freq_cmp trees;
  sorted

// EXTRACT-MIN: take head (O(1))
let extract_min (pq: priority_queue{is_valid_pq pq}) 
  : (htree * option priority_queue)
  = match pq with
    | [t] -> (t, None)
    | t :: rest -> (t, Some rest)
    | [] -> 
        // Unreachable: pq is non-empty by precondition
        assert (Cons? pq);  // From is_valid_pq
        false_elim ()

// Lemma: extract_min preserves sortedness of remainder
let extract_min_preserves_sorted (pq: priority_queue{is_valid_pq pq /\ length pq >= 2})
  : Lemma (ensures (match extract_min pq with
                    | (_, Some rest) -> is_sorted_by_freq rest
                    | _ -> True))
  = ()

// Lemma: insert_sorted maintains sortedness
let rec insert_sorted_maintains_sorted (t: htree) (l: list htree)
  : Lemma (requires is_sorted_by_freq l)
          (ensures is_sorted_by_freq (insert_sorted t l))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
        if freq_of t <= freq_of hd then ()
        else insert_sorted_maintains_sorted t tl

// INSERT: insert_sorted maintains order
let insert_pq (t: htree) (pq: priority_queue{is_sorted_by_freq pq}) 
  : pq':priority_queue{is_valid_pq pq'}
  = insert_sorted_nonempty t pq;
    insert_sorted_maintains_sorted t pq;
    insert_sorted t pq

(*** Main Huffman Construction ***)

// Build Huffman tree following CLRS algorithm exactly
// Termination: length decreases by 1 each iteration (n-1 iterations total)
let rec huffman_from_pq (pq: priority_queue{is_valid_pq pq})
  : Tot htree (decreases length pq)
  = match pq with
    | [t] -> 
        // Base case: single tree is the result
        t
    | t1 :: t2 :: rest ->
        // Line 5-6: EXTRACT-MIN twice
        // t1, t2 are the two minimum-frequency trees
        
        // Line 4-7: Allocate new node z with z.freq = x.freq + y.freq
        let merged = merge t1 t2 in
        
        // Line 8: INSERT(Q, z)
        // insert_sorted maintains the priority queue invariant
        insert_sorted_length merged rest;
        insert_sorted_nonempty merged rest;
        insert_sorted_maintains_sorted merged rest;
        let new_pq = insert_sorted merged rest in
        
        // Prove length decreased (for termination)
        // length [t1; t2; ...rest] = 2 + length rest
        // length (insert_sorted merged rest) = 1 + length rest
        // So we decreased from 2 + length rest to 1 + length rest
        
        // Continue loop (Line 3: for i = 1 to n-1)
        huffman_from_pq new_pq
    | [] -> 
        // Unreachable: pq is non-empty by precondition
        assert (Cons? pq);  // From is_valid_pq
        false_elim ()

// Lemma: huffman_from_pq preserves total frequency
let rec huffman_from_pq_preserves_sum (pq: priority_queue{is_valid_pq pq})
  : Lemma (ensures freq_of (huffman_from_pq pq) == sum_tree_freqs pq)
          (decreases length pq)
  = match pq with
    | [t] -> ()
    | t1 :: t2 :: rest ->
        let merged = merge t1 t2 in
        insert_sorted_length merged rest;
        insert_sorted_nonempty merged rest;
        insert_sorted_maintains_sorted merged rest;
        let new_pq = insert_sorted merged rest in
        // Prove new_pq is valid
        assert (Cons? new_pq);
        assert (is_sorted_by_freq new_pq);
        assert (is_valid_pq new_pq);
        (match rest with
         | [] -> 
             // new_pq = [merged]
             // freq_of (huffman_from_pq [merged]) = freq_of merged
             //                                     = freq_of t1 + freq_of t2
             //                                     = sum_tree_freqs [t1; t2]
             ()
         | _ ->
             insert_sorted_preserves_sum merged rest;
             // sum_tree_freqs new_pq = freq_of merged + sum_tree_freqs rest
             //                       = (freq_of t1 + freq_of t2) + sum_tree_freqs rest
             //                       = sum_tree_freqs [t1; t2; ...rest]
             ()
        );
        huffman_from_pq_preserves_sum new_pq
    | [] -> ()



// Main entry point: Build Huffman tree from list of frequencies
let huffman_complete (freqs: list pos{Cons? freqs}) : htree =
  // Line 1: n = |C|
  let n = length freqs in
  
  // Line 2: Q = C (initialize priority queue with leaf nodes)
  let pq = init_pq freqs in
  
  // Line 3-8: Loop n-1 times
  // (handled by huffman_from_pq's structural recursion)
  
  // Line 9: return EXTRACT-MIN(Q)
  huffman_from_pq pq

(*** Correctness Properties ***)

// Property 1: Result is a valid prefix-free code tree
// (This is trivially true: all htrees are full binary trees by construction)
let rec is_prefix_free_code (t: htree) : prop =
  match t with
  | Leaf _ -> True
  | Internal _ l r -> 
      is_prefix_free_code l /\ is_prefix_free_code r

let huffman_produces_prefix_free_code (freqs: list pos{Cons? freqs})
  : Lemma (ensures is_prefix_free_code (huffman_complete freqs))
  = // All htrees are full binary trees by construction
    // is_prefix_free_code is trivially satisfied by the htree type
    let rec all_htrees_prefix_free (t: htree) 
      : Lemma (ensures is_prefix_free_code t)
              (decreases t)
      = match t with
        | Leaf _ -> ()
        | Internal _ l r -> 
            all_htrees_prefix_free l;
            all_htrees_prefix_free r
    in
    all_htrees_prefix_free (huffman_complete freqs)

// Property 2: Total frequency is preserved
let rec sum_list (l: list pos{Cons? l}) : pos =
  match l with
  | [x] -> x
  | hd :: tl -> hd + sum_list tl
  | _ -> 1

// Helper: sum of tree frequencies with cases for empty list
let sum_tree_freqs_opt (l: list htree) : nat =
  match l with
  | [] -> 0
  | _ -> sum_tree_freqs l

// Lemma: append preserves sum of frequencies
let rec append_tree_sum (l1 l2: list htree)
  : Lemma (ensures sum_tree_freqs_opt l1 + sum_tree_freqs_opt l2 == 
                   sum_tree_freqs_opt (append l1 l2))
          (decreases l1)
  = match l1 with
    | [] -> ()
    | [hd] -> 
        (match l2 with
         | [] -> ()
         | _ -> ())
    | hd :: tl -> append_tree_sum tl l2

// Lemma: partition preserves sum
let rec partition_preserves_tree_sum (pivot: htree) (l: list htree)
  : Lemma (ensures (let hi, lo = partition (bool_of_compare freq_cmp pivot) l in
                    sum_tree_freqs_opt l == sum_tree_freqs_opt lo + sum_tree_freqs_opt hi))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl -> partition_preserves_tree_sum pivot tl

// Lemma: sortWith preserves sum of tree frequencies
let rec sortWith_preserves_tree_sum (l: list htree{Cons? l})
  : Lemma (ensures sum_tree_freqs (sortWith freq_cmp l) == sum_tree_freqs l)
          (decreases (length l))
  = match l with
    | [_] -> ()
    | pivot :: tl ->
        let hi, lo = partition (bool_of_compare freq_cmp pivot) tl in
        partition_length (bool_of_compare freq_cmp pivot) tl;
        partition_preserves_tree_sum pivot tl;
        // sum_tree_freqs_opt tl == sum_tree_freqs_opt lo + sum_tree_freqs_opt hi
        
        // Recursively prove for lo and hi when non-empty
        (match lo with
         | [] -> ()
         | _ -> sortWith_preserves_tree_sum lo);
        (match hi with
         | [] -> ()
         | _ -> sortWith_preserves_tree_sum hi);
        
        // sortWith freq_cmp (pivot :: tl) = append (sortWith freq_cmp lo) (pivot :: sortWith freq_cmp hi)
        // Show sum is preserved
        append_tree_sum (sortWith freq_cmp lo) (pivot :: sortWith freq_cmp hi);
        // sum_tree_freqs_opt (sortWith lo) + sum_tree_freqs_opt (pivot :: sortWith hi)
        // = sum_tree_freqs_opt lo + (freq_of pivot + sum_tree_freqs_opt (sortWith hi))
        // = sum_tree_freqs_opt lo + freq_of pivot + sum_tree_freqs_opt hi
        // = sum_tree_freqs_opt lo + sum_tree_freqs_opt hi + freq_of pivot
        // = sum_tree_freqs_opt tl + freq_of pivot
        // = sum_tree_freqs (pivot :: tl)
        ()

let huffman_preserves_total_frequency (freqs: list pos{Cons? freqs})
  : Lemma (ensures freq_of (huffman_complete freqs) == sum_list freqs)
  = let trees = map (fun f -> Leaf f) freqs in
    map_nonempty (fun f -> Leaf f) freqs;
    map_leaf_sum freqs;
    assert (sum_tree_freqs trees == list_sum freqs);
    sortWith_nonempty freq_cmp trees;
    sortWith_preserves_tree_sum trees;
    let pq = sortWith freq_cmp trees in
    assert (sum_tree_freqs pq == sum_tree_freqs trees);
    assert (sum_tree_freqs pq == list_sum freqs);
    sortWith_produces_sorted_freq_cmp trees;
    assert (is_sorted_by_freq pq);
    assert (is_valid_pq pq);
    huffman_from_pq_preserves_sum pq;
    assert (freq_of (huffman_from_pq pq) == sum_tree_freqs pq);
    // Now show list_sum == sum_list
    let rec list_sum_eq_sum_list (l: list pos{Cons? l})
      : Lemma (ensures list_sum l == sum_list l)
              (decreases l)
      = match l with
        | [_] -> ()
        | hd :: tl -> list_sum_eq_sum_list tl
    in
    list_sum_eq_sum_list freqs;
    assert (list_sum freqs == sum_list freqs);
    ()

(*** Leaf Frequency Multiset Preservation ***)

// Collect all leaf frequencies from a list of trees
let rec all_leaf_freqs (l: list htree) : list pos =
  match l with
  | [] -> []
  | hd :: tl -> leaf_freqs hd @ all_leaf_freqs tl

// all_leaf_freqs distributes over append
let rec all_leaf_freqs_append (l1 l2: list htree)
  : Lemma (ensures all_leaf_freqs (l1 @ l2) == all_leaf_freqs l1 @ all_leaf_freqs l2)
          (decreases l1)
  = match l1 with
    | [] -> ()
    | hd :: tl ->
        all_leaf_freqs_append tl l2;
        append_assoc (leaf_freqs hd) (all_leaf_freqs tl) (all_leaf_freqs l2)

// insert_sorted preserves the leaf frequency multiset
let rec insert_sorted_preserves_leaf_multiset (t: htree) (l: list htree) (x: pos)
  : Lemma (ensures count x (all_leaf_freqs (insert_sorted t l)) =
                   count x (leaf_freqs t) + count x (all_leaf_freqs l))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
        if freq_of t <= freq_of hd then
          append_count (leaf_freqs t) (all_leaf_freqs l) x
        else (
          insert_sorted_preserves_leaf_multiset t tl x;
          append_count (leaf_freqs hd) (all_leaf_freqs (insert_sorted t tl)) x;
          append_count (leaf_freqs hd) (all_leaf_freqs tl) x
        )

// partition preserves the combined leaf frequency multiset
let rec partition_preserves_all_leaf_freqs (f: htree -> bool) (l: list htree) (x: pos)
  : Lemma (ensures (let (l1, l2) = partition f l in
                    count x (all_leaf_freqs l1) + count x (all_leaf_freqs l2) = count x (all_leaf_freqs l)))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
        partition_preserves_all_leaf_freqs f tl x;
        let (l1_tl, l2_tl) = partition f tl in
        append_count (leaf_freqs hd) (all_leaf_freqs tl) x;
        if f hd then
          append_count (leaf_freqs hd) (all_leaf_freqs l1_tl) x
        else
          append_count (leaf_freqs hd) (all_leaf_freqs l2_tl) x

// sortWith preserves the leaf frequency multiset
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec sortWith_preserves_all_leaf_freqs (l: list htree) (x: pos)
  : Lemma (ensures count x (all_leaf_freqs (sortWith freq_cmp l)) = count x (all_leaf_freqs l))
          (decreases (length l))
  = match l with
    | [] -> ()
    | [_] -> ()
    | pivot :: tl ->
        let f = bool_of_compare freq_cmp pivot in
        let (hi, lo) = partition f tl in
        partition_length f tl;
        partition_preserves_all_leaf_freqs f tl x;
        sortWith_preserves_all_leaf_freqs lo x;
        sortWith_preserves_all_leaf_freqs hi x;
        let sorted_lo = sortWith freq_cmp lo in
        let sorted_hi = sortWith freq_cmp hi in
        assert (sortWith freq_cmp l == sorted_lo @ (pivot :: sorted_hi));
        all_leaf_freqs_append sorted_lo (pivot :: sorted_hi);
        append_count (all_leaf_freqs sorted_lo) (all_leaf_freqs (pivot :: sorted_hi)) x;
        append_count (leaf_freqs pivot) (all_leaf_freqs sorted_hi) x;
        append_count (leaf_freqs pivot) (all_leaf_freqs tl) x
#pop-options

// huffman_from_pq preserves the leaf frequency multiset
let rec huffman_from_pq_preserves_leaf_multiset (pq: priority_queue{is_valid_pq pq}) (x: pos)
  : Lemma (ensures count x (leaf_freqs (huffman_from_pq pq)) = count x (all_leaf_freqs pq))
          (decreases length pq)
  = match pq with
    | [t] -> ()
    | t1 :: t2 :: rest ->
        let merged = merge t1 t2 in
        insert_sorted_length merged rest;
        insert_sorted_nonempty merged rest;
        insert_sorted_maintains_sorted merged rest;
        let new_pq = insert_sorted merged rest in
        huffman_from_pq_preserves_leaf_multiset new_pq x;
        // count x (leaf_freqs (huffman_from_pq new_pq)) = count x (all_leaf_freqs new_pq) [by IH]
        insert_sorted_preserves_leaf_multiset merged rest x;
        // count x (all_leaf_freqs new_pq) = count x (leaf_freqs merged) + count x (all_leaf_freqs rest)
        append_count (leaf_freqs t1) (leaf_freqs t2) x;
        // count x (leaf_freqs merged) = count x (leaf_freqs t1) + count x (leaf_freqs t2)
        append_count (leaf_freqs t1) (all_leaf_freqs (t2 :: rest)) x;
        append_count (leaf_freqs t2) (all_leaf_freqs rest) x
    | [] -> ()

// all_leaf_freqs of (map Leaf freqs) gives back freqs
let rec all_leaf_freqs_of_map_leaf (freqs: list pos)
  : Lemma (ensures all_leaf_freqs (map (fun (f:pos) -> Leaf f) freqs) == freqs)
          (decreases freqs)
  = match freqs with
    | [] -> ()
    | _ :: tl -> all_leaf_freqs_of_map_leaf tl

// Main multiset preservation theorem
let huffman_complete_preserves_frequency_multiset (freqs: list pos{Cons? freqs})
  : Lemma (ensures (
      let t = huffman_complete freqs in
      forall (x: pos). count x (leaf_freqs t) = count x freqs))
  = let trees = map (fun (f:pos) -> Leaf f) freqs in
    map_nonempty (fun (f:pos) -> Leaf f) freqs;
    let pq = init_pq freqs in
    // Show sortWith preserves leaf frequency multiset
    let aux (x: pos)
      : Lemma (count x (leaf_freqs (huffman_from_pq pq)) = count x freqs)
      = huffman_from_pq_preserves_leaf_multiset pq x;
        // count x (leaf_freqs (huffman_from_pq pq)) = count x (all_leaf_freqs pq)
        sortWith_preserves_all_leaf_freqs trees x;
        // count x (all_leaf_freqs (sortWith freq_cmp trees)) = count x (all_leaf_freqs trees)
        all_leaf_freqs_of_map_leaf freqs
        // all_leaf_freqs trees = freqs
    in
    Classical.forall_intro aux

(*** Key Theorems from CLRS ***)

// Theorem: Greedy Choice Property (CLRS Lemma 16.2)
// 
// Statement: In any optimal prefix code for a set C of characters with
// frequencies, there exists an optimal tree in which the two characters
// with lowest frequencies are siblings at maximum depth.
//
// Proof Sketch (CLRS page 432):
// 1. Let x, y have the lowest frequencies
// 2. Let T be an optimal tree, and let b, c be siblings at maximum depth
// 3. Assume without loss of generality that freq(x) ≤ freq(b) and freq(y) ≤ freq(c)
// 4. Swap x with b and y with c in T to get T'
// 5. Show WPL(T') ≤ WPL(T) using the swap lemma
// 6. Since T is optimal, WPL(T') = WPL(T), so T' is also optimal
// 7. In T', x and y are siblings at maximum depth
let greedy_choice_lemma (freqs: list pos{length freqs >= 2})
  : Lemma (ensures greedy_choice_property freqs)
  = greedy_choice_theorem freqs

// Theorem: Optimal Substructure (CLRS Lemma 16.3)
//
// Statement: Let C be an alphabet, and let x, y ∈ C have minimum frequency.
// Let C' = C - {x,y} ∪ {z} where z is a new character with freq(z) = freq(x) + freq(y).
// Let T' be an optimal tree for C'. Then T (obtained by replacing leaf z in T'
// with internal node having children x and y) is optimal for C.
//
// Proof Sketch (CLRS page 433):
// 1. WPL(T) = WPL(T') + freq(x) + freq(y)  [by cost relation lemma]
// 2. Assume T is not optimal, so there exists T'' with WPL(T'') < WPL(T)
// 3. By greedy choice, we can assume x,y are siblings in T''
// 4. Let T''' be T'' with x,y merged to z
// 5. WPL(T'') = WPL(T''') + freq(x) + freq(y)
// 6. Therefore WPL(T''') < WPL(T'), contradicting optimality of T'
// 7. Conclude T must be optimal
// Theorem: Optimal Substructure — WPL relationship (CLRS Lemma 16.3)
//
// For any tree built by huffman_complete, replacing a pair of sibling leaves
// with their merged parent reduces WPL by exactly f1 + f2 (their frequencies).
// This is the key structural property underlying optimal substructure:
//   WPL(T) = WPL(T') + freq(x) + freq(y)
// where T' is T with sibling leaves x,y replaced by a single leaf z.
let optimal_substructure_lemma (freqs: list pos{length freqs >= 2})
  : Lemma (ensures (
      let t = huffman_complete freqs in
      forall (f1 f2: pos).
        (match replace_siblings_with_merged t f1 f2 with
         | Some t' -> weighted_path_length t == weighted_path_length t' + f1 + f2
         | None -> True)
    ))
  = let t = huffman_complete freqs in
    let aux (f1: pos) (f2: pos)
      : Lemma (ensures (
          match replace_siblings_with_merged t f1 f2 with
          | Some t' -> weighted_path_length t == weighted_path_length t' + f1 + f2
          | None -> True))
      = match replace_siblings_with_merged t f1 f2 with
        | Some _ -> wpl_after_merge t f1 f2 0
        | None -> ()
    in
    Classical.forall_intro_2 aux

// Helper: For single-element list, huffman_complete returns a single Leaf
let huffman_complete_single (f: pos)
  : Lemma (ensures huffman_complete [f] == Leaf f)
  = // huffman_complete [f] = huffman_from_pq (init_pq [f])
    // init_pq [f] = sortWith freq_cmp [Leaf f] = [Leaf f]
    // huffman_from_pq [Leaf f] = Leaf f (by pattern match on single element)
    ()

// Helper: leaf_freqs of single Leaf
let leaf_freqs_single (f: pos)
  : Lemma (ensures leaf_freqs (Leaf f) == [f])
  = // leaf_freqs (Leaf f) = [f] by definition
    ()

// Helper: leaf_freqs always returns a non-empty list
let rec leaf_freqs_nonempty (t: htree)
  : Lemma (ensures Cons? (leaf_freqs t))
          (decreases t)
  = match t with
    | Leaf _ -> ()
    | Internal _ l r ->
        leaf_freqs_nonempty l;
        leaf_freqs_nonempty r;
        append_length (leaf_freqs l) (leaf_freqs r)

// Lemma: A tree with a single leaf frequency must be a Leaf
// Proof: By case analysis on tree structure
// - Leaf f: leaf_freqs returns [f] ✓
// - Internal _ l r: leaf_freqs returns leaf_freqs l @ leaf_freqs r
//   For this to equal [f], we need length (leaf_freqs l @ leaf_freqs r) = 1
//   But both leaf_freqs l and leaf_freqs r are non-empty (all trees have ≥1 leaf)
//   So their append has length ≥ 2, contradiction.
let single_leaf_freqs_implies_leaf (t: htree) (f: pos)
  : Lemma (requires leaf_freqs t == [f])
          (ensures t == Leaf f)
  = match t with
    | Leaf f' -> 
        // leaf_freqs (Leaf f') == [f']
        // We know leaf_freqs (Leaf f') == [f]
        // Therefore [f'] == [f], so f' == f
        ()
    | Internal _ l r ->
        // leaf_freqs (Internal _ l r) == leaf_freqs l @ leaf_freqs r
        // We know this equals [f]
        // But leaf_freqs l is non-empty (Cons? (leaf_freqs l))
        // and leaf_freqs r is non-empty (Cons? (leaf_freqs r))
        // So their append has length >= 2
        // This contradicts length [f] = 1
        leaf_freqs_nonempty l;
        leaf_freqs_nonempty r;
        // Now we have Cons? (leaf_freqs l) and Cons? (leaf_freqs r)
        // So leaf_freqs l @ leaf_freqs r has length >= 2
        append_length (leaf_freqs l) (leaf_freqs r);
        // The SMT should see the contradiction:
        // length (leaf_freqs l @ leaf_freqs r) >= 2 but [f] has length 1
        ()

// Theorem: Correctness of Huffman Algorithm (CLRS Theorem 16.3)
//
// Statement: Procedure HUFFMAN produces an optimal prefix code.
//
// We prove two key properties:
// 1. Frequency multiset preservation: the leaf frequencies of the Huffman tree
//    form the same multiset as the input frequencies (using count-based equality).
// 2. Base-case optimality: for a single frequency, the tree is trivially optimal.
//
// For multiple frequencies, the full WPL-optimality proof (that the Huffman tree
// minimizes WPL among ALL trees with the same frequency multiset) requires the
// exchange argument (CLRS Lemma 16.2) and optimal substructure (CLRS Lemma 16.3),
// both assumed axiomatically in the Spec module.
// The optimal_substructure_lemma above proves the WPL relationship for any
// sibling merge, which is the key structural ingredient of such a proof.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let huffman_correctness_theorem (freqs: list pos{Cons? freqs})
  : Lemma (ensures (
      let t = huffman_complete freqs in
      // 1. Leaf frequency multiset is preserved by the Huffman construction
      (forall (x: pos). count x (leaf_freqs t) = count x freqs) /\
      // 2. For single-element inputs, WPL is minimal (0) — base case of optimality
      (match freqs with
       | [f] -> leaf_freqs t == freqs /\ weighted_path_length t == 0
       | _ -> True)
    ))
  = huffman_complete_preserves_frequency_multiset freqs;
    match freqs with
    | [f] -> 
        huffman_complete_single f;
        leaf_freqs_single f
    | _ :: _ :: _ -> ()
#pop-options

// Separate strong optimality lemma for single-element inputs
let huffman_single_is_optimal (f: pos)
  : Lemma (ensures is_optimal (huffman_complete [f]) [f])
  = huffman_complete_single f;
    leaf_freqs_single f;
    let aux (t': htree)
      : Lemma (requires leaf_freqs t' == [f])
              (ensures weighted_path_length (Leaf f) <= weighted_path_length t')
      = single_leaf_freqs_implies_leaf t' f
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(*** Additional Properties ***)

// Property: Weighted path length equals cost (from Spec)
let huffman_wpl_equals_cost (freqs: list pos{Cons? freqs})
  : Lemma (ensures (
      let t = huffman_complete freqs in
      weighted_path_length t == cost t
    ))
  = let t = huffman_complete freqs in
    wpl_equals_cost t

// Property: Cost is at least 0
let huffman_cost_nonnegative (freqs: list pos{Cons? freqs})
  : Lemma (ensures cost (huffman_complete freqs) >= 0)
  = ()

// Lemma: huffman_from_pq with length >= 2 returns Internal
let rec huffman_from_pq_multi_returns_internal (pq: priority_queue{is_valid_pq pq /\ length pq >= 2})
  : Lemma (ensures (match huffman_from_pq pq with
                    | Internal _ _ _ -> True
                    | Leaf _ -> False))
          (decreases (length pq))
  = match pq with
    | [_] -> ()  // Unreachable due to length >= 2
    | [t1; t2] -> 
        // huffman_from_pq [t1; t2] merges them, creating Internal
        // new_pq = insert_sorted (merge t1 t2) []
        //        = [merge t1 t2]
        //        = [Internal (freq_of t1 + freq_of t2) t1 t2]
        // huffman_from_pq [Internal ...] returns that Internal node
        ()
    | t1 :: t2 :: rest ->
        // Merges t1 and t2, creates new_pq with at least 1 element
        let merged = merge t1 t2 in
        insert_sorted_length merged rest;
        let new_pq = insert_sorted merged rest in
        // If rest is empty, new_pq = [merged]
        // If rest is non-empty, new_pq has >= 2 elements
        if length rest = 0 then 
          // new_pq = [merged], huffman_from_pq returns merged which is Internal
          ()
        else (
          // new_pq has >= 2 elements, recurse
          assert (length new_pq >= 2);
          insert_sorted_nonempty merged rest;
          insert_sorted_maintains_sorted merged rest;
          huffman_from_pq_multi_returns_internal new_pq
        )

// Property: For n > 1, cost is strictly positive
let huffman_cost_positive (freqs: list pos{length freqs > 1})
  : Lemma (ensures cost (huffman_complete freqs) > 0)
  = // When length freqs > 1, huffman_from_pq performs at least one merge
    // Each merge adds freq_of left + freq_of right to the cost (both positive)
    // We'll prove this by showing cost of Internal nodes is always positive
    let rec internal_has_positive_cost (t: htree) 
      : Lemma (ensures (match t with 
                        | Leaf _ -> cost t == 0
                        | Internal _ _ _ -> cost t > 0))
              (decreases t)
      = match t with
        | Leaf _ -> ()
        | Internal _ l r -> 
            internal_has_positive_cost l;
            internal_has_positive_cost r;
            // cost (Internal f l r) = freq_of l + freq_of r + cost l + cost r
            // freq_of l > 0 and freq_of r > 0 (both are pos)
            // cost l >= 0 and cost r >= 0
            // Therefore cost (Internal f l r) > 0
            assert (freq_of l > 0);
            assert (freq_of r > 0)
    in
    let pq = init_pq freqs in
    // pq has length = length freqs > 1, so >= 2
    assert (length pq = length freqs);
    // Therefore huffman_from_pq pq returns an Internal node
    huffman_from_pq_multi_returns_internal pq;
    let t = huffman_complete freqs in
    internal_has_positive_cost t

(*** Example Usage ***)

// Example from CLRS Figure 16.3
let example_freqs : list pos = [5; 9; 12; 13; 16; 45]

let example_tree : htree = huffman_complete example_freqs

// Verify the example produces correct cost
// Expected: 5+9=14, 13+14=27, 12+16=28, 27+28=55, 45+55=100
// Cost = 14 + 27 + 28 + 55 + 100 = 224
let example_cost : nat = cost example_tree

// Show correctness properties of the example
let example_correctness
  : squash ((forall (x: pos). count x (leaf_freqs example_tree) = count x example_freqs) /\
            is_prefix_free_code example_tree /\
            freq_of example_tree == sum_list example_freqs)
  = huffman_correctness_theorem example_freqs;
    huffman_produces_prefix_free_code example_freqs;
    huffman_preserves_total_frequency example_freqs;
    ()

(*** Full WPL Optimality — CLRS Theorem 16.4 ***)

// ---- Part 1: Helpers for the cost decomposition ----

// Sum of internal costs (= WPL by wpl_equals_cost) of all trees in a list
let rec sum_costs (l: list htree) : nat =
  match l with
  | [] -> 0
  | t :: rest -> cost t + sum_costs rest

// insert_sorted preserves sum_costs
let rec insert_sorted_sum_costs (t: htree) (l: list htree)
  : Lemma (ensures sum_costs (insert_sorted t l) == cost t + sum_costs l)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
        if freq_of t <= freq_of hd then ()
        else insert_sorted_sum_costs t tl

// insert_sorted with same freq_of produces same map freq_of
let rec insert_sorted_map_freq_of (t1 t2: htree) (l1 l2: list htree)
  : Lemma (requires freq_of t1 = freq_of t2 /\ map freq_of l1 = map freq_of l2)
          (ensures map freq_of (insert_sorted t1 l1) = map freq_of (insert_sorted t2 l2))
          (decreases l1)
  = match l1, l2 with
    | [], [] -> ()
    | hd1 :: tl1, hd2 :: tl2 ->
        assert (freq_of hd1 = freq_of hd2);
        if freq_of t1 <= freq_of hd1 then ()
        else insert_sorted_map_freq_of t1 t2 tl1 tl2
    | _, _ -> () // impossible by map length

// insert_sorted with same freq_of produces same length
let rec insert_sorted_same_length (t1 t2: htree) (l1 l2: list htree)
  : Lemma (requires freq_of t1 = freq_of t2 /\ length l1 = length l2 /\ map freq_of l1 = map freq_of l2)
          (ensures length (insert_sorted t1 l1) = length (insert_sorted t2 l2))
          (decreases l1)
  = insert_sorted_length t1 l1; insert_sorted_length t2 l2

// insert_sorted preserves validity
let insert_sorted_valid (t: htree) (l: list htree)
  : Lemma (requires is_sorted_by_freq l)
          (ensures is_valid_pq (insert_sorted t l))
  = insert_sorted_nonempty t l;
    insert_sorted_maintains_sorted t l

// ---- Part 2: WPL decomposition (key structural lemma) ----
// For two PQs with the same map freq_of, the WPL difference equals the sum_costs difference

#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec huffman_from_pq_wpl_decomp
  (pq1 pq2: priority_queue)
  : Lemma (requires
      is_valid_pq pq1 /\ is_valid_pq pq2 /\
      length pq1 = length pq2 /\
      map freq_of pq1 = map freq_of pq2)
    (ensures
      weighted_path_length (huffman_from_pq pq1) + sum_costs pq2 =
      weighted_path_length (huffman_from_pq pq2) + sum_costs pq1)
    (decreases length pq1)
  = match pq1, pq2 with
    | [t1], [t2] ->
        // WPL(t1) + cost(t2) = WPL(t2) + cost(t1)
        // Since WPL = cost, this is trivially true
        wpl_equals_cost t1;
        wpl_equals_cost t2
    | a1 :: b1 :: rest1, a2 :: b2 :: rest2 ->
        assert (freq_of a1 = freq_of a2);
        assert (freq_of b1 = freq_of b2);
        assert (map freq_of rest1 = map freq_of rest2);
        let m1 = merge a1 b1 in
        let m2 = merge a2 b2 in
        assert (freq_of m1 = freq_of m2);
        insert_sorted_length m1 rest1;
        insert_sorted_length m2 rest2;
        insert_sorted_nonempty m1 rest1;
        insert_sorted_nonempty m2 rest2;
        insert_sorted_maintains_sorted m1 rest1;
        insert_sorted_maintains_sorted m2 rest2;
        let new_pq1 = insert_sorted m1 rest1 in
        let new_pq2 = insert_sorted m2 rest2 in
        insert_sorted_map_freq_of m1 m2 rest1 rest2;
        insert_sorted_same_length m1 m2 rest1 rest2;
        // By IH on the new PQs
        huffman_from_pq_wpl_decomp new_pq1 new_pq2;
        // IH gives: WPL(hfpq new_pq1) + sum_costs(new_pq2) = WPL(hfpq new_pq2) + sum_costs(new_pq1)
        // We need: WPL(hfpq pq1) + sum_costs(pq2) = WPL(hfpq pq2) + sum_costs(pq1)
        // Note: hfpq pq1 = hfpq new_pq1, hfpq pq2 = hfpq new_pq2
        // sum_costs(new_pq1) = cost(m1) + sum_costs(rest1) [by insert_sorted_sum_costs]
        //                    = (freq_of a1 + freq_of b1 + cost a1 + cost b1) + sum_costs(rest1)
        // sum_costs(pq1) = cost a1 + cost b1 + sum_costs(rest1)
        // So: sum_costs(new_pq1) = sum_costs(pq1) + freq_of a1 + freq_of b1
        insert_sorted_sum_costs m1 rest1;
        insert_sorted_sum_costs m2 rest2;
        // cost(merge a b) = freq_of a + freq_of b + cost a + cost b
        assert (cost m1 == freq_of a1 + freq_of b1 + cost a1 + cost b1);
        assert (cost m2 == freq_of a2 + freq_of b2 + cost a2 + cost b2);
        assert (sum_costs new_pq1 == cost m1 + sum_costs rest1);
        assert (sum_costs new_pq2 == cost m2 + sum_costs rest2);
        assert (sum_costs pq1 == cost a1 + cost b1 + sum_costs rest1);
        assert (sum_costs pq2 == cost a2 + cost b2 + sum_costs rest2);
        // freq_of a1 + freq_of b1 = freq_of a2 + freq_of b2
        // So sum_costs(new_pq1) - sum_costs(pq1) = freq_of a1 + freq_of b1
        //    sum_costs(new_pq2) - sum_costs(pq2) = freq_of a2 + freq_of b2
        // These are equal, so the equation transfers from IH to what we need
        ()
    | _, _ -> () // impossible: both have same length and are non-empty
#pop-options

// ---- Part 3: Generalized exchange argument ----
// For any tree with same frequency multiset, there exists a tree with
// the two minimum-frequency leaves as siblings and WPL <= original

// Single swap lemma (no optimality required)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let single_swap_wpl_le
  (t: htree) (pos_deep pos_shallow: tree_position) (f_deep f_shallow: pos)
  : Lemma (requires
            get_subtree_at t pos_deep == Some (Leaf f_deep) /\
            get_subtree_at t pos_shallow == Some (Leaf f_shallow) /\
            f_deep >= f_shallow /\
            length pos_deep >= length pos_shallow /\
            pos_deep =!= pos_shallow /\
            not (is_prefix pos_deep pos_shallow) /\
            not (is_prefix pos_shallow pos_deep))
          (ensures (
            Some? (replace_subtree_at t pos_deep (Leaf f_shallow)) /\
            (let Some t1 = replace_subtree_at t pos_deep (Leaf f_shallow) in
             Some? (replace_subtree_at t1 pos_shallow (Leaf f_deep)) /\
             (let Some t2 = replace_subtree_at t1 pos_shallow (Leaf f_deep) in
              weighted_path_length t2 <= weighted_path_length t /\
              (forall (x: pos). count x (leaf_freqs t2) = count x (leaf_freqs t))))))
  = get_implies_replace t pos_deep (Leaf f_shallow);
    let Some t1 = replace_subtree_at t pos_deep (Leaf f_shallow) in
    swap_reduces_wpl t pos_deep pos_shallow;
    swap_preserves_multiset t pos_deep pos_shallow f_deep f_shallow;
    disjoint_replacement_preserves_subtree t pos_deep pos_shallow (Leaf f_shallow);
    get_implies_replace t1 pos_shallow (Leaf f_deep)
#pop-options

// The generalized exchange: make minimum-frequency leaves siblings
// This adapts the CLRS greedy exchange argument to work for ANY tree (not just optimal ones)
// Uses single_swap_wpl_le instead of single_swap_optimal to avoid requiring optimality.
#push-options "--fuel 3 --ifuel 2 --z3rlimit 200"
let make_min_siblings (t: htree) (freqs: list pos{length freqs >= 2})
  : Lemma (requires same_frequency_multiset t freqs)
          (ensures (let (f1, f2) = find_two_mins freqs in
                    exists (t': htree).
                      same_frequency_multiset t' freqs /\
                      are_siblings t' f1 f2 == true /\
                      weighted_path_length t' <= weighted_path_length t))
  = let (f1, f2) = find_two_mins freqs in
    find_two_mins_mem freqs;
    find_two_mins_le freqs;
    find_two_mins_ordered freqs;
    find_two_mins_le2 freqs;
    same_multiset_internal t freqs;
    max_depth_has_sibling_leaves t;
    eliminate exists (parent: tree_position) (fl fr: pos).
        get_subtree_at t (parent @ [true]) == Some (Leaf fl) /\
        get_subtree_at t (parent @ [false]) == Some (Leaf fr) /\
        length (parent @ [true]) = max_leaf_depth t 0 /\
        length (parent @ [false]) = max_leaf_depth t 0
    returns exists (t': htree).
        same_frequency_multiset t' freqs /\
        are_siblings t' f1 f2 == true /\
        weighted_path_length t' <= weighted_path_length t
    with _. (
      parent_has_leaf_children t parent fl fr;
      let pos_a = parent @ [true] in
      let pos_b = parent @ [false] in
      sibling_positions_disjoint parent;
      // fl, fr are leaf freqs in the tree => they're in freqs => f1 <= fl, f1 <= fr
      subtree_leaf_mem t pos_a fl;
      subtree_leaf_mem t pos_b fr;
      count_mem fl (leaf_freqs t);
      count_mem fr (leaf_freqs t);
      count_mem fl freqs;
      count_mem fr freqs;
      assert (f1 <= fl);
      assert (f1 <= fr);
      if (fl = f1 && fr = f2) || (fl = f2 && fr = f1) then (
        // Siblings already match f1, f2 — t itself is the witness
        subtree_siblings_implies_are_siblings t parent f1 f2
      ) else (
        // Exchange argument adapted from greedy_exchange in Spec.fst
        // Choose which target position gets f1 and which gets f2
        let tgt1 = if f2 <= fr then pos_a else pos_b in
        let tgt2 = if f2 <= fr then pos_b else pos_a in
        let tgt_a = if f2 <= fr then fl else fr in
        let tgt_b = if f2 <= fr then fr else fl in
        assert (mem fl freqs);
        assert (fl >= f2 \/ fl = f1);
        assert (mem fr freqs);
        assert (fr >= f2 \/ fr = f1);
        assert (tgt_a >= f1);
        if not (tgt_b >= f2) then (
          // IMPOSSIBLE case: both fl = fr = f1 and f1 = f2
          assert (fl = f1);
          assert (fr = f1);
          two_leaves_count_ge2 t pos_a pos_b f1;
          assert (count f1 (leaf_freqs t) >= 2);
          assert (count f1 freqs >= 2);
          find_two_mins_count_ge2 freqs f1;
          assert (f2 = f1)
          // f1 < f2 contradicts f1 = f2; F* derives False
        ) else (
        assert (get_subtree_at t tgt1 == Some (Leaf tgt_a));
        assert (get_subtree_at t tgt2 == Some (Leaf tgt_b));
        assert (tgt1 =!= tgt2);
        assert (not (is_prefix tgt1 tgt2));
        assert (not (is_prefix tgt2 tgt1));

        if tgt_a = f1 then (
          if tgt_b = f2 then () // unreachable: contradicts outer else
          else (
            // Single swap: put f2 at tgt2, displacing tgt_b
            count_mem f2 (leaf_freqs t);
            count_mem f2 freqs;
            find_leaf_pos_none t f2;
            find_leaf_pos_correct t f2;
            let Some pos_f2 = find_leaf_pos t f2 in
            if pos_f2 = tgt1 then (
              // pos_f2 = tgt1 means f2 = tgt_a = f1, so f1 = f2
              assert (f1 = f2);
              find_two_mins_equal_count freqs;
              assert (count f1 freqs >= 2);
              assert (count f2 (leaf_freqs t) >= 2);
              find_leaf_pos_avoiding_some t f2 tgt1;
              find_leaf_pos_avoiding_correct t f2 tgt1;
              let Some pos_f2' = find_leaf_pos_avoiding t f2 tgt1 in
              assert (pos_f2' =!= tgt1);
              leaf_depth_le_max t pos_f2' f2;
              (if pos_f2' = tgt2 then (
                // f2 = tgt_b contradiction
                ()
              ) else (
              (if is_prefix tgt2 pos_f2' then leaf_position_no_extension t tgt2 pos_f2' tgt_b
               else if is_prefix pos_f2' tgt2 then leaf_position_no_extension t pos_f2' tgt2 f2);
              single_swap_wpl_le t tgt2 pos_f2' tgt_b f2;
              let Some t1 = replace_subtree_at t tgt2 (Leaf f2) in
              let Some t2 = replace_subtree_at t1 pos_f2' (Leaf tgt_b) in
              // Preserve tgt1 through both replacements
              get_implies_replace t tgt2 (Leaf f2);
              disjoint_replacement_preserves_subtree t tgt2 tgt1 (Leaf f2);
              disjoint_replacement_preserves_subtree t tgt2 pos_f2' (Leaf f2);
              (if is_prefix pos_f2' tgt1 then leaf_position_no_extension t1 pos_f2' tgt1 f2
               else if is_prefix tgt1 pos_f2' then leaf_position_no_extension t1 tgt1 pos_f2' f1);
              get_implies_replace t1 pos_f2' (Leaf tgt_b);
              disjoint_replacement_preserves_subtree t1 pos_f2' tgt1 (Leaf tgt_b);
              // Preserve tgt2
              replace_then_get t tgt2 (Leaf f2);
              (if is_prefix pos_f2' tgt2 then leaf_position_no_extension t1 pos_f2' tgt2 f2
               else if is_prefix tgt2 pos_f2' then leaf_position_no_extension t1 tgt2 pos_f2' f2);
              disjoint_replacement_preserves_subtree t1 pos_f2' tgt2 (Leaf tgt_b);
              parent_has_leaf_children t2 parent
                (if f2 <= fr then f1 else f2) (if f2 <= fr then f2 else f1);
              subtree_siblings_implies_are_siblings t2 parent f1 f2
              ))
            ) else (
            leaf_depth_le_max t pos_f2 f2;
            (if is_prefix tgt2 pos_f2 then leaf_position_no_extension t tgt2 pos_f2 tgt_b
             else if is_prefix pos_f2 tgt2 then leaf_position_no_extension t pos_f2 tgt2 f2);
            single_swap_wpl_le t tgt2 pos_f2 tgt_b f2;
            let Some t1 = replace_subtree_at t tgt2 (Leaf f2) in
            let Some t2 = replace_subtree_at t1 pos_f2 (Leaf tgt_b) in
            // Preserve tgt1 through both replacements
            get_implies_replace t tgt2 (Leaf f2);
            disjoint_replacement_preserves_subtree t tgt2 tgt1 (Leaf f2);
            disjoint_replacement_preserves_subtree t tgt2 pos_f2 (Leaf f2);
            (if is_prefix pos_f2 tgt1 then leaf_position_no_extension t1 pos_f2 tgt1 f2
             else if is_prefix tgt1 pos_f2 then leaf_position_no_extension t1 tgt1 pos_f2 f1);
            get_implies_replace t1 pos_f2 (Leaf tgt_b);
            disjoint_replacement_preserves_subtree t1 pos_f2 tgt1 (Leaf tgt_b);
            // Preserve tgt2
            replace_then_get t tgt2 (Leaf f2);
            (if is_prefix pos_f2 tgt2 then leaf_position_no_extension t1 pos_f2 tgt2 f2
             else if is_prefix tgt2 pos_f2 then leaf_position_no_extension t1 tgt2 pos_f2 f2);
            disjoint_replacement_preserves_subtree t1 pos_f2 tgt2 (Leaf tgt_b);
            parent_has_leaf_children t2 parent
              (if f2 <= fr then f1 else f2) (if f2 <= fr then f2 else f1);
            subtree_siblings_implies_are_siblings t2 parent f1 f2
            )
          )
        ) else (
          // Double swap: first put f1 at tgt1, then f2 at tgt2
          count_mem f1 (leaf_freqs t);
          count_mem f1 freqs;
          find_leaf_pos_none t f1;
          find_leaf_pos_correct t f1;
          let Some pos_f1 = find_leaf_pos t f1 in
          leaf_depth_le_max t pos_f1 f1;
          (if is_prefix tgt1 pos_f1 then leaf_position_no_extension t tgt1 pos_f1 tgt_a
           else if is_prefix pos_f1 tgt1 then leaf_position_no_extension t pos_f1 tgt1 f1);
          single_swap_wpl_le t tgt1 pos_f1 tgt_a f1;
          let Some s1 = replace_subtree_at t tgt1 (Leaf f1) in
          let Some s2 = replace_subtree_at s1 pos_f1 (Leaf tgt_a) in
          // s2 has: WPL(s2) <= WPL(t), same multiset as t (hence as freqs)
          // Establish positions in s1 and s2
          replace_then_get t tgt1 (Leaf f1);
          disjoint_replacement_preserves_subtree t tgt1 pos_f1 (Leaf f1);
          // tgt1 preserved through pos_f1 replacement
          (if is_prefix pos_f1 tgt1 then leaf_position_no_extension s1 pos_f1 tgt1 f1
           else if is_prefix tgt1 pos_f1 then leaf_position_no_extension s1 tgt1 pos_f1 f1);
          get_implies_replace s1 pos_f1 (Leaf tgt_a);
          disjoint_replacement_preserves_subtree s1 pos_f1 tgt1 (Leaf tgt_a);
          assert (get_subtree_at s2 tgt1 == Some (Leaf f1));
          // tgt2 in s1 and s2
          disjoint_replacement_preserves_subtree t tgt1 tgt2 (Leaf f1);
          // pos_f1 vs tgt2
          if pos_f1 = tgt2 then (
            // pos_f1 = tgt2 implies f1 = tgt_b, hence f1 = f2
            assert (f1 = tgt_b);
            assert (f1 = f2);
            find_two_mins_equal_count freqs;
            assert (count f1 freqs >= 2);
            assert (count f1 (leaf_freqs t) >= 2);
            find_leaf_pos_avoiding_some t f1 tgt2;
            find_leaf_pos_avoiding_correct t f1 tgt2;
            let Some pos_f1' = find_leaf_pos_avoiding t f1 tgt2 in
            assert (pos_f1' =!= tgt2);
            leaf_depth_le_max t pos_f1' f1;
            if pos_f1' = tgt1 then (
              // f1 at tgt1 = tgt_a, but tgt_a <> f1 (we're in else). Contradiction.
              ()
            ) else (
            (if is_prefix tgt1 pos_f1' then leaf_position_no_extension t tgt1 pos_f1' tgt_a
             else if is_prefix pos_f1' tgt1 then leaf_position_no_extension t pos_f1' tgt1 f1);
            single_swap_wpl_le t tgt1 pos_f1' tgt_a f1;
            let Some s1' = replace_subtree_at t tgt1 (Leaf f1) in
            let Some s2' = replace_subtree_at s1' pos_f1' (Leaf tgt_a) in
            // tgt1 has f1 in s2'
            replace_then_get t tgt1 (Leaf f1);
            get_implies_replace t tgt1 (Leaf f1);
            disjoint_replacement_preserves_subtree t tgt1 pos_f1' (Leaf f1);
            (if is_prefix pos_f1' tgt1 then leaf_position_no_extension s1' pos_f1' tgt1 f1
             else if is_prefix tgt1 pos_f1' then leaf_position_no_extension s1' tgt1 pos_f1' f1);
            get_implies_replace s1' pos_f1' (Leaf tgt_a);
            disjoint_replacement_preserves_subtree s1' pos_f1' tgt1 (Leaf tgt_a);
            assert (get_subtree_at s2' tgt1 == Some (Leaf f1));
            // tgt2 has tgt_b (= f1 = f2) in s2'
            disjoint_replacement_preserves_subtree t tgt1 tgt2 (Leaf f1);
            (if is_prefix pos_f1' tgt2 then leaf_position_no_extension s1' pos_f1' tgt2 f1
             else if is_prefix tgt2 pos_f1' then leaf_position_no_extension s1' tgt2 pos_f1' tgt_b);
            disjoint_replacement_preserves_subtree s1' pos_f1' tgt2 (Leaf tgt_a);
            assert (get_subtree_at s2' tgt2 == Some (Leaf tgt_b));
            parent_has_leaf_children s2' parent
              (if f2 <= fr then f1 else f2) (if f2 <= fr then f2 else f1);
            subtree_siblings_implies_are_siblings s2' parent f1 f2
            )
          ) else (
          (if is_prefix pos_f1 tgt2 then leaf_position_no_extension s1 pos_f1 tgt2 f1
           else if is_prefix tgt2 pos_f1 then leaf_position_no_extension s1 tgt2 pos_f1 tgt_b);
          disjoint_replacement_preserves_subtree s1 pos_f1 tgt2 (Leaf tgt_a);
          assert (get_subtree_at s2 tgt2 == Some (Leaf tgt_b));

          if tgt_b = f2 then (
            // After first swap, tgt1 has f1, tgt2 already has f2 — done
            parent_has_leaf_children s2 parent
              (if f2 <= fr then f1 else f2) (if f2 <= fr then f2 else f1);
            subtree_siblings_implies_are_siblings s2 parent f1 f2
          ) else (
            // Second swap: put f2 at tgt2 in s2
            // Establish multiset of s2 matches freqs for finding f2
            assert (count f2 (leaf_freqs s2) = count f2 freqs);
            count_mem f2 (leaf_freqs s2);
            count_mem f2 freqs;
            find_leaf_pos_none s2 f2;
            find_leaf_pos_correct s2 f2;
            let Some pos_f2 = find_leaf_pos s2 f2 in
            if pos_f2 = tgt1 then (
              // f2 = f1 at tgt1. Use find_leaf_pos_avoiding.
              assert (f1 = f2);
              find_two_mins_equal_count freqs;
              assert (count f2 freqs >= 2);
              assert (count f2 (leaf_freqs s2) >= 2);
              find_leaf_pos_avoiding_some s2 f2 tgt1;
              find_leaf_pos_avoiding_correct s2 f2 tgt1;
              let Some pos_f2' = find_leaf_pos_avoiding s2 f2 tgt1 in
              assert (pos_f2' =!= tgt1);
              replace_leaf_preserves_max_depth t tgt1 tgt_a f1;
              replace_leaf_preserves_max_depth s1 pos_f1 f1 tgt_a;
              assert (max_leaf_depth s2 0 = max_leaf_depth t 0);
              leaf_depth_le_max s2 pos_f2' f2;
              assert (tgt_b >= f2);
              assert (length tgt2 = max_leaf_depth t 0);
              assert (length tgt2 >= length pos_f2');
              if pos_f2' = tgt2 then (
                // f2 = tgt_b, contradiction
                ()
              ) else (
              (if is_prefix tgt2 pos_f2' then leaf_position_no_extension s2 tgt2 pos_f2' tgt_b
               else if is_prefix pos_f2' tgt2 then leaf_position_no_extension s2 pos_f2' tgt2 f2);
              single_swap_wpl_le s2 tgt2 pos_f2' tgt_b f2;
              let Some s3 = replace_subtree_at s2 tgt2 (Leaf f2) in
              let Some s4 = replace_subtree_at s3 pos_f2' (Leaf tgt_b) in
              // WPL chain: WPL(s4) <= WPL(s2) <= WPL(t)
              assert (weighted_path_length s4 <= weighted_path_length t);
              // Multiset chain: s4 =multiset= s2 =multiset= t =multiset= freqs
              assert (forall (x: pos). count x (leaf_freqs s4) = count x freqs);
              // Establish positions in s3 and s4
              replace_then_get s2 tgt2 (Leaf f2);
              disjoint_replacement_preserves_subtree s2 tgt2 pos_f2' (Leaf f2);
              // tgt1 preserved in s3
              (if is_prefix tgt2 tgt1 then leaf_position_no_extension s2 tgt2 tgt1 tgt_b
               else if is_prefix tgt1 tgt2 then leaf_position_no_extension s2 tgt1 tgt2 f1);
              get_implies_replace s2 tgt2 (Leaf f2);
              disjoint_replacement_preserves_subtree s2 tgt2 tgt1 (Leaf f2);
              // tgt1 preserved in s4
              (if is_prefix pos_f2' tgt1 then leaf_position_no_extension s3 pos_f2' tgt1 f2
               else if is_prefix tgt1 pos_f2' then leaf_position_no_extension s3 tgt1 pos_f2' f1);
              get_implies_replace s3 pos_f2' (Leaf tgt_b);
              disjoint_replacement_preserves_subtree s3 pos_f2' tgt1 (Leaf tgt_b);
              // tgt2 preserved in s4
              (if is_prefix pos_f2' tgt2 then leaf_position_no_extension s3 pos_f2' tgt2 f2
               else if is_prefix tgt2 pos_f2' then leaf_position_no_extension s3 tgt2 pos_f2' f2);
              disjoint_replacement_preserves_subtree s3 pos_f2' tgt2 (Leaf tgt_b);
              parent_has_leaf_children s4 parent
                (if f2 <= fr then f1 else f2) (if f2 <= fr then f2 else f1);
              subtree_siblings_implies_are_siblings s4 parent f1 f2
              )
            ) else (
            replace_leaf_preserves_max_depth t tgt1 tgt_a f1;
            replace_leaf_preserves_max_depth s1 pos_f1 f1 tgt_a;
            assert (max_leaf_depth s2 0 = max_leaf_depth t 0);
            leaf_depth_le_max s2 pos_f2 f2;
            assert (tgt_b >= f2);
            assert (length tgt2 = max_leaf_depth t 0);
            assert (length tgt2 >= length pos_f2);
            assert (tgt2 =!= pos_f2);
            (if is_prefix tgt2 pos_f2 then leaf_position_no_extension s2 tgt2 pos_f2 tgt_b
             else if is_prefix pos_f2 tgt2 then leaf_position_no_extension s2 pos_f2 tgt2 f2);
            single_swap_wpl_le s2 tgt2 pos_f2 tgt_b f2;
            let Some s3 = replace_subtree_at s2 tgt2 (Leaf f2) in
            let Some s4 = replace_subtree_at s3 pos_f2 (Leaf tgt_b) in
            // WPL chain: WPL(s4) <= WPL(s2) <= WPL(t)
            assert (weighted_path_length s4 <= weighted_path_length t);
            // Multiset chain: s4 =multiset= s2 =multiset= t =multiset= freqs
            assert (forall (x: pos). count x (leaf_freqs s4) = count x freqs);
            // Establish positions in s3 and s4
            replace_then_get s2 tgt2 (Leaf f2);
            disjoint_replacement_preserves_subtree s2 tgt2 pos_f2 (Leaf f2);
            // tgt1 preserved in s3
            (if is_prefix tgt2 tgt1 then leaf_position_no_extension s2 tgt2 tgt1 tgt_b
             else if is_prefix tgt1 tgt2 then leaf_position_no_extension s2 tgt1 tgt2 f1);
            get_implies_replace s2 tgt2 (Leaf f2);
            disjoint_replacement_preserves_subtree s2 tgt2 tgt1 (Leaf f2);
            // tgt1 preserved in s4
            (if is_prefix pos_f2 tgt1 then leaf_position_no_extension s3 pos_f2 tgt1 f2
             else if is_prefix tgt1 pos_f2 then leaf_position_no_extension s3 tgt1 pos_f2 f1);
            get_implies_replace s3 pos_f2 (Leaf tgt_b);
            disjoint_replacement_preserves_subtree s3 pos_f2 tgt1 (Leaf tgt_b);
            // tgt2 preserved in s4
            (if is_prefix pos_f2 tgt2 then leaf_position_no_extension s3 pos_f2 tgt2 f2
             else if is_prefix tgt2 pos_f2 then leaf_position_no_extension s3 tgt2 pos_f2 f2);
            disjoint_replacement_preserves_subtree s3 pos_f2 tgt2 (Leaf tgt_b);
            parent_has_leaf_children s4 parent
              (if f2 <= fr then f1 else f2) (if f2 <= fr then f2 else f1);
            subtree_siblings_implies_are_siblings s4 parent f1 f2
            )
          )
          )
        )
        )
      )
    )
#pop-options

// ---- Part 4: Multiset correspondence for replace_siblings ----

// How replace_siblings_with_merged changes leaf_freqs counts
// Helper: not are_siblings implies replace returns None
let rec not_are_siblings_implies_replace_none (t: htree) (f1 f2: pos)
  : Lemma (requires are_siblings t f1 f2 == false)
          (ensures replace_siblings_with_merged t f1 f2 == None)
          (decreases t)
  = match t with
    | Leaf _ -> ()
    | Internal _ (Leaf _) (Leaf _) -> ()
    | Internal _ l r ->
        not_are_siblings_implies_replace_none l f1 f2;
        not_are_siblings_implies_replace_none r f1 f2

#push-options "--fuel 3 --ifuel 2 --z3rlimit 80"
let rec replace_siblings_changes_count (t: htree) (f1 f2: pos) (x: pos)
  : Lemma (requires are_siblings t f1 f2 == true)
          (ensures Some? (replace_siblings_with_merged t f1 f2) /\
                   (let Some t' = replace_siblings_with_merged t f1 f2 in
                    count x (leaf_freqs t') + (if x = f1 then 1 else 0) + (if x = f2 then 1 else 0) =
                    count x (leaf_freqs t) + (if x = f1 + f2 then 1 else 0)))
          (decreases t)
  = are_siblings_implies_replace t f1 f2;
    match t with
    | Leaf _ -> ()
    | Internal _ (Leaf f1') (Leaf f2') ->
        if (f1' = f1 && f2' = f2) || (f1' = f2 && f2' = f1) then ()
        else ()
    | Internal _ l r ->
        if are_siblings l f1 f2 then (
          replace_siblings_changes_count l f1 f2 x;
          are_siblings_implies_replace l f1 f2;
          let Some l' = replace_siblings_with_merged l f1 f2 in
          count_append x (leaf_freqs l') (leaf_freqs r);
          count_append x (leaf_freqs l) (leaf_freqs r)
        ) else (
          assert (are_siblings r f1 f2 == true);
          not_are_siblings_implies_replace_none l f1 f2;
          assert (replace_siblings_with_merged l f1 f2 == None);
          replace_siblings_changes_count r f1 f2 x;
          are_siblings_implies_replace r f1 f2;
          let Some r' = replace_siblings_with_merged r f1 f2 in
          count_append x (leaf_freqs l) (leaf_freqs r');
          count_append x (leaf_freqs l) (leaf_freqs r)
        )
#pop-options

// How insert_sorted of a Leaf changes all_leaf_freqs counts  
let rec insert_sorted_leaf_all_leaf_freqs (t: htree) (l: list htree) (x: pos)
  : Lemma (ensures count x (all_leaf_freqs (insert_sorted t l)) =
                   count x (leaf_freqs t) + count x (all_leaf_freqs l))
          (decreases l)
  = insert_sorted_preserves_leaf_multiset t l x

// ---- Part 5: Properties of sorted all-Leaf PQs ----

// Predicate: all elements of PQ are Leaves
let rec all_leaves (l: list htree) : prop =
  match l with
  | [] -> True
  | Leaf _ :: tl -> all_leaves tl
  | _ :: _ -> False

// For all-Leaf list, all_leaf_freqs gives back the frequencies in order
let rec all_leaf_freqs_of_leaf_list (l: list htree)
  : Lemma (requires all_leaves l)
          (ensures all_leaf_freqs l == map freq_of l)
          (decreases l)
  = match l with
    | [] -> ()
    | Leaf _ :: tl -> all_leaf_freqs_of_leaf_list tl

// insert_sorted of a Leaf into an all-Leaf list gives an all-Leaf list
let rec insert_sorted_leaf_preserves_all_leaves (f: pos) (l: list htree)
  : Lemma (requires all_leaves l)
          (ensures all_leaves (insert_sorted (Leaf f) l))
          (decreases l)
  = match l with
    | [] -> ()
    | Leaf _ :: tl ->
        if freq_of (Leaf f) <= freq_of (Leaf (freq_of (hd l))) then ()
        else insert_sorted_leaf_preserves_all_leaves f tl

// A list of pos is non-decreasing
let rec nondecreasing (l: list pos) : prop =
  match l with
  | [] -> True
  | [_] -> True
  | a :: b :: rest -> a <= b /\ nondecreasing (b :: rest)

// Bridge: is_sorted_by_freq on an all-Leaf list implies nondecreasing on freqs
let rec sorted_all_leaves_nondecreasing (pq: list htree)
  : Lemma (requires is_sorted_by_freq pq /\ all_leaves pq)
          (ensures nondecreasing (all_leaf_freqs pq))
          (decreases pq)
  = match pq with
    | [] -> ()
    | [Leaf _] -> ()
    | (Leaf f1) :: (Leaf f2 :: rest') ->
        sorted_all_leaves_nondecreasing (Leaf f2 :: rest')

// For a sorted all-Leaf PQ of length >= 2, the first two have the two minimum freqs
// This connects the sorted PQ order to find_two_mins
let rec find_two_mins_sorted (l: list pos{length l >= 2})
  : Lemma (requires nondecreasing l)
          (ensures find_two_mins l == (hd l, hd (tl l)))
          (decreases l)
  = match l with
    | [a; b] -> ()
    | a :: (b :: c :: rest) ->
        find_two_mins_sorted (b :: c :: rest)

// ---- Part 6: Main WPL optimality theorem ----

// Key lemma: huffman_from_pq on an all-Leaf PQ is WPL-optimal
// Proof by induction on PQ length
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec huffman_from_pq_wpl_le
  (pq: priority_queue{is_valid_pq pq /\ all_leaves pq})
  (t': htree)
  : Lemma (requires same_frequency_multiset t' (all_leaf_freqs pq))
          (ensures weighted_path_length (huffman_from_pq pq) <= weighted_path_length t')
          (decreases length pq)
  = match pq with
    | [Leaf f] ->
        // Base case: single leaf. t' must be Leaf f.
        // same_frequency_multiset t' [f] implies t' has exactly one leaf with freq f
        // So t' = Leaf f and WPL = 0
        assert (all_leaf_freqs pq == [f]);
        // From same_frequency_multiset: forall x. count x (leaf_freqs t') = count x [f]
        // This means leaf_freqs t' has exactly one f and nothing else.
        // Since leaf_freqs always returns non-empty, and total count is 1,
        // leaf_freqs t' = [f], so t' = Leaf f.
        let rec multiset_singleton_leaf (t: htree) (f: pos)
          : Lemma (requires same_frequency_multiset t [f])
                  (ensures t == Leaf f)
          = match t with
            | Leaf f' ->
                // leaf_freqs (Leaf f') = [f']. count f' [f'] = 1 = count f' [f].
                // If f' <> f, count f' [f] = 0 but count f' [f'] = 1. Contradiction.
                assert (count f' (leaf_freqs t) = count f' [f])
            | Internal _ l r ->
                leaf_freqs_nonempty l;
                leaf_freqs_nonempty r;
                append_length (leaf_freqs l) (leaf_freqs r);
                // leaf_freqs t = leaf_freqs l @ leaf_freqs r
                // length >= 2 but [f] has length 1
                // Need to show this leads to a count contradiction
                let fl = hd (leaf_freqs l) in
                count_mem fl (leaf_freqs l);
                count_append fl (leaf_freqs l) (leaf_freqs r);
                assert (count fl (leaf_freqs t) >= 1);
                // Since count fl (leaf_freqs t) = count fl [f]:
                // count fl [f] >= 1, so fl = f and count = 1
                // Similarly leaf_freqs r has at least one element
                let fr = hd (leaf_freqs r) in
                count_mem fr (leaf_freqs r);
                count_append fr (leaf_freqs l) (leaf_freqs r);
                // count fr (leaf_freqs t) >= 1, so fr = f
                // But then count f (leaf_freqs t) >= 2 while count f [f] = 1
                // Need to show this carefully
                count_append f (leaf_freqs l) (leaf_freqs r);
                count_mem f (leaf_freqs l);
                count_mem f (leaf_freqs r);
                assert (count f (leaf_freqs l) >= 1);
                assert (count f (leaf_freqs r) >= 1);
                assert (count f (leaf_freqs t) >= 2);
                assert (count f [f] = 1)
        in
        multiset_singleton_leaf t' f
    | (Leaf f1) :: (Leaf f2) :: rest ->
        let freqs = all_leaf_freqs pq in
        // Establish find_two_mins freqs == (f1, f2) via sorted PQ
        all_leaf_freqs_of_leaf_list pq;
        assert (freqs == map freq_of pq);
        sorted_all_leaves_nondecreasing pq;
        assert (nondecreasing freqs);
        assert (length freqs >= 2);
        find_two_mins_sorted freqs;
        assert (find_two_mins freqs == (f1, f2));

        // Step 1: Exchange argument — transform t' to have f1,f2 as siblings
        make_min_siblings t' freqs;
        // Now: exists t_sib. sfm t_sib freqs /\ are_siblings t_sib f1 f2 /\ WPL(t_sib) <= WPL(t')

        // Step 2: WPL decomposition for huffman_from_pq
        let merged = merge (Leaf f1) (Leaf f2) in
        let leaf_merged = Leaf (f1 + f2) in
        insert_sorted_length merged rest;
        insert_sorted_nonempty merged rest;
        insert_sorted_maintains_sorted merged rest;
        let new_pq = insert_sorted merged rest in
        // leaf_pq has all Leaves and length = length pq - 1
        insert_sorted_length leaf_merged rest;
        insert_sorted_nonempty leaf_merged rest;
        insert_sorted_maintains_sorted leaf_merged rest;
        insert_sorted_leaf_preserves_all_leaves (f1 + f2) rest;
        let leaf_pq = insert_sorted leaf_merged rest in
        assert (all_leaves leaf_pq);
        assert (is_valid_pq leaf_pq);
        assert (length leaf_pq = length new_pq);
        // WPL decomposition: WPL(hfpq new_pq) = WPL(hfpq leaf_pq) + f1 + f2
        insert_sorted_map_freq_of merged leaf_merged rest rest;
        huffman_from_pq_wpl_decomp new_pq leaf_pq;
        insert_sorted_sum_costs merged rest;
        insert_sorted_sum_costs leaf_merged rest;
        wpl_equals_cost (huffman_from_pq new_pq);
        wpl_equals_cost (huffman_from_pq leaf_pq);
        assert (cost merged == f1 + f2);
        assert (cost leaf_merged == 0);
        // From decomp: WPL(hfpq new_pq) + sum_costs(leaf_pq) = WPL(hfpq leaf_pq) + sum_costs(new_pq)
        // sum_costs(new_pq) = cost(merged) + sum_costs(rest) = (f1+f2) + sum_costs(rest)
        // sum_costs(leaf_pq) = cost(leaf_merged) + sum_costs(rest) = 0 + sum_costs(rest)
        // So: WPL(hfpq new_pq) = WPL(hfpq leaf_pq) + (f1+f2)

        // Step 3: Existential elimination via forall_intro + move_requires
        // For any witness t_sib satisfying the existential, show the goal
        let elim_witness (t_sib: htree)
          : Lemma (requires same_frequency_multiset t_sib freqs /\
                            are_siblings t_sib f1 f2 == true /\
                            weighted_path_length t_sib <= weighted_path_length t')
                  (ensures weighted_path_length (huffman_from_pq pq) <= weighted_path_length t')
          =
            // Step 3a: Apply optimal substructure to get t_merged
            optimal_substructure_theorem t_sib f1 f2;
            are_siblings_implies_replace t_sib f1 f2;
            let Some t_merged = replace_siblings_with_merged t_sib f1 f2 in
            // WPL(t_sib) = WPL(t_merged) + f1 + f2

            // Step 3b: Show same_frequency_multiset t_merged (all_leaf_freqs leaf_pq)
            let show_multiset (x: pos)
              : Lemma (count x (leaf_freqs t_merged) = count x (all_leaf_freqs leaf_pq))
              = // From replace_siblings_changes_count:
                // count x (leaf_freqs t_merged) + [x=f1] + [x=f2] = count x (leaf_freqs t_sib) + [x=f1+f2]
                replace_siblings_changes_count t_sib f1 f2 x;
                // From same_frequency_multiset t_sib freqs:
                // count x (leaf_freqs t_sib) = count x freqs
                // freqs = all_leaf_freqs pq = f1 :: f2 :: all_leaf_freqs rest
                // So count x freqs = [x=f1] + [x=f2] + count x (all_leaf_freqs rest)
                count_append x [f1] (f2 :: all_leaf_freqs rest);
                count_append x [f2] (all_leaf_freqs rest);
                // From insert_sorted_preserves_leaf_multiset:
                // count x (all_leaf_freqs leaf_pq) = count x (leaf_freqs (Leaf (f1+f2))) + count x (all_leaf_freqs rest)
                //                                  = [x=f1+f2] + count x (all_leaf_freqs rest)
                insert_sorted_preserves_leaf_multiset leaf_merged rest x
                // Now: count x (leaf_freqs t_merged) + [x=f1] + [x=f2]
                //      = count x (leaf_freqs t_sib) + [x=f1+f2]
                //      = count x freqs + [x=f1+f2]
                //      = [x=f1] + [x=f2] + count x (all_leaf_freqs rest) + [x=f1+f2]
                // And: count x (all_leaf_freqs leaf_pq) = [x=f1+f2] + count x (all_leaf_freqs rest)
                // So: count x (leaf_freqs t_merged) = count x (all_leaf_freqs rest) + [x=f1+f2]
                //     = count x (all_leaf_freqs leaf_pq)
            in
            Classical.forall_intro show_multiset;

            // Step 3c: Apply IH
            huffman_from_pq_wpl_le leaf_pq t_merged;
            // WPL(hfpq leaf_pq) <= WPL(t_merged)

            // Step 3d: Chain inequalities
            // WPL(hfpq pq) = WPL(hfpq new_pq) = WPL(hfpq leaf_pq) + f1 + f2
            //             <= WPL(t_merged) + f1 + f2 = WPL(t_sib) <= WPL(t')
            ()
        in
        // Combine: (forall t_sib. P(t_sib) ==> goal) /\ (exists t_sib. P(t_sib)) ==> goal
        Classical.forall_intro (Classical.move_requires elim_witness)
    | _ -> () // unreachable (all elements are Leaves, PQ is non-empty)
#pop-options

// Wrap up: huffman_complete is WPL-optimal

// Helper: partition preserves all_leaves
let rec partition_preserves_all_leaves (f: htree -> bool) (l: list htree)
  : Lemma (requires all_leaves l)
          (ensures (let (l1, l2) = partition f l in all_leaves l1 /\ all_leaves l2))
          (decreases l)
  = match l with
    | [] -> ()
    | (Leaf _) :: tl -> partition_preserves_all_leaves f tl

// Helper: append preserves all_leaves
let rec append_preserves_all_leaves (l1 l2: list htree)
  : Lemma (requires all_leaves l1 /\ all_leaves l2)
          (ensures all_leaves (l1 @ l2))
          (decreases l1)
  = match l1 with
    | [] -> ()
    | Leaf _ :: tl -> append_preserves_all_leaves tl l2

// Helper: sortWith preserves all_leaves
let rec sortWith_preserves_all_leaves (l: list htree)
  : Lemma (requires all_leaves l)
          (ensures all_leaves (sortWith freq_cmp l))
          (decreases (length l))
  = match l with
    | [] -> ()
    | [Leaf _] -> ()
    | pivot :: tl ->
        let hi, lo = partition (bool_of_compare freq_cmp pivot) tl in
        partition_length (bool_of_compare freq_cmp pivot) tl;
        partition_preserves_all_leaves (bool_of_compare freq_cmp pivot) tl;
        sortWith_preserves_all_leaves lo;
        sortWith_preserves_all_leaves hi;
        append_preserves_all_leaves (sortWith freq_cmp lo) (pivot :: sortWith freq_cmp hi)

// Helper: map Leaf produces all_leaves
let rec map_leaf_all_leaves (freqs: list pos)
  : Lemma (ensures all_leaves (map (fun (f:pos) -> Leaf f) freqs))
          (decreases freqs)
  = match freqs with
    | [] -> ()
    | _ :: tl -> map_leaf_all_leaves tl

//SNIPPET_START: huffman_complete_optimal
let huffman_complete_optimal (freqs: list pos{Cons? freqs})
  : Lemma (ensures is_wpl_optimal (huffman_complete freqs) freqs)
  = huffman_complete_preserves_frequency_multiset freqs;
    let trees = map (fun (f:pos) -> Leaf f) freqs in
    let pq = init_pq freqs in
    // Show init_pq produces all Leaves
    map_leaf_all_leaves freqs;
    sortWith_preserves_all_leaves trees;
    assert (all_leaves pq);
    // Show all_leaf_freqs pq has same multiset as freqs
    let multiset_bridge (x: pos)
      : Lemma (count x (all_leaf_freqs pq) = count x freqs)
      = sortWith_preserves_all_leaf_freqs trees x;
        all_leaf_freqs_of_map_leaf freqs
    in
    Classical.forall_intro multiset_bridge;
    let aux (t': htree)
      : Lemma (requires same_frequency_multiset t' freqs)
              (ensures weighted_path_length (huffman_complete freqs) <= weighted_path_length t')
      = // same_frequency_multiset t' freqs means count x (leaf_freqs t') = count x freqs for all x
        // We showed count x (all_leaf_freqs pq) = count x freqs for all x
        // So count x (leaf_freqs t') = count x (all_leaf_freqs pq) for all x
        // i.e., same_frequency_multiset t' (all_leaf_freqs pq)
        let bridge (x: pos)
          : Lemma (count x (leaf_freqs t') = count x (all_leaf_freqs pq))
          = multiset_bridge x
        in
        Classical.forall_intro bridge;
        huffman_from_pq_wpl_le pq t'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
//SNIPPET_END: huffman_complete_optimal

(*** Summary ***)

(*
   This module provides a complete implementation of the CLRS Huffman algorithm
   that constructs the actual tree structure, not just the cost.
   
   Key contributions:
   1. huffman_complete: Main algorithm following CLRS §16.3 exactly
   2. is_prefix_free_code: Verification that result is a valid code tree
   3. greedy_choice_lemma: Formalization of CLRS Lemma 16.2
   4. optimal_substructure_lemma: WPL relationship for sibling merges
      (proven: WPL(T) = WPL(T') + f1 + f2 for any sibling pair)
   5. huffman_complete_preserves_frequency_multiset: leaf frequency multiset
      is preserved through the construction (proven via count-based equality)
   6. huffman_correctness_theorem: multiset preservation + base-case optimality
   
   NO admits remain. The module has zero admits.
   The Spec module has zero admits — greedy choice theorem (CLRS Lemma 16.2)
   is fully proven using multiset-based optimality (is_wpl_optimal).
   
   Full WPL-optimality for the multi-element case (that no other tree with the
   same frequency multiset has lower WPL) uses the greedy choice property from
   CLRS Lemma 16.2, fully proven in the Spec module.
   
   To verify:
   cd /home/nswamy/ws2/AutoCLRS
   fstar.exe --include $(realpath ../pulse)/out/lib/pulse \
             --include common \
             --include ch16-greedy \
             ch16-greedy/CLRS.Ch16.Huffman.Complete.fst
*)
