module CLRS.Ch16.Huffman.Optimality

// Pure F* module for greedy cost infrastructure and WPL optimality proof.
// Separated from the Pulse module to avoid #lang-pulse elaboration issues.

open FStar.List.Tot.Base
open FStar.List.Tot.Properties
open FStar.Math.Lib

module HSpec = CLRS.Ch16.Huffman.Spec
module HComp = CLRS.Ch16.Huffman.Complete
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties

// ========== Sorted multiset uniqueness ==========

let rec sorted_head_le_all (l: list pos)
  : Lemma (requires HComp.nondecreasing l /\ Cons? l)
          (ensures forall (x: pos). mem x l ==> hd l <= x)
          (decreases l)
  = match l with
    | [_] -> ()
    | _ :: b :: rest -> sorted_head_le_all (b :: rest)

let rec sorted_no_smaller (l: list pos) (x: pos)
  : Lemma (requires HComp.nondecreasing l /\ Cons? l /\ x < hd l)
          (ensures count x l = 0)
          (decreases l)
  = match l with
    | [_] -> ()
    | a :: b :: rest ->
        if x = a then ()
        else sorted_no_smaller (b :: rest) x

let rec sorted_multiset_unique (l1 l2: list pos)
  : Lemma (requires HComp.nondecreasing l1 /\ HComp.nondecreasing l2 /\
                    (forall (x: pos). count x l1 = count x l2))
          (ensures l1 == l2)
          (decreases length l1)
  = match l1, l2 with
    | [], [] -> ()
    | [], hd2 :: _ -> assert (count hd2 l2 >= 1)
    | hd1 :: _, [] -> assert (count hd1 l1 >= 1)
    | h1 :: t1, h2 :: t2 ->
        if h1 < h2 then sorted_no_smaller l2 h1
        else if h2 < h1 then sorted_no_smaller l1 h2
        else sorted_multiset_unique t1 t2

// ========== sortWith pos_compare ==========

// pos_compare is defined in the .fsti

let rec partition_pos_le (pivot: pos) (l: list pos)
  : Lemma (ensures (let hi, lo = partition (bool_of_compare pos_compare pivot) l in
                    (forall x. mem x lo ==> x <= pivot) /\
                    (forall x. mem x hi ==> x >= pivot)))
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> partition_pos_le pivot tl

let rec sortWith_preserves_le_pivot (pivot: pos) (l: list pos)
  : Lemma (requires forall x. mem x l ==> x <= pivot)
          (ensures forall x. mem x (sortWith pos_compare l) ==> x <= pivot)
          (decreases length l)
  = sortWith_permutation pos_compare l;
    let sorted = sortWith pos_compare l in
    let aux (x: pos)
      : Lemma (requires mem x sorted) (ensures x <= pivot)
      = HSpec.count_mem x sorted; HSpec.count_mem x l
    in
    Classical.forall_intro (Classical.move_requires aux)

let rec sortWith_preserves_ge_pivot (pivot: pos) (l: list pos)
  : Lemma (requires forall x. mem x l ==> x >= pivot)
          (ensures forall x. mem x (sortWith pos_compare l) ==> x >= pivot)
          (decreases length l)
  = sortWith_permutation pos_compare l;
    let sorted = sortWith pos_compare l in
    let aux (x: pos)
      : Lemma (requires mem x sorted) (ensures x >= pivot)
      = HSpec.count_mem x sorted; HSpec.count_mem x l
    in
    Classical.forall_intro (Classical.move_requires aux)

let rec nondecreasing_append (lo hi: list pos)
  : Lemma (requires HComp.nondecreasing lo /\ HComp.nondecreasing hi /\
                    (Nil? lo \/ Nil? hi \/
                     (Cons? lo /\ Cons? hi /\
                      (forall x. mem x lo ==> x <= hd hi))))
          (ensures HComp.nondecreasing (lo @ hi))
          (decreases lo)
  = match lo with
    | [] -> ()
    | [x] -> ()
    | x :: y :: rest -> nondecreasing_append (y :: rest) hi

let rec sortWith_pos_nondecreasing (l: list pos)
  : Lemma (ensures HComp.nondecreasing (sortWith pos_compare l))
          (decreases length l)
  = match l with
    | [] -> ()
    | [_] -> ()
    | pivot :: tl ->
        let hi, lo = partition (bool_of_compare pos_compare pivot) tl in
        partition_length (bool_of_compare pos_compare pivot) tl;
        partition_pos_le pivot tl;
        sortWith_pos_nondecreasing lo;
        sortWith_pos_nondecreasing hi;
        sortWith_preserves_le_pivot pivot lo;
        sortWith_preserves_ge_pivot pivot hi;
        let sorted_lo = sortWith pos_compare lo in
        let sorted_hi = sortWith pos_compare hi in
        (match sorted_hi with
         | [] -> ()
         | shd :: _ -> sorted_head_le_all sorted_hi);
        nondecreasing_append sorted_lo (pivot :: sorted_hi)

let sortWith_pos_perm (l: list pos) (x: pos)
  : Lemma (ensures count x l = count x (sortWith pos_compare l))
  = sortWith_permutation pos_compare l

let sortWith_pos_length (l: list pos)
  : Lemma (ensures length (sortWith pos_compare l) = length l)
  = HComp.sortWith_length pos_compare l

// Two pos lists with the same multiset sort to the same result
let sortWith_same_multiset (l1 l2: list pos)
  : Lemma (requires forall (x: pos). count x l1 = count x l2)
          (ensures sortWith pos_compare l1 == sortWith pos_compare l2)
  = sortWith_pos_nondecreasing l1;
    sortWith_pos_nondecreasing l2;
    let s1 = sortWith pos_compare l1 in
    let s2 = sortWith pos_compare l2 in
    let aux (x: pos)
      : Lemma (count x s1 = count x s2)
      = sortWith_pos_perm l1 x; sortWith_pos_perm l2 x
    in
    Classical.forall_intro aux;
    sorted_multiset_unique s1 s2

// ========== Greedy cost ==========

let rec greedy_cost (freqs: list pos) : Tot nat (decreases length freqs) =
  if length freqs <= 1 then 0
  else begin
    sortWith_pos_length freqs;
    let sorted = sortWith pos_compare freqs in
    match sorted with
    | f1 :: f2 :: rest ->
        (f1 + f2) + greedy_cost ((f1 + f2) :: rest)
    | _ -> 0
  end

let greedy_cost_singleton (f: pos)
  : Lemma (greedy_cost [f] == 0)
  = sortWith_pos_length [f]

let greedy_cost_multiset_invariant (l1 l2: list pos)
  : Lemma (requires forall (x: pos). count x l1 = count x l2)
          (ensures greedy_cost l1 == greedy_cost l2)
  = sortWith_same_multiset l1 l2;
    sortWith_pos_length l1;
    sortWith_pos_length l2

let greedy_cost_sorted_unfold (freqs: list pos)
  : Lemma (requires length freqs >= 2 /\ HComp.nondecreasing freqs)
          (ensures (let f1 :: f2 :: rest = freqs in
                    greedy_cost freqs == (f1 + f2) + greedy_cost ((f1 + f2) :: rest)))
  = sortWith_pos_length freqs;
    sortWith_pos_nondecreasing freqs;
    let sorted = sortWith pos_compare freqs in
    let aux (x: pos) : Lemma (count x freqs = count x sorted)
      = sortWith_pos_perm freqs x in
    Classical.forall_intro aux;
    sorted_multiset_unique freqs sorted

// ========== Bridge: huffman_complete cost == greedy_cost ==========

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec huffman_from_pq_cost_eq_greedy (pq: HComp.priority_queue)
  : Lemma (requires HComp.is_valid_pq pq /\ HComp.all_leaves pq)
          (ensures HSpec.cost (HComp.huffman_from_pq pq) == greedy_cost (HComp.all_leaf_freqs pq))
          (decreases length pq)
  = match pq with
    | [HSpec.Leaf f] -> ()
    | (HSpec.Leaf f1) :: (HSpec.Leaf f2) :: rest ->
        let merged = HSpec.merge (HSpec.Leaf f1) (HSpec.Leaf f2) in
        let leaf_merged = HSpec.Leaf (f1 + f2) in
        HSpec.insert_sorted_length merged rest;
        HSpec.insert_sorted_nonempty merged rest;
        HComp.insert_sorted_maintains_sorted merged rest;
        let new_pq = HSpec.insert_sorted merged rest in
        HSpec.insert_sorted_length leaf_merged rest;
        HSpec.insert_sorted_nonempty leaf_merged rest;
        HComp.insert_sorted_maintains_sorted leaf_merged rest;
        HComp.insert_sorted_leaf_preserves_all_leaves (f1 + f2) rest;
        let leaf_pq = HSpec.insert_sorted leaf_merged rest in
        // WPL decomposition: cost(hfpq new_pq) = cost(hfpq leaf_pq) + (f1 + f2)
        HComp.insert_sorted_map_freq_of merged leaf_merged rest rest;
        HComp.huffman_from_pq_wpl_decomp new_pq leaf_pq;
        HSpec.wpl_equals_cost (HComp.huffman_from_pq new_pq);
        HSpec.wpl_equals_cost (HComp.huffman_from_pq leaf_pq);
        HComp.insert_sorted_sum_costs merged rest;
        HComp.insert_sorted_sum_costs leaf_merged rest;
        // IH on leaf_pq
        huffman_from_pq_cost_eq_greedy leaf_pq;
        // greedy_cost(all_leaf_freqs pq) = (f1+f2) + greedy_cost((f1+f2)::rest_freqs)
        HComp.sorted_all_leaves_nondecreasing pq;
        greedy_cost_sorted_unfold (HComp.all_leaf_freqs pq);
        // greedy_cost(all_leaf_freqs leaf_pq) = greedy_cost((f1+f2)::all_leaf_freqs rest) by multiset
        let aux (x: pos)
          : Lemma (count x (HComp.all_leaf_freqs leaf_pq) =
                   count x ((f1 + f2) :: HComp.all_leaf_freqs rest))
          = HComp.insert_sorted_preserves_leaf_multiset leaf_merged rest x
        in
        Classical.forall_intro aux;
        greedy_cost_multiset_invariant (HComp.all_leaf_freqs leaf_pq)
                                       ((f1 + f2) :: HComp.all_leaf_freqs rest)
    | _ -> ()
#pop-options

let huffman_complete_cost_eq_greedy (freqs: list pos{Cons? freqs})
  : Lemma (ensures HSpec.cost (HComp.huffman_complete freqs) == greedy_cost freqs)
  = let pq = HComp.init_pq freqs in
    HComp.map_leaf_all_leaves freqs;
    HComp.sortWith_preserves_all_leaves (map (fun (f:pos) -> HSpec.Leaf f) freqs);
    huffman_from_pq_cost_eq_greedy pq;
    let aux (x: pos)
      : Lemma (count x (HComp.all_leaf_freqs pq) = count x freqs)
      = HComp.sortWith_preserves_all_leaf_freqs
          (map (fun (f:pos) -> HSpec.Leaf f) freqs) x;
        HComp.all_leaf_freqs_of_map_leaf freqs
    in
    Classical.forall_intro aux;
    greedy_cost_multiset_invariant (HComp.all_leaf_freqs pq) freqs

// ========== Optimality theorem ==========

let cost_eq_implies_optimal (ft: HSpec.htree) (freqs: list pos{Cons? freqs})
  : Lemma (requires HSpec.same_frequency_multiset ft freqs /\
                    HSpec.cost ft == HSpec.cost (HComp.huffman_complete freqs))
          (ensures HSpec.is_wpl_optimal ft freqs)
  = HComp.huffman_complete_optimal freqs;
    HSpec.wpl_equals_cost ft;
    HSpec.wpl_equals_cost (HComp.huffman_complete freqs);
    let aux (t': HSpec.htree)
      : Lemma (requires HSpec.same_frequency_multiset t' freqs)
              (ensures HSpec.weighted_path_length ft <= HSpec.weighted_path_length t')
      = HSpec.wpl_equals_cost t'
    in
    Classical.forall_intro (Classical.move_requires aux)

// Helper: cost(ft) == greedy_cost(freqs) ==> is_wpl_optimal ft freqs
let greedy_cost_implies_optimal (ft: HSpec.htree) (freqs: list pos{Cons? freqs})
  : Lemma (requires HSpec.same_frequency_multiset ft freqs /\
                    HSpec.cost ft == greedy_cost freqs)
          (ensures HSpec.is_wpl_optimal ft freqs)
  = huffman_complete_cost_eq_greedy freqs;
    cost_eq_implies_optimal ft freqs

// ========== Greedy cost merge step ==========

// Helper: the first element of a nondecreasing list is the minimum
let nondecreasing_hd_is_min (sorted: list pos) (f: pos)
  : Lemma (requires HComp.nondecreasing sorted /\ Cons? sorted /\
                    mem f sorted /\ (forall x. mem x sorted ==> f <= x))
          (ensures hd sorted == f)
  = sorted_head_le_all sorted // hd sorted <= f (since f is in sorted)
    // f <= hd sorted (since hd sorted is in sorted and f <= all)

// Helper: removing hd from a nondecreasing list gives nondecreasing tail
let nondecreasing_tail (sorted: list pos)
  : Lemma (requires HComp.nondecreasing sorted /\ length sorted >= 2)
          (ensures HComp.nondecreasing (tl sorted))
  = ()

// Helper: count x (hd :: tl) = (if x = hd then 1 else 0) + count x tl
let count_cons (x: pos) (h: pos) (tl: list pos)
  : Lemma (ensures count x (h :: tl) = (if x = h then 1 else 0) + count x tl)
  = ()

// Key lemma: greedy_cost unfolds using ANY pair of minimums
// If f1 is the global minimum and f2 is the minimum of (freqs - {f1}),
// and remaining is freqs - {f1} - {f2}, then
// greedy_cost(freqs) == (f1+f2) + greedy_cost((f1+f2)::remaining)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let greedy_cost_unfold_with_mins (freqs: list pos) (f1 f2: pos) (remaining: list pos)
  : Lemma (requires
      length freqs >= 2 /\
      // f1 is the minimum of freqs
      (forall x. mem x freqs ==> f1 <= x) /\
      // Multiset decomposition: freqs = {f1} + {f2} + remaining
      (forall (x: pos). count x freqs = (if x = f1 then 1 else 0) +
                                    (if x = f2 then 1 else 0) +
                                    count x remaining) /\
      // f2 is the minimum of remaining
      (forall x. mem x remaining ==> f2 <= x))
    (ensures greedy_cost freqs == (f1 + f2) + greedy_cost ((f1 + f2) :: remaining))
  = // Step 1: Get sorted version
    sortWith_pos_length freqs;
    sortWith_pos_nondecreasing freqs;
    let sorted = sortWith pos_compare freqs in
    let aux_perm (x: pos) : Lemma (count x sorted = count x freqs)
      = sortWith_pos_perm freqs x in
    Classical.forall_intro aux_perm;
    // Step 2: sorted[0] == f1
    assert (count f1 freqs >= 1);
    HSpec.count_mem f1 freqs;
    HSpec.count_mem f1 sorted;
    let aux_f1_le (x: pos) : Lemma (requires mem x sorted) (ensures f1 <= x)
      = HSpec.count_mem x sorted; HSpec.count_mem x freqs in
    Classical.forall_intro (Classical.move_requires aux_f1_le);
    nondecreasing_hd_is_min sorted f1;
    // Step 3: sorted_tail multiset = {f2} + remaining
    let sorted_tail = tl sorted in
    nondecreasing_tail sorted;
    let aux_tail (x: pos)
      : Lemma (count x sorted_tail = (if x = f2 then 1 else 0) + count x remaining)
      = count_cons x f1 sorted_tail  // count x sorted = (if x=f1 then 1 else 0) + count x sorted_tail
    in
    Classical.forall_intro aux_tail;
    // Step 4: sorted_tail[0] == f2
    assert (count f2 sorted_tail >= 1);
    HSpec.count_mem f2 sorted_tail;
    let aux_f2_le (x: pos) : Lemma (requires mem x sorted_tail) (ensures f2 <= x)
      = HSpec.count_mem x sorted_tail;
        if x = f2 then ()
        else begin
          count_cons x f1 sorted_tail;
          assert (count x sorted_tail = count x remaining);
          HSpec.count_mem x remaining
        end
    in
    Classical.forall_intro (Classical.move_requires aux_f2_le);
    nondecreasing_hd_is_min sorted_tail f2;
    // Step 5: greedy_cost(freqs) unfolds to (sorted[0]+sorted[1]) + greedy_cost((sorted[0]+sorted[1])::rest)
    greedy_cost_sorted_unfold sorted;
    // greedy_cost freqs == greedy_cost sorted (multiset invariance)
    greedy_cost_multiset_invariant freqs sorted;
    // Now: greedy_cost freqs == (hd sorted + hd sorted_tail) + greedy_cost((hd sorted + hd sorted_tail) :: sorted_rest)
    //     = (f1 + f2) + greedy_cost((f1+f2) :: sorted_rest)
    // Step 6: multiset of sorted_rest == multiset of remaining
    let sorted_rest = tl sorted_tail in
    let aux_rest (x: pos)
      : Lemma (count x sorted_rest = count x remaining)
      = count_cons x f2 sorted_rest  // count x sorted_tail = (if x=f2 then 1 else 0) + count x sorted_rest
    in
    Classical.forall_intro aux_rest;
    let aux_final (x: pos)
      : Lemma (count x ((f1+f2) :: sorted_rest) = count x ((f1+f2) :: remaining))
      = count_cons x (f1+f2) sorted_rest;
        count_cons x (f1+f2) remaining
    in
    Classical.forall_intro aux_final;
    greedy_cost_multiset_invariant ((f1+f2) :: sorted_rest) ((f1+f2) :: remaining)
#pop-options
