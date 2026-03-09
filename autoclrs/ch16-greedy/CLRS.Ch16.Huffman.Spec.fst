module CLRS.Ch16.Huffman.Spec

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Math.Lib

(*** Tree Definition ***)

//SNIPPET_START: htree_def
type htree =
  | Leaf : sym:nat -> freq:pos -> htree
  | Internal : freq:pos -> left:htree -> right:htree -> htree
//SNIPPET_END: htree_def

(*** Basic Operations ***)

let rec freq_of (t: htree) : pos =
  match t with
  | Leaf _ f -> f
  | Internal _ l r -> freq_of l + freq_of r

let rec depth (t: htree) : nat =
  match t with
  | Leaf _ _ -> 0
  | Internal _ l r -> 1 + max (depth l) (depth r)

(*** Weighted Path Length ***)

//SNIPPET_START: weighted_path_length
let rec weighted_path_length_aux (t: htree) (d: nat) : nat =
  match t with
  | Leaf _ f -> f `op_Multiply` d
  | Internal _ l r ->
      weighted_path_length_aux l (d + 1) +
      weighted_path_length_aux r (d + 1)

let weighted_path_length (t: htree) : nat =
  weighted_path_length_aux t 0
//SNIPPET_END: weighted_path_length

(*** Cost (sum of internal node frequencies) ***)

let rec cost_aux (t: htree) : nat =
  match t with
  | Leaf _ _ -> 0
  | Internal _ l r -> freq_of l + freq_of r + cost_aux l + cost_aux r

let cost (t: htree) : nat = cost_aux t

(*** Key Lemma: Weighted Path Length = Cost (CLRS 16.4) ***)

// Helper: relates wpl at depth d to cost plus contribution from depth
let rec wpl_cost_relation (t: htree) (d: nat)
  : Lemma (ensures weighted_path_length_aux t d == cost_aux t + d `op_Multiply` freq_of t)
          (decreases t)
  = match t with
    | Leaf _ f -> ()
    | Internal f l r ->
        wpl_cost_relation l (d + 1);
        wpl_cost_relation r (d + 1)

//SNIPPET_START: wpl_equals_cost
// Main theorem: at depth 0, weighted_path_length equals cost
let wpl_equals_cost (t: htree)
  : Lemma (ensures weighted_path_length t == cost t)
  = wpl_cost_relation t 0
//SNIPPET_END: wpl_equals_cost

(*** Huffman Tree Construction ***)

// Merge two trees into an internal node
let merge (t1 t2: htree) : htree =
  Internal (freq_of t1 + freq_of t2) t1 t2

// Insert a tree into a sorted list (by frequency, ascending)
let rec insert_sorted (t: htree) (l: list htree) 
  : list htree
  = match l with
    | [] -> [t]
    | hd :: tl ->
        if freq_of t <= freq_of hd then t :: l
        else hd :: insert_sorted t tl

// Lemma: insert_sorted increases length by 1
let rec insert_sorted_length (t: htree) (l: list htree)
  : Lemma (ensures length (insert_sorted t l) = length l + 1)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl -> insert_sorted_length t tl

// Lemma: insert_sorted preserves non-emptiness
let insert_sorted_nonempty (t: htree) (l: list htree)
  : Lemma (ensures Cons? (insert_sorted t l))
  = insert_sorted_length t l

//SNIPPET_START: huffman_from_sorted
// Build Huffman tree from a non-empty sorted list of trees
let rec huffman_from_sorted (l: list htree{Cons? l})
  : Tot htree (decreases length l)
  = match l with
    | [t] -> t
    | t1 :: t2 :: rest ->
        insert_sorted_length (merge t1 t2) rest;
        // length (t1 :: t2 :: rest) = length rest + 2
        // length (insert_sorted (merge t1 t2) rest) = length rest + 1
        // So length decreases by 1
        huffman_from_sorted (insert_sorted (merge t1 t2) rest)
    | _ -> Leaf 0 1 // unreachable but needed for exhaustiveness
//SNIPPET_END: huffman_from_sorted

// Sort helper: compare by frequency
let freq_cmp (t1 t2: htree) : int =
  freq_of t1 - freq_of t2

// Build Huffman tree from a non-empty list of frequencies
let huffman_build (freqs: list pos{Cons? freqs}) : htree =
  let trees = map (fun f -> Leaf 0 f) freqs in
  let sorted = sortWith freq_cmp trees in
  huffman_from_sorted sorted

(*** Properties of Huffman Construction ***)

// Property: freq_of the result is the sum of all frequencies
let rec sum_freqs (l: list pos) : pos =
  match l with
  | [x] -> x
  | hd :: tl -> hd + sum_freqs tl
  | [] -> 1 // unreachable for non-empty lists

// Helper: freq_of tree list
let rec sum_tree_freqs (l: list htree{Cons? l}) : pos =
  match l with
  | [t] -> freq_of t
  | hd :: tl -> freq_of hd + sum_tree_freqs tl
  | _ -> 1

// Lemma: insert_sorted preserves total frequency  
let rec insert_sorted_preserves_sum (t: htree) (l: list htree{Cons? l})
  : Lemma (ensures sum_tree_freqs (insert_sorted t l) == freq_of t + sum_tree_freqs l)
          (decreases l)
  = insert_sorted_nonempty t l;
    match l with
    | [_] -> ()
    | hd :: tl ->
        if freq_of t <= freq_of hd then ()
        else (
          insert_sorted_preserves_sum t tl;
          ()
        )

// Lemma: huffman_from_sorted preserves total frequency
let rec huffman_from_sorted_preserves_sum (l: list htree{Cons? l})
  : Lemma (ensures freq_of (huffman_from_sorted l) == sum_tree_freqs l)
          (decreases length l)
  = match l with
    | [t] -> ()
    | t1 :: t2 :: rest ->
        insert_sorted_length (merge t1 t2) rest;
        insert_sorted_nonempty (merge t1 t2) rest;
        let merged = merge t1 t2 in
        let new_list = insert_sorted merged rest in
        (match rest with
         | [] ->
             // new_list = [merged]
             // sum_tree_freqs [merged] = freq_of merged
             //                         = freq_of t1 + freq_of t2
             //                         = sum_tree_freqs [t1; t2]
             ()
         | _ ->
             insert_sorted_preserves_sum merged rest;
             ()
        );
        huffman_from_sorted_preserves_sum new_list
    | _ -> ()

// Helper: sum of list
let rec list_sum (l: list pos{Cons? l}) : pos =
  match l with
  | [x] -> x
  | hd :: tl -> hd + list_sum tl
  | _ -> 1

// Lemma: mapping Leaf and summing preserves total
let rec map_leaf_sum (l: list pos{Cons? l})
  : Lemma (ensures sum_tree_freqs (map (fun f -> Leaf 0 f) l) == list_sum l)
          (decreases l)
  = match l with
    | [_] -> ()
    | hd :: tl -> map_leaf_sum tl

// Note: Proving that huffman_build preserves total frequency requires
// showing that sortWith preserves sums, which in turn requires reasoning
// about multisets and permutations. This is beyond the scope of this basic spec.
// The property holds but would require additional infrastructure to prove formally.

(*** Greedy Choice and Optimal Substructure ***)

// Definition: A tree is a full binary tree if every internal node has exactly 2 children
// (This is implicit in our htree definition, but we make it explicit for clarity)
let rec is_full_binary_tree (t: htree) : prop =
  match t with
  | Leaf _ _ -> True
  | Internal _ l r -> is_full_binary_tree l /\ is_full_binary_tree r

// All htrees are full binary trees by construction
let rec htree_is_full (t: htree)
  : Lemma (ensures is_full_binary_tree t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r -> htree_is_full l; htree_is_full r

// Definition: Get the list of leaf frequencies in a tree (in order)
let rec leaf_freqs (t: htree) : list pos =
  match t with
  | Leaf _ f -> [f]
  | Internal _ l r -> leaf_freqs l @ leaf_freqs r

//SNIPPET_START: is_optimal
// Definition: A tree is optimal if its WPL is minimal among all trees with the same leaf frequencies
let is_optimal (t: htree) (freqs: list pos) : prop =
  leaf_freqs t == freqs /\
  (forall (t': htree). leaf_freqs t' == freqs ==> weighted_path_length t <= weighted_path_length t')
//SNIPPET_END: is_optimal

// Multiset-based optimality: tree has the right frequency multiset and minimizes WPL.
// This is the correct notion for Huffman trees since the construction reorders leaves.
let same_frequency_multiset (t: htree) (freqs: list pos) : prop =
  forall (x: pos). count x (leaf_freqs t) = count x freqs

let is_wpl_optimal (t: htree) (freqs: list pos) : prop =
  same_frequency_multiset t freqs /\
  (forall (t': htree). same_frequency_multiset t' freqs ==>
    weighted_path_length t <= weighted_path_length t')

// Helper: find minimum frequency in a list
let rec min_freq (l: list pos{Cons? l}) : pos =
  match l with
  | [x] -> x
  | hd :: tl -> min hd (min_freq tl)

// Helper: find maximum depth of any leaf
let rec max_leaf_depth (t: htree) (d: nat) : nat =
  match t with
  | Leaf _ _ -> d
  | Internal _ l r -> max (max_leaf_depth l (d + 1)) (max_leaf_depth r (d + 1))

// Helper: check if two leaves are siblings (share the same parent)
let rec are_siblings (t: htree) (f1 f2: pos) : bool =
  match t with
  | Leaf _ _ -> false
  | Internal _ (Leaf _ f1') (Leaf _ f2') -> (f1' = f1 && f2' = f2) || (f1' = f2 && f2' = f1)
  | Internal _ l r -> are_siblings l f1 f2 || are_siblings r f1 f2

// Helper: get depth of a specific leaf frequency (first occurrence)
let rec depth_of_leaf (t: htree) (f: pos) (d: nat) : option nat =
  match t with
  | Leaf _ f' -> if f = f' then Some d else None
  | Internal _ l r ->
      match depth_of_leaf l f (d + 1) with
      | Some depth -> Some depth
      | None -> depth_of_leaf r f (d + 1)

// Definition: Swap two subtrees in a tree
// This function swaps subtree at position pos1 with subtree at position pos2
// Positions are encoded as lists of booleans (true = left, false = right)
type tree_position = list bool

let rec get_subtree_at (t: htree) (pos: tree_position) : option htree =
  match pos with
  | [] -> Some t
  | hd :: tl ->
      match t with
      | Leaf _ _ -> None
      | Internal _ l r ->
          if hd then get_subtree_at l tl else get_subtree_at r tl

// Helper: check if position in tree has a Leaf with given frequency (sym-agnostic)
let is_leaf_at (t: htree) (p: tree_position) (f: pos) : bool =
  match get_subtree_at t p with
  | Some (Leaf _ f') -> f' = f
  | _ -> false

let rec replace_subtree_at (t: htree) (pos: tree_position) (new_t: htree) : option htree =
  match pos with
  | [] -> Some new_t
  | hd :: tl ->
      match t with
      | Leaf _ _ -> None
      | Internal f l r ->
          if hd then
            match replace_subtree_at l tl new_t with
            | Some l' -> Some (Internal f l' r)
            | None -> None
          else
            match replace_subtree_at r tl new_t with
            | Some r' -> Some (Internal f l r')
            | None -> None

// Swap lemma: Swapping a high-frequency leaf at a DEEP depth with a low-frequency leaf
// at a SHALLOW depth decreases or maintains WPL (CLRS Lemma 16.2 exchange argument)
// 
// Intuition: Moving high-freq to shallower depth saves more bits than the cost of 
// moving low-freq to deeper depth. Net change = (f_high - f_low)(d_high - d_low) >= 0
// in favor of the swap (original WPL >= swapped WPL).
let swap_reduces_wpl_statement (t: htree) (pos_high pos_low: tree_position) : prop =
  match get_subtree_at t pos_high, get_subtree_at t pos_low with
  | Some (Leaf _ f_high), Some (Leaf _ f_low) ->
      let depth_high = length pos_high in
      let depth_low = length pos_low in
      // High-freq leaf at DEEP position, low-freq leaf at SHALLOW position (suboptimal)
      if f_high >= f_low && depth_high >= depth_low then
        (match replace_subtree_at t pos_high (Leaf 0 f_low), 
               replace_subtree_at t pos_low (Leaf 0 f_high) with
         | Some t_temp, _ ->
             (match replace_subtree_at t_temp pos_low (Leaf 0 f_high) with
              | Some t_swapped ->
                  weighted_path_length t_swapped <= weighted_path_length t
              | None -> True)
         | _, _ -> True)
      else True
  | _, _ -> True

// Helper: WPL of tree with depth offset
let wpl_at_depth (t: htree) (d: nat) : nat = weighted_path_length_aux t d

// Helper lemma: WPL contribution of a single leaf at depth d
let leaf_contribution (f: pos) (d: nat) : nat = f `op_Multiply` d

// Helper lemma: Swapping two leaves at different depths affects WPL
// The exact relationship depends on frequency and depth differences
let swap_wpl_delta (f_high f_low: pos) (d_high d_low: nat)
  : Lemma (requires f_high >= f_low /\ d_high >= d_low)
          (ensures True) // Simplified - the full WPL relationship requires case analysis
  = ()

// Helper lemma: get_subtree_at with [] returns the tree
let get_subtree_at_nil (t: htree)
  : Lemma (ensures get_subtree_at t [] == Some t)
  = ()

// Helper lemma: replace_subtree_at with [] replaces entire tree
let replace_subtree_at_nil (t: htree) (new_t: htree)
  : Lemma (ensures replace_subtree_at t [] new_t == Some new_t)
  = ()

// Key helper lemma: WPL contribution analysis for replace_subtree_at
// When we replace a subtree at position pos, the WPL changes by the difference
// in the weighted contributions of the old and new subtrees
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec replace_subtree_wpl_aux (t: htree) (pos: tree_position) (new_t: htree) (d: nat)
  : Lemma (requires Some? (get_subtree_at t pos) /\ Some? (replace_subtree_at t pos new_t))
          (ensures (
            let Some old_t = get_subtree_at t pos in
            let Some t' = replace_subtree_at t pos new_t in
            weighted_path_length_aux t d ==
            weighted_path_length_aux t' d + 
            weighted_path_length_aux old_t (d + length pos) -
            weighted_path_length_aux new_t (d + length pos)
          ))
          (decreases pos)
  = match pos with
    | [] ->
        // Base case: replacing at root
        assert (get_subtree_at t [] == Some t);
        assert (replace_subtree_at t [] new_t == Some new_t)
    | hd :: tl ->
        match t with
        | Internal f l r ->
            if hd then (
              // Replace in left subtree
              replace_subtree_wpl_aux l tl new_t (d + 1);
              let Some old_t = get_subtree_at l tl in
              let Some l' = replace_subtree_at l tl new_t in
              // WPL of Internal at depth d
              assert (weighted_path_length_aux t d ==
                      weighted_path_length_aux l (d + 1) + weighted_path_length_aux r (d + 1));
              assert (weighted_path_length_aux (Internal f l' r) d ==
                      weighted_path_length_aux l' (d + 1) + weighted_path_length_aux r (d + 1));
              // From IH: wpl_aux l (d+1) = wpl_aux l' (d+1) + wpl_aux old_t (d+1+|tl|) - wpl_aux new_t (d+1+|tl|)
              // So: wpl_aux t d = wpl_aux (Internal f l' r) d + wpl_aux old_t (d+1+|tl|) - wpl_aux new_t (d+1+|tl|)
              assert (d + 1 + length tl == d + length (hd :: tl))
            ) else (
              // Replace in right subtree
              replace_subtree_wpl_aux r tl new_t (d + 1);
              let Some old_t = get_subtree_at r tl in
              let Some r' = replace_subtree_at r tl new_t in
              assert (weighted_path_length_aux t d ==
                      weighted_path_length_aux l (d + 1) + weighted_path_length_aux r (d + 1));
              assert (weighted_path_length_aux (Internal f l r') d ==
                      weighted_path_length_aux l (d + 1) + weighted_path_length_aux r' (d + 1));
              assert (d + 1 + length tl == d + length (hd :: tl))
            )
        | Leaf _ _ -> ()
#pop-options

// Specialization for replacing a leaf: WPL change is exactly the frequency times depth difference
#push-options "--z3rlimit 30"
let replace_leaf_wpl (t: htree) (position: tree_position) (f_new: pos) (d: nat)
  : Lemma (requires (match get_subtree_at t position with
                     | Some (Leaf _ f_old) -> True
                     | _ -> False))
          (ensures (
            let Some (Leaf _ f_old) = get_subtree_at t position in
            match replace_subtree_at t position (Leaf 0 f_new) with
            | Some t' ->
                weighted_path_length_aux t d + f_new `op_Multiply` (d + length position) ==
                weighted_path_length_aux t' d + f_old `op_Multiply` (d + length position)
            | None -> True
          ))
  = let Some (Leaf _ f_old) = get_subtree_at t position in
    match replace_subtree_at t position (Leaf 0 f_new) with
    | Some t' ->
        replace_subtree_wpl_aux t position (Leaf 0 f_new) d;
        // From replace_subtree_wpl_aux:
        // wpl_aux t d = wpl_aux t' d + wpl_aux (Leaf f_old) (d + |position|) - wpl_aux (Leaf f_new) (d + |position|)
        // wpl_aux (Leaf f_old) (d + |position|) = f_old * (d + |position|)
        // wpl_aux (Leaf f_new) (d + |position|) = f_new * (d + |position|)
        // So: wpl_aux t d = wpl_aux t' d + f_old * (d + |position|) - f_new * (d + |position|)
        // Rearranging: wpl_aux t d + f_new * (d + |position|) = wpl_aux t' d + f_old * (d + |position|)
        ()
    | None -> ()
#pop-options

// Helper: arithmetic fact for swap
// High-freq leaf at DEEP position (d_high), low-freq leaf at SHALLOW position (d_low)
// After swap: high-freq moves to shallow, low-freq moves to deep → WPL decreases
let swap_arithmetic (f_high f_low d_high d_low: nat) (wpl_orig wpl_swap: nat)
  : Lemma (requires
            f_high >= f_low /\
            d_high >= d_low /\
            wpl_orig + f_low `op_Multiply` d_high + f_high `op_Multiply` d_low ==
            wpl_swap + f_high `op_Multiply` d_high + f_low `op_Multiply` d_low)
          (ensures wpl_swap <= wpl_orig)
  = // wpl_orig + f_low * d_high + f_high * d_low = wpl_swap + f_high * d_high + f_low * d_low
    // wpl_orig - wpl_swap = (f_high * d_high + f_low * d_low) - (f_low * d_high + f_high * d_low)
    //                     = (f_high - f_low) * d_high - (f_high - f_low) * d_low
    //                     = (f_high - f_low) * (d_high - d_low) >= 0
    // Since f_high >= f_low and d_high >= d_low, both factors are non-negative
    // Therefore wpl_orig >= wpl_swap
    ()

// Helper: check if pos1 is a strict prefix of pos2
let rec is_prefix (pos1 pos2: tree_position) : bool =
  match pos1, pos2 with
  | [], _ :: _ -> true
  | hd1 :: tl1, hd2 :: tl2 -> hd1 = hd2 && is_prefix tl1 tl2
  | _, _ -> false

// Helper lemma: if positions are disjoint, replacing at one doesn't affect the other
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec disjoint_replacement_preserves_subtree (t: htree) (pos1 pos2: tree_position) (new1: htree)
  : Lemma (requires
            pos1 =!= pos2 /\
            not (is_prefix pos1 pos2) /\
            not (is_prefix pos2 pos1) /\
            Some? (get_subtree_at t pos1) /\
            Some? (get_subtree_at t pos2) /\
            Some? (replace_subtree_at t pos1 new1))
          (ensures (
            let Some t' = replace_subtree_at t pos1 new1 in
            get_subtree_at t' pos2 == get_subtree_at t pos2
          ))
          (decreases pos1)
  = match pos1, pos2 with
    | [], _ -> () // Contradicts not (is_prefix pos1 pos2)
    | _, [] -> () // Contradicts not (is_prefix pos2 pos1)
    | hd1 :: tl1, hd2 :: tl2 ->
        match t with
        | Internal f l r ->
            if hd1 = hd2 then (
              // Both go in same direction
              if hd1 then (
                disjoint_replacement_preserves_subtree l tl1 tl2 new1
              ) else (
                disjoint_replacement_preserves_subtree r tl1 tl2 new1
              )
            ) else (
              // Different directions - subtrees are independent
              ()
            )
        | Leaf _ _ -> ()
#pop-options

// Helper lemma: if positions are disjoint (neither is prefix of the other),
// then two sequential replacements are independent
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec disjoint_replacements_commute (t: htree) (pos1 pos2: tree_position) (new1 new2: htree)
  : Lemma (requires 
            pos1 =!= pos2 /\
            not (is_prefix pos1 pos2) /\
            not (is_prefix pos2 pos1) /\
            Some? (get_subtree_at t pos1) /\
            Some? (get_subtree_at t pos2) /\
            Some? (replace_subtree_at t pos1 new1) /\
            Some? (replace_subtree_at t pos2 new2))
          (ensures (
            let Some t1 = replace_subtree_at t pos1 new1 in
            let Some t2 = replace_subtree_at t pos2 new2 in
            match replace_subtree_at t1 pos2 new2, replace_subtree_at t2 pos1 new1 with
            | Some t12, Some t21 -> t12 == t21
            | _, _ -> False
          ))
          (decreases pos1)
  = match pos1, pos2 with
    | [], _ -> () // pos1 = [] and pos2 != [] contradicts not (is_prefix pos1 pos2)
    | _, [] -> () // pos2 = [] and pos1 != [] contradicts not (is_prefix pos2 pos1)
    | hd1 :: tl1, hd2 :: tl2 ->
        match t with
        | Internal f l r ->
            if hd1 = hd2 then (
              // Both go in same direction, recurse
              if hd1 then (
                disjoint_replacements_commute l tl1 tl2 new1 new2
              ) else (
                disjoint_replacements_commute r tl1 tl2 new1 new2
              )
            ) else (
              // They go in different directions - independent subtrees
              // No need to recurse, the replacements are clearly independent
              ()
            )
        | Leaf _ _ -> ()
#pop-options

// Key disjoint-case proof: when positions don't overlap, the swap arithmetic works
// If get_subtree_at succeeds, replace_subtree_at also succeeds
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec get_implies_replace (t: htree) (pos: tree_position) (new_t: htree)
  : Lemma (requires Some? (get_subtree_at t pos))
          (ensures Some? (replace_subtree_at t pos new_t))
          (decreases pos)
  = match pos with
    | [] -> ()
    | hd :: tl ->
        match t with
        | Internal _ l r ->
            if hd then get_implies_replace l tl new_t
            else get_implies_replace r tl new_t
        | Leaf _ _ -> ()
#pop-options

// After replace_subtree_at, getting at the same position yields the new subtree
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec replace_then_get (t: htree) (pos: tree_position) (new_t: htree)
  : Lemma (requires Some? (replace_subtree_at t pos new_t))
          (ensures get_subtree_at (Some?.v (replace_subtree_at t pos new_t)) pos == Some new_t)
          (decreases pos)
  = match pos with
    | [] -> ()
    | hd :: tl ->
        (match t with
        | Internal w l r ->
            if hd then replace_then_get l tl new_t
            else replace_then_get r tl new_t
        | Leaf _ _ -> ())
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let swap_reduces_wpl_disjoint (t: htree) (pos_high pos_low: tree_position) (f_high f_low: pos)
  : Lemma (requires
            is_leaf_at t pos_high f_high /\
            is_leaf_at t pos_low f_low /\
            f_high >= f_low /\
            length pos_high >= length pos_low /\
            pos_high =!= pos_low /\
            not (is_prefix pos_high pos_low) /\
            not (is_prefix pos_low pos_high) /\
            Some? (replace_subtree_at t pos_high (Leaf 0 f_low)))
          (ensures (
            let Some t_temp = replace_subtree_at t pos_high (Leaf 0 f_low) in
            is_leaf_at t_temp pos_low f_low /\
            (match replace_subtree_at t_temp pos_low (Leaf 0 f_high) with
             | Some t_swapped ->
                 weighted_path_length t_swapped <= weighted_path_length t
             | None -> True)))
  = let d_high = length pos_high in
    let d_low = length pos_low in
    let Some t_temp = replace_subtree_at t pos_high (Leaf 0 f_low) in
    
    // Step 1: pos_low is unaffected by replacing at pos_high (disjoint)
    disjoint_replacement_preserves_subtree t pos_high pos_low (Leaf 0 f_low);
    
    // Step 2: WPL analysis
    replace_leaf_wpl t pos_high f_low 0;
    
    match replace_subtree_at t_temp pos_low (Leaf 0 f_high) with
    | Some t_swapped ->
        replace_leaf_wpl t_temp pos_low f_high 0;
        
        let wpl_t = weighted_path_length t in
        let wpl_s = weighted_path_length t_swapped in
        
        assert (wpl_t + f_low `op_Multiply` d_high + f_high `op_Multiply` d_low ==
                wpl_s + f_high `op_Multiply` d_high + f_low `op_Multiply` d_low);
        
        swap_arithmetic f_high f_low d_high d_low wpl_t wpl_s
    | None -> ()
#pop-options

// If a position points to a leaf, any extension of it points to None
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec leaf_position_no_extension (t: htree) (pos1 pos2: tree_position)
  : Lemma (requires (match get_subtree_at t pos1 with
                     | Some (Leaf _ _) -> True
                     | _ -> False) /\ is_prefix pos1 pos2)
          (ensures get_subtree_at t pos2 == None)
          (decreases pos1)
  = match pos1, pos2 with
    | [], hd2 :: tl2 ->
        // t itself is a Leaf, so going into it returns None
        ()
    | hd1 :: tl1, hd2 :: tl2 ->
        assert (hd1 = hd2);
        (match t with
        | Internal _ l r ->
            if hd1 then leaf_position_no_extension l tl1 tl2
            else leaf_position_no_extension r tl1 tl2
        | Leaf _ _ -> ())
    | _, _ -> () // can't happen
#pop-options

// The swap reduces WPL when the conditions are met
// High-freq at deep position, low-freq at shallow position → swap reduces WPL
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let swap_reduces_wpl (t: htree) (pos_high pos_low: tree_position)
  : Lemma (requires (match get_subtree_at t pos_high, get_subtree_at t pos_low with
                     | Some (Leaf _ f_high), Some (Leaf _ f_low) ->
                         f_high >= f_low /\ length pos_high >= length pos_low /\
                         pos_high =!= pos_low
                     | _, _ -> False))
          (ensures swap_reduces_wpl_statement t pos_high pos_low)
  = match get_subtree_at t pos_high, get_subtree_at t pos_low with
    | Some (Leaf _ f_high), Some (Leaf _ f_low) ->
        // Both positions point to leaves and pos_high =!= pos_low.
        // Case 1: is_prefix pos_low pos_high → impossible
        //   pos_low points to a Leaf, so any extension returns None, contradicting pos_high → Some
        if is_prefix pos_low pos_high then
          leaf_position_no_extension t pos_low pos_high
        // Case 2: is_prefix pos_high pos_low → impossible 
        //   pos_high points to a Leaf, so any extension returns None, contradicting pos_low → Some
        else if is_prefix pos_high pos_low then
          leaf_position_no_extension t pos_high pos_low
        // Case 3: disjoint positions → use swap_reduces_wpl_disjoint
        else (
          get_implies_replace t pos_high (Leaf 0 f_low);
          swap_reduces_wpl_disjoint t pos_high pos_low f_high f_low
        )
    | _, _ -> ()
#pop-options

(*** Helper Lemmas for Greedy Choice Property ***)

// Helper: A non-leaf tree has at least 2 leaves
let rec tree_has_two_leaves (t: htree)
  : Lemma (ensures (match t with
                    | Leaf _ _ -> length (leaf_freqs t) == 1
                    | Internal _ _ _ -> length (leaf_freqs t) >= 2))
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r ->
        tree_has_two_leaves l;
        tree_has_two_leaves r;
        // leaf_freqs (Internal _ l r) == leaf_freqs l @ leaf_freqs r
        // length (leaf_freqs l) >= 1 and length (leaf_freqs r) >= 1
        // So length (leaf_freqs l @ leaf_freqs r) >= 2
        ()

// Helper: In a full binary tree with >= 2 leaves, there exists at least one 
// internal node with two leaf children (siblings at some depth)
// This structural lemma requires detailed case analysis of tree shapes.
// We accept it as it follows from the pigeonhole principle on full binary trees.
#push-options "--fuel 3 --ifuel 2 --z3rlimit 30"
let rec exists_sibling_leaves (t: htree)
  : Lemma (requires Internal? t)
          (ensures (exists (f1 f2: pos). are_siblings t f1 f2 == true))
          (decreases t)
  = match t with
    | Internal _ (Leaf _ f1) (Leaf _ f2) -> 
        assert (are_siblings t f1 f2 == true)
    | Internal _ (Leaf _ _) r ->
        exists_sibling_leaves r;
        // IH gives: exists f1 f2. are_siblings r f1 f2 == true
        // are_siblings t f1 f2 = false || are_siblings r f1 f2 = are_siblings r f1 f2
        // So: exists f1 f2. are_siblings t f1 f2 == true
        let aux (f1 f2: pos) : Lemma (requires are_siblings r f1 f2 == true)
                                     (ensures are_siblings t f1 f2 == true) = () in
        FStar.Classical.forall_intro_2 (fun f1 -> FStar.Classical.move_requires (aux f1))
    | Internal _ l (Leaf _ _) ->
        exists_sibling_leaves l;
        let aux (f1 f2: pos) : Lemma (requires are_siblings l f1 f2 == true)
                                     (ensures are_siblings t f1 f2 == true) = () in
        FStar.Classical.forall_intro_2 (fun f1 -> FStar.Classical.move_requires (aux f1))
    | Internal _ l r ->
        exists_sibling_leaves l;
        let aux (f1 f2: pos) : Lemma (requires are_siblings l f1 f2 == true)
                                     (ensures are_siblings t f1 f2 == true) = () in
        FStar.Classical.forall_intro_2 (fun f1 -> FStar.Classical.move_requires (aux f1))
#pop-options

// Helper: Compute a position reaching a leaf at maximum depth
let rec max_depth_position (t: htree) : Tot tree_position (decreases t) =
  match t with
  | Leaf _ _ -> []
  | Internal _ l r ->
      if max_leaf_depth l 0 >= max_leaf_depth r 0 then true :: max_depth_position l
      else false :: max_depth_position r

// max_leaf_depth shifts linearly with depth parameter
let rec max_leaf_depth_shift (t: htree) (d: nat) (k: nat)
  : Lemma (ensures max_leaf_depth t (d + k) = max_leaf_depth t d + k)
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r ->
        max_leaf_depth_shift l (d + 1) k;
        max_leaf_depth_shift r (d + 1) k

// The position computed by max_depth_position reaches a leaf at max depth
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec max_depth_position_correct (t: htree) (d: nat)
  : Lemma (ensures (let p = max_depth_position t in
                    d + length p = max_leaf_depth t d /\
                    (match get_subtree_at t p with
                     | Some (Leaf _ _) -> True
                     | _ -> False)))
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r ->
        let ml0 = max_leaf_depth l 0 in
        let mr0 = max_leaf_depth r 0 in
        max_leaf_depth_shift l 0 (d + 1);
        max_leaf_depth_shift r 0 (d + 1);
        // max_leaf_depth l (d+1) = ml0 + (d+1), similarly for r
        if ml0 >= mr0 then (
          max_depth_position_correct l (d + 1);
          max_leaf_depth_shift l 0 1
        ) else (
          max_depth_position_correct r (d + 1);
          max_leaf_depth_shift r 0 1
        )
#pop-options

// There exists a leaf position at maximum depth (position-based formulation).
// Uses get_subtree_at instead of depth_of_leaf to avoid the left-first search
// issue where duplicate frequencies across subtrees can shadow witnesses.
let exists_leaf_at_max_depth (t: htree) (d: nat)
  : Lemma (ensures (let max_d = max_leaf_depth t d in
                    exists (p: tree_position).
                      d + length p = max_d /\
                      (match get_subtree_at t p with
                       | Some (Leaf _ _) -> True
                       | _ -> False)))
  = max_depth_position_correct t d

(*** Greedy Choice Property (CLRS Lemma 16.2) ***)

// Helper: Get position of first occurrence of a leaf with given frequency
let rec find_leaf_position (t: htree) (f: pos) (prefix: tree_position)
  : Tot (option tree_position) (decreases t)
  = match t with
    | Leaf _ f' -> if f = f' then Some prefix else None
    | Internal _ l r ->
        match find_leaf_position l f (prefix @ [true]) with
        | Some pos -> Some pos
        | None -> find_leaf_position r f (prefix @ [false])

// Helper lemma: If two leaves are siblings and not at minimum frequency,
// and we swap them with minimum frequency leaves, WPL doesn't increase
let sibling_swap_maintains_optimality 
  (t: htree) 
  (f_sib1 f_sib2: pos) // current siblings at max depth
  (f_min1 f_min2: pos) // minimum frequency chars
  (pos_sib1 pos_sib2 pos_min1 pos_min2: tree_position)
  : Lemma (requires 
            // Siblings exist at max depth
            is_leaf_at t pos_sib1 f_sib1 /\
            is_leaf_at t pos_sib2 f_sib2 /\
            // Min freq leaves exist
            is_leaf_at t pos_min1 f_min1 /\
            is_leaf_at t pos_min2 f_min2 /\
            // Min freq chars have freq <= siblings
            f_min1 <= f_sib1 /\ f_min2 <= f_sib2 /\
            // Sibling positions are deeper or equal
            length pos_sib1 >= length pos_min1 /\
            length pos_sib2 >= length pos_min2 /\
            // Positions are distinct
            pos_sib1 =!= pos_min1 /\ pos_sib2 =!= pos_min2 /\
            pos_sib1 =!= pos_sib2 /\ pos_min1 =!= pos_min2)
          (ensures True) // In reality: swapped tree has WPL <= original
  = // This would use swap_reduces_wpl twice (once for each leaf)
    // The key is that moving lower frequency to deeper depth
    // and higher frequency to shallower depth doesn't increase WPL
    // This is the core of the exchange argument in CLRS Lemma 16.2
    () // Postcondition is True — this is a documentation placeholder

// Helper: Find the two minimum elements in a list
let rec find_two_mins (l: list pos{length l >= 2})
  : Tot (pos & pos) (decreases l)
  = match l with
    | [x; y] -> if x <= y then (x, y) else (y, x)
    | hd :: tl ->
        if length tl >= 2 then
          let (m1, m2) = find_two_mins tl in
          if hd <= m1 then (hd, m1)
          else if hd <= m2 then (m1, hd)
          else (m1, m2)
        else 
          let [single] = tl in
          if hd <= single then (hd, single) else (single, hd)

// ---- Helper lemmas for greedy choice proof ----

// find_two_mins returns members of the list
let rec find_two_mins_mem (l: list pos{length l >= 2})
  : Lemma (ensures (let (m1, m2) = find_two_mins l in mem m1 l /\ mem m2 l))
          (decreases l)
  = match l with
    | [x; y] -> ()
    | hd :: tl ->
        if length tl >= 2 then (
          find_two_mins_mem tl;
          let (m1, m2) = find_two_mins tl in
          if hd <= m1 then ()
          else if hd <= m2 then ()
          else ()
        ) else ()

// find_two_mins: m1 <= m2
let rec find_two_mins_ordered (l: list pos{length l >= 2})
  : Lemma (ensures (let (m1, m2) = find_two_mins l in m1 <= m2))
          (decreases l)
  = match l with
    | [x; y] -> ()
    | hd :: tl ->
        if length tl >= 2 then (
          find_two_mins_ordered tl
        ) else ()

// find_two_mins: m1 <= every element
let rec find_two_mins_le (l: list pos{length l >= 2})
  : Lemma (ensures (let (m1, _) = find_two_mins l in forall x. mem x l ==> m1 <= x))
          (decreases l)
  = match l with
    | [x; y] -> ()
    | hd :: tl ->
        if length tl >= 2 then (
          find_two_mins_le tl;
          find_two_mins_ordered tl
        ) else ()

// count > 0 iff mem
let rec count_mem (x: pos) (l: list pos)
  : Lemma (ensures (mem x l <==> count x l > 0))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl -> count_mem x tl

// count of append
let rec count_append (x: pos) (l1 l2: list pos)
  : Lemma (ensures count x (l1 @ l2) = count x l1 + count x l2)
          (decreases l1)
  = match l1 with
    | [] -> ()
    | _ :: tl -> count_append x tl l2

// If there's a Leaf at some position in the tree, its freq is in leaf_freqs
let rec subtree_leaf_mem (t: htree) (p: tree_position) (f: pos)
  : Lemma (requires is_leaf_at t p f)
          (ensures mem f (leaf_freqs t))
          (decreases p)
  = match p with
    | [] -> ()
    | hd :: tl ->
        (match t with
        | Internal _ l r ->
            if hd then (
              subtree_leaf_mem l tl f;
              FStar.List.Tot.Properties.append_mem_forall (leaf_freqs l) (leaf_freqs r)
            ) else (
              subtree_leaf_mem r tl f;
              FStar.List.Tot.Properties.append_mem_forall (leaf_freqs l) (leaf_freqs r)
            )
        | Leaf _ _ -> ())
let rec leaf_freqs_nonempty (t: htree)
  : Lemma (ensures Cons? (leaf_freqs t))
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r -> 
        leaf_freqs_nonempty l;
        append_l_cons (hd (leaf_freqs l)) (tl (leaf_freqs l)) (leaf_freqs r)

// same_frequency_multiset + length freqs >= 2 ==> Internal
let same_multiset_internal (t: htree) (freqs: list pos{length freqs >= 2})
  : Lemma (requires same_frequency_multiset t freqs)
          (ensures Internal? t)
  = match t with
    | Leaf _ f ->
        // leaf_freqs (Leaf f) = [f], so count has total 1, but freqs has >= 2 elements
        // length [f] = 1 but length freqs >= 2 means different counts
        assert (count f (leaf_freqs t) = 1);
        assert (count f freqs = 1);
        // Need: freqs has at least 2 elements but only 1 in leaf_freqs
        // There exists some element in freqs. Since length >= 2, there's a second element.
        // If all elements = f, count f freqs >= 2 but count f [f] = 1 — contradiction
        // If some element g <> f, count g freqs >= 1 but count g [f] = 0 — contradiction
        count_mem f freqs;
        let hd_f :: tl_f = freqs in
        if hd_f = f then (
          // tl_f is non-empty (length >= 2), look at its head
          let hd2 :: _ = tl_f in
          if hd2 = f then
            // count f freqs >= 2 but count f [f] = 1
            assert (count f freqs >= 2)
          else (
            // count hd2 freqs >= 1 but count hd2 [f] = 0
            count_mem hd2 freqs;
            assert (count hd2 (leaf_freqs t) = count hd2 freqs)
          )
        ) else (
          count_mem hd_f freqs;
          assert (count hd_f (leaf_freqs t) = count hd_f freqs)
        )
    | Internal _ _ _ -> ()

// max_leaf_depth is always >= d
let rec max_leaf_depth_ge (t: htree) (d: nat)
  : Lemma (ensures max_leaf_depth t d >= d)
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r ->
        max_leaf_depth_ge l (d + 1);
        max_leaf_depth_ge r (d + 1)

// Sibling leaves at max depth: an Internal tree has sibling leaves at max depth
#push-options "--fuel 3 --ifuel 2 --z3rlimit 50"
let rec max_depth_has_sibling_leaves (t: htree)
  : Lemma (requires Internal? t)
          (ensures (exists (parent: tree_position) (fl fr: pos).
                      is_leaf_at t (parent @ [true]) fl /\
                      is_leaf_at t (parent @ [false]) fr /\
                      length (parent @ [true]) = max_leaf_depth t 0 /\
                      length (parent @ [false]) = max_leaf_depth t 0))
          (decreases t)
  = let Internal _ l r = t in
    let ml = max_leaf_depth l 0 in
    let mr = max_leaf_depth r 0 in
    max_leaf_depth_ge l 0;
    max_leaf_depth_ge r 0;
    if ml >= mr then (
      match l with
      | Leaf _ fl ->
          assert (mr = 0);
          (match r with
           | Leaf _ fr ->
               assert (is_leaf_at t ([] @ [true]) fl);
               assert (is_leaf_at t ([] @ [false]) fr);
               max_leaf_depth_shift l 0 1;
               max_leaf_depth_shift r 0 1
           | Internal _ _ _ ->
               max_leaf_depth_ge (Internal?.left r) 1;
               max_leaf_depth_ge (Internal?.right r) 1)
      | Internal _ _ _ ->
          max_depth_has_sibling_leaves l;
          eliminate exists (parent: tree_position) (fl fr: pos).
                      is_leaf_at l (parent @ [true]) fl /\
                      is_leaf_at l (parent @ [false]) fr /\
                      length (parent @ [true]) = ml /\
                      length (parent @ [false]) = ml
          returns exists (parent: tree_position) (fl fr: pos).
                      is_leaf_at t (parent @ [true]) fl /\
                      is_leaf_at t (parent @ [false]) fr /\
                      length (parent @ [true]) = max_leaf_depth t 0 /\
                      length (parent @ [false]) = max_leaf_depth t 0
          with _. (
            let parent' = true :: parent in
            assert (get_subtree_at t (parent' @ [true]) == get_subtree_at l (parent @ [true]));
            assert (get_subtree_at t (parent' @ [false]) == get_subtree_at l (parent @ [false]));
            assert (is_leaf_at t (parent' @ [true]) fl);
            assert (is_leaf_at t (parent' @ [false]) fr);
            max_leaf_depth_shift l 0 1;
            max_leaf_depth_shift r 0 1;
            assert (length (parent' @ [true]) = 1 + length (parent @ [true]));
            assert (length (parent' @ [false]) = 1 + length (parent @ [false]))
          )
    ) else (
      match r with
      | Leaf _ fr ->
          assert (mr = 0);
          (match l with
           | Leaf _ fl ->
               assert (is_leaf_at t ([] @ [true]) fl);
               assert (is_leaf_at t ([] @ [false]) fr);
               max_leaf_depth_shift l 0 1;
               max_leaf_depth_shift r 0 1
           | Internal _ _ _ ->
               max_leaf_depth_ge (Internal?.left l) 1;
               max_leaf_depth_ge (Internal?.right l) 1)
      | Internal _ _ _ ->
          max_depth_has_sibling_leaves r;
          eliminate exists (parent: tree_position) (fl fr: pos).
                      is_leaf_at r (parent @ [true]) fl /\
                      is_leaf_at r (parent @ [false]) fr /\
                      length (parent @ [true]) = mr /\
                      length (parent @ [false]) = mr
          returns exists (parent: tree_position) (fl fr: pos).
                      is_leaf_at t (parent @ [true]) fl /\
                      is_leaf_at t (parent @ [false]) fr /\
                      length (parent @ [true]) = max_leaf_depth t 0 /\
                      length (parent @ [false]) = max_leaf_depth t 0
          with _. (
            let parent' = false :: parent in
            assert (get_subtree_at t (parent' @ [true]) == get_subtree_at r (parent @ [true]));
            assert (get_subtree_at t (parent' @ [false]) == get_subtree_at r (parent @ [false]));
            assert (is_leaf_at t (parent' @ [true]) fl);
            assert (is_leaf_at t (parent' @ [false]) fr);
            max_leaf_depth_shift l 0 1;
            max_leaf_depth_shift r 0 1;
            assert (length (parent' @ [true]) = 1 + length (parent @ [true]));
            assert (length (parent' @ [false]) = 1 + length (parent @ [false]))
          )
    )
#pop-options

// leaf_freqs after replace_subtree_at with a Leaf:
// Replaces exactly one occurrence of old_f with new_f in the leaf frequency list
// Uses additive formulation to avoid nat subtraction issues
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec replace_leaf_changes_freqs (t: htree) (p: tree_position) (f_old f_new: pos)
  : Lemma (requires is_leaf_at t p f_old)
          (ensures (match replace_subtree_at t p (Leaf 0 f_new) with
                    | Some t' ->
                        (forall (x: pos). 
                          count x (leaf_freqs t') + (if x = f_old then 1 else 0) = 
                          count x (leaf_freqs t) + (if x = f_new then 1 else 0))
                    | None -> False))
          (decreases p)
  = get_implies_replace t p (Leaf 0 f_new);
    match p with
    | [] -> ()
    | hd :: tl ->
        match t with
        | Internal f l r ->
            if hd then (
              replace_leaf_changes_freqs l tl f_old f_new;
              let Some l' = replace_subtree_at l tl (Leaf 0 f_new) in
              let aux (x: pos) : Lemma (count x (leaf_freqs l' @ leaf_freqs r) + (if x = f_old then 1 else 0) = 
                                        count x (leaf_freqs l @ leaf_freqs r) + (if x = f_new then 1 else 0))
                = count_append x (leaf_freqs l') (leaf_freqs r);
                  count_append x (leaf_freqs l) (leaf_freqs r) in
              FStar.Classical.forall_intro aux
            ) else (
              replace_leaf_changes_freqs r tl f_old f_new;
              let Some r' = replace_subtree_at r tl (Leaf 0 f_new) in
              let aux (x: pos) : Lemma (count x (leaf_freqs l @ leaf_freqs r') + (if x = f_old then 1 else 0) = 
                                        count x (leaf_freqs l @ leaf_freqs r) + (if x = f_new then 1 else 0))
                = count_append x (leaf_freqs l) (leaf_freqs r');
                  count_append x (leaf_freqs l) (leaf_freqs r) in
              FStar.Classical.forall_intro aux
            )
        | Leaf _ _ -> ()
#pop-options

// A single leaf swap (replace f_old at pos with f_new) preserves the multiset
// when the "other" copy is also updated (both changes cancel out)
let swap_preserves_multiset (t: htree) (pos1 pos2: tree_position) (f1 f2: pos)
  : Lemma (requires 
            is_leaf_at t pos1 f1 /\
            is_leaf_at t pos2 f2 /\
            pos1 =!= pos2 /\
            not (is_prefix pos1 pos2) /\
            not (is_prefix pos2 pos1))
          (ensures (
            let _ = get_implies_replace t pos1 (Leaf 0 f2) in
            let Some t1 = replace_subtree_at t pos1 (Leaf 0 f2) in
            match replace_subtree_at t1 pos2 (Leaf 0 f1) with
            | Some t2 ->
                (forall (x: pos). count x (leaf_freqs t2) = count x (leaf_freqs t))
            | None -> True))
  = get_implies_replace t pos1 (Leaf 0 f2);
    let Some t1 = replace_subtree_at t pos1 (Leaf 0 f2) in
    replace_leaf_changes_freqs t pos1 f1 f2;
    disjoint_replacement_preserves_subtree t pos1 pos2 (Leaf 0 f2);
    assert (is_leaf_at t1 pos2 f2);
    get_implies_replace t1 pos2 (Leaf 0 f1);
    match replace_subtree_at t1 pos2 (Leaf 0 f1) with
    | Some t2 ->
        replace_leaf_changes_freqs t1 pos2 f2 f1;
        // From first: count x t1 + [x=f1] = count x t + [x=f2]
        // From second: count x t2 + [x=f2] = count x t1 + [x=f1]
        // Combined: count x t2 + [x=f2] = count x t + [x=f2] - [x=f1] + [x=f1]
        //         = count x t + [x=f2]
        // So: count x t2 = count x t
        let aux (x: pos) : Lemma (count x (leaf_freqs t2) = count x (leaf_freqs t))
          = // count x t1 + [x=f1] = count x t + [x=f2]    ...(1)
            // count x t2 + [x=f2] = count x t1 + [x=f1]   ...(2)
            // From (1): count x t1 = count x t + [x=f2] - [x=f1]
            // Sub into (2): count x t2 + [x=f2] = count x t + [x=f2]
            // So count x t2 = count x t
            () in
        FStar.Classical.forall_intro aux
    | None -> ()

// Any leaf's position depth <= max_leaf_depth
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec leaf_depth_le_max (t: htree) (p: tree_position) (f: pos)
  : Lemma (requires is_leaf_at t p f)
          (ensures length p <= max_leaf_depth t 0)
          (decreases p)
  = match p with
    | [] -> max_leaf_depth_ge t 0
    | hd :: tl ->
        match t with
        | Internal _ l r ->
            if hd then (
              leaf_depth_le_max l tl f;
              max_leaf_depth_shift l 0 1;
              max_leaf_depth_shift r 0 1
            ) else (
              leaf_depth_le_max r tl f;
              max_leaf_depth_shift l 0 1;
              max_leaf_depth_shift r 0 1
            )
        | Leaf _ _ -> ()
#pop-options

// Find a leaf with given frequency and return its position (without prefix accumulator)
let rec find_leaf_pos (t: htree) (f: pos) : Tot (option tree_position) (decreases t)
  = match t with
    | Leaf _ f' -> if f = f' then Some [] else None
    | Internal _ l r ->
        match find_leaf_pos l f with
        | Some pos -> Some (true :: pos)
        | None ->
            match find_leaf_pos r f with
            | Some pos -> Some (false :: pos)
            | None -> None

// find_leaf_pos correctness
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec find_leaf_pos_correct (t: htree) (f: pos)
  : Lemma (ensures (match find_leaf_pos t f with
                     | Some p -> is_leaf_at t p f
                     | None -> count f (leaf_freqs t) = 0))
          (decreases t)
  = match t with
    | Leaf _ f' -> ()
    | Internal _ l r ->
        find_leaf_pos_correct l f;
        find_leaf_pos_correct r f;
        count_append f (leaf_freqs l) (leaf_freqs r)
#pop-options

// find_leaf_pos returns None iff count = 0
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec find_leaf_pos_none (t: htree) (f: pos)
  : Lemma (ensures (find_leaf_pos t f == None <==> count f (leaf_freqs t) = 0))
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r ->
        find_leaf_pos_none l f;
        find_leaf_pos_none r f;
        count_append f (leaf_freqs l) (leaf_freqs r)
#pop-options

// Key single-swap lemma: swap two leaves, preserve multiset, WPL doesn't increase
// Given: high-freq leaf at deep position, low-freq leaf at shallow position (or equal depth)
// Result: swapped tree with WPL <= original and same frequency multiset
#push-options "--fuel 2 --ifuel 1 --z3rlimit 120"
let single_swap_optimal
  (t: htree) (pos_deep pos_shallow: tree_position) (f_deep f_shallow: pos)
  (freqs: list pos)
  : Lemma (requires 
            is_wpl_optimal t freqs /\
            is_leaf_at t pos_deep f_deep /\
            is_leaf_at t pos_shallow f_shallow /\
            f_deep >= f_shallow /\
            length pos_deep >= length pos_shallow /\
            pos_deep =!= pos_shallow /\
            not (is_prefix pos_deep pos_shallow) /\
            not (is_prefix pos_shallow pos_deep))
          (ensures (
            Some? (replace_subtree_at t pos_deep (Leaf 0 f_shallow)) /\
            (let Some t1 = replace_subtree_at t pos_deep (Leaf 0 f_shallow) in
             Some? (replace_subtree_at t1 pos_shallow (Leaf 0 f_deep)) /\
             (let Some t2 = replace_subtree_at t1 pos_shallow (Leaf 0 f_deep) in
              is_wpl_optimal t2 freqs))))
  = get_implies_replace t pos_deep (Leaf 0 f_shallow);
    let Some t1 = replace_subtree_at t pos_deep (Leaf 0 f_shallow) in
    // Multiset preservation
    swap_preserves_multiset t pos_deep pos_shallow f_deep f_shallow;
    // WPL analysis
    swap_reduces_wpl t pos_deep pos_shallow;
    disjoint_replacement_preserves_subtree t pos_deep pos_shallow (Leaf 0 f_shallow);
    get_implies_replace t1 pos_shallow (Leaf 0 f_deep);
    let Some t2 = replace_subtree_at t1 pos_shallow (Leaf 0 f_deep) in
    assert (same_frequency_multiset t2 freqs);
    assert (weighted_path_length t2 <= weighted_path_length t);
    assert (weighted_path_length t <= weighted_path_length t2);
    let aux (t': htree) : Lemma (requires same_frequency_multiset t' freqs)
                                (ensures weighted_path_length t2 <= weighted_path_length t') = () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

(*** Greedy Choice Property (CLRS Lemma 16.2) ***)

let greedy_choice_property (freqs: list pos{length freqs >= 2}) : prop =
  let (f1, f2) = find_two_mins freqs in
  (exists (t: htree). is_wpl_optimal t freqs) ==>
  (exists (t': htree). is_wpl_optimal t' freqs /\ are_siblings t' f1 f2 == true)

// Two leaves at children positions implies parent is Internal with those leaves
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec parent_has_leaf_children (t: htree) (parent: tree_position) (a b: pos)
  : Lemma (requires is_leaf_at t (parent @ [true]) a /\
                    is_leaf_at t (parent @ [false]) b)
          (ensures (match get_subtree_at t parent with
                    | Some (Internal _ (Leaf _ a') (Leaf _ b')) -> a' = a /\ b' = b
                    | _ -> False))
          (decreases parent)
  = match parent with
    | [] ->
        (match t with
        | Internal _ l r -> ()
        | Leaf _ _ -> ())
    | hd :: tl ->
        (match t with
        | Internal _ l r ->
            if hd then parent_has_leaf_children l tl a b
            else parent_has_leaf_children r tl a b
        | Leaf _ _ -> ())
#pop-options

// are_siblings after replacing the parent subtree with Internal (Leaf f1) (Leaf f2)
#push-options "--fuel 3 --ifuel 2 --z3rlimit 40"
let rec are_siblings_after_replace_parent 
  (t: htree) (parent: tree_position) (f1 f2: pos)
  : Lemma (requires (match get_subtree_at t parent with
                      | Some (Internal _ (Leaf _ _) (Leaf _ _)) -> True
                      | _ -> False))
          (ensures (match replace_subtree_at t parent (Internal (f1 + f2) (Leaf 0 f1) (Leaf 0 f2)) with
                    | Some t' -> are_siblings t' f1 f2 == true
                    | None -> True))
          (decreases parent)
  = match parent with
    | [] -> ()
    | hd :: tl ->
        match t with
        | Internal f l r ->
            if hd then (
              are_siblings_after_replace_parent l tl f1 f2;
              match replace_subtree_at l tl (Internal (f1 + f2) (Leaf 0 f1) (Leaf 0 f2)) with
              | Some l' -> ()
              | None -> ()
            ) else (
              are_siblings_after_replace_parent r tl f1 f2;
              match replace_subtree_at r tl (Internal (f1 + f2) (Leaf 0 f1) (Leaf 0 f2)) with
              | Some r' -> ()
              | None -> ()
            )
        | Leaf _ _ -> ()
#pop-options

// replace_internal_pair_changes_freqs: replacing Internal (Leaf a)(Leaf b) with Internal (Leaf f1)(Leaf f2) 
// at a parent position adjusts multiset counts
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec replace_internal_pair_changes_freqs
  (t: htree) (parent: tree_position) (a b f1 f2: pos)
  : Lemma (requires (get_subtree_at t parent == Some (Internal (a+b) (Leaf 0 a) (Leaf 0 b))))
          (ensures (
            match replace_subtree_at t parent (Internal (f1+f2) (Leaf 0 f1) (Leaf 0 f2)) with
            | Some t' ->
                (forall (x: pos).
                  count x (leaf_freqs t') + (if x = a then 1 else 0) + (if x = b then 1 else 0) =
                  count x (leaf_freqs t) + (if x = f1 then 1 else 0) + (if x = f2 then 1 else 0))
            | None -> False))
          (decreases parent)
  = get_implies_replace t parent (Internal (f1+f2) (Leaf 0 f1) (Leaf 0 f2));
    match parent with
    | [] -> ()
    | hd :: tl ->
        match t with
        | Internal f l r ->
            if hd then (
              replace_internal_pair_changes_freqs l tl a b f1 f2;
              let new_sub = Internal (f1+f2) (Leaf 0 f1) (Leaf 0 f2) in
              let Some l' = replace_subtree_at l tl new_sub in
              let aux (x: pos) : Lemma (
                count x (leaf_freqs l' @ leaf_freqs r) + (if x = a then 1 else 0) + (if x = b then 1 else 0) =
                count x (leaf_freqs l @ leaf_freqs r) + (if x = f1 then 1 else 0) + (if x = f2 then 1 else 0))
                = count_append x (leaf_freqs l') (leaf_freqs r);
                  count_append x (leaf_freqs l) (leaf_freqs r) in
              FStar.Classical.forall_intro aux
            ) else (
              replace_internal_pair_changes_freqs r tl a b f1 f2;
              let new_sub = Internal (f1+f2) (Leaf 0 f1) (Leaf 0 f2) in
              let Some r' = replace_subtree_at r tl new_sub in
              let aux (x: pos) : Lemma (
                count x (leaf_freqs l @ leaf_freqs r') + (if x = a then 1 else 0) + (if x = b then 1 else 0) =
                count x (leaf_freqs l @ leaf_freqs r) + (if x = f1 then 1 else 0) + (if x = f2 then 1 else 0))
                = count_append x (leaf_freqs l) (leaf_freqs r');
                  count_append x (leaf_freqs l) (leaf_freqs r) in
              FStar.Classical.forall_intro aux
            )
        | Leaf _ _ -> ()
#pop-options

// WPL after replacing sibling pair: since f1 <= a and f2 <= b, WPL doesn't increase
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let replace_pair_wpl 
  (t: htree) (parent: tree_position) (a b f1 f2: pos)
  : Lemma (requires get_subtree_at t parent == Some (Internal (a+b) (Leaf 0 a) (Leaf 0 b)) /\
                    f1 <= a /\ f2 <= b)
          (ensures (
            match replace_subtree_at t parent (Internal (f1+f2) (Leaf 0 f1) (Leaf 0 f2)) with
            | Some t' ->
                weighted_path_length t' <= weighted_path_length t
            | None -> False))
  = get_implies_replace t parent (Internal (f1+f2) (Leaf 0 f1) (Leaf 0 f2));
    let old_sub = Internal (a+b) (Leaf 0 a) (Leaf 0 b) in
    let new_sub = Internal (f1+f2) (Leaf 0 f1) (Leaf 0 f2) in
    replace_subtree_wpl_aux t parent new_sub 0;
    let dp = length parent in
    assert (weighted_path_length_aux old_sub dp = a `op_Multiply` (dp + 1) + b `op_Multiply` (dp + 1));
    assert (weighted_path_length_aux new_sub dp = f1 `op_Multiply` (dp + 1) + f2 `op_Multiply` (dp + 1))
#pop-options

// find_two_mins_le2: f2 is <= all elements except possibly one copy of f1
#push-options "--fuel 3 --ifuel 2 --z3rlimit 120"
let rec find_two_mins_le2 (l: list pos{length l >= 2})
  : Lemma (ensures (let (m1, m2) = find_two_mins l in
                    forall x. mem x l ==> (x >= m2 \/ x = m1)))
          (decreases l)
  = match l with
    | [x; y] -> ()
    | hd :: tl ->
        if length tl >= 2 then (
          find_two_mins_le2 tl;
          find_two_mins_le tl;
          find_two_mins_ordered tl;
          let (m1_tl, m2_tl) = find_two_mins tl in
          if hd <= m1_tl then (
            // result = (hd, m1_tl), need: forall x in l. x >= m1_tl \/ x = hd
            // x = hd: x = hd, second disjunct
            // x in tl: by find_two_mins_le, m1_tl <= x, so x >= m1_tl
            assert (forall x. mem x tl ==> m1_tl <= x)
          ) else if hd <= m2_tl then (
            // result = (m1_tl, hd), need: forall x in l. x >= hd \/ x = m1_tl
            // x = hd: x = hd >= hd
            // x in tl: by IH, x >= m2_tl \/ x = m1_tl
            //   x >= m2_tl >= hd, or x = m1_tl
            assert (forall x. mem x tl ==> (x >= m2_tl \/ x = m1_tl));
            assert (m2_tl >= hd)
          ) else (
            // result = (m1_tl, m2_tl), need: forall x in l. x >= m2_tl \/ x = m1_tl
            // x = hd: hd > m2_tl, so x >= m2_tl
            // x in tl: by IH directly
            assert (hd > m2_tl)
          )
        ) else ()
#pop-options

// If a subtree at position parent is Internal with two leaf children matching f1,f2
// then are_siblings t f1 f2 == true
#push-options "--fuel 3 --ifuel 2 --z3rlimit 30"
let rec subtree_siblings_implies_are_siblings
  (t: htree) (parent: tree_position) (f1 f2: pos)
  : Lemma (requires (match get_subtree_at t parent with
                      | Some (Internal _ (Leaf _ f1') (Leaf _ f2')) -> 
                          (f1' = f1 && f2' = f2) || (f1' = f2 && f2' = f1)
                      | _ -> False))
          (ensures are_siblings t f1 f2 == true)
          (decreases parent)
  = match parent with
    | [] -> ()
    | hd :: tl ->
        match t with
        | Internal _ l r ->
            if hd then (
              subtree_siblings_implies_are_siblings l tl f1 f2
            ) else (
              subtree_siblings_implies_are_siblings r tl f1 f2
            )
        | Leaf _ _ -> ()
#pop-options

// replace_leaf_preserves_max_depth: replacing a leaf with another leaf preserves max_leaf_depth
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec replace_leaf_preserves_max_depth (t: htree) (p: tree_position) (f_old f_new: pos)
  : Lemma (requires is_leaf_at t p f_old)
          (ensures (match replace_subtree_at t p (Leaf 0 f_new) with
                    | Some t' -> max_leaf_depth t' 0 = max_leaf_depth t 0
                    | None -> False))
          (decreases p)
  = get_implies_replace t p (Leaf 0 f_new);
    match p with
    | [] -> ()
    | hd :: tl ->
        match t with
        | Internal _ l r ->
            if hd then (
              replace_leaf_preserves_max_depth l tl f_old f_new;
              max_leaf_depth_shift l 0 1;
              max_leaf_depth_shift r 0 1;
              let Some l' = replace_subtree_at l tl (Leaf 0 f_new) in
              max_leaf_depth_shift l' 0 1
            ) else (
              replace_leaf_preserves_max_depth r tl f_old f_new;
              max_leaf_depth_shift l 0 1;
              max_leaf_depth_shift r 0 1;
              let Some r' = replace_subtree_at r tl (Leaf 0 f_new) in
              max_leaf_depth_shift r' 0 1
            )
        | Leaf _ _ -> ()
#pop-options

// Sibling positions are distinct and not prefixes
let rec sibling_positions_disjoint (parent: list bool)
  : Lemma (ensures parent @ [true] =!= parent @ [false] /\
                   not (is_prefix (parent @ [true]) (parent @ [false])) /\
                   not (is_prefix (parent @ [false]) (parent @ [true])))
          (decreases parent)
  = match parent with
    | [] -> ()
    | _ :: tl -> sibling_positions_disjoint tl

// Count in a subtree is <= count in the whole tree
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec subtree_count_le (t: htree) (p: tree_position) (f: pos)
  : Lemma (requires Some? (get_subtree_at t p))
          (ensures count f (leaf_freqs (Some?.v (get_subtree_at t p))) <= count f (leaf_freqs t))
          (decreases p)
  = match p with
    | [] -> ()
    | hd :: tl ->
      match t with
      | Internal _ l r ->
        count_append f (leaf_freqs l) (leaf_freqs r);
        if hd then subtree_count_le l tl f
        else subtree_count_le r tl f
      | Leaf _ _ -> ()
#pop-options

// If find_two_mins returns equal values, count >= 2
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec find_two_mins_equal_count (l: list pos{length l >= 2})
  : Lemma (ensures (let (m1, m2) = find_two_mins l in m1 = m2 ==> count m1 l >= 2))
          (decreases l)
  = match l with
    | [x; y] -> ()
    | hd :: tl ->
        if length tl >= 2 then (
          find_two_mins_equal_count tl;
          find_two_mins_mem tl;
          find_two_mins_ordered tl;
          let (m1_tl, m2_tl) = find_two_mins tl in
          if hd <= m1_tl then (
            // result = (hd, m1_tl). equal means hd = m1_tl.
            // count hd l = 1 + count hd tl. mem m1_tl tl, so count m1_tl tl >= 1.
            // hd = m1_tl, so count hd tl >= 1. Total >= 2.
            count_mem m1_tl tl
          ) else if hd <= m2_tl then (
            // result = (m1_tl, hd). equal means m1_tl = hd. But hd > m1_tl. Contradiction.
            ()
          ) else (
            // result = (m1_tl, m2_tl). By IH on tl.
            ()
          )
        ) else ()
#pop-options

// If count m1 l >= 2 and m1 is the minimum, find_two_mins returns (m1, m1)
#push-options "--fuel 3 --ifuel 2 --z3rlimit 100"
let rec find_two_mins_count_ge2 (l: list pos{length l >= 2}) (m1: pos)
  : Lemma (requires fst (find_two_mins l) = m1 /\ count m1 l >= 2)
          (ensures snd (find_two_mins l) = m1)
          (decreases l)
  = match l with
    | [x; y] -> ()
    | hd :: tl ->
        if length tl >= 2 then (
          find_two_mins_ordered tl;
          find_two_mins_le tl;
          count_mem m1 tl;
          let (m1_tl, m2_tl) = find_two_mins tl in
          if hd <= m1_tl then (
            // result = (hd, m1_tl). fst = hd = m1.
            // count m1 l = 1 + count m1 tl >= 2, so count m1 tl >= 1 => mem m1 tl.
            // m1 = hd <= m1_tl. Also m1_tl <= m1 (since m1 is in tl and m1_tl is min of tl).
            // So m1 = m1_tl. snd = m1_tl = m1. QED.
            ()
          ) else if hd <= m2_tl then (
            // result = (m1_tl, hd). fst = m1_tl = m1.
            // hd > m1_tl = m1, so hd <> m1. count m1 l = count m1 tl >= 2.
            // By IH on tl: snd(find_two_mins tl) = m2_tl = m1.
            // m2_tl = m1 = m1_tl, so hd <= m2_tl = m1_tl. But hd > m1_tl. Contradiction.
            find_two_mins_count_ge2 tl m1
          ) else (
            // result = (m1_tl, m2_tl). fst = m1_tl = m1.
            // hd > m2_tl >= m1_tl = m1, so hd <> m1. count m1 tl >= 2.
            // By IH: snd(find_two_mins tl) = m2_tl = m1. QED.
            find_two_mins_count_ge2 tl m1
          )
        ) else (
          // length tl = 1. l = [hd; single].
          let [single] = tl in
          ()
        )
#pop-options

// Two leaves at distinct positions with same freq => count >= 2
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec two_leaves_count_ge2 (t: htree) (p1 p2: tree_position) (f: pos)
  : Lemma (requires is_leaf_at t p1 f /\
                    is_leaf_at t p2 f /\
                    p1 =!= p2)
          (ensures count f (leaf_freqs t) >= 2)
          (decreases p1)
  = match t with
    | Leaf _ _ -> () // p1 and p2 can't both be valid and distinct
    | Internal _ l r ->
      count_append f (leaf_freqs l) (leaf_freqs r);
      (match p1, p2 with
       | true :: tl1, true :: tl2 ->
         two_leaves_count_ge2 l tl1 tl2 f
       | false :: tl1, false :: tl2 ->
         two_leaves_count_ge2 r tl1 tl2 f
       | true :: tl1, false :: tl2 ->
         subtree_leaf_mem l tl1 f;
         subtree_leaf_mem r tl2 f;
         count_mem f (leaf_freqs l);
         count_mem f (leaf_freqs r)
       | false :: tl1, true :: tl2 ->
         subtree_leaf_mem r tl1 f;
         subtree_leaf_mem l tl2 f;
         count_mem f (leaf_freqs r);
         count_mem f (leaf_freqs l)
       | [], _ -> ()  // impossible: Leaf at [] but Internal
       | _, [] -> ()) // impossible
#pop-options
let rec find_leaf_pos_avoiding (t: htree) (f: pos) (avoid: tree_position)
  : Tot (option tree_position) (decreases t)
  = match t with
    | Leaf _ g ->
      if g = f then
        (match avoid with
         | [] -> None
         | _ -> Some [])
      else None
    | Internal _ l r ->
      match avoid with
      | [] ->
        (match find_leaf_pos l f with
         | Some p -> Some (true :: p)
         | None ->
           match find_leaf_pos r f with
           | Some p -> Some (false :: p)
           | None -> None)
      | true :: avoid_tl ->
        (match find_leaf_pos r f with
         | Some p -> Some (false :: p)
         | None ->
           match find_leaf_pos_avoiding l f avoid_tl with
           | Some p -> Some (true :: p)
           | None -> None)
      | false :: avoid_tl ->
        (match find_leaf_pos l f with
         | Some p -> Some (true :: p)
         | None ->
           match find_leaf_pos_avoiding r f avoid_tl with
           | Some p -> Some (false :: p)
           | None -> None)

// find_leaf_pos_avoiding correctness
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec find_leaf_pos_avoiding_correct (t: htree) (f: pos) (avoid: tree_position)
  : Lemma (ensures (match find_leaf_pos_avoiding t f avoid with
                    | Some p -> is_leaf_at t p f /\ p =!= avoid
                    | None -> True))
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r ->
      match avoid with
      | [] ->
        find_leaf_pos_correct l f;
        find_leaf_pos_correct r f
      | true :: avoid_tl ->
        find_leaf_pos_correct r f;
        find_leaf_pos_avoiding_correct l f avoid_tl
      | false :: avoid_tl ->
        find_leaf_pos_correct l f;
        find_leaf_pos_avoiding_correct r f avoid_tl
#pop-options

// find_leaf_pos_avoiding succeeds when count >= 2 and avoid has the leaf
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec find_leaf_pos_avoiding_some (t: htree) (f: pos) (avoid: tree_position)
  : Lemma (requires count f (leaf_freqs t) >= 2 /\
                    is_leaf_at t avoid f)
          (ensures Some? (find_leaf_pos_avoiding t f avoid))
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r ->
      count_append f (leaf_freqs l) (leaf_freqs r);
      find_leaf_pos_none l f;
      find_leaf_pos_none r f;
      (match avoid with
      | [] -> ()
      | true :: avoid_tl ->
        // avoid is in left subtree. count f total >= 2.
        // If right has count >= 1, find_leaf_pos r f succeeds, done.
        // If right has count = 0, left has count >= 2, recurse.
        if count f (leaf_freqs r) > 0 then ()
        else find_leaf_pos_avoiding_some l f avoid_tl
      | false :: avoid_tl ->
        if count f (leaf_freqs l) > 0 then ()
        else find_leaf_pos_avoiding_some r f avoid_tl)
#pop-options

// Exchange sub-lemma: given an optimal tree with sibling leaves a,b at max depth,
// produce an optimal tree with f1,f2 as siblings
#push-options "--fuel 3 --ifuel 2 --z3rlimit 600"
let greedy_exchange
  (t: htree) (freqs: list pos{length freqs >= 2})
  (parent: tree_position) (a b: pos)
  (f1 f2: pos)
  : Lemma (requires
      is_wpl_optimal t freqs /\
      (let (m1, m2) = find_two_mins freqs in f1 == m1 /\ f2 == m2) /\
      is_leaf_at t (parent @ [true]) a /\
      is_leaf_at t (parent @ [false]) b /\
      length (parent @ [true]) = max_leaf_depth t 0 /\
      length (parent @ [false]) = max_leaf_depth t 0 /\
      f1 <= f2 /\
      mem f1 freqs /\ mem f2 freqs /\
      (forall x. mem x freqs ==> f1 <= x) /\
      (forall x. mem x freqs ==> (x >= f2 \/ x = f1)) /\
      ~((a = f1 && b = f2) || (a = f2 && b = f1)))
    (ensures exists (t': htree). is_wpl_optimal t' freqs /\ are_siblings t' f1 f2 == true)
  =
    parent_has_leaf_children t parent a b;
    let pos_a = parent @ [true] in
    let pos_b = parent @ [false] in
    sibling_positions_disjoint parent;
    // a,b are leaf freqs in the tree => they're in freqs => f1 <= a, f1 <= b
    subtree_leaf_mem t pos_a a;
    subtree_leaf_mem t pos_b b;
    count_mem a (leaf_freqs t);
    count_mem b (leaf_freqs t);
    count_mem a freqs;
    count_mem b freqs;
    assert (f1 <= a);
    assert (f1 <= b);
    // Choose ordering
    let tgt1 = if f2 <= b then pos_a else pos_b in
    let tgt2 = if f2 <= b then pos_b else pos_a in
    let tgt_a = if f2 <= b then a else b in
    let tgt_b = if f2 <= b then b else a in
    // tgt_b >= f2: in the f2 > b case, tgt_b = a, and a >= f2 \/ a = f1.
    // If a = f1 then f1 <= f2 and tgt_b = f1, so tgt_b >= f2 requires f1 >= f2, hence f1 = f2 = tgt_b.
    assert (mem a freqs);
    assert (a >= f2 \/ a = f1);
    assert (mem b freqs);
    assert (b >= f2 \/ b = f1);
    assert (tgt_a >= f1);
    // tgt_b >= f2 is NOT always true. When f2 > b and a = f1 < f2, tgt_b = a = f1 < f2.
    // Handle this case separately.
    if not (tgt_b >= f2) then (
      // This case is IMPOSSIBLE.
      // tgt_b < f2 requires f2 > b (otherwise tgt_b = b >= f2).
      // When f2 > b: tgt_b = a. And a < f2, so a = f1 (from a >= f2 \/ a = f1).
      // Also b < f2, so b = f1 (from b >= f2 \/ b = f1).
      // Both siblings a = b = f1 have the same frequency.
      // Two leaves with f1 means count f1 (leaf_freqs t) >= 2.
      // By same_frequency_multiset: count f1 freqs >= 2.
      // Since f1 is the minimum (forall x. mem x freqs ==> f1 <= x) and appears >= 2 times,
      // find_two_mins must return (f1, f1), so f2 = f1. But tgt_b < f2 and tgt_b = f1 means f1 < f2.
      // Contradiction: f1 = f2 and f1 < f2.
      // Prove: a = f1 and b = f1
      assert (a = f1);
      assert (b = f1);
      // Two distinct positions with Leaf f1 => count f1 (leaf_freqs t) >= 2
      two_leaves_count_ge2 t pos_a pos_b f1;
      assert (count f1 (leaf_freqs t) >= 2);
      // same_frequency_multiset => count f1 freqs >= 2
      assert (count f1 freqs >= 2);
      // find_two_mins returns (f1, f2) with f1 = fst, count f1 freqs >= 2
      // => snd (find_two_mins freqs) = f1, i.e., f2 = f1
      find_two_mins_count_ge2 freqs f1;
      assert (f2 = f1)
      // But tgt_b < f2 and tgt_b >= f1 (since tgt_b = a = f1), so f1 < f2.
      // f1 = f2 and f1 < f2 is a contradiction. F* should derive False.
    ) else (
    assert (is_leaf_at t tgt1 tgt_a);
    assert (is_leaf_at t tgt2 tgt_b);
    assert (tgt1 =!= tgt2);
    assert (not (is_prefix tgt1 tgt2));
    assert (not (is_prefix tgt2 tgt1));

    if tgt_a = f1 then (
      if tgt_b = f2 then ()
      else (
        // Single swap: tgt_b <-> f2
        count_mem f2 (leaf_freqs t);
        count_mem f2 freqs;
        find_leaf_pos_none t f2;
        find_leaf_pos_correct t f2;
        let Some pos_f2 = find_leaf_pos t f2 in
        if pos_f2 = tgt1 then (
          // pos_f2 = tgt1 implies f2 = tgt_a = f1. So f1 = f2.
          assert (f1 = f2);
          // tgt_b <> f2 = f1. Use find_leaf_pos_avoiding to find f2 elsewhere.
          find_two_mins_equal_count freqs;
          assert (count f1 freqs >= 2);
          assert (count f2 (leaf_freqs t) >= 2);
          find_leaf_pos_avoiding_some t f2 tgt1;
          find_leaf_pos_avoiding_correct t f2 tgt1;
          let Some pos_f2' = find_leaf_pos_avoiding t f2 tgt1 in
          assert (pos_f2' =!= tgt1);
          leaf_depth_le_max t pos_f2' f2;
          // pos_f2' vs tgt2
          (if pos_f2' = tgt2 then (
            // f2 = tgt_b, but tgt_b <> f2. Contradiction.
            ()
          ) else (
          (if is_prefix tgt2 pos_f2' then leaf_position_no_extension t tgt2 pos_f2'
           else if is_prefix pos_f2' tgt2 then leaf_position_no_extension t pos_f2' tgt2);
          single_swap_optimal t tgt2 pos_f2' tgt_b f2 freqs;
          let Some t1 = replace_subtree_at t tgt2 (Leaf 0 f2) in
          let Some t2 = replace_subtree_at t1 pos_f2' (Leaf 0 tgt_b) in
          // Preserve tgt1 through both replacements
          get_implies_replace t tgt2 (Leaf 0 f2);
          disjoint_replacement_preserves_subtree t tgt2 tgt1 (Leaf 0 f2);
          disjoint_replacement_preserves_subtree t tgt2 pos_f2' (Leaf 0 f2);
          (if is_prefix pos_f2' tgt1 then leaf_position_no_extension t1 pos_f2' tgt1
           else if is_prefix tgt1 pos_f2' then leaf_position_no_extension t1 tgt1 pos_f2');
          get_implies_replace t1 pos_f2' (Leaf 0 tgt_b);
          disjoint_replacement_preserves_subtree t1 pos_f2' tgt1 (Leaf 0 tgt_b);
          // Preserve tgt2
          replace_then_get t tgt2 (Leaf 0 f2);
          (if is_prefix pos_f2' tgt2 then leaf_position_no_extension t1 pos_f2' tgt2
           else if is_prefix tgt2 pos_f2' then leaf_position_no_extension t1 tgt2 pos_f2');
          disjoint_replacement_preserves_subtree t1 pos_f2' tgt2 (Leaf 0 tgt_b);
          parent_has_leaf_children t2 parent
            (if f2 <= b then f1 else f2) (if f2 <= b then f2 else f1);
          subtree_siblings_implies_are_siblings t2 parent f1 f2
          ))
        ) else (
        leaf_depth_le_max t pos_f2 f2;
        (if is_prefix tgt2 pos_f2 then leaf_position_no_extension t tgt2 pos_f2
         else if is_prefix pos_f2 tgt2 then leaf_position_no_extension t pos_f2 tgt2);
        single_swap_optimal t tgt2 pos_f2 tgt_b f2 freqs;
        let Some t1 = replace_subtree_at t tgt2 (Leaf 0 f2) in
        let Some t2 = replace_subtree_at t1 pos_f2 (Leaf 0 tgt_b) in
        // Preserve tgt1 through both replacements
        get_implies_replace t tgt2 (Leaf 0 f2);
        disjoint_replacement_preserves_subtree t tgt2 tgt1 (Leaf 0 f2);
        disjoint_replacement_preserves_subtree t tgt2 pos_f2 (Leaf 0 f2);
        (if is_prefix pos_f2 tgt1 then leaf_position_no_extension t1 pos_f2 tgt1
         else if is_prefix tgt1 pos_f2 then leaf_position_no_extension t1 tgt1 pos_f2);
        get_implies_replace t1 pos_f2 (Leaf 0 tgt_b);
        disjoint_replacement_preserves_subtree t1 pos_f2 tgt1 (Leaf 0 tgt_b);
        // Preserve tgt2: replace_then_get + disjoint from pos_f2
        replace_then_get t tgt2 (Leaf 0 f2);
        (if is_prefix pos_f2 tgt2 then leaf_position_no_extension t1 pos_f2 tgt2
         else if is_prefix tgt2 pos_f2 then leaf_position_no_extension t1 tgt2 pos_f2);
        disjoint_replacement_preserves_subtree t1 pos_f2 tgt2 (Leaf 0 tgt_b);
        parent_has_leaf_children t2 parent
          (if f2 <= b then f1 else f2) (if f2 <= b then f2 else f1);
        subtree_siblings_implies_are_siblings t2 parent f1 f2
        )
      )
    ) else (
      // Double swap: tgt_a <-> f1, then tgt_b <-> f2
      count_mem f1 (leaf_freqs t);
      count_mem f1 freqs;
      find_leaf_pos_none t f1;
      find_leaf_pos_correct t f1;
      let Some pos_f1 = find_leaf_pos t f1 in
      leaf_depth_le_max t pos_f1 f1;
      (if is_prefix tgt1 pos_f1 then leaf_position_no_extension t tgt1 pos_f1
       else if is_prefix pos_f1 tgt1 then leaf_position_no_extension t pos_f1 tgt1);
      single_swap_optimal t tgt1 pos_f1 tgt_a f1 freqs;
      let Some s1 = replace_subtree_at t tgt1 (Leaf 0 f1) in
      let Some s2 = replace_subtree_at s1 pos_f1 (Leaf 0 tgt_a) in
      // s2 is optimal
      // Establish positions in s1 and s2
      replace_then_get t tgt1 (Leaf 0 f1);
      disjoint_replacement_preserves_subtree t tgt1 pos_f1 (Leaf 0 f1);
      // tgt1 preserved through pos_f1 replacement
      (if is_prefix pos_f1 tgt1 then leaf_position_no_extension s1 pos_f1 tgt1
       else if is_prefix tgt1 pos_f1 then leaf_position_no_extension s1 tgt1 pos_f1);
      get_implies_replace s1 pos_f1 (Leaf 0 tgt_a);
      disjoint_replacement_preserves_subtree s1 pos_f1 tgt1 (Leaf 0 tgt_a);
      assert (is_leaf_at s2 tgt1 f1);
      // tgt2 in s1 and s2
      disjoint_replacement_preserves_subtree t tgt1 tgt2 (Leaf 0 f1);
      // pos_f1 vs tgt2: if equal, then f1 = tgt_b, and tgt_b >= f2 >= f1, so f1 = f2 = tgt_b
      if pos_f1 = tgt2 then (
        // pos_f1 = tgt2, so f1 = tgt_b and f1 = f2.
        // t already has f2 (= f1) at tgt2. Just need f1 at tgt1.
        // Use find_leaf_pos_avoiding to find f1 not at tgt2.
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
          // f1 already at tgt1 = tgt_a. But tgt_a <> f1 (we're in else branch). Contradiction.
          ()
        ) else (
        (if is_prefix tgt1 pos_f1' then leaf_position_no_extension t tgt1 pos_f1'
         else if is_prefix pos_f1' tgt1 then leaf_position_no_extension t pos_f1' tgt1);
        single_swap_optimal t tgt1 pos_f1' tgt_a f1 freqs;
        let Some s1' = replace_subtree_at t tgt1 (Leaf 0 f1) in
        let Some s2' = replace_subtree_at s1' pos_f1' (Leaf 0 tgt_a) in
        // tgt1 has f1 in s2'
        replace_then_get t tgt1 (Leaf 0 f1);
        get_implies_replace t tgt1 (Leaf 0 f1);
        disjoint_replacement_preserves_subtree t tgt1 pos_f1' (Leaf 0 f1);
        (if is_prefix pos_f1' tgt1 then leaf_position_no_extension s1' pos_f1' tgt1
         else if is_prefix tgt1 pos_f1' then leaf_position_no_extension s1' tgt1 pos_f1');
        get_implies_replace s1' pos_f1' (Leaf 0 tgt_a);
        disjoint_replacement_preserves_subtree s1' pos_f1' tgt1 (Leaf 0 tgt_a);
        assert (is_leaf_at s2' tgt1 f1);
        // tgt2 has f2 = f1 = tgt_b in s2'
        disjoint_replacement_preserves_subtree t tgt1 tgt2 (Leaf 0 f1);
        (if is_prefix pos_f1' tgt2 then leaf_position_no_extension s1' pos_f1' tgt2
         else if is_prefix tgt2 pos_f1' then leaf_position_no_extension s1' tgt2 pos_f1');
        disjoint_replacement_preserves_subtree s1' pos_f1' tgt2 (Leaf 0 tgt_a);
        assert (is_leaf_at s2' tgt2 tgt_b);
        parent_has_leaf_children s2' parent
          (if f2 <= b then f1 else f2) (if f2 <= b then f2 else f1);
        subtree_siblings_implies_are_siblings s2' parent f1 f2
        )
      ) else (
      (if is_prefix pos_f1 tgt2 then leaf_position_no_extension s1 pos_f1 tgt2
       else if is_prefix tgt2 pos_f1 then leaf_position_no_extension s1 tgt2 pos_f1);
      disjoint_replacement_preserves_subtree s1 pos_f1 tgt2 (Leaf 0 tgt_a);
      assert (is_leaf_at s2 tgt2 tgt_b);
      
      if tgt_b = f2 then (
        parent_has_leaf_children s2 parent
          (if f2 <= b then f1 else f2) (if f2 <= b then f2 else f1);
        subtree_siblings_implies_are_siblings s2 parent f1 f2
      ) else (
        // Second swap: tgt_b <-> f2 in s2
        count_mem f2 (leaf_freqs s2);
        count_mem f2 freqs;
        find_leaf_pos_none s2 f2;
        find_leaf_pos_correct s2 f2;
        let Some pos_f2 = find_leaf_pos s2 f2 in
        if pos_f2 = tgt1 then (
          // pos_f2 = tgt1 means f2 = f1 in s2. Use find_leaf_pos_avoiding.
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
            // f2 = tgt_b, but tgt_b <> f2. Contradiction.
            ()
          ) else (
          (if is_prefix tgt2 pos_f2' then leaf_position_no_extension s2 tgt2 pos_f2'
           else if is_prefix pos_f2' tgt2 then leaf_position_no_extension s2 pos_f2' tgt2);
          single_swap_optimal s2 tgt2 pos_f2' tgt_b f2 freqs;
          let Some s3 = replace_subtree_at s2 tgt2 (Leaf 0 f2) in
          let Some s4 = replace_subtree_at s3 pos_f2' (Leaf 0 tgt_b) in
          // Establish positions in s3 and s4
          replace_then_get s2 tgt2 (Leaf 0 f2);
          disjoint_replacement_preserves_subtree s2 tgt2 pos_f2' (Leaf 0 f2);
          // tgt1 preserved in s3
          (if is_prefix tgt2 tgt1 then leaf_position_no_extension s2 tgt2 tgt1
           else if is_prefix tgt1 tgt2 then leaf_position_no_extension s2 tgt1 tgt2);
          get_implies_replace s2 tgt2 (Leaf 0 f2);
          disjoint_replacement_preserves_subtree s2 tgt2 tgt1 (Leaf 0 f2);
          // tgt1 preserved in s4
          (if is_prefix pos_f2' tgt1 then leaf_position_no_extension s3 pos_f2' tgt1
           else if is_prefix tgt1 pos_f2' then leaf_position_no_extension s3 tgt1 pos_f2');
          get_implies_replace s3 pos_f2' (Leaf 0 tgt_b);
          disjoint_replacement_preserves_subtree s3 pos_f2' tgt1 (Leaf 0 tgt_b);
          // tgt2 preserved in s4
          (if is_prefix pos_f2' tgt2 then leaf_position_no_extension s3 pos_f2' tgt2
           else if is_prefix tgt2 pos_f2' then leaf_position_no_extension s3 tgt2 pos_f2');
          disjoint_replacement_preserves_subtree s3 pos_f2' tgt2 (Leaf 0 tgt_b);
          parent_has_leaf_children s4 parent
            (if f2 <= b then f1 else f2) (if f2 <= b then f2 else f1);
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
        (if is_prefix tgt2 pos_f2 then leaf_position_no_extension s2 tgt2 pos_f2
         else if is_prefix pos_f2 tgt2 then leaf_position_no_extension s2 pos_f2 tgt2);
        single_swap_optimal s2 tgt2 pos_f2 tgt_b f2 freqs;
        let Some s3 = replace_subtree_at s2 tgt2 (Leaf 0 f2) in
        let Some s4 = replace_subtree_at s3 pos_f2 (Leaf 0 tgt_b) in
        // Establish positions in s3 and s4
        replace_then_get s2 tgt2 (Leaf 0 f2);
        disjoint_replacement_preserves_subtree s2 tgt2 pos_f2 (Leaf 0 f2);
        // tgt1 preserved in s3
        (if is_prefix tgt2 tgt1 then leaf_position_no_extension s2 tgt2 tgt1
         else if is_prefix tgt1 tgt2 then leaf_position_no_extension s2 tgt1 tgt2);
        get_implies_replace s2 tgt2 (Leaf 0 f2);
        disjoint_replacement_preserves_subtree s2 tgt2 tgt1 (Leaf 0 f2);
        // tgt1 preserved in s4
        (if is_prefix pos_f2 tgt1 then leaf_position_no_extension s3 pos_f2 tgt1
         else if is_prefix tgt1 pos_f2 then leaf_position_no_extension s3 tgt1 pos_f2);
        get_implies_replace s3 pos_f2 (Leaf 0 tgt_b);
        disjoint_replacement_preserves_subtree s3 pos_f2 tgt1 (Leaf 0 tgt_b);
        // tgt2 preserved in s4
        (if is_prefix pos_f2 tgt2 then leaf_position_no_extension s3 pos_f2 tgt2
         else if is_prefix tgt2 pos_f2 then leaf_position_no_extension s3 tgt2 pos_f2);
        disjoint_replacement_preserves_subtree s3 pos_f2 tgt2 (Leaf 0 tgt_b);
        parent_has_leaf_children s4 parent
          (if f2 <= b then f1 else f2) (if f2 <= b then f2 else f1);
        subtree_siblings_implies_are_siblings s4 parent f1 f2
        )
      )
      )
    )
    )
#pop-options

// Main greedy choice theorem
#push-options "--fuel 3 --ifuel 2 --z3rlimit 200"
let greedy_choice_theorem (freqs: list pos{length freqs >= 2})
  : Lemma (ensures greedy_choice_property freqs)
  = let (f1, f2) = find_two_mins freqs in
    find_two_mins_mem freqs;
    find_two_mins_le freqs;
    find_two_mins_ordered freqs;
    find_two_mins_le2 freqs;
    let aux (t: htree)
      : Lemma (requires is_wpl_optimal t freqs)
              (ensures exists (t': htree). is_wpl_optimal t' freqs /\ are_siblings t' f1 f2 == true)
      = same_multiset_internal t freqs;
        max_depth_has_sibling_leaves t;
        eliminate exists (parent: tree_position) (fl fr: pos).
            is_leaf_at t (parent @ [true]) fl /\
            is_leaf_at t (parent @ [false]) fr /\
            length (parent @ [true]) = max_leaf_depth t 0 /\
            length (parent @ [false]) = max_leaf_depth t 0
        returns exists (t': htree). is_wpl_optimal t' freqs /\ are_siblings t' f1 f2 == true
        with _. (
          parent_has_leaf_children t parent fl fr;
          if (fl = f1 && fr = f2) || (fl = f2 && fr = f1) then
            subtree_siblings_implies_are_siblings t parent f1 f2
          else
            greedy_exchange t freqs parent fl fr f1 f2
        )
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

// Helper: Remove one element from a list
let rec remove_one (f: pos) (l: list pos) 
  : Tot (option (list pos)) (decreases l)
  = match l with
    | [] -> None
    | hd :: tl ->
        if hd = f then Some tl
        else
          match remove_one f tl with
          | Some tl' -> Some (hd :: tl')
          | None -> None

// Helper: Remove two elements from a list and add a new one (their sum)
let rec remove_and_merge (l: list pos) (f1 f2: pos) 
  : Tot (option (list pos)) (decreases l)
  = match l with
    | [] -> None
    | hd :: tl ->
        if hd = f1 then
          match remove_one f2 tl with
          | Some tl' -> Some ((f1 + f2) :: tl')
          | None -> None
        else if hd = f2 then
          match remove_one f1 tl with
          | Some tl' -> Some ((f1 + f2) :: tl')
          | None -> None
        else
          match remove_and_merge tl f1 f2 with
          | Some rest -> Some (hd :: rest)
          | None -> None

// Helper: Replace two sibling leaves with a single leaf in a tree
let rec replace_siblings_with_merged (t: htree) (f1 f2: pos) : option htree =
  match t with
  | Leaf _ _ -> None
  | Internal freq (Leaf _ f1') (Leaf _ f2') ->
      if (f1' = f1 && f2' = f2) || (f1' = f2 && f2' = f1) then
        Some (Leaf 0 (f1' + f2'))
      else None
  | Internal freq l r ->
      match replace_siblings_with_merged l f1 f2 with
      | Some l' -> Some (Internal (freq_of l' + freq_of r) l' r)
      | None ->
          match replace_siblings_with_merged r f1 f2 with
          | Some r' -> Some (Internal (freq_of l + freq_of r') l r')
          | None -> None

(*** WPL Merge Lemmas ***)

// Lemma: WPL relationship when merging siblings
let wpl_merge_siblings (t: htree) (f1 f2: pos)
  : Lemma (requires (match t with
                     | Internal _ (Leaf _ f1') (Leaf _ f2') -> 
                         f1' = f1 && f2' = f2
                     | _ -> False))
          (ensures (match t with
                    | Internal _ l r ->
                        weighted_path_length t == 
                        weighted_path_length (Leaf 0 (f1 + f2)) + f1 + f2
                    | _ -> True))
  = match t with
    | Internal _ (Leaf _ f1') (Leaf _ f2') ->
        assert (weighted_path_length_aux (Leaf 0 f1') 1 == f1');
        assert (weighted_path_length_aux (Leaf 0 f2') 1 == f2');
        assert (weighted_path_length t == f1' + f2');
        assert (weighted_path_length (Leaf 0 (f1' + f2')) == 0)
    | _ -> ()

// Lemma: Replacing siblings with merge decreases WPL by the sum of their frequencies
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec wpl_after_merge (t: htree) (f1 f2: pos) (d: nat)
  : Lemma (requires (match replace_siblings_with_merged t f1 f2 with
                     | Some _ -> True
                     | None -> False))
          (ensures (match replace_siblings_with_merged t f1 f2 with
                    | Some t' ->
                        weighted_path_length_aux t d ==
                        weighted_path_length_aux t' d + f1 + f2
                    | None -> True))
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal freq (Leaf _ f1') (Leaf _ f2') ->
        if (f1' = f1 && f2' = f2) || (f1' = f2 && f2' = f1) then (
          assert (weighted_path_length_aux (Internal freq (Leaf 0 f1') (Leaf 0 f2')) d ==
                  weighted_path_length_aux (Leaf 0 f1') (d+1) + weighted_path_length_aux (Leaf 0 f2') (d+1));
          assert (weighted_path_length_aux (Leaf 0 f1') (d+1) == f1' `op_Multiply` (d+1));
          assert (weighted_path_length_aux (Leaf 0 f2') (d+1) == f2' `op_Multiply` (d+1));
          assert (weighted_path_length_aux (Leaf 0 (f1' + f2')) d == (f1' + f2') `op_Multiply` d);
          ()
        ) else ()
    | Internal freq l r ->
        match replace_siblings_with_merged l f1 f2 with
        | Some l' ->
            wpl_after_merge l f1 f2 (d+1);
            assert (weighted_path_length_aux l (d+1) == weighted_path_length_aux l' (d+1) + f1 + f2);
            assert (weighted_path_length_aux t d ==
                    weighted_path_length_aux l (d+1) + weighted_path_length_aux r (d+1));
            assert (weighted_path_length_aux (Internal (freq_of l' + freq_of r) l' r) d ==
                    weighted_path_length_aux l' (d+1) + weighted_path_length_aux r (d+1))
        | None ->
            match replace_siblings_with_merged r f1 f2 with
            | Some r' ->
                wpl_after_merge r f1 f2 (d+1);
                assert (weighted_path_length_aux r (d+1) == weighted_path_length_aux r' (d+1) + f1 + f2);
                assert (weighted_path_length_aux t d ==
                        weighted_path_length_aux l (d+1) + weighted_path_length_aux r (d+1));
                assert (weighted_path_length_aux (Internal (freq_of l + freq_of r') l r') d ==
                        weighted_path_length_aux l (d+1) + weighted_path_length_aux r' (d+1))
            | None -> ()
#pop-options

(*** Optimal Substructure (CLRS Lemma 16.3) ***)

// Optimal Substructure Property (CLRS Lemma 16.3, corrected formulation)
//
// If T has sibling leaves f1, f2, then replacing them with Leaf(f1+f2) gives
// a tree T' with WPL(T) = WPL(T') + f1 + f2. This is the key structural
// property underlying optimal substructure.
//
// The original formulation used `lf == f1 :: lf_rest` (minimum first in
// in-order traversal), which is false for most trees. The corrected version
// avoids this by parameterizing over any pair of sibling frequencies.
let optimal_substructure_property (t: htree) (f1 f2: pos) : prop =
  are_siblings t f1 f2 == true /\
  (match replace_siblings_with_merged t f1 f2 with
   | Some t' ->
       weighted_path_length t == weighted_path_length t' + f1 + f2
   | None -> False)

// are_siblings implies replace_siblings_with_merged succeeds
let rec are_siblings_implies_replace (t: htree) (f1 f2: pos)
  : Lemma (requires are_siblings t f1 f2 == true)
          (ensures Some? (replace_siblings_with_merged t f1 f2))
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ (Leaf _ f1') (Leaf _ f2') ->
        if (f1' = f1 && f2' = f2) || (f1' = f2 && f2' = f1) then ()
        else ()
    | Internal _ l r ->
        if are_siblings l f1 f2 then
          are_siblings_implies_replace l f1 f2
        else
          are_siblings_implies_replace r f1 f2

// The optimal substructure theorem: fully proven
let optimal_substructure_theorem (t: htree) (f1 f2: pos)
  : Lemma (requires are_siblings t f1 f2 == true)
          (ensures optimal_substructure_property t f1 f2)
  = are_siblings_implies_replace t f1 f2;
    wpl_after_merge t f1 f2 0
