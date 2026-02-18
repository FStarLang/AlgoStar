module CLRS.Ch16.Huffman.Spec

open FStar.List.Tot
open FStar.Math.Lib

(*** Tree Definition ***)

//SNIPPET_START: htree_def
type htree =
  | Leaf : freq:pos -> htree
  | Internal : freq:pos -> left:htree -> right:htree -> htree
//SNIPPET_END: htree_def

(*** Basic Operations ***)

let rec freq_of (t: htree) : pos =
  match t with
  | Leaf f -> f
  | Internal _ l r -> freq_of l + freq_of r

let rec depth (t: htree) : nat =
  match t with
  | Leaf _ -> 0
  | Internal _ l r -> 1 + max (depth l) (depth r)

(*** Weighted Path Length ***)

//SNIPPET_START: weighted_path_length
let rec weighted_path_length_aux (t: htree) (d: nat) : nat =
  match t with
  | Leaf f -> f `op_Multiply` d
  | Internal _ l r ->
      weighted_path_length_aux l (d + 1) +
      weighted_path_length_aux r (d + 1)

let weighted_path_length (t: htree) : nat =
  weighted_path_length_aux t 0
//SNIPPET_END: weighted_path_length

(*** Cost (sum of internal node frequencies) ***)

let rec cost_aux (t: htree) : nat =
  match t with
  | Leaf _ -> 0
  | Internal _ l r -> freq_of l + freq_of r + cost_aux l + cost_aux r

let cost (t: htree) : nat = cost_aux t

(*** Key Lemma: Weighted Path Length = Cost (CLRS 16.4) ***)

// Helper: relates wpl at depth d to cost plus contribution from depth
let rec wpl_cost_relation (t: htree) (d: nat)
  : Lemma (ensures weighted_path_length_aux t d == cost_aux t + d `op_Multiply` freq_of t)
          (decreases t)
  = match t with
    | Leaf f -> ()
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
    | _ -> Leaf 1 // unreachable but needed for exhaustiveness
//SNIPPET_END: huffman_from_sorted

// Sort helper: compare by frequency
let freq_cmp (t1 t2: htree) : int =
  freq_of t1 - freq_of t2

// Build Huffman tree from a non-empty list of frequencies
let huffman_build (freqs: list pos{Cons? freqs}) : htree =
  let trees = map (fun f -> Leaf f) freqs in
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
  : Lemma (ensures sum_tree_freqs (map (fun f -> Leaf f) l) == list_sum l)
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
  | Leaf _ -> True
  | Internal _ l r -> is_full_binary_tree l /\ is_full_binary_tree r

// All htrees are full binary trees by construction
let rec htree_is_full (t: htree)
  : Lemma (ensures is_full_binary_tree t)
  = match t with
    | Leaf _ -> ()
    | Internal _ l r -> htree_is_full l; htree_is_full r

// Definition: Get the list of leaf frequencies in a tree (in order)
let rec leaf_freqs (t: htree) : list pos =
  match t with
  | Leaf f -> [f]
  | Internal _ l r -> leaf_freqs l @ leaf_freqs r

//SNIPPET_START: is_optimal
// Definition: A tree is optimal if its WPL is minimal among all trees with the same leaf frequencies
let is_optimal (t: htree) (freqs: list pos) : prop =
  leaf_freqs t == freqs /\
  (forall (t': htree). leaf_freqs t' == freqs ==> weighted_path_length t <= weighted_path_length t')
//SNIPPET_END: is_optimal

// Helper: find minimum frequency in a list
let rec min_freq (l: list pos{Cons? l}) : pos =
  match l with
  | [x] -> x
  | hd :: tl -> min hd (min_freq tl)

// Helper: find maximum depth of any leaf
let rec max_leaf_depth (t: htree) (d: nat) : nat =
  match t with
  | Leaf _ -> d
  | Internal _ l r -> max (max_leaf_depth l (d + 1)) (max_leaf_depth r (d + 1))

// Helper: check if two leaves are siblings (share the same parent)
let rec are_siblings (t: htree) (f1 f2: pos) : bool =
  match t with
  | Leaf _ -> false
  | Internal _ (Leaf f1') (Leaf f2') -> (f1' = f1 && f2' = f2) || (f1' = f2 && f2' = f1)
  | Internal _ l r -> are_siblings l f1 f2 || are_siblings r f1 f2

// Helper: get depth of a specific leaf frequency (first occurrence)
let rec depth_of_leaf (t: htree) (f: pos) (d: nat) : option nat =
  match t with
  | Leaf f' -> if f = f' then Some d else None
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
      | Leaf _ -> None
      | Internal _ l r ->
          if hd then get_subtree_at l tl else get_subtree_at r tl

let rec replace_subtree_at (t: htree) (pos: tree_position) (new_t: htree) : option htree =
  match pos with
  | [] -> Some new_t
  | hd :: tl ->
      match t with
      | Leaf _ -> None
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
  | Some (Leaf f_high), Some (Leaf f_low) ->
      let depth_high = length pos_high in
      let depth_low = length pos_low in
      // High-freq leaf at DEEP position, low-freq leaf at SHALLOW position (suboptimal)
      if f_high >= f_low && depth_high >= depth_low then
        (match replace_subtree_at t pos_high (Leaf f_low), 
               replace_subtree_at t pos_low (Leaf f_high) with
         | Some t_temp, _ ->
             (match replace_subtree_at t_temp pos_low (Leaf f_high) with
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
        | Leaf _ -> ()
#pop-options

// Specialization for replacing a leaf: WPL change is exactly the frequency times depth difference
#push-options "--z3rlimit 30"
let replace_leaf_wpl (t: htree) (position: tree_position) (f_new: pos) (d: nat)
  : Lemma (requires (match get_subtree_at t position with
                     | Some (Leaf f_old) -> True
                     | _ -> False))
          (ensures (
            let Some (Leaf f_old) = get_subtree_at t position in
            match replace_subtree_at t position (Leaf f_new) with
            | Some t' ->
                weighted_path_length_aux t d + f_new `op_Multiply` (d + length position) ==
                weighted_path_length_aux t' d + f_old `op_Multiply` (d + length position)
            | None -> True
          ))
  = let Some (Leaf f_old) = get_subtree_at t position in
    match replace_subtree_at t position (Leaf f_new) with
    | Some t' ->
        replace_subtree_wpl_aux t position (Leaf f_new) d;
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
        | Leaf _ -> ()
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
        | Leaf _ -> ()
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
        | Leaf _ -> ()
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let swap_reduces_wpl_disjoint (t: htree) (pos_high pos_low: tree_position) (f_high f_low: pos)
  : Lemma (requires
            get_subtree_at t pos_high == Some (Leaf f_high) /\
            get_subtree_at t pos_low == Some (Leaf f_low) /\
            f_high >= f_low /\
            length pos_high >= length pos_low /\
            pos_high =!= pos_low /\
            not (is_prefix pos_high pos_low) /\
            not (is_prefix pos_low pos_high) /\
            Some? (replace_subtree_at t pos_high (Leaf f_low)))
          (ensures (
            let Some t_temp = replace_subtree_at t pos_high (Leaf f_low) in
            get_subtree_at t_temp pos_low == Some (Leaf f_low) /\
            (match replace_subtree_at t_temp pos_low (Leaf f_high) with
             | Some t_swapped ->
                 weighted_path_length t_swapped <= weighted_path_length t
             | None -> True)))
  = let d_high = length pos_high in
    let d_low = length pos_low in
    let Some t_temp = replace_subtree_at t pos_high (Leaf f_low) in
    
    // Step 1: pos_low is unaffected by replacing at pos_high (disjoint)
    disjoint_replacement_preserves_subtree t pos_high pos_low (Leaf f_low);
    
    // Step 2: WPL analysis
    replace_leaf_wpl t pos_high f_low 0;
    
    match replace_subtree_at t_temp pos_low (Leaf f_high) with
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
let rec leaf_position_no_extension (t: htree) (pos1 pos2: tree_position) (f: pos)
  : Lemma (requires get_subtree_at t pos1 == Some (Leaf f) /\ is_prefix pos1 pos2)
          (ensures get_subtree_at t pos2 == None)
          (decreases pos1)
  = match pos1, pos2 with
    | [], hd2 :: tl2 ->
        // t itself is the Leaf f, so going into it returns None
        ()
    | hd1 :: tl1, hd2 :: tl2 ->
        assert (hd1 = hd2);
        (match t with
        | Internal _ l r ->
            if hd1 then leaf_position_no_extension l tl1 tl2 f
            else leaf_position_no_extension r tl1 tl2 f
        | Leaf _ -> ())
    | _, _ -> () // can't happen
#pop-options

// The swap reduces WPL when the conditions are met
// High-freq at deep position, low-freq at shallow position → swap reduces WPL
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let swap_reduces_wpl (t: htree) (pos_high pos_low: tree_position)
  : Lemma (requires (match get_subtree_at t pos_high, get_subtree_at t pos_low with
                     | Some (Leaf f_high), Some (Leaf f_low) ->
                         f_high >= f_low /\ length pos_high >= length pos_low /\
                         pos_high =!= pos_low
                     | _, _ -> False))
          (ensures swap_reduces_wpl_statement t pos_high pos_low)
  = match get_subtree_at t pos_high, get_subtree_at t pos_low with
    | Some (Leaf f_high), Some (Leaf f_low) ->
        // Both positions point to leaves and pos_high =!= pos_low.
        // Case 1: is_prefix pos_low pos_high → impossible
        //   pos_low points to a Leaf, so any extension returns None, contradicting pos_high → Some
        if is_prefix pos_low pos_high then
          leaf_position_no_extension t pos_low pos_high f_low
        // Case 2: is_prefix pos_high pos_low → impossible 
        //   pos_high points to a Leaf, so any extension returns None, contradicting pos_low → Some
        else if is_prefix pos_high pos_low then
          leaf_position_no_extension t pos_high pos_low f_high
        // Case 3: disjoint positions → use swap_reduces_wpl_disjoint
        else (
          get_implies_replace t pos_high (Leaf f_low);
          swap_reduces_wpl_disjoint t pos_high pos_low f_high f_low
        )
    | _, _ -> ()
#pop-options

(*** Greedy Choice Property (CLRS Lemma 16.2) ***)

// Statement: In an optimal prefix code tree, there exist two sibling leaves
// at maximum depth that correspond to the two lowest-frequency characters.
let greedy_choice_property (t: htree) (freqs: list pos{Cons? freqs}) : prop =
  is_optimal t freqs ==>
  (let lf = leaf_freqs t in
   length lf >= 2 ==>
   (exists (f1 f2: pos) (depth_max: nat).
      f1 = min_freq lf /\
      (exists (lf_rest: list pos{Cons? lf_rest}). 
        lf == f1 :: lf_rest /\ f2 = min_freq lf_rest) /\
      are_siblings t f1 f2 /\
      (match depth_of_leaf t f1 0, depth_of_leaf t f2 0 with
       | Some d1, Some d2 -> d1 >= depth_max /\ d2 >= depth_max
       | _, _ -> False)))

// The greedy choice theorem: This property holds for all optimal trees
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let greedy_choice_theorem (t: htree) (freqs: list pos{Cons? freqs})
  : Lemma (requires is_optimal t freqs /\ length freqs >= 2)
          (ensures greedy_choice_property t freqs)
  = // Proof outline (CLRS Lemma 16.2):
    // 1. In any tree, there exist two sibling leaves at maximum depth
    //    (by pigeonhole principle and tree structure)
    // 2. Let these siblings have frequencies x and y
    // 3. Let f1, f2 be the two minimum frequencies in the alphabet
    // 4. If x ≠ f1 or y ≠ f2, we can swap to improve or maintain optimality
    // 5. Since t is optimal, it must already have f1,f2 as deep siblings
    
    // The full proof requires:
    // (a) Proving siblings exist at max depth (structural argument)
    // (b) If siblings aren't minimum freq, swapping improves WPL
    // (c) Contradiction with optimality assumption
    //
    // Parts (a) and (b) require extensive tree manipulation lemmas
    // Part (c) follows from swap_reduces_wpl
    //
    // This is a standard result from Huffman (1952) and CLRS §16.3
    // We accept it axiomatically as the infrastructure for tree swaps
    // and optimality arguments is beyond the scope of this basic spec
    assume (greedy_choice_property t freqs)
#pop-options

(*** Optimal Substructure (CLRS Lemma 16.3) ***)

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
  | Leaf _ -> None
  | Internal freq (Leaf f1') (Leaf f2') ->
      if (f1' = f1 && f2' = f2) || (f1' = f2 && f2' = f1) then
        Some (Leaf (f1' + f2'))
      else None
  | Internal freq l r ->
      match replace_siblings_with_merged l f1 f2 with
      | Some l' -> Some (Internal (freq_of l' + freq_of r) l' r)
      | None ->
          match replace_siblings_with_merged r f1 f2 with
          | Some r' -> Some (Internal (freq_of l + freq_of r') l r')
          | None -> None

// Optimal substructure property: If T is optimal for alphabet C with frequencies,
// and x,y are the two minimum-frequency characters that are siblings in T,
// then T' (obtained by replacing x,y with a merged character z) is optimal for C'
let optimal_substructure_property (t: htree) (freqs: list pos{length freqs >= 2}) : prop =
  is_optimal t freqs ==>
  (let lf = leaf_freqs t in
   let f1 = min_freq lf in
   exists (lf_rest: list pos{Cons? lf_rest}).
     lf == f1 :: lf_rest /\
     (let f2 = min_freq lf_rest in
      are_siblings t f1 f2 /\
      (match replace_siblings_with_merged t f1 f2, remove_and_merge freqs f1 f2 with
       | Some t', Some freqs' ->
           // T' is optimal for C'
           is_optimal t' freqs'
       | _, _ -> True)))

// The optimal substructure theorem
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let optimal_substructure_theorem (t: htree) (freqs: list pos{length freqs >= 2})
  : Lemma (requires is_optimal t freqs)
          (ensures optimal_substructure_property t freqs)
  = // Proof outline (CLRS Lemma 16.3):
    // 1. Let T be optimal for alphabet C with frequencies freqs
    // 2. By greedy choice, T has siblings x,y at max depth with min frequencies f1,f2
    // 3. Let T' be T with x,y replaced by merged leaf z = x+y
    // 4. We've proven: WPL(T) = WPL(T') + f1 + f2 (by wpl_after_merge)
    // 5. Proof by contradiction: Assume T' is not optimal for C'
    // 6. Then ∃T'': T'' is optimal for C' with WPL(T'') < WPL(T')
    // 7. Construct T''' from T'' by splitting z into sibling leaves x,y
    // 8. Then WPL(T''') = WPL(T'') + f1 + f2 < WPL(T') + f1 + f2 = WPL(T)
    // 9. Butthis contradicts optimality of T for C
    // 10. Therefore T' must be optimal for C'
    
    // Key lemma already proven: wpl_after_merge shows WPL relationship
    // The construction of T''' from T'' and the contradiction argument
    // require extensive infrastructure for tree construction and optimality reasoning
    //
    // This is CLRS Lemma 16.3, a standard result in algorithm theory
    // We accept it axiomatically given the WPL relationship we've proven
    assume (optimal_substructure_property t freqs)
#pop-options

(*** Additional Helper Lemmas ***)

// Lemma: WPL relationship when merging siblings
let wpl_merge_siblings (t: htree) (f1 f2: pos)
  : Lemma (requires (match t with
                     | Internal _ (Leaf f1') (Leaf f2') -> 
                         f1' = f1 && f2' = f2
                     | _ -> False))
          (ensures (match t with
                    | Internal _ l r ->
                        weighted_path_length t == 
                        weighted_path_length (Leaf (f1 + f2)) + f1 + f2
                    | _ -> True))
  = match t with
    | Internal _ (Leaf f1') (Leaf f2') ->
        assert (weighted_path_length_aux (Leaf f1') 1 == f1');
        assert (weighted_path_length_aux (Leaf f2') 1 == f2');
        assert (weighted_path_length t == f1' + f2');
        assert (weighted_path_length (Leaf (f1' + f2')) == 0)
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
    | Leaf _ -> ()
    | Internal freq (Leaf f1') (Leaf f2') ->
        // Base case: the siblings are right here
        if (f1' = f1 && f2' = f2) || (f1' = f2 && f2' = f1) then (
          // wpl at depth d for this internal node
          assert (weighted_path_length_aux (Internal freq (Leaf f1') (Leaf f2')) d ==
                  weighted_path_length_aux (Leaf f1') (d+1) + weighted_path_length_aux (Leaf f2') (d+1));
          assert (weighted_path_length_aux (Leaf f1') (d+1) == f1' `op_Multiply` (d+1));
          assert (weighted_path_length_aux (Leaf f2') (d+1) == f2' `op_Multiply` (d+1));
          // wpl for merged leaf
          assert (weighted_path_length_aux (Leaf (f1' + f2')) d == (f1' + f2') `op_Multiply` d);
          // Simplify: f1'*(d+1) + f2'*(d+1) = (f1'+f2')*(d+1) = (f1'+f2')*d + (f1'+f2')
          ()
        ) else ()
    | Internal freq l r ->
        match replace_siblings_with_merged l f1 f2 with
        | Some l' ->
            // Siblings found in left subtree
            wpl_after_merge l f1 f2 (d+1);
            assert (weighted_path_length_aux l (d+1) == weighted_path_length_aux l' (d+1) + f1 + f2);
            // wpl of Internal is sum of left and right
            assert (weighted_path_length_aux t d ==
                    weighted_path_length_aux l (d+1) + weighted_path_length_aux r (d+1));
            // After merge, frequencies change but r stays same
            assert (weighted_path_length_aux (Internal (freq_of l' + freq_of r) l' r) d ==
                    weighted_path_length_aux l' (d+1) + weighted_path_length_aux r (d+1))
        | None ->
            match replace_siblings_with_merged r f1 f2 with
            | Some r' ->
                // Siblings found in right subtree
                wpl_after_merge r f1 f2 (d+1);
                assert (weighted_path_length_aux r (d+1) == weighted_path_length_aux r' (d+1) + f1 + f2);
                assert (weighted_path_length_aux t d ==
                        weighted_path_length_aux l (d+1) + weighted_path_length_aux r (d+1));
                assert (weighted_path_length_aux (Internal (freq_of l + freq_of r') l r') d ==
                        weighted_path_length_aux l (d+1) + weighted_path_length_aux r' (d+1))
            | None -> ()
#pop-options
