module CLRS.Ch16.Huffman.Spec

open FStar.List.Tot
open FStar.Math.Lib

(*** Tree Definition ***)

type htree =
  | Leaf : freq:pos -> htree
  | Internal : freq:pos -> left:htree -> right:htree -> htree

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

let rec weighted_path_length_aux (t: htree) (d: nat) : nat =
  match t with
  | Leaf f -> f `op_Multiply` d
  | Internal _ l r ->
      weighted_path_length_aux l (d + 1) +
      weighted_path_length_aux r (d + 1)

let weighted_path_length (t: htree) : nat =
  weighted_path_length_aux t 0

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

// Main theorem: at depth 0, weighted_path_length equals cost
let wpl_equals_cost (t: htree)
  : Lemma (ensures weighted_path_length t == cost t)
  = wpl_cost_relation t 0

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

// Definition: A tree is optimal if its WPL is minimal among all trees with the same leaf frequencies
let is_optimal (t: htree) (freqs: list pos) : prop =
  leaf_freqs t == freqs /\
  (forall (t': htree). leaf_freqs t' == freqs ==> weighted_path_length t <= weighted_path_length t')

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

// Swap lemma: Swapping a high-frequency leaf at shallow depth with a low-frequency leaf
// at greater depth decreases or maintains WPL
let swap_reduces_wpl_statement (t: htree) (pos_high pos_low: tree_position) : prop =
  match get_subtree_at t pos_high, get_subtree_at t pos_low with
  | Some (Leaf f_high), Some (Leaf f_low) ->
      let depth_high = length pos_high in
      let depth_low = length pos_low in
      if f_high > f_low && depth_high < depth_low then
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

// The swap reduces WPL when the conditions are met
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let swap_reduces_wpl (t: htree) (pos_high pos_low: tree_position)
  : Lemma (requires (match get_subtree_at t pos_high, get_subtree_at t pos_low with
                     | Some (Leaf f_high), Some (Leaf f_low) ->
                         f_high > f_low /\ length pos_high < length pos_low /\
                         pos_high =!= pos_low
                     | _, _ -> False))
          (ensures swap_reduces_wpl_statement t pos_high pos_low)
  = admit() // Proof requires detailed case analysis on tree structure
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
let greedy_choice_theorem (t: htree) (freqs: list pos{Cons? freqs})
  : Lemma (requires is_optimal t freqs /\ length freqs >= 2)
          (ensures greedy_choice_property t freqs)
  = admit() // Full proof requires:
            // 1. Show that in any optimal tree, there exist siblings at max depth
            // 2. If these siblings don't have minimum frequencies, swap them with min freq leaves
            // 3. Use swap_reduces_wpl to show the swap doesn't increase WPL
            // 4. Conclude that the original must have had min freq leaves as deep siblings

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
  = admit() // Full proof requires:
            // 1. Let T be optimal for C, with x,y as siblings with min frequencies
            // 2. Let T' be T with x,y replaced by merged leaf z
            // 3. Show WPL(T) = WPL(T') + freq(x) + freq(y) (by wpl_cost_relation)
            // 4. Assume T' is not optimal, so there exists T'' with WPL(T'') < WPL(T')
            // 5. Construct T''' from T'' by splitting z back into x,y
            // 6. Show WPL(T''') < WPL(T), contradicting optimality of T
            // 7. Conclude T' must be optimal
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
  = admit() // Proof by structural induction on t
#pop-options
