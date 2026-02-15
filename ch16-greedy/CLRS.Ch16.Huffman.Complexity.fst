(*
   Huffman Encoding Algorithm with Complexity Bound

   CLRS §16.3: Huffman algorithm constructs an optimal prefix code.
   
   COMPLEXITY ANALYSIS:
   -------------------
   With a simple sorted list (linear scan for min extraction):
   - n-1 iterations (merge two minimum-frequency trees each time)
   - Each iteration:
     * Extract min twice: O(1) from sorted list head
     * Insert merged tree back: O(n) to maintain sorted order
   - Total: (n-1) × O(n) = O(n²)

   With a min-heap:
   - n-1 iterations
   - Each iteration:
     * Extract min twice: 2 × O(log n)
     * Insert merged tree: O(log n)
   - Total: (n-1) × 3 × O(log n) = O(n log n)

   This module proves the O(n²) bound for the sorted list implementation.
   
   TICK COUNTING:
   -------------
   We count "ticks" for key operations:
   - Each insertion into sorted list: counts comparisons (≤ n per insert)
   - Each iteration contributes at most n ticks
   - Total ticks for n symbols: ≤ (n-1) × n = n² - n
   
   NO admits in the core complexity bound proof.
*)

module CLRS.Ch16.Huffman.Complexity

open FStar.List.Tot
open FStar.Math.Lib
open FStar.Classical
open CLRS.Ch16.Huffman.Spec

(*** Tick Counting Versions of Core Operations ***)

// Count comparisons in insert_sorted
let rec insert_sorted_ticks (t: htree) (l: list htree)
  : Tot nat (decreases l)
  = match l with
    | [] -> 0  // No comparisons needed
    | hd :: tl ->
        if freq_of t <= freq_of hd then
          1  // One comparison, then insert at head
        else
          1 + insert_sorted_ticks t tl  // One comparison, recurse

// Lemma: insert_sorted_ticks is bounded by list length
let rec insert_sorted_ticks_bounded (t: htree) (l: list htree)
  : Lemma (ensures insert_sorted_ticks t l <= length l)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl -> insert_sorted_ticks_bounded t tl

// Build Huffman tree with tick counting
// Returns: (tree, total_ticks)
let rec huffman_with_ticks (l: list htree{Cons? l})
  : Tot (htree * nat) (decreases length l)
  = match l with
    | [t] -> 
        // Base case: single tree, no operations needed
        (t, 0)
    | t1 :: t2 :: rest ->
        // Merge the two minimum trees
        let merged = merge t1 t2 in
        
        // Insert back into sorted list (count ticks for insertion)
        let insert_cost = insert_sorted_ticks merged rest in
        insert_sorted_length merged rest;
        insert_sorted_nonempty merged rest;
        
        // Recurse on the new list
        let new_list = insert_sorted merged rest in
        let (result_tree, recursive_ticks) = huffman_with_ticks new_list in
        
        // Total cost: this insertion + recursive cost
        (result_tree, insert_cost + recursive_ticks)

// Extract just the tick count
let huffman_ticks (l: list htree{Cons? l}) : nat =
  let (_, ticks) = huffman_with_ticks l in
  ticks

(*** Complexity Bound Theorem ***)

// Lemma: After one iteration, list length decreases by 1
let huffman_length_decreases (t1 t2: htree) (rest: list htree)
  : Lemma (ensures (
      let new_list = insert_sorted (merge t1 t2) rest in
      length new_list == length rest + 1 /\
      length new_list == length (t1 :: t2 :: rest) - 1
    ))
  = insert_sorted_length (merge t1 t2) rest

// Helper: square function to avoid parsing issues with `*` in ensures clauses
let square (n: nat) : Tot nat = op_Multiply n n

// Key lemma: Prove ticks bounded by n²
let rec huffman_ticks_bounded (l: list htree{Cons? l})
  : Lemma (ensures huffman_ticks l <= square (length l))
          (decreases length l)
  = match l with
    | [t] -> 
        // Base case: n=1, ticks=0, bound = 1×1 = 1 ✓
        ()
    | t1 :: t2 :: rest ->
        // Inductive case
        let merged = merge t1 t2 in
        let new_list = insert_sorted merged rest in
        
        // Prove insert_cost ≤ length rest
        insert_sorted_ticks_bounded merged rest;
        
        // Apply inductive hypothesis to new_list
        insert_sorted_length merged rest;
        insert_sorted_nonempty merged rest;
        huffman_ticks_bounded new_list
        // The rest follows from induction and arithmetic

// Main complexity theorem: O(n²) bound
let huffman_complexity (l: list htree{Cons? l})
  : Lemma (ensures huffman_ticks l <= square (length l))
  = huffman_ticks_bounded l

// Simplified bound for readability: O(n²)
// This follows from huffman_complexity but requires forall instantiation
let huffman_complexity_simple (n: nat{n >= 1})
  : Lemma (ensures (
      forall (l: list htree). 
        Cons? l /\ length l == n ==>
        huffman_ticks l <= square n
    ))
  = introduce forall (l: list htree). Cons? l /\ length l == n ==> huffman_ticks l <= square n
    with (
      introduce _ ==> _
      with _. huffman_complexity l
    )

(*** Example: Verify on concrete input ***)

// Example from CLRS Figure 16.3: frequencies [5; 9; 12; 13; 16; 45]
let example_trees : list htree = 
  [Leaf 5; Leaf 9; Leaf 12; Leaf 13; Leaf 16; Leaf 45]

// Verify it's already sorted by frequency
let example_sorted : squash (
  freq_of (Leaf 5) <= freq_of (Leaf 9) /\
  freq_of (Leaf 9) <= freq_of (Leaf 12) /\
  freq_of (Leaf 12) <= freq_of (Leaf 13) /\
  freq_of (Leaf 13) <= freq_of (Leaf 16) /\
  freq_of (Leaf 16) <= freq_of (Leaf 45)
) = ()

// Compute the tick count for this example
let example_ticks : nat = huffman_ticks example_trees

// Verify the bound holds
let example_complexity_check : squash (example_ticks <= 36) =
  huffman_complexity example_trees;
  // n = 6, so n² = 36
  ()

(*** Connection to Original Algorithm ***)

// The trees built are the same (only ticks added)
let rec huffman_with_ticks_correct (l: list htree{Cons? l})
  : Lemma (ensures (
      let (tree_with_ticks, _) = huffman_with_ticks l in
      let tree_without_ticks = huffman_from_sorted l in
      tree_with_ticks == tree_without_ticks
    ))
    (decreases length l)
  = match l with
    | [t] -> ()
    | t1 :: t2 :: rest ->
        let merged = merge t1 t2 in
        let new_list = insert_sorted merged rest in
        insert_sorted_length merged rest;
        insert_sorted_nonempty merged rest;
        huffman_with_ticks_correct new_list

(*** Summary ***)

(*
   This module proves the O(n²) time complexity of Huffman encoding
   with a sorted list implementation:
   
   KEY RESULTS:
   -----------
   1. huffman_with_ticks: Instrumented version that counts operations
   2. huffman_ticks_bounded: Proves ticks ≤ n²
   3. huffman_complexity: Main theorem proving O(n²) complexity
   4. huffman_with_ticks_correct: Equivalence to original algorithm
   
   COMPLEXITY BREAKDOWN:
   --------------------
   - n-1 iterations (each merges two trees)
   - Each iteration: insert_sorted does ≤ (current_list_length) comparisons
   - Iteration i processes list of length (n-i+1), does ≤ (n-i) comparisons
   - Total: Σ(i=1 to n-1) (n-i) = (n-1) + (n-2) + ... + 1 = (n-1)×n/2
   - Upper bound: (n-1)×n, which is O(n²)
   
   With a min-heap, each iteration would be O(log n), giving O(n log n).
   But this implementation uses sorted list for simplicity.
   
   NO admits in complexity proofs.
   
   To verify:
   cd /home/nswamy/workspace/everest/AutoCLRS
   fstar.exe --include $(realpath ../pulse)/out/lib/pulse \
             --include common \
             --include ch16-greedy \
             ch16-greedy/CLRS.Ch16.Huffman.Complexity.fst
*)
