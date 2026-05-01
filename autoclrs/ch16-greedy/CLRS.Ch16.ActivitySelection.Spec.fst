(*
   Activity Selection - Full Optimality Proof
   
   This module proves that the greedy activity selection algorithm produces
   an optimal solution using:
   
   1. Greedy Choice Property (CLRS Theorem 16.1):
      The earliest-finishing activity is always part of some optimal solution.
      Proof: exchange argument - replace first activity in any optimal solution.
   
   2. Optimal Substructure:
      After selecting the earliest-finishing activity, the remaining problem
      (activities compatible with it) has optimal substructure.
   
   3. Main Optimality Theorem:
      The greedy algorithm produces a selection of maximum cardinality.
*)

module CLRS.Ch16.ActivitySelection.Spec

open FStar.List.Tot
open FStar.Classical

module L = FStar.List.Tot
module Seq = FStar.Seq
module AL = CLRS.Ch16.ActivitySelection.Lemmas

// ========== Basic Definitions ==========

//SNIPPET_START: activity_defs
(* Activities are sorted by finish time *)
let finish_sorted (f: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\ j < Seq.length f ==> Seq.index f i <= Seq.index f j

(* Valid activity: start <= finish *)
// CLRS assumes s_i < f_i (strict inequality, positive-duration activities)
let valid_activity (s: Seq.seq int) (f: Seq.seq int) (i: nat) : prop =
  i < Seq.length s /\ i < Seq.length f /\ Seq.index s i < Seq.index f i

// ========== Compatibility Definitions ==========

(* Two activities i and j are compatible if they don't overlap *)
let compatible (start: Seq.seq int) (finish: Seq.seq int) (i j: nat) : prop =
  i < Seq.length start /\ i < Seq.length finish /\
  j < Seq.length start /\ j < Seq.length finish /\
  (Seq.index finish i <= Seq.index start j \/ Seq.index finish j <= Seq.index start i)

(* A list of activities is mutually compatible *)
let rec mutually_compatible (start: Seq.seq int) (finish: Seq.seq int) (selected: list nat) : prop =
  match selected with
  | [] -> True
  | [x] -> x < Seq.length start /\ x < Seq.length finish
  | x :: xs ->
      x < Seq.length start /\ x < Seq.length finish /\
      mutually_compatible start finish xs /\
      (forall (y: nat). L.mem y xs ==> compatible start finish x y)
//SNIPPET_END: activity_defs

(* Sequential compatibility: for a sorted list, only check consecutive pairs *)
let rec sequentially_compatible (start: Seq.seq int) (finish: Seq.seq int) (selected: list nat) : prop =
  match selected with
  | [] -> True
  | [x] -> x < Seq.length start /\ x < Seq.length finish
  | x :: y :: rest ->
      x < Seq.length start /\ x < Seq.length finish /\
      y < Seq.length start /\ y < Seq.length finish /\
      Seq.index finish x <= Seq.index start y /\
      sequentially_compatible start finish (y :: rest)

(* All elements in the list are valid indices and sorted *)
let rec list_sorted_indices (selected: list nat) (n: nat) : prop =
  match selected with
  | [] -> True
  | [x] -> x < n
  | x :: y :: rest -> x < y /\ y < n /\ list_sorted_indices (y :: rest) n

// ========== Key Lemma: Sequential implies Mutual Compatibility ==========

// Helper: if finish[x] <= start[y] and start[y] <= finish[y] and finish[y] <= start[z], 
// then finish[x] <= start[z]
let lemma_transitivity_compat (x y z: nat) (start finish: Seq.seq int) 
  : Lemma 
    (requires 
      x < Seq.length start /\ x < Seq.length finish /\
      y < Seq.length start /\ y < Seq.length finish /\
      z < Seq.length start /\ z < Seq.length finish /\
      Seq.index finish x <= Seq.index start y /\
      Seq.index start y <= Seq.index finish y /\
      Seq.index finish y <= Seq.index start z)
    (ensures 
      Seq.index finish x <= Seq.index start z)
  = ()

// Helper: in a sorted list y::rest, y < all elements in rest
let rec lemma_head_less_than_rest (lst: list nat) (y: nat) (z: nat) (n: nat)
  : Lemma 
    (requires list_sorted_indices (y :: lst) n /\ L.mem z lst)
    (ensures y < z)
    (decreases lst)
  = match lst with
    | [] -> ()
    | hd :: tl ->
        if z = hd then ()
        else lemma_head_less_than_rest tl hd z n

// Helper: any member of a sorted index list is < n
let rec lemma_mem_sorted_bound (lst: list nat) (z: nat) (n: nat)
  : Lemma
    (requires list_sorted_indices lst n /\ L.mem z lst)
    (ensures z < n)
    (decreases lst)
  = match lst with
    | [x] -> ()
    | x :: y :: rest ->
        if z = x then
          lemma_head_less_than_rest (y :: rest) x y n
        else
          lemma_mem_sorted_bound (y :: rest) z n

// Helper: a list with sorted indices starting >= lo and < n has length <= n - lo
let rec lemma_sorted_indices_length_aux (lst: list nat) (n: nat) (lo: nat)
  : Lemma
    (requires list_sorted_indices lst n /\ 
             lo <= n /\
             (match lst with [] -> True | x :: _ -> x >= lo))
    (ensures L.length lst <= n - lo)
    (decreases lst)
  = match lst with
    | [] -> ()
    | [x] -> 
        // x >= lo and x < n (from list_sorted_indices [x] n)
        assert (x >= lo /\ x < n);
        assert (n - lo >= 1)
    | x :: y :: rest ->
        // x >= lo, x < y, so y >= x + 1 >= lo + 1
        assert (x >= lo);
        assert (x < y);
        assert (y >= lo + 1);
        lemma_sorted_indices_length_aux (y :: rest) n (lo + 1)
        // IH gives: L.length (y :: rest) <= n - (lo + 1) = n - lo - 1
        // So L.length (x :: y :: rest) = 1 + L.length (y :: rest) <= 1 + n - lo - 1 = n - lo

// Helper: a list with sorted indices in [0,n) has length <= n
let lemma_sorted_indices_length (lst: list nat) (n: nat)
  : Lemma
    (requires list_sorted_indices lst n)
    (ensures L.length lst <= n)
  = match lst with
    | [] -> ()
    | _ -> lemma_sorted_indices_length_aux lst n 0

// Helper: extract the ordering from compatibility in a sorted list
// With finish_sorted and strict valid_activity, compatible i j with i < j
// implies finish[i] <= start[j] (the "natural" direction).
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec lemma_compat_order (start finish: Seq.seq int) (lst: list nat) (i j: nat)
  : Lemma 
    (requires 
      finish_sorted finish /\
      (forall (k:nat). k < Seq.length start ==> valid_activity start finish k) /\
      Seq.length start == Seq.length finish /\
      list_sorted_indices lst (Seq.length start) /\
      mutually_compatible start finish lst /\
      L.mem i lst /\ L.mem j lst /\ i < j)
    (ensures Seq.index finish i <= Seq.index start j)
    (decreases lst)
  = // We need to extract compatible i j from mutually_compatible.
    // By definition, mutually_compatible (x :: xs) says:
    //   forall y in xs. compatible x y
    //   mutually_compatible xs
    // So if i = x, then compatible i j follows from j in xs.
    // Otherwise, both i and j are in xs, and we recurse.
    match lst with
    | x :: xs ->
        if i = x then begin
          // i is the head, j is in the tail xs
          // Since i < j and i = x, and L.mem j (x :: xs), j must be in xs
          assert (L.mem j xs);
          // From mutually_compatible: forall y in xs. compatible x y
          // Instantiate with y = j
          assert (compatible start finish x j);
          // Equivalently: compatible i j
          ()
        end
        else begin
          // i is not the head, so i is in xs
          assert (L.mem i xs);
          // Need to show j <> x, and thus L.mem j xs
          // From list_sorted_indices: x is strictly less than all elements of xs
          // Since L.mem i xs, x < i (by lemma_head_less_than_rest or directly from sorted structure)
          begin match xs with
          | [] -> () // impossible since L.mem i xs  
          | y :: rest' -> 
            // From list_sorted_indices (x :: y :: rest'), x < y
            // All elements in y :: rest' are >= y > x
            // Since L.mem i (y :: rest'), i >= y > x. So x < i < j.
            // If j = x, then j < i, contradicting i < j.
            lemma_head_less_than_rest xs x i (Seq.length start);
            assert (x < i);
            // Now x < i < j, so j <> x
            assert (j <> x);
            assert (L.mem j xs);
            assert (mutually_compatible start finish xs);
            assert (list_sorted_indices xs (Seq.length start));
            lemma_compat_order start finish xs i j
          end
        end
#pop-options

// Helper: in a sequentially compatible sorted list, finish[i] <= start[j] for i before j
// This doesn't need finish_sorted because sequential compatibility already gives direction.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec lemma_seq_compat_finish_le_start
  (start finish: Seq.seq int) (selected: list nat) (i j: nat)
  : Lemma
    (requires
      sequentially_compatible start finish selected /\
      list_sorted_indices selected (Seq.length start) /\
      Seq.length start == Seq.length finish /\
      (forall (k:nat). k < Seq.length start ==> Seq.index start k < Seq.index finish k) /\
      L.mem i selected /\ L.mem j selected /\ i < j /\
      i < Seq.length start /\ j < Seq.length start)
    (ensures Seq.index finish i <= Seq.index start j)
    (decreases selected)
  = match selected with
    | x :: y :: rest ->
        if i = x && j = y then ()
        else if i = x then begin
          lemma_head_less_than_rest rest y j (Seq.length start);
          lemma_mem_sorted_bound (y :: rest) y (Seq.length start);
          lemma_mem_sorted_bound (y :: rest) j (Seq.length start);
          lemma_seq_compat_finish_le_start start finish (y :: rest) y j
        end
        else begin
          if i = y then begin
            lemma_mem_sorted_bound (y :: rest) i (Seq.length start);
            lemma_mem_sorted_bound (y :: rest) j (Seq.length start);
            lemma_seq_compat_finish_le_start start finish (y :: rest) i j
          end
          else begin
            lemma_head_less_than_rest (y :: rest) x i (Seq.length start);
            lemma_mem_sorted_bound (y :: rest) i (Seq.length start);
            lemma_mem_sorted_bound (y :: rest) j (Seq.length start);
            lemma_seq_compat_finish_le_start start finish (y :: rest) i j
          end
        end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let rec lemma_sequential_implies_mutual 
  (start: Seq.seq int) (finish: Seq.seq int) (selected: list nat)
  : Lemma 
    (requires 
      sequentially_compatible start finish selected /\
      list_sorted_indices selected (Seq.length start) /\
      Seq.length start == Seq.length finish /\
      (forall (i:nat). i < Seq.length start ==> Seq.index start i < Seq.index finish i))
    (ensures mutually_compatible start finish selected)
    (decreases selected)
  = match selected with
  | [] -> ()
  | [x] -> ()
  | x :: y :: rest ->
      lemma_sequential_implies_mutual start finish (y :: rest);
      let lemma_x_compat_all (z: nat) 
        : Lemma (requires L.mem z (y :: rest)) (ensures compatible start finish x z)
        = if z = y then ()
          else begin
            assert (L.mem z rest);
            lemma_head_less_than_rest rest y z (Seq.length start);
            assert (y < z);
            assert (x < z);
            lemma_mem_sorted_bound (x :: y :: rest) x (Seq.length start);
            lemma_mem_sorted_bound (x :: y :: rest) z (Seq.length start);
            lemma_seq_compat_finish_le_start start finish (x :: y :: rest) x z
          end
      in
      Classical.forall_intro (Classical.move_requires lemma_x_compat_all);
      ()
#pop-options

// ========== Maximum Compatible Count ==========

(* Find the largest k in [0..limit] such that a compatible set of size k exists *)
let rec find_max_compatible (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (k: nat)
  : GTot nat (decreases k) =
  if k = 0 then 0
  else
    if FStar.IndefiniteDescription.strong_excluded_middle
         (exists (sel: list nat). L.length sel = k /\
                                 mutually_compatible start finish sel /\
                                 list_sorted_indices sel n)
    then k
    else find_max_compatible start finish n (k - 1)

(* Maximum size of any mutually compatible subset *)
(* This is a ghost specification-level definition *)
[@@"opaque_to_smt"]
let max_compatible_count (start: Seq.seq int) (finish: Seq.seq int) (n: nat) : GTot nat =
  find_max_compatible start finish n n

//SNIPPET_START: is_optimal_selection
(* An optimal selection has maximum cardinality *)
let is_optimal_selection (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (selected: list nat) : prop =
  mutually_compatible start finish selected /\
  list_sorted_indices selected n /\
  L.length selected == max_compatible_count start finish n
//SNIPPET_END: is_optimal_selection

(* Lemma: max_compatible_count is 0 when n is 0 — no activities to select *)
let max_compatible_count_zero (start finish: Seq.seq int)
  : Lemma (max_compatible_count start finish 0 == 0)
  = reveal_opaque (`%max_compatible_count) (max_compatible_count start finish 0)

(* Key property: if a compatible set of size m exists, then find_max_compatible >= m *)
let rec find_max_compatible_lower_bound
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (k: nat) (m: nat)
  (sel: list nat)
  : Lemma (requires m <= k /\ L.length sel = m /\
                   mutually_compatible start finish sel /\
                   list_sorted_indices sel n)
          (ensures find_max_compatible start finish n k >= m)
          (decreases k)
  = if k = 0 then ()
    else if FStar.IndefiniteDescription.strong_excluded_middle
              (exists (sel: list nat). L.length sel = k /\
                                      mutually_compatible start finish sel /\
                                      list_sorted_indices sel n)
    then ()  // find_max_compatible returns k >= m
    else begin
      // find_max_compatible returns find_max_compatible (k-1)
      if m <= k - 1 then
        find_max_compatible_lower_bound start finish n (k - 1) m sel
      else
        // m = k, but strong_excluded_middle says no set of size k exists
        // But sel has size m = k. Contradiction!
        assert (L.length sel = k);
        assert (mutually_compatible start finish sel);
        assert (list_sorted_indices sel n)
        // The strong_excluded_middle check for k should have returned true
        // since sel witnesses the existential. But it returned false.
        // This is a contradiction — Z3 should derive False.
    end

(* Upper bound: find_max_compatible <= k *)
let rec find_max_compatible_upper_bound
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (k: nat)
  : Lemma (ensures find_max_compatible start finish n k <= k)
          (decreases k)
  = if k = 0 then ()
    else if FStar.IndefiniteDescription.strong_excluded_middle
              (exists (sel: list nat). L.length sel = k /\
                                      mutually_compatible start finish sel /\
                                      list_sorted_indices sel n)
    then ()
    else find_max_compatible_upper_bound start finish n (k - 1)

(* If all compatible sets have size <= bound, then max_compatible_count <= bound *)
#push-options "--fuel 2 --ifuel 1"
let rec find_max_compatible_no_larger
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (k: nat) (bound: nat)
  : Lemma 
    (requires
      bound <= k /\
      (forall (sel: list nat). 
        mutually_compatible start finish sel /\
        list_sorted_indices sel n ==>
        L.length sel <= bound))
    (ensures find_max_compatible start finish n k <= bound)
    (decreases k)
  = if k = 0 then ()
    else 
      let b = FStar.IndefiniteDescription.strong_excluded_middle
                (exists (sel: list nat). L.length sel = k /\
                                        mutually_compatible start finish sel /\
                                        list_sorted_indices sel n) in
      if b then begin
        // find_max_compatible returns k
        // The existential witness has L.length = k and is compatible/sorted
        // The forall gives L.length <= bound, so k <= bound
        // For Z3: the `b = true` means the existential holds, and the forall
        // should apply to the witness. But Z3 can't connect them directly.
        // So we need: k <= bound. If k > bound, then the witness has
        // L.length = k > bound, but forall says L.length <= bound. Contradiction.
        ()
      end
      else begin
        // find_max_compatible recurses to k-1
        if bound <= k - 1 then
          find_max_compatible_no_larger start finish n (k - 1) bound
        else
          // bound = k but no set of size k exists
          // find_max_compatible(k-1) <= k-1 < k = bound
          find_max_compatible_upper_bound start finish n (k - 1)
      end
#pop-options

(* Corollary: max_compatible_count >= 1 when n > 0 and activities are valid *)
let max_compatible_count_pos (start: Seq.seq int) (finish: Seq.seq int) (n: nat)
  : Lemma (requires n > 0 /\ Seq.length start == n /\ Seq.length finish == n /\
                   (forall (i:nat). i < n ==> valid_activity start finish i))
          (ensures max_compatible_count start finish n >= 1)
  = reveal_opaque (`%max_compatible_count) (max_compatible_count start finish n);
    // [0] is a valid compatible set of size 1
    let singleton : list nat = [0] in
    assert (L.length singleton = 1);
    assert (mutually_compatible start finish singleton);
    assert (list_sorted_indices singleton n);
    find_max_compatible_lower_bound start finish n n 1 singleton

// ========== Greedy Choice Property (CLRS Theorem 16.1) ==========

(*
   Theorem: If activity 1 (index 0) has the earliest finish time,
   then there exists an optimal solution containing activity 1.
   
   Proof Strategy (Exchange Argument):
   - Let O be any optimal solution
   - Let k be the first activity in O (sorted by finish time)
   - If k = 0, we're done
   - If k > 0:
     * From finish_sorted: finish[0] <= finish[k]
     * Let O' = O with k replaced by 0
     * If O has only one activity: O' = [0] is valid (trivial)
     * If O has multiple activities, let j be the second activity in O
     * From mutual compatibility: finish[k] <= start[j]
     * By transitivity: finish[0] <= finish[k] <= start[j]
     * So 0 is compatible with j (and all later activities by similar argument)
     * O' is still mutually compatible with same size
     * Therefore O' is also optimal and contains activity 0
*)

let lemma_greedy_choice_helper
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (opt: list nat) (k: nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (i:nat). i < n ==> valid_activity start finish i) /\
      mutually_compatible start finish opt /\
      list_sorted_indices opt n /\
      opt <> [] /\
      L.hd opt == k)
    (ensures
      (let opt' = 0 :: L.tl opt in
       mutually_compatible start finish opt' /\
       list_sorted_indices opt' n /\
       L.length opt' == L.length opt))
    (decreases opt)
  = if k = 0 then ()
    else begin
      // k > 0, finish[0] <= finish[k] by finish_sorted
      assert (Seq.index finish 0 <= Seq.index finish k);
      
      match opt with
      | [_] ->
          // opt = [k], opt' = [0]
          // Trivially mutually_compatible
          ()
      | hd :: snd :: rest ->
          // opt = k :: j :: ..., opt' = 0 :: j :: ...
          // Need: 0 is compatible with all elements in (snd :: rest)
          let j = snd in
          
          // From mutually_compatible opt: k is compatible with all in (snd :: rest)
          // In particular, k is compatible with j
          assert (compatible start finish k j);
          
          // From list_sorted_indices: k < j
          assert (k < j);
          
          // Since k and j are compatible and k < j in sorted activities,
          // we have finish[k] <= start[j]
          lemma_compat_order start finish opt k j;
          assert (Seq.index finish k <= Seq.index start j);
          
          // From finish_sorted and 0 < k: finish[0] <= finish[k]
          assert (Seq.index finish 0 <= Seq.index finish k);
          
          // By transitivity: finish[0] <= start[j]
          assert (Seq.index finish 0 <= Seq.index start j);
          
          // Therefore 0 is compatible with j
          assert (compatible start finish 0 j);
          
          // For any other element z in rest: similar argument
          let lemma_zero_compatible_with_all (z: nat) : Lemma 
            (requires L.mem z (snd :: rest))
            (ensures compatible start finish 0 z)
          = 
            // k is compatible with z
            assert (compatible start finish k z);
            // From list_sorted: k < z
            // Need to prove k < z using list structure
            // opt = k :: snd :: rest, so list_sorted_indices opt n gives us k < snd < ...
            // If z = snd, then k < snd = z
            // If z is in rest, then k < snd and snd < z by lemma_head_less_than_rest
            if z = snd then ()
            else lemma_head_less_than_rest rest snd z n;
            assert (k < z);
            // Therefore finish[k] <= start[z]
            lemma_compat_order start finish opt k z;
            assert (Seq.index finish k <= Seq.index start z);
            // From finish[0] <= finish[k]: finish[0] <= start[z]
            assert (Seq.index finish 0 <= Seq.index start z);
            // So 0 is compatible with z
            ()
          in
          Classical.forall_intro (Classical.move_requires lemma_zero_compatible_with_all);
          ()
    end

//SNIPPET_START: lemma_greedy_choice
let lemma_greedy_choice
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (opt: list nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (i:nat). i < n ==> valid_activity start finish i) /\
      is_optimal_selection start finish n opt)
    (ensures
      (exists (opt': list nat).
        is_optimal_selection start finish n opt' /\
        opt' <> [] /\
        L.hd opt' == 0))
//SNIPPET_END: lemma_greedy_choice
  = if opt = [] then begin
      // If opt is empty and optimal, then max_compatible_count = 0
      // But max_compatible_count >= 1 when n > 0, contradiction
      max_compatible_count_pos start finish n
    end
    else if L.hd opt = 0 then
      // Already contains 0
      ()
    else begin
      // Use exchange argument
      let k = L.hd opt in
      lemma_greedy_choice_helper start finish n opt k;
      let opt' = 0 :: L.tl opt in
      // opt' is mutually compatible, sorted, and same length as opt
      // Since L.length opt = max_compatible_count and L.length opt' = L.length opt,
      // opt' is also optimal
      assert (L.length opt' == L.length opt);
      assert (is_optimal_selection start finish n opt')
    end

// ========== Optimal Substructure ==========

(*
   After selecting activity 0 (earliest finish), consider the subproblem:
   S' = {activities j : start[j] >= finish[0]}
   
   Theorem: An optimal solution to the original problem consists of:
   - Activity 0
   - An optimal solution to the subproblem S'
   
   Proof:
   - Let O be optimal for original, containing activity 0 (by greedy choice)
   - Let O' = O \ {0} (remove activity 0)
   - O' must be optimal for S', otherwise we could improve O
*)

(* Activities compatible with activity i *)
let compatible_with (start: Seq.seq int) (finish: Seq.seq int) (i: nat) (j: nat) : prop =
  i < Seq.length start /\ i < Seq.length finish /\
  j < Seq.length start /\ j < Seq.length finish /\
  j > i /\
  Seq.index finish i <= Seq.index start j

let lemma_optimal_substructure
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (opt: list nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (i:nat). i < n ==> valid_activity start finish i) /\
      is_optimal_selection start finish n opt /\
      opt <> [] /\
      L.hd opt == 0)
    (ensures
      (let subproblem = L.tl opt in
       // subproblem is optimal for activities compatible with 0
       mutually_compatible start finish subproblem /\
       L.length opt == 1 + L.length subproblem))
  = // The subproblem after removing activity 0 must be mutually compatible
    // This follows directly from the definition of mutually_compatible
    // If opt = [0], then tl opt = [], which is trivially compatible
    // If opt = 0 :: rest, then rest must be mutually compatible by definition
    match opt with
    | [_] -> ()
    | hd :: tl -> ()
    // The length property is immediate from the definition of tl

// ========== Greedy Algorithm Specification ==========

(*
   The greedy algorithm maintains:
   - A selection list (in increasing order of indices)
   - All selected activities are mutually compatible
   - Each newly selected activity i satisfies: start[i] >= finish[last]
*)

(* Greedy selection property: models the algorithm's choices *)
(* The inner recursive predicate does not require head == 0 *)
let rec is_greedy_selection_inner (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (selected: list nat) : prop =
  match selected with
  | [] -> True
  | [x] -> x < n /\ x < Seq.length start /\ x < Seq.length finish /\
      // x is the last selected: no compatible activities after x
      (forall (z: nat). x < z /\ z < n /\ z < Seq.length start /\ z < Seq.length finish ==>
        Seq.index start z < Seq.index finish x)
  | x :: y :: rest ->
      x < n /\ y < n /\
      x < Seq.length start /\ x < Seq.length finish /\
      y < Seq.length start /\ y < Seq.length finish /\
      Seq.index finish x <= Seq.index start y /\
      x < y /\
      is_greedy_selection_inner start finish n (y :: rest) /\
      // y is the earliest compatible activity after x
      (forall (z: nat). x < z /\ z < y /\ z < n /\ z < Seq.length start /\ z < Seq.length finish ==>
        Seq.index start z < Seq.index finish x)

(* Top-level greedy selection: starts with activity 0 *)
let is_greedy_selection (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (selected: list nat) : prop =
  match selected with
  | [] -> True
  | x :: _ -> x == 0 /\ is_greedy_selection_inner start finish n selected

// ========== Main Optimality Theorem ==========

(*
   Theorem: The greedy algorithm produces an optimal solution.
   
   Proof combines:
   1. Greedy choice: activity 0 is in some optimal solution
   2. Optimal substructure: recursively apply to remaining activities
   3. By induction, greedy produces optimal solution
*)

(*
   OPTIMALITY PROOF: Exchange argument (CLRS Theorem 16.1)
   
   Key lemma: The i-th greedy activity finishes no later than the i-th activity
   in any optimal solution. This is proven by induction using the "earliest compatible"
   property of the greedy selection.
*)

// Helper: get the i-th element of a list
let rec list_index (#a:Type) (l: list a) (i: nat{i < L.length l}) : a =
  match l with
  | hd :: tl -> if i = 0 then hd else list_index tl (i - 1)

// The i-th element of a sorted-indices list is a valid index
let rec lemma_list_index_bound (l: list nat) (i: nat) (n: nat)
  : Lemma
    (requires list_sorted_indices l n /\ i < L.length l)
    (ensures list_index l i < n)
    (decreases l)
  = match l with
    | [_] -> ()
    | x :: y :: rest ->
        if i = 0 then ()
        else lemma_list_index_bound (y :: rest) (i - 1) n

// In a sorted list, list_index is strictly increasing
let rec lemma_list_index_sorted (l: list nat) (i j: nat) (n: nat)
  : Lemma
    (requires list_sorted_indices l n /\ i < j /\ j < L.length l)
    (ensures list_index l i < list_index l j)
    (decreases l)
  = match l with
    | x :: y :: rest ->
        if i = 0 then begin
          if j = 1 then ()
          else lemma_list_index_sorted (y :: rest) 0 (j - 1) n
        end
        else
          lemma_list_index_sorted (y :: rest) (i - 1) (j - 1) n

// The i-th element of a list is a member of that list
let rec lemma_list_index_mem (#a:eqtype) (l: list a) (i: nat)
  : Lemma
    (requires i < L.length l)
    (ensures L.mem (list_index l i) l)
    (decreases l)
  = match l with
    | hd :: tl ->
        if i = 0 then ()
        else lemma_list_index_mem tl (i - 1)

// Extract "earliest compatible" property from is_greedy_selection_inner at position i
// Also: extract the last-element exhaustiveness
let rec lemma_greedy_last_exhaustive
  (start finish: Seq.seq int) (n: nat) (greedy: list nat)
  : Lemma
    (requires
      is_greedy_selection_inner start finish n greedy /\
      list_sorted_indices greedy n /\
      n == Seq.length start /\ n == Seq.length finish /\
      L.length greedy >= 1)
    (ensures (
      let last = list_index greedy (L.length greedy - 1) in
      last < n /\
      (forall (z:nat). last < z /\ z < n /\ z < Seq.length start /\ z < Seq.length finish ==>
        Seq.index start z < Seq.index finish last)))
    (decreases greedy)
  = lemma_list_index_bound greedy (L.length greedy - 1) n;
    match greedy with
    | [x] -> ()
    | x :: y :: rest ->
        lemma_greedy_last_exhaustive start finish n (y :: rest)

// Extract "earliest compatible" property from is_greedy_selection_inner at position i
let rec lemma_greedy_earliest_compat
  (start finish: Seq.seq int) (n: nat) (greedy: list nat) (i: nat)
  : Lemma
    (requires
      is_greedy_selection_inner start finish n greedy /\
      list_sorted_indices greedy n /\
      n == Seq.length start /\ n == Seq.length finish /\
      i + 1 < L.length greedy)
    (ensures (
      let gi = list_index greedy i in
      let gi1 = list_index greedy (i + 1) in
      gi < n /\ gi1 < n /\
      gi < gi1 /\
      Seq.index finish gi <= Seq.index start gi1 /\
      (forall (z:nat). gi < z /\ z < gi1 /\ z < n /\ z < Seq.length start /\ z < Seq.length finish ==>
        Seq.index start z < Seq.index finish gi)))
    (decreases greedy)
  = lemma_list_index_bound greedy i n;
    lemma_list_index_bound greedy (i + 1) n;
    match greedy with
    | x :: y :: rest ->
        if i = 0 then ()
        else lemma_greedy_earliest_compat start finish n (y :: rest) (i - 1)

// Key lemma: greedy[i] <= other[i] and finish[greedy[i]] <= finish[other[i]]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec lemma_greedy_dominates
  (start finish: Seq.seq int) (n: nat)
  (greedy other: list nat)
  (i: nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (k:nat). k < n ==> valid_activity start finish k) /\
      is_greedy_selection_inner start finish n greedy /\
      mutually_compatible start finish other /\
      list_sorted_indices other n /\
      list_sorted_indices greedy n /\
      i < L.length greedy /\ i < L.length other /\
      L.hd greedy <= L.hd other)
    (ensures
      list_index greedy i <= list_index other i)
    (decreases i)
  = lemma_list_index_bound greedy i n;
    lemma_list_index_bound other i n;
    if i = 0 then ()
    else begin
      // IH at i-1
      lemma_greedy_dominates start finish n greedy other (i - 1);
      lemma_list_index_bound greedy (i - 1) n;
      lemma_list_index_bound other (i - 1) n;
      let gi_1 = list_index greedy (i - 1) in
      let oi_1 = list_index other (i - 1) in
      let gi = list_index greedy i in
      let oi = list_index other i in
      // IH: gi_1 <= oi_1
      assert (gi_1 <= oi_1);
      
      // From sorted other: oi > oi_1 >= gi_1
      lemma_list_index_sorted other (i - 1) i n;
      assert (oi_1 < oi);
      assert (oi > gi_1);
      
      // Establish membership for lemma_compat_order
      lemma_list_index_mem other (i - 1);
      lemma_list_index_mem other i;
      
      // From compatibility of other: finish[oi_1] <= start[oi]
      lemma_compat_order start finish other oi_1 oi;
      // From IH + finish_sorted: finish[gi_1] <= finish[oi_1]
      assert (Seq.index finish gi_1 <= Seq.index finish oi_1);
      // Chain: finish[gi_1] <= start[oi]
      assert (Seq.index finish gi_1 <= Seq.index start oi);
      
      // From greedy earliest: for all z with gi_1 < z < gi: start[z] < finish[gi_1]
      lemma_greedy_earliest_compat start finish n greedy (i - 1);
      // Since start[oi] >= finish[gi_1] and oi > gi_1, oi cannot be in (gi_1, gi)
      // So oi >= gi
      assert (oi >= gi)
    end
#pop-options

// Maximality: no compatible set can be strictly larger than the greedy selection
// Uses: lemma_greedy_dominates + last-element exhaustiveness
#push-options "--fuel 2 --ifuel 1 --z3rlimit 15"
let lemma_greedy_is_maximal
  (start finish: Seq.seq int) (n: nat)
  (greedy other: list nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (k:nat). k < n ==> valid_activity start finish k) /\
      is_greedy_selection start finish n greedy /\
      mutually_compatible start finish greedy /\
      list_sorted_indices greedy n /\
      mutually_compatible start finish other /\
      list_sorted_indices other n /\
      L.length greedy >= 1)
    (ensures L.length other <= L.length greedy)
  = if L.length other <= L.length greedy then ()
    else begin
      let j = L.length greedy - 1 in
      
      lemma_greedy_dominates start finish n greedy other j;
      let gj = list_index greedy j in
      let oj = list_index other j in
      
      lemma_list_index_bound other (j + 1) n;
      let oj1 = list_index other (j + 1) in
      
      lemma_list_index_sorted other j (j + 1) n;
      
      lemma_list_index_mem other j;
      lemma_list_index_mem other (j + 1);
      lemma_compat_order start finish other oj oj1;
      
      lemma_list_index_bound greedy j n;
      // finish_sorted + gj <= oj: finish[gj] <= finish[oj] <= start[oj1]
      
      // Last-element exhaustiveness: all z > gj have start[z] < finish[gj]
      lemma_greedy_last_exhaustive start finish n greedy;
      // oj1 > oj >= gj, oj1 < n, so start[oj1] < finish[gj]
      // Contradiction: finish[gj] <= start[oj1] < finish[gj]
      assert false
    end
#pop-options

let lemma_greedy_is_optimal_helper
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (greedy_sel: list nat) (fuel: nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (i:nat). i < n ==> valid_activity start finish i) /\
      is_greedy_selection start finish n greedy_sel /\
      mutually_compatible start finish greedy_sel /\
      list_sorted_indices greedy_sel n /\
      L.length greedy_sel >= 1 /\
      fuel >= L.length greedy_sel)
    (ensures
      is_optimal_selection start finish n greedy_sel)
    (decreases fuel)
  = // Strategy: show L.length greedy_sel == max_compatible_count
    // Lower bound: greedy is a compatible set, so max_compatible_count >= L.length greedy_sel
    reveal_opaque (`%max_compatible_count) (max_compatible_count start finish n);
    lemma_sorted_indices_length greedy_sel n;
    find_max_compatible_lower_bound start finish n n (L.length greedy_sel) greedy_sel;
    // Upper bound: use lemma_greedy_is_maximal to show all compatible sets have <= L.length greedy_sel
    let bound = L.length greedy_sel in
    let aux (sel: list nat) 
      : Lemma
        (requires mutually_compatible start finish sel /\ list_sorted_indices sel n)
        (ensures L.length sel <= bound) =
      lemma_greedy_is_maximal start finish n greedy_sel sel
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    find_max_compatible_no_larger start finish n n bound


//SNIPPET_START: lemma_greedy_is_optimal
let lemma_greedy_is_optimal
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (greedy_sel: list nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (i:nat). i < n ==> valid_activity start finish i) /\
      is_greedy_selection start finish n greedy_sel /\
      mutually_compatible start finish greedy_sel /\
      list_sorted_indices greedy_sel n /\
      L.length greedy_sel >= 1)
    (ensures
      is_optimal_selection start finish n greedy_sel)
  = lemma_sorted_indices_length greedy_sel n;
    lemma_greedy_is_optimal_helper start finish n greedy_sel n
//SNIPPET_END: lemma_greedy_is_optimal

// ========== Connection to Implementation ==========

(*
   The Pulse implementation (CLRS.Ch16.ActivitySelection.fst) maintains:
   - A sequence sel of selected activity indices
   - pairwise_compatible: forall i. finish[sel[i]] <= start[sel[i+1]]
   - strictly_increasing: sel is sorted
   
   We now connect this to optimality:
*)

(* Convert sequence to list *)
let rec seq_to_list_aux (s: Seq.seq 'a) (i: nat{i <= Seq.length s}) : Tot (list 'a) (decreases (Seq.length s - i)) =
  if i >= Seq.length s then []
  else Seq.index s i :: seq_to_list_aux s (i + 1)

let seq_to_list (s: Seq.seq 'a) : list 'a =
  seq_to_list_aux s 0

(* Pairwise compatible (from Lemmas.fst) *)
let pairwise_compatible (sel: Seq.seq nat) (s f: Seq.seq int) : prop =
  (forall (i: nat). i < Seq.length sel ==> Seq.index sel i < Seq.length s /\ Seq.index sel i < Seq.length f) /\
  (forall (i: nat). i + 1 < Seq.length sel ==>
    Seq.index f (Seq.index sel i) <= Seq.index s (Seq.index sel (i + 1)))

(* Strictly increasing (from Lemmas.fst) *)
let strictly_increasing (sel: Seq.seq nat) : prop =
  forall (i j: nat). i < j /\ j < Seq.length sel ==> Seq.index sel i < Seq.index sel j

// Work with seq_to_list_aux directly to avoid slicing complexity
let rec lemma_pairwise_is_sequential_aux
  (start: Seq.seq int) (finish: Seq.seq int) (sel: Seq.seq nat) (i: nat)
  : Lemma
    (requires
      i <= Seq.length sel /\
      pairwise_compatible sel start finish /\
      strictly_increasing sel /\
      i < Seq.length sel)
    (ensures
      sequentially_compatible start finish (seq_to_list_aux sel i))
    (decreases Seq.length sel - i)
  = if i + 1 >= Seq.length sel then
      // Only one element left
      ()
    else begin
      // At least 2 elements from index i: sel[i] and sel[i+1]
      // From pairwise_compatible: finish[sel[i]] <= start[sel[i+1]]
      lemma_pairwise_is_sequential_aux start finish sel (i + 1);
      ()
    end

let lemma_pairwise_is_sequential
  (start: Seq.seq int) (finish: Seq.seq int) (sel: Seq.seq nat)
  : Lemma
    (requires
      pairwise_compatible sel start finish /\
      strictly_increasing sel /\
      Seq.length sel > 0)
    (ensures
      sequentially_compatible start finish (seq_to_list sel))
  = lemma_pairwise_is_sequential_aux start finish sel 0

let rec lemma_implementation_is_greedy_aux
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (sel: Seq.seq nat) (i: nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (k:nat). k < n ==> valid_activity start finish k) /\
      pairwise_compatible sel start finish /\
      strictly_increasing sel /\
      Seq.length sel > 0 /\
      (forall (k:nat). k < Seq.length sel ==> Seq.index sel k < n) /\
      AL.earliest_compatible sel start finish n n /\
      i <= Seq.length sel /\ i < Seq.length sel)
    (ensures
      is_greedy_selection_inner start finish n (seq_to_list_aux sel i))
    (decreases Seq.length sel - i)
  = if i + 1 >= Seq.length sel then begin
      // Singleton case: [sel[i]]
      // Need: forall z. sel[i] < z < n ==> start[z] < finish[sel[i]]
      // From earliest_compatible "after last": sel[last] < z < n ==> start[z] < finish[sel[last]]
      // Since i == last (i = |sel| - 1), this is exactly what we need
      assert (i == Seq.length sel - 1);
      ()
    end else begin
      // At least 2 elements: sel[i] :: sel[i+1] :: ...
      // Need: finish[sel[i]] <= start[sel[i+1]]  (from pairwise_compatible at i)
      //       sel[i] < sel[i+1]  (from strictly_increasing)
      //       is_greedy_selection_inner (sel[i+1] :: ...)  (recursive call)
      //       forall z. sel[i] < z < sel[i+1] ==> start[z] < finish[sel[i]]  (from earliest_compatible)
      lemma_implementation_is_greedy_aux start finish n sel (i + 1);
      ()
    end

let lemma_implementation_is_greedy
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (sel: Seq.seq nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (i:nat). i < n ==> valid_activity start finish i) /\
      pairwise_compatible sel start finish /\
      strictly_increasing sel /\
      Seq.length sel > 0 /\
      Seq.index sel 0 == 0 /\
      (forall (i:nat). i < Seq.length sel ==> Seq.index sel i < n) /\
      AL.earliest_compatible sel start finish n n)
    (ensures
      is_greedy_selection start finish n (seq_to_list sel))
  = lemma_implementation_is_greedy_aux start finish n sel 0

(*
   Main Theorem: The implementation produces optimal results
*)

(* Helper: convert seq properties to list properties *)
// Work with seq_to_list_aux directly to avoid slicing complexity
let rec lemma_seq_to_list_aux_preserves_sorted
  (sel: Seq.seq nat) (n: nat) (i: nat)
  : Lemma
    (requires
      i <= Seq.length sel /\
      strictly_increasing sel /\
      (forall (j:nat). j < Seq.length sel ==> Seq.index sel j < n))
    (ensures
      list_sorted_indices (seq_to_list_aux sel i) n)
    (decreases Seq.length sel - i)
  = if i >= Seq.length sel then ()
    else if i + 1 >= Seq.length sel then ()
    else begin
      // sel has at least 2 elements from index i
      // Seq.index sel i < Seq.index sel (i+1) from strictly_increasing
      lemma_seq_to_list_aux_preserves_sorted sel n (i + 1);
      ()
    end

let lemma_seq_to_list_preserves_sorted
  (sel: Seq.seq nat) (n: nat)
  : Lemma
    (requires
      strictly_increasing sel /\
      (forall (i:nat). i < Seq.length sel ==> Seq.index sel i < n))
    (ensures
      list_sorted_indices (seq_to_list sel) n)
  = lemma_seq_to_list_aux_preserves_sorted sel n 0

//SNIPPET_START: theorem_implementation_optimal

(* Helper lemmas for seq_to_list length *)
let rec lemma_seq_to_list_length_aux (s: Seq.seq 'a) (i: nat{i <= Seq.length s})
  : Lemma (ensures L.length (seq_to_list_aux s i) == Seq.length s - i)
          (decreases Seq.length s - i)
  = if i >= Seq.length s then ()
    else lemma_seq_to_list_length_aux s (i + 1)

let lemma_seq_to_list_length (s: Seq.seq 'a) 
  : Lemma (ensures L.length (seq_to_list s) == Seq.length s)
  = lemma_seq_to_list_length_aux s 0

let theorem_implementation_optimal
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (sel: Seq.seq nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (i:nat). i < n ==> valid_activity start finish i) /\
      pairwise_compatible sel start finish /\
      strictly_increasing sel /\
      Seq.length sel > 0 /\
      Seq.index sel 0 == 0 /\
      (forall (i:nat). i < Seq.length sel ==> Seq.index sel i < n) /\
      AL.earliest_compatible sel start finish n n)
    (ensures
      (let sel_list = seq_to_list sel in
       is_optimal_selection start finish n sel_list /\
       L.length sel_list == Seq.length sel))
  = lemma_pairwise_is_sequential start finish sel;
    lemma_seq_to_list_preserves_sorted sel n;
    lemma_sequential_implies_mutual start finish (seq_to_list sel);
    lemma_implementation_is_greedy start finish n sel;
    lemma_greedy_is_optimal start finish n (seq_to_list sel);
    lemma_seq_to_list_length sel
//SNIPPET_END: theorem_implementation_optimal

// ========== Corollaries ==========

(*
   Corollary: The greedy algorithm achieves the maximum possible count
*)
let corollary_greedy_count_is_maximum
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (sel: Seq.seq nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (i:nat). i < n ==> valid_activity start finish i) /\
      pairwise_compatible sel start finish /\
      strictly_increasing sel /\
      Seq.length sel > 0 /\
      Seq.index sel 0 == 0 /\
      (forall (i:nat). i < Seq.length sel ==> Seq.index sel i < n) /\
      AL.earliest_compatible sel start finish n n)
    (ensures
      Seq.length sel == max_compatible_count start finish n)
  = theorem_implementation_optimal start finish n sel;
    // From theorem: is_optimal_selection ... (seq_to_list sel)
    // From is_optimal_selection: L.length (seq_to_list sel) == max_compatible_count
    // Need to prove: Seq.length sel == L.length (seq_to_list sel)
    // This follows from the definition of seq_to_list
    lemma_seq_to_list_length sel;
    ()

(*
   Corollary: No other valid selection can be larger
*)
let corollary_no_larger_selection
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (greedy_sel other_sel: Seq.seq nat)
  : Lemma
    (requires
      finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (i:nat). i < n ==> valid_activity start finish i) /\
      // greedy_sel from the implementation
      pairwise_compatible greedy_sel start finish /\
      strictly_increasing greedy_sel /\
      Seq.length greedy_sel > 0 /\
      Seq.index greedy_sel 0 == 0 /\
      (forall (i:nat). i < Seq.length greedy_sel ==> Seq.index greedy_sel i < n) /\
      AL.earliest_compatible greedy_sel start finish n n /\
      // other_sel is any other valid selection
      pairwise_compatible other_sel start finish /\
      strictly_increasing other_sel /\
      (forall (i:nat). i < Seq.length other_sel ==> Seq.index other_sel i < n))
    (ensures
      Seq.length other_sel <= Seq.length greedy_sel)
  = // Strategy: 
    // 1. Use corollary_greedy_count_is_maximum: Seq.length greedy_sel == max_compatible_count
    // 2. Convert other_sel to list, show mutually_compatible
    // 3. Use find_max_compatible_lower_bound: max_compatible_count >= L.length (list other_sel)
    // 4. Show L.length (list other_sel) == Seq.length other_sel
    corollary_greedy_count_is_maximum start finish n greedy_sel;
    // Seq.length greedy_sel == max_compatible_count start finish n
    
    if Seq.length other_sel = 0 then ()
    else begin
      // Convert other_sel to list  
      let other_list = seq_to_list other_sel in
      lemma_seq_to_list_length other_sel;
      assert (L.length other_list == Seq.length other_sel);
      
      // Show other_list is sequentially compatible
      lemma_pairwise_is_sequential start finish other_sel;
      
      // Show other_list has sorted indices
      lemma_seq_to_list_preserves_sorted other_sel n;
      
      // Show other_list is mutually compatible
      lemma_sequential_implies_mutual start finish other_list;
      
      // Need: Seq.length other_sel <= n (from strictly increasing indices in [0,n))
      // The last element of a strictly increasing seq of length m with values < n must be >= m-1
      // So m-1 < n, hence m <= n
      // Use a simpler argument: convert to list, list_sorted_indices implies length <= n
      assert (list_sorted_indices other_list n);
      lemma_sorted_indices_length other_list n;
      reveal_opaque (`%max_compatible_count) (max_compatible_count start finish n);
      find_max_compatible_lower_bound start finish n n (Seq.length other_sel) other_list
    end

(* Corollary using Lemmas predicates — for direct use from Pulse code *)
let corollary_greedy_count_is_maximum_l
  (start: Seq.seq int) (finish: Seq.seq int) (n: nat) (sel: Seq.seq nat)
  : Lemma
    (requires
      AL.finish_sorted finish /\
      n == Seq.length start /\ n == Seq.length finish /\ n > 0 /\
      (forall (i:nat). i < n ==> AL.valid_activity start finish i) /\
      AL.pairwise_compatible sel start finish /\
      AL.strictly_increasing sel /\
      Seq.length sel > 0 /\
      Seq.index sel 0 == 0 /\
      AL.all_valid_indices sel n /\
      AL.earliest_compatible sel start finish n n)
    (ensures
      Seq.length sel == max_compatible_count start finish n)
  = corollary_greedy_count_is_maximum start finish n sel
