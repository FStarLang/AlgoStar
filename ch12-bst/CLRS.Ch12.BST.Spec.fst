module CLRS.Ch12.BST.Spec

(* ========================================================================
   Pure BST Specification - Complete CLRS Chapter 12 Implementation
   
   This module provides a complete pure functional specification of
   binary search trees following CLRS Chapter 12, including:
   - Inductive BST data structure
   - Validity predicate (BST property)
   - Search operations (TREE-SEARCH, TREE-MINIMUM, TREE-MAXIMUM)
   - Modification operations (TREE-INSERT, TREE-DELETE)
   - Inorder traversal
   - Correctness lemmas
   ======================================================================== *)

open FStar.List.Tot

(* ========================================================================
   § 1. BST Data Structure
   ======================================================================== *)

//SNIPPET_START: pure_bst_type
type bst =
  | Leaf : bst
  | Node : left:bst -> key:int -> right:bst -> bst
//SNIPPET_END: pure_bst_type

(* ========================================================================
   § 2. Helper Functions for Bounds Checking
   ======================================================================== *)

// Check if all elements in a list satisfy a predicate
let rec all (p: int -> bool) (xs: list int) : bool =
  match xs with
  | [] -> true
  | x :: xs' -> p x && all p xs'

// Check if all elements are less than bound
let all_less (bound: int) (xs: list int) : bool =
  all (fun x -> x < bound) xs

// Check if all elements are greater than bound
let all_greater (bound: int) (xs: list int) : bool =
  all (fun x -> x > bound) xs

(* ========================================================================
   § 3. Inorder Traversal (CLRS §12.1)
   ======================================================================== *)

let rec bst_inorder (t: bst) : list int =
  match t with
  | Leaf -> []
  | Node left key right ->
      bst_inorder left @ [key] @ bst_inorder right

(* ========================================================================
   § 4. BST Validity Predicate (CLRS BST Property)
   
   The BST property: For every node, all keys in left subtree < node's key
   and all keys in right subtree > node's key
   ======================================================================== *)

//SNIPPET_START: bst_valid
let rec bst_valid (t: bst) : bool =
  match t with
  | Leaf -> true
  | Node left key right ->
      bst_valid left &&
      bst_valid right &&
      all_less key (bst_inorder left) &&
      all_greater key (bst_inorder right)
//SNIPPET_END: bst_valid

(* ========================================================================
   § 5. BST Search (CLRS §12.2 TREE-SEARCH)
   ======================================================================== *)

//SNIPPET_START: bst_search
let rec bst_search (t: bst) (k: int) : bool =
  match t with
  | Leaf -> false
  | Node left key right ->
      if k = key then true
      else if k < key then bst_search left k
      else bst_search right k
//SNIPPET_END: bst_search

(* ========================================================================
   § 6. BST Minimum (CLRS §12.2 TREE-MINIMUM)
   ======================================================================== *)

let rec bst_minimum (t: bst) : option int =
  match t with
  | Leaf -> None
  | Node Leaf key _ -> Some key
  | Node left _ _ -> bst_minimum left

(* ========================================================================
   § 7. BST Maximum (CLRS §12.2 TREE-MAXIMUM)
   ======================================================================== *)

let rec bst_maximum (t: bst) : option int =
  match t with
  | Leaf -> None
  | Node _ key Leaf -> Some key
  | Node _ _ right -> bst_maximum right

(* ========================================================================
   § 8. BST Insert (CLRS §12.3 TREE-INSERT)
   ======================================================================== *)

//SNIPPET_START: bst_insert
let rec bst_insert (t: bst) (k: int) : bst =
  match t with
  | Leaf -> Node Leaf k Leaf
  | Node left key right ->
      if k < key then Node (bst_insert left k) key right
      else if k > key then Node left key (bst_insert right k)
      else t  // Key already exists, return unchanged
//SNIPPET_END: bst_insert

(* ========================================================================
   § 9. BST Delete (CLRS §12.3 TREE-DELETE)
   
   Three cases:
   1. Node has no children: remove it
   2. Node has one child: replace with that child
   3. Node has two children: replace with successor (minimum of right subtree)
   ======================================================================== *)

//SNIPPET_START: bst_delete
let rec bst_delete (t: bst) (k: int) : bst =
  match t with
  | Leaf -> Leaf
  | Node left key right ->
      if k < key then
        Node (bst_delete left k) key right
      else if k > key then
        Node left key (bst_delete right k)
      else
        // Found the key to delete
        match left, right with
        | Leaf, Leaf -> Leaf  // Case 1: No children
        | Leaf, _ -> right    // Case 2a: Only right child
        | _, Leaf -> left     // Case 2b: Only left child
        | _, _ ->    // Case 3: Two children
            // Replace with successor (minimum of right subtree)
            match bst_minimum right with
            | Some successor_key ->
                Node left successor_key (bst_delete right successor_key)
            | None -> t  // Should never happen when right is not Leaf
//SNIPPET_END: bst_delete

(* ========================================================================
   § 10. Helper Lemmas for List Properties
   ======================================================================== *)

// Membership in list
let rec mem (x: int) (xs: list int) : bool =
  match xs with
  | [] -> false
  | y :: ys -> x = y || mem x ys

// Lemma: append preserves all_less
let rec lemma_append_all_less (bound: int) (xs ys: list int)
  : Lemma (all_less bound (xs @ ys) <==> (all_less bound xs && all_less bound ys))
  = match xs with
    | [] -> ()
    | _ :: xs' -> lemma_append_all_less bound xs' ys

// Lemma: append preserves all_greater
let rec lemma_append_all_greater (bound: int) (xs ys: list int)
  : Lemma (all_greater bound (xs @ ys) <==> (all_greater bound xs && all_greater bound ys))
  = match xs with
    | [] -> ()
    | _ :: xs' -> lemma_append_all_greater bound xs' ys

// Lemma: singleton list with x satisfies all_less bound iff x < bound
let lemma_singleton_all_less (x bound: int)
  : Lemma (all_less bound [x] <==> x < bound)
  = ()

// Lemma: singleton list with x satisfies all_greater bound iff x > bound
let lemma_singleton_all_greater (x bound: int)
  : Lemma (all_greater bound [x] <==> x > bound)
  = ()

// Lemma: membership in append
let rec lemma_mem_append (x: int) (xs ys: list int)
  : Lemma (mem x (xs @ ys) <==> (mem x xs || mem x ys))
  = match xs with
    | [] -> ()
    | _ :: xs' -> lemma_mem_append x xs' ys

// Check if a list is sorted
let rec sorted (xs: list int) : bool =
  match xs with
  | [] -> true
  | [_] -> true
  | x :: y :: rest -> x < y && sorted (y :: rest)

(* ========================================================================
   § 11. Key Correctness Lemmas
   ======================================================================== *)

(* ------------------------------------------------------------------------
   Helper lemmas for search correctness
   ------------------------------------------------------------------------ *)

// Helper: if all elements are greater than key and k <= key, then k not in list
let rec lemma_all_greater_implies_not_mem (k: int) (key: int) (xs: list int)
  : Lemma
    (requires all_greater key xs /\ k < key)
    (ensures ~(mem k xs))
  = match xs with
    | [] -> ()
    | x :: xs' -> lemma_all_greater_implies_not_mem k key xs'

// Helper: if all elements are less than key and k >= key, then k not in list
let rec lemma_all_less_implies_not_mem (k: int) (key: int) (xs: list int)
  : Lemma
    (requires all_less key xs /\ k > key)
    (ensures ~(mem k xs))
  = match xs with
    | [] -> ()
    | x :: xs' -> lemma_all_less_implies_not_mem k key xs'

(* ------------------------------------------------------------------------
   Lemma: bst_search is correct w.r.t. membership in inorder traversal
   ------------------------------------------------------------------------ *)

//SNIPPET_START: bst_search_correct
let rec bst_search_correct (t: bst) (k: int)
  : Lemma 
    (requires bst_valid t)
    (ensures bst_search t k <==> mem k (bst_inorder t))
//SNIPPET_END: bst_search_correct
  = match t with
    | Leaf -> ()
    | Node left key right ->
        // Induction on left and right subtrees
        bst_search_correct left k;
        bst_search_correct right k;
        
        // Prove the equivalence for the current node
        lemma_mem_append k (bst_inorder left) ([key] @ bst_inorder right);
        lemma_mem_append k [key] (bst_inorder right);
        
        // Use BST property to show search correctness
        if k = key then ()
        else if k < key then begin
          // k < key, so search goes left
          // Need to show k is not in right subtree
          assert (all_greater key (bst_inorder right));
          lemma_all_greater_implies_not_mem k key (bst_inorder right)
        end
        else begin
          // k > key, so search goes right
          // Need to show k is not in left subtree
          assert (all_less key (bst_inorder left));
          lemma_all_less_implies_not_mem k key (bst_inorder left)
        end

(* ------------------------------------------------------------------------
   Helper lemmas for insert preservation
   ------------------------------------------------------------------------ *)

// Helper: inserting k into left subtree preserves all_less when k < bound
let rec lemma_insert_preserves_all_less (t: bst) (k: int) (bound: int)
  : Lemma
    (requires bst_valid t /\ all_less bound (bst_inorder t) /\ k < bound)
    (ensures all_less bound (bst_inorder (bst_insert t k)))
  = match t with
    | Leaf -> ()
    | Node left key right ->
        if k < key then begin
          // Establish preconditions for recursive call
          assert (bst_valid left);
          assert (all_less key (bst_inorder left));
          assert (all_less bound (bst_inorder left @ [key] @ bst_inorder right));
          lemma_append_all_less bound (bst_inorder left) ([key] @ bst_inorder right);
          lemma_append_all_less bound [key] (bst_inorder right);
          assert (all_less bound (bst_inorder left));
          
          lemma_insert_preserves_all_less left k bound;
          lemma_append_all_less bound (bst_inorder (bst_insert left k)) ([key] @ bst_inorder right);
          lemma_append_all_less bound [key] (bst_inorder right)
        end
        else if k > key then begin
          // Establish preconditions for recursive call
          assert (bst_valid right);
          assert (all_less bound (bst_inorder left @ [key] @ bst_inorder right));
          lemma_append_all_less bound (bst_inorder left) ([key] @ bst_inorder right);
          lemma_append_all_less bound [key] (bst_inorder right);
          assert (all_less bound (bst_inorder right));
          
          lemma_insert_preserves_all_less right k bound;
          lemma_append_all_less bound (bst_inorder left) ([key] @ bst_inorder (bst_insert right k));
          lemma_append_all_less bound [key] (bst_inorder (bst_insert right k))
        end
        else ()

// Helper: inserting k into right subtree preserves all_greater when k > bound
let rec lemma_insert_preserves_all_greater (t: bst) (k: int) (bound: int)
  : Lemma
    (requires bst_valid t /\ all_greater bound (bst_inorder t) /\ k > bound)
    (ensures all_greater bound (bst_inorder (bst_insert t k)))
  = match t with
    | Leaf -> ()
    | Node left key right ->
        if k < key then begin
          // Establish preconditions for recursive call
          assert (bst_valid left);
          assert (all_greater bound (bst_inorder left @ [key] @ bst_inorder right));
          lemma_append_all_greater bound (bst_inorder left) ([key] @ bst_inorder right);
          lemma_append_all_greater bound [key] (bst_inorder right);
          assert (all_greater bound (bst_inorder left));
          
          lemma_insert_preserves_all_greater left k bound;
          lemma_append_all_greater bound (bst_inorder (bst_insert left k)) ([key] @ bst_inorder right);
          lemma_append_all_greater bound [key] (bst_inorder right)
        end
        else if k > key then begin
          // Establish preconditions for recursive call
          assert (bst_valid right);
          assert (all_greater bound (bst_inorder left @ [key] @ bst_inorder right));
          lemma_append_all_greater bound (bst_inorder left) ([key] @ bst_inorder right);
          lemma_append_all_greater bound [key] (bst_inorder right);
          assert (all_greater bound (bst_inorder right));
          
          lemma_insert_preserves_all_greater right k bound;
          lemma_append_all_greater bound (bst_inorder left) ([key] @ bst_inorder (bst_insert right k));
          lemma_append_all_greater bound [key] (bst_inorder (bst_insert right k))
        end
        else ()

(* ------------------------------------------------------------------------
   Lemma: bst_insert preserves validity
   ------------------------------------------------------------------------ *)

//SNIPPET_START: bst_insert_valid
let rec bst_insert_valid (t: bst) (k: int)
  : Lemma
    (requires bst_valid t)
    (ensures bst_valid (bst_insert t k))
//SNIPPET_END: bst_insert_valid
  = match t with
    | Leaf -> ()
    | Node left key right ->
        if k < key then begin
          bst_insert_valid left k;
          // Need to show all_less key (bst_inorder (bst_insert left k))
          lemma_insert_preserves_all_less left k key;
          // Need to show all_greater key (bst_inorder right) still holds
          ()
        end
        else if k > key then begin
          bst_insert_valid right k;
          // Need to show all_greater key (bst_inorder (bst_insert right k))
          lemma_insert_preserves_all_greater right k key;
          // Need to show all_less key (bst_inorder left) still holds
          ()
        end
        else ()  // k = key, tree unchanged

(* ------------------------------------------------------------------------
   Helper: insert adds k to inorder traversal
   ------------------------------------------------------------------------ *)

let rec lemma_insert_adds_member (t: bst) (k: int)
  : Lemma
    (requires bst_valid t)
    (ensures mem k (bst_inorder (bst_insert t k)))
  = match t with
    | Leaf -> ()
    | Node left key right ->
        if k < key then begin
          lemma_insert_adds_member left k;
          lemma_mem_append k (bst_inorder (bst_insert left k)) ([key] @ bst_inorder right)
        end
        else if k > key then begin
          lemma_insert_adds_member right k;
          lemma_mem_append k (bst_inorder left) ([key] @ bst_inorder (bst_insert right k));
          lemma_mem_append k [key] (bst_inorder (bst_insert right k))
        end
        else begin
          // k = key, tree unchanged, k is already at root
          lemma_mem_append k (bst_inorder left) ([key] @ bst_inorder right);
          lemma_mem_append k [key] (bst_inorder right)
        end

(* ------------------------------------------------------------------------
   Lemma: after inserting k, searching for k returns true
   ------------------------------------------------------------------------ *)

let bst_insert_member (t: bst) (k: int)
  : Lemma
    (requires bst_valid t)
    (ensures (
      let t' = bst_insert t k in
      bst_valid t' /\
      bst_search t' k
    ))
  = bst_insert_valid t k;
    lemma_insert_adds_member t k;
    bst_search_correct (bst_insert t k) k

(* ------------------------------------------------------------------------
   Helper lemmas for delete preservation
   ------------------------------------------------------------------------ *)

// Helper: all_less is transitive with list elements
let rec lemma_all_less_transitive (bound1 bound2: int) (xs: list int)
  : Lemma
    (requires all_less bound1 xs /\ bound1 < bound2)
    (ensures all_less bound2 xs)
  = match xs with
    | [] -> ()
    | _ :: xs' -> lemma_all_less_transitive bound1 bound2 xs'

// Lemma: bst_minimum returns a member of the inorder traversal
let rec bst_minimum_in_tree (t: bst)
  : Lemma
    (requires bst_valid t /\ bst_minimum t <> None)
    (ensures (match bst_minimum t with
              | Some m -> mem m (bst_inorder t)
              | None -> False))
  = match t with
    | Leaf -> ()
    | Node Leaf key right -> 
        lemma_mem_append key (bst_inorder Leaf) ([key] @ bst_inorder right);
        lemma_mem_append key [key] (bst_inorder right)
    | Node left key right ->
        bst_minimum_in_tree left;
        match bst_minimum left with
        | Some m -> 
            lemma_mem_append m (bst_inorder left) ([key] @ bst_inorder right);
            ()
        | None -> ()

// Helper: if all elements are < bound and x is a member, then x < bound
let rec lemma_all_less_implies_mem_less (bound x: int) (xs: list int)
  : Lemma
    (requires all_less bound xs /\ mem x xs)
    (ensures x < bound)
  = match xs with
    | [] -> ()
    | y :: ys -> 
        if x = y then ()
        else lemma_all_less_implies_mem_less bound x ys

// Helper: all_greater is transitive with list elements
let rec lemma_all_greater_transitive (bound1 bound2: int) (xs: list int)
  : Lemma
    (requires all_greater bound2 xs /\ bound2 > bound1)
    (ensures all_greater bound1 xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> 
        // x > bound2 from assumption, and bound2 > bound1
        // Therefore x > bound1 by transitivity
        lemma_all_greater_transitive bound1 bound2 xs'

// Helper: all_greater on filtered list
let rec lemma_all_greater_filter (bound: int) (xs: list int)
  : Lemma (requires all_less bound xs)
          (ensures all_less bound (FStar.List.Tot.filter (fun x -> x <> bound) xs))
  = match xs with
    | [] -> ()
    | x :: xs' -> lemma_all_greater_filter bound xs'

// Helper: filtered list membership
let rec lemma_filter_mem (x y: int) (xs: list int)
  : Lemma (mem x (FStar.List.Tot.filter (fun z -> z <> y) xs) <==> (mem x xs /\ x <> y))
  = match xs with
    | [] -> ()
    | z :: zs -> lemma_filter_mem x y zs

// Helper: if no element in xs equals y, then filter is identity
let rec lemma_filter_identity (y: int) (xs: list int)
  : Lemma (requires ~(mem y xs))
          (ensures FStar.List.Tot.filter (fun x -> x <> y) xs == xs)
  = match xs with
    | [] -> ()
    | x :: xs' -> lemma_filter_identity y xs'

// Helper: if all elements in xs are > m, then m is not in xs
let rec lemma_all_greater_excludes_bound (m: int) (xs: list int)
  : Lemma (requires all_greater m xs)
          (ensures ~(mem m xs))
  = match xs with
    | [] -> ()
    | x :: xs' -> lemma_all_greater_excludes_bound m xs'

// Helper: if all elements in xs are > m, then filtered list also has all > m
let rec lemma_all_greater_on_filter (m: int) (xs: list int)
  : Lemma (requires all_greater m xs)
          (ensures all_greater m (FStar.List.Tot.filter (fun x -> x <> m) xs))
  = match xs with
    | [] -> ()
    | x :: xs' -> lemma_all_greater_on_filter m xs'

// Helper: filter distributes over append
let rec lemma_filter_append (p: int -> bool) (xs ys: list int)
  : Lemma (FStar.List.Tot.filter p (xs @ ys) == 
           FStar.List.Tot.filter p xs @ FStar.List.Tot.filter p ys)
  = match xs with
    | [] -> ()
    | x :: xs' -> lemma_filter_append p xs' ys

// Helper: filtering out m from a BST tree where m is the minimum
// Results in all elements being > m
let rec lemma_filter_all_greater_tree (t: bst) (m: int)
  : Lemma (requires bst_valid t /\ bst_minimum t = Some m)
          (ensures all_greater m (FStar.List.Tot.filter (fun x -> x <> m) (bst_inorder t)))
  = match t with
    | Leaf -> ()
    | Node Leaf key right ->
        // m = key
        // bst_inorder t = [key] @ bst_inorder right
        // Filter removes key, leaving just bst_inorder right
        // All elements in right are > key = m
        assert (m = key);
        lemma_filter_append (fun x -> x <> m) [key] (bst_inorder right);
        // filter [key] with (x <> key) = []
        // So filter (bst_inorder t) = filter (bst_inorder right)
        // All elements in right are > m from BST validity
        assert (all_greater m (bst_inorder right));
        // Since all elements in right > m, m is not in right
        lemma_all_greater_excludes_bound m (bst_inorder right);
        assert (~(mem m (bst_inorder right)));
        // So filter right = right
        lemma_filter_identity m (bst_inorder right);
        assert (FStar.List.Tot.filter (fun x -> x <> m) (bst_inorder right) == bst_inorder right);
        ()
    | Node left key right ->
        // m = bst_minimum left
        // By induction on left
        lemma_filter_all_greater_tree left m;
        assert (all_greater m (FStar.List.Tot.filter (fun x -> x <> m) (bst_inorder left)));
        
        // m < key (because m is in left and all of left < key)
        bst_minimum_in_tree left;
        lemma_all_less_implies_mem_less key m (bst_inorder left);
        assert (m < key);
        
        // All elements in right are > key, so > m
        assert (all_greater key (bst_inorder right));
        lemma_all_greater_transitive m key (bst_inorder right);
        assert (all_greater m (bst_inorder right));
        
        // Now apply filter to bst_inorder t = bst_inorder left @ [key] @ bst_inorder right
        lemma_filter_append (fun x -> x <> m) (bst_inorder left) ([key] @ bst_inorder right);
        lemma_filter_append (fun x -> x <> m) [key] (bst_inorder right);
        
        // Filter on each part:
        // - filter left: all > m (by induction)
        // - key <> m, so filter [key] = [key], and key > m
        // - no element in right equals m, so filter right = right, and all > m
        
        // Since m <> key, filter [key] = [key]
        assert (key <> m);
        assert (FStar.List.Tot.filter (fun x -> x <> m) [key] == [key]);
        
        // No element in right equals m (since all in right > key > m)
        lemma_all_greater_excludes_bound m (bst_inorder right);
        lemma_filter_identity m (bst_inorder right);
        assert (FStar.List.Tot.filter (fun x -> x <> m) (bst_inorder right) == bst_inorder right);
        
        // Combine: filtered result = filter left @ [key] @ right
        // Need to show all > m
        // filter left: all > m by induction
        assert (all_greater m (FStar.List.Tot.filter (fun x -> x <> m) (bst_inorder left)));
        
        // [key] @ right: all > m
        lemma_append_all_greater m [key] (bst_inorder right);
        assert (all_greater m ([key] @ bst_inorder right));
        
        // So filter [key] @ right = [key] @ right, which is all > m
        assert (FStar.List.Tot.filter (fun x -> x <> m) ([key] @ bst_inorder right) == 
                [key] @ bst_inorder right);
        
        // Combine
        lemma_append_all_greater m 
          (FStar.List.Tot.filter (fun x -> x <> m) (bst_inorder left))
          (FStar.List.Tot.filter (fun x -> x <> m) ([key] @ bst_inorder right));
        ()


// Lemma: bst_minimum returns the smallest element
// The minimum is a member and all other elements are strictly greater
let bst_minimum_is_minimum (t: bst) (m: int)
  : Lemma (requires bst_valid t /\ bst_minimum t = Some m)
          (ensures mem m (bst_inorder t) /\ 
                   all_greater m (FStar.List.Tot.filter (fun x -> x <> m) (bst_inorder t)))
  = bst_minimum_in_tree t;
    lemma_filter_all_greater_tree t m

// Helper: if all elements are > bound and x is a member, then x > bound
let rec lemma_all_greater_implies_mem_greater (bound x: int) (xs: list int)
  : Lemma
    (requires all_greater bound xs /\ mem x xs)
    (ensures x > bound)
  = match xs with
    | [] -> ()
    | y :: ys -> 
        if x = y then ()
        else lemma_all_greater_implies_mem_greater bound x ys

// Simpler version: minimum of right subtree is greater than all of left
let bst_minimum_greater_than_left (left right: bst) (key: int)
  : Lemma
    (requires 
      bst_valid (Node left key right) /\
      bst_minimum right <> None)
    (ensures (match bst_minimum right with
              | Some m -> all_less m (bst_inorder left)
              | None -> False))
  = match bst_minimum right with
    | Some m ->
        // m is in right subtree
        bst_minimum_in_tree right;
        // All elements in right are > key
        assert (all_greater key (bst_inorder right));
        // m is a member of right's inorder traversal
        assert (mem m (bst_inorder right));
        // Need to show m > key
        lemma_all_greater_implies_mem_greater key m (bst_inorder right);
        assert (m > key);
        // All elements in left are < key
        assert (all_less key (bst_inorder left));
        // So all elements in left < key < m
        lemma_all_less_transitive key m (bst_inorder left)
    | None -> ()

// Lemma: minimum is less than all other elements in tree after deleting it
let rec bst_minimum_less_than_rest (t: bst) (m: int)
  : Lemma
    (requires bst_valid t /\ bst_minimum t = Some m)
    (ensures all_greater m (bst_inorder (bst_delete t m)))
  = match t with
    | Leaf -> ()  // Can't have minimum in Leaf
    | Node left key right ->
        match left with
        | Leaf -> 
            // When left is Leaf, m = key (minimum is the root)
            // After deleting key, we're left with right
            // Need: all_greater key (bst_inorder right)
            // We have this from BST validity
            assert (m = key);
            assert (bst_delete t m = right);
            ()
        | _ -> 
            // When left is not Leaf, m = bst_minimum left
            // After deleting m, we get Node (bst_delete left m) key right
            // Need: all elements in (bst_delete left m), key, and right are > m
            
            // By induction: all elements in (bst_delete left m) are > m
            bst_minimum_less_than_rest left m;
            assert (all_greater m (bst_inorder (bst_delete left m)));
            
            // m is in left, and all elements in left are < key (BST validity)
            bst_minimum_in_tree left;
            assert (mem m (bst_inorder left));
            lemma_all_less_implies_mem_less key m (bst_inorder left);
            assert (m < key);
            
            // So key > m
            // All elements in right are > key > m
            assert (all_greater key (bst_inorder right));
            lemma_all_greater_transitive m key (bst_inorder right);
            assert (all_greater m (bst_inorder right));
            
            // Combine: (bst_delete left m) @ [key] @ right all > m
            lemma_append_all_greater m (bst_inorder (bst_delete left m)) ([key] @ bst_inorder right);
            lemma_append_all_greater m [key] (bst_inorder right);
            ()

// Helper: deleting from subtree preserves all_less bound
let rec lemma_delete_preserves_bounds_less (t: bst) (k: int) (bound: int)
  : Lemma
    (requires bst_valid t /\ all_less bound (bst_inorder t))
    (ensures all_less bound (bst_inorder (bst_delete t k)))
  = match t with
    | Leaf -> ()
    | Node left key right ->
        // Decompose the all_less bound assumption
        lemma_append_all_less bound (bst_inorder left) ([key] @ bst_inorder right);
        lemma_append_all_less bound [key] (bst_inorder right);
        
        if k < key then begin
          // Deleting from left subtree
          lemma_delete_preserves_bounds_less left k bound;
          lemma_append_all_less bound (bst_inorder (bst_delete left k)) ([key] @ bst_inorder right);
          lemma_append_all_less bound [key] (bst_inorder right)
        end
        else if k > key then begin
          // Deleting from right subtree
          lemma_delete_preserves_bounds_less right k bound;
          lemma_append_all_less bound (bst_inorder left) ([key] @ bst_inorder (bst_delete right k));
          lemma_append_all_less bound [key] (bst_inorder (bst_delete right k))
        end
        else begin
          // Deleting the root: k = key
          match left, right with
          | Leaf, Leaf -> ()
          | Leaf, _ -> ()  // Result is right, which already satisfies all_less bound
          | _, Leaf -> ()  // Result is left, which already satisfies all_less bound
          | _, _ ->
              // Two children: replace with successor
              match bst_minimum right with
              | Some successor_key ->
                  // The result is Node left successor_key (bst_delete right successor_key)
                  // Need to show all_less bound on this
                  // successor_key is in right, so it's < bound
                  bst_minimum_in_tree right;
                  assert (mem successor_key (bst_inorder right));
                  lemma_mem_append successor_key (bst_inorder left) ([key] @ bst_inorder right);
                  lemma_mem_append successor_key [key] (bst_inorder right);
                  assert (mem successor_key (bst_inorder (Node left key right)));
                  lemma_all_less_implies_mem_less bound successor_key (bst_inorder (Node left key right));
                  assert (successor_key < bound);
                  // left is < bound (already have this)
                  // bst_delete right successor_key is still < bound
                  lemma_delete_preserves_bounds_less right successor_key bound;
                  lemma_append_all_less bound (bst_inorder left) ([successor_key] @ bst_inorder (bst_delete right successor_key));
                  lemma_append_all_less bound [successor_key] (bst_inorder (bst_delete right successor_key))
              | None -> ()
        end

// Helper: deleting from subtree preserves all_greater bound  
let rec lemma_delete_preserves_bounds_greater (t: bst) (k: int) (bound: int)
  : Lemma
    (requires bst_valid t /\ all_greater bound (bst_inorder t))
    (ensures all_greater bound (bst_inorder (bst_delete t k)))
  = match t with
    | Leaf -> ()
    | Node left key right ->
        // Decompose the all_greater bound assumption
        lemma_append_all_greater bound (bst_inorder left) ([key] @ bst_inorder right);
        lemma_append_all_greater bound [key] (bst_inorder right);
        
        if k < key then begin
          // Deleting from left subtree
          lemma_delete_preserves_bounds_greater left k bound;
          lemma_append_all_greater bound (bst_inorder (bst_delete left k)) ([key] @ bst_inorder right);
          lemma_append_all_greater bound [key] (bst_inorder right)
        end
        else if k > key then begin
          // Deleting from right subtree
          lemma_delete_preserves_bounds_greater right k bound;
          lemma_append_all_greater bound (bst_inorder left) ([key] @ bst_inorder (bst_delete right k));
          lemma_append_all_greater bound [key] (bst_inorder (bst_delete right k))
        end
        else begin
          // Deleting the root: k = key
          match left, right with
          | Leaf, Leaf -> ()
          | Leaf, _ -> ()  // Result is right, which already satisfies all_greater bound
          | _, Leaf -> ()  // Result is left, which already satisfies all_greater bound
          | _, _ ->
              // Two children: replace with successor
              match bst_minimum right with
              | Some successor_key ->
                  // The result is Node left successor_key (bst_delete right successor_key)
                  // Need to show all_greater bound on this
                  // successor_key is in right, so it's > bound
                  bst_minimum_in_tree right;
                  assert (mem successor_key (bst_inorder right));
                  lemma_mem_append successor_key (bst_inorder left) ([key] @ bst_inorder right);
                  lemma_mem_append successor_key [key] (bst_inorder right);
                  assert (mem successor_key (bst_inorder (Node left key right)));
                  lemma_all_greater_implies_mem_greater bound successor_key (bst_inorder (Node left key right));
                  assert (successor_key > bound);
                  // left is > bound (already have this)
                  // bst_delete right successor_key is still > bound
                  lemma_delete_preserves_bounds_greater right successor_key bound;
                  lemma_append_all_greater bound (bst_inorder left) ([successor_key] @ bst_inorder (bst_delete right successor_key));
                  lemma_append_all_greater bound [successor_key] (bst_inorder (bst_delete right successor_key))
              | None -> ()
        end

(* ------------------------------------------------------------------------
   Lemma: bst_delete preserves validity
   ------------------------------------------------------------------------ *)

//SNIPPET_START: bst_delete_valid
let rec bst_delete_valid (t: bst) (k: int)
  : Lemma
    (requires bst_valid t)
    (ensures bst_valid (bst_delete t k))
//SNIPPET_END: bst_delete_valid
  = match t with
    | Leaf -> ()
    | Node left key right ->
        if k < key then begin
          bst_delete_valid left k;
          // Show all_less key is preserved after deleting from left
          lemma_delete_preserves_bounds_less left k key;
          ()
        end
        else if k > key then begin
          bst_delete_valid right k;
          // Show all_greater key is preserved after deleting from right
          lemma_delete_preserves_bounds_greater right k key;
          ()
        end
        else begin
          // Deleting the root: k = key
          match left, right with
          | Leaf, Leaf -> ()
          | Leaf, _ -> ()
          | _, Leaf -> ()
          | _, _ ->
              // Two children case: replace with successor
              // right is not Leaf, so bst_minimum right returns Some
              match bst_minimum right with
              | Some successor_key ->
                  // Recursive call on right subtree
                  bst_delete_valid right successor_key;
                  
                  // Need to prove BST properties for Node left successor_key (bst_delete right successor_key)
                  // 1. bst_valid left - already have this
                  assert (bst_valid left);
                  
                  // 2. bst_valid (bst_delete right successor_key) - from recursive call
                  assert (bst_valid (bst_delete right successor_key));
                  
                  // 3. all_less successor_key (bst_inorder left)
                  // successor_key is minimum of right, and right has all_greater key
                  // left has all_less key, so left < key < successor_key
                  bst_minimum_greater_than_left left right key;
                  assert (all_less successor_key (bst_inorder left));
                  
                  // 4. all_greater successor_key (bst_inorder (bst_delete right successor_key))
                  // This requires showing minimum is less than remaining elements
                  bst_minimum_less_than_rest right successor_key;
                  assert (all_greater successor_key (bst_inorder (bst_delete right successor_key)));
                  
                  ()
              | None -> ()  // Cannot happen since right is not Leaf
        end

(* ------------------------------------------------------------------------
   Helper lemmas for sorted lists
   ------------------------------------------------------------------------ *)

// Helper: appending two sorted lists with proper bounds gives sorted list
let rec lemma_append_sorted (xs ys: list int)
  : Lemma
    (requires 
      sorted xs /\ sorted ys /\
      (match xs, ys with
       | [], _ -> true
       | _, [] -> true
       | _, y :: _ -> all_less y xs))
    (ensures sorted (xs @ ys))
  = match xs with
    | [] -> ()
    | [x] -> 
        (match ys with
         | [] -> ()
         | y :: _ -> ())
    | x :: x' :: rest ->
        lemma_append_sorted (x' :: rest) ys

// Helper: if all elements in xs are < bound and xs is sorted,
// then xs @ [bound] is sorted
let rec lemma_sorted_append_less (xs: list int) (bound: int)
  : Lemma
    (requires all_less bound xs /\ sorted xs)
    (ensures sorted (xs @ [bound]))
  = match xs with
    | [] -> ()
    | [x] -> ()
    | x :: y :: rest ->
        lemma_sorted_append_less (y :: rest) bound

// Helper: show that xs @ [bound] has all elements < y when xs has all < bound and bound < y
let rec lemma_all_less_concat_singleton (xs: list int) (bound y: int)
  : Lemma
    (requires all_less bound xs /\ bound < y)
    (ensures all_less y (xs @ [bound]))
  = match xs with
    | [] -> ()
    | x :: xs' -> 
        lemma_all_less_concat_singleton xs' bound y;
        ()  // x < bound < y, and xs' @ [bound] all < y, so x :: (xs' @ [bound]) all < y

// Helper: if all elements in ys are > bound and ys is sorted,
// then [bound] @ ys is sorted
let lemma_sorted_prepend_greater (bound: int) (ys: list int)
  : Lemma
    (requires all_greater bound ys /\ sorted ys)
    (ensures sorted ([bound] @ ys))
  = match ys with
    | [] -> ()
    | [y] -> ()
    | y :: rest -> ()

// Helper: if xs is sorted, all_less bound xs, ys is sorted, all_greater bound ys,
// then xs @ [bound] @ ys is sorted
#push-options "--z3rlimit 20"

let lemma_sorted_concat (xs: list int) (bound: int) (ys: list int)
  : Lemma
    (requires 
      sorted xs /\ all_less bound xs /\
      sorted ys /\ all_greater bound ys)
    (ensures sorted (xs @ [bound] @ ys))
  = // First show xs @ [bound] is sorted
    lemma_sorted_append_less xs bound;
    // Then show [bound] @ ys is sorted
    lemma_sorted_prepend_greater bound ys;
    // Now append them: (xs @ [bound]) @ ys
    // We need to show the join point is valid
    match ys with
    | [] -> 
        // xs @ [bound] @ [] = xs @ [bound]
        FStar.List.Tot.Properties.append_l_nil (xs @ [bound])
    | y :: _ -> 
        // Since all_greater bound ys, we have y > bound
        // So xs @ [bound] has all elements < y
        lemma_all_less_concat_singleton xs bound y;
        assert (all_less y (xs @ [bound]));
        lemma_append_sorted (xs @ [bound]) ys;
        // Now we have sorted ((xs @ [bound]) @ ys)
        // Need to show this equals xs @ [bound] @ ys
        FStar.List.Tot.Properties.append_assoc xs [bound] ys

#pop-options

(* ------------------------------------------------------------------------
   Lemma: inorder traversal of a valid BST is sorted
   ------------------------------------------------------------------------ *)

//SNIPPET_START: bst_inorder_sorted
// Main lemma: inorder traversal is sorted for valid BSTs
let rec bst_inorder_sorted (t: bst)
  : Lemma
    (requires bst_valid t)
    (ensures sorted (bst_inorder t))
//SNIPPET_END: bst_inorder_sorted
  = match t with
    | Leaf -> ()
    | Node left key right ->
        bst_inorder_sorted left;
        bst_inorder_sorted right;
        lemma_sorted_concat (bst_inorder left) key (bst_inorder right)
