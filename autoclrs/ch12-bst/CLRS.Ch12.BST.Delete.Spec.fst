module CLRS.Ch12.BST.Delete.Spec

(**
 * BST Delete Key Set Specification
 * 
 * Theorem: key_set(delete(t,k)) = key_set(t) \ {k} for valid BST t where k ∈ t
 * 
 * Uses list-based BST from CLRS.Ch12.BST.Spec
 * Main lemma verified with zero admits (FiniteSet algebra via all_finite_set_facts_lemma)
 *)

open FStar.List.Tot
module FS = FStar.FiniteSet.Base
open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BST.KeySet

let rec lemma_all_less_excludes_bound (m: int) (xs: list int)
  : Lemma (requires all_less m xs) (ensures ~(mem m xs))
  = match xs with [] -> () | _ :: xs' -> lemma_all_less_excludes_bound m xs'

// Helper lemma: if k ∉ s2, then (s1 ∪ s2) \ {k} = (s1 \ {k}) ∪ s2
let lemma_remove_union_no_mem (k: int) (s1 s2: FS.set int)
  : Lemma (requires ~(FS.mem k s2))
          (ensures FS.equal (FS.remove k (FS.union s1 s2))
                           (FS.union (FS.remove k s1) s2))
  = FS.all_finite_set_facts_lemma ()

// Helper lemma: if k ∉ s1, then (s1 ∪ s2) \ {k} = s1 ∪ (s2 \ {k})
let lemma_remove_union_no_mem_left (k: int) (s1 s2: FS.set int)
  : Lemma (requires ~(FS.mem k s1))
          (ensures FS.equal (FS.remove k (FS.union s1 s2))
                           (FS.union s1 (FS.remove k s2)))
  = FS.all_finite_set_facts_lemma ()

// Helper lemma: {x} \ {x} = ∅
let lemma_remove_singleton (x: int)
  : Lemma (FS.equal (FS.remove x (FS.singleton x)) FS.emptyset)
  = FS.all_finite_set_facts_lemma ()

// Helper lemma: if x ≠ y, then {x} \ {y} = {x}
let lemma_remove_singleton_diff (x y: int)
  : Lemma (requires x <> y)
          (ensures FS.equal (FS.remove y (FS.singleton x)) (FS.singleton x))
  = FS.all_finite_set_facts_lemma ()

// Helper lemma: prove set equality by extensionality
let lemma_set_equal_by_mem (s1 s2: FS.set int)
  : Lemma (requires (forall x. FS.mem x s1 <==> FS.mem x s2))
          (ensures FS.equal s1 s2)
  = FS.all_finite_set_facts_lemma ()

// Helper lemma: {x} ∪ (s \ {x}) = s when x ∈ s
let lemma_insert_remove_inverse (x: int) (s: FS.set int)
  : Lemma (requires FS.mem x s)
          (ensures FS.equal (FS.union (FS.singleton x) (FS.remove x s)) s)
  = FS.all_finite_set_facts_lemma ()

// Helper lemma: non-Leaf BST has a minimum
let rec bst_minimum_exists (t: bst)
  : Lemma (requires bst_valid t /\ t <> Leaf)
          (ensures bst_minimum t <> None)
  = match t with
    | Leaf -> ()
    | Node Leaf _ _ -> ()
    | Node left _ _ -> bst_minimum_exists left

#push-options "--fuel 1 --ifuel 1"

//SNIPPET_START: delete_key_set_lemma
val delete_key_set_lemma: t:bst -> k:int ->
  Lemma (requires bst_valid t /\ bst_search t k)
        (ensures FS.equal (key_set (bst_delete t k))
                          (FS.remove k (key_set t)))
        (decreases t)
//SNIPPET_END: delete_key_set_lemma

let rec delete_key_set_lemma t k =
  FS.all_finite_set_facts_lemma ();
  bst_search_correct t k;
  match t with
  | Leaf -> 
      // bst_search Leaf k = false, but precondition requires bst_search t k = true
      // This is a contradiction - the Leaf case is impossible
      // We need to assert False to discharge the postcondition
      assert (bst_search Leaf k = false);
      assert False
  | Node left key right ->
      bst_delete_valid t k;
      lemma_list_to_set_append (bst_inorder left) ([key] @ bst_inorder right);
      lemma_list_to_set_append [key] (bst_inorder right);
      lemma_list_to_set_singleton key;
      
      // Establish original structure: key_set(t) = key_set(left) ∪ {key} ∪ key_set(right)
      assert (FS.equal (key_set t)
                      (FS.union (key_set left) 
                               (FS.union (FS.singleton key) (key_set right))));
      
      if k < key then begin
        // Case 1: k < key, deletion recurses into left subtree
        delete_key_set_lemma left k;
        lemma_all_greater_implies_not_mem k key (bst_inorder right);
        lemma_list_to_set_mem k (bst_inorder right);
        
        // k is not in right subtree (since all elements in right > key > k)
        assert (~(FS.mem k (key_set right)));
        // k ≠ key since k < key
        assert (k <> key);
        lemma_remove_singleton_diff key k;
        assert (FS.equal (FS.remove k (FS.singleton key)) (FS.singleton key));
        
        // From IH: key_set(delete(left, k)) = key_set(left) \ {k}
        assert (FS.equal (key_set (bst_delete left k)) (FS.remove k (key_set left)));
        
        // Structure of result: delete(t, k) = Node (delete(left, k)) key right
        lemma_list_to_set_append (bst_inorder (bst_delete left k)) ([key] @ bst_inorder right);
        lemma_list_to_set_append [key] (bst_inorder right);
        assert (FS.equal (key_set (bst_delete t k))
                        (FS.union (key_set (bst_delete left k))
                                 (FS.union (FS.singleton key) (key_set right))));
        
        // Substitute IH
        assert (FS.equal (key_set (bst_delete t k))
                        (FS.union (FS.remove k (key_set left))
                                 (FS.union (FS.singleton key) (key_set right))));
        
        // Use lemma: (s1 \ {k}) ∪ s2 = (s1 ∪ s2) \ {k} when k ∉ s2
        lemma_remove_union_no_mem k (key_set left) (FS.union (FS.singleton key) (key_set right));
        assert (FS.equal (FS.union (FS.remove k (key_set left))
                                   (FS.union (FS.singleton key) (key_set right)))
                        (FS.remove k (FS.union (key_set left)
                                              (FS.union (FS.singleton key) (key_set right)))));
        
        // Conclude
        assert (FS.equal (key_set (bst_delete t k)) (FS.remove k (key_set t)))
        
      end else if k > key then begin
        // Case 2: k > key, deletion recurses into right subtree
        delete_key_set_lemma right k;
        lemma_all_less_implies_not_mem k key (bst_inorder left);
        lemma_list_to_set_mem k (bst_inorder left);
        
        // k is not in left subtree (since all elements in left < key < k)
        assert (~(FS.mem k (key_set left)));
        // k ≠ key since k > key
        assert (k <> key);
        lemma_remove_singleton_diff key k;
        
        // From IH: key_set(delete(right, k)) = key_set(right) \ {k}
        assert (FS.equal (key_set (bst_delete right k)) (FS.remove k (key_set right)));
        
        // Structure of result: delete(t, k) = Node left key (delete(right, k))
        lemma_list_to_set_append (bst_inorder left) ([key] @ bst_inorder (bst_delete right k));
        lemma_list_to_set_append [key] (bst_inorder (bst_delete right k));
        assert (FS.equal (key_set (bst_delete t k))
                        (FS.union (key_set left)
                                 (FS.union (FS.singleton key) (key_set (bst_delete right k)))));
        
        // Substitute IH
        assert (FS.equal (key_set (bst_delete t k))
                        (FS.union (key_set left)
                                 (FS.union (FS.singleton key) (FS.remove k (key_set right)))));
        
        // Use lemma: s1 ∪ (s2 \ {k}) = (s1 ∪ s2) \ {k} when k ∉ s1
        lemma_remove_union_no_mem_left k (FS.union (key_set left) (FS.singleton key)) (key_set right);
        assert (FS.equal (FS.union (FS.union (key_set left) (FS.singleton key))
                                   (FS.remove k (key_set right)))
                        (FS.remove k (FS.union (FS.union (key_set left) (FS.singleton key))
                                              (key_set right))));
        
        // Conclude using associativity
        assert (FS.equal (key_set (bst_delete t k)) (FS.remove k (key_set t)))
        
      end else begin
        // Case 3: k = key, delete the root
        assert (k = key);
        match left, right with
        | Leaf, Leaf -> 
            // Case 3a: No children - result is Leaf
            // Need: key_set(Leaf) = key_set(Node Leaf key Leaf) \ {key}
            //     = ({} ∪ {key} ∪ {}) \ {key} = {key} \ {key} = {}
            assert (key_set (bst_delete t k) == list_to_set []);
            assert (FS.equal (key_set (bst_delete t k)) FS.emptyset);
            lemma_remove_singleton key;
            assert (FS.equal (FS.remove key (FS.singleton key)) FS.emptyset);
            assert (FS.equal (key_set t) (FS.singleton key));
            assert (FS.equal (FS.remove k (key_set t)) FS.emptyset)
            
        | Leaf, _ ->
            // Case 3b: Only right child - result is right
            // Need: key_set(right) = key_set(Node Leaf key right) \ {key}
            //     = ({} ∪ {key} ∪ key_set(right)) \ {key}
            //     = key_set(right) ∪ {key} \ {key}
            //     Since key < all elements in right (from BST validity), key ∉ key_set(right)
            //     = key_set(right)
            assert (key_set left == list_to_set []);
            assert (FS.equal (key_set left) FS.emptyset);
            assert (key_set (bst_delete t k) == key_set right);
            
            // key ∉ key_set(right) because all elements in right > key
            // Since k = key and all_greater key (bst_inorder right), we have key ∉ right
            assert (all_greater key (bst_inorder right));
            lemma_all_greater_excludes_bound key (bst_inorder right);
            assert (~(mem key (bst_inorder right)));
            lemma_list_to_set_mem key (bst_inorder right);
            assert (~(FS.mem key (key_set right)));
            
            // key_set(t) = {key} ∪ key_set(right) since key_set(left) = {}
            assert (FS.equal (key_set t) (FS.union (FS.singleton key) (key_set right)));
            
            // ({key} ∪ key_set(right)) \ {key} = key_set(right) when key ∉ key_set(right)
            lemma_remove_union_no_mem k (FS.singleton key) (key_set right);
            lemma_remove_singleton key;
            assert (FS.equal (FS.remove k (key_set t)) (key_set right))
            
        | _, Leaf ->
            // Case 3c: Only left child - result is left
            // Need: key_set(left) = key_set(Node left key Leaf) \ {key}
            //     = (key_set(left) ∪ {key} ∪ {}) \ {key}
            //     Since key > all elements in left (from BST validity), key ∉ key_set(left)
            //     = key_set(left)
            assert (key_set right == list_to_set []);
            assert (FS.equal (key_set right) FS.emptyset);
            assert (key_set (bst_delete t k) == key_set left);
            
            // key ∉ key_set(left) because all elements in left < key
            lemma_all_less_excludes_bound key (bst_inorder left);
            lemma_list_to_set_mem key (bst_inorder left);
            assert (~(FS.mem key (key_set left)));
            
            // key_set(t) = key_set(left) ∪ {key} since key_set(right) = {}
            assert (FS.equal (key_set t) (FS.union (key_set left) (FS.singleton key)));
            
            // (key_set(left) ∪ {key}) \ {key} = key_set(left) when key ∉ key_set(left)
            lemma_remove_union_no_mem_left k (key_set left) (FS.singleton key);
            lemma_remove_singleton key;
            assert (FS.equal (FS.remove k (key_set t)) (key_set left))
            
        | _, _ ->
            // Case 3d: Two children - replace with successor from right
            (match bst_minimum right with
             | Some s ->
                 // Result: Node left s (delete(right, s))
                 // Need: key_set(Node left s (delete(right, s))) 
                 //     = key_set(Node left key right) \ {key}
                 
                 // s is the minimum of right, so s ∈ right
                 bst_minimum_in_tree right;
                 assert (mem s (bst_inorder right));
                 lemma_list_to_set_mem s (bst_inorder right);
                 assert (FS.mem s (key_set right));
                 
                 // s > key (all elements in right > key)
                 lemma_all_greater_implies_mem_greater key s (bst_inorder right);
                 assert (s > key);
                 assert (s <> key);
                 
                 // s > all elements in left (since key < s and all left < key)
                 bst_minimum_greater_than_left left right key;
                 assert (all_less s (bst_inorder left));
                 lemma_all_less_excludes_bound s (bst_inorder left);
                 assert (~(mem s (bst_inorder left)));
                 lemma_list_to_set_mem s (bst_inorder left);
                 assert (~(FS.mem s (key_set left)));
                 
                 // By induction: key_set(delete(right, s)) = key_set(right) \ {s}
                 // First, need to establish preconditions for recursion:
                 // bst_valid right is inherited from bst_valid t
                 // Need to show: bst_search right s = true
                 bst_minimum_in_tree right;
                 assert (mem s (bst_inorder right));
                 bst_search_correct right s;
                 assert (bst_search right s);
                 delete_key_set_lemma right s;
                 assert (FS.equal (key_set (bst_delete right s)) (FS.remove s (key_set right)));
                 
                 // Structure of result
                 lemma_list_to_set_append (bst_inorder left) ([s] @ bst_inorder (bst_delete right s));
                 lemma_list_to_set_append [s] (bst_inorder (bst_delete right s));
                 lemma_list_to_set_singleton s;
                 assert (FS.equal (key_set (bst_delete t k))
                                 (FS.union (key_set left)
                                          (FS.union (FS.singleton s) (key_set (bst_delete right s)))));
                 
                 // Substitute IH for delete(right, s)
                 assert (FS.equal (key_set (bst_delete t k))
                                 (FS.union (key_set left)
                                          (FS.union (FS.singleton s) (FS.remove s (key_set right)))));
                 
                 // Simplify: {s} ∪ (key_set(right) \ {s})
                 // Since s ∈ key_set(right), we have {s} ∪ (key_set(right) \ {s}) = key_set(right)
                 // This needs a helper lemma
                 lemma_insert_remove_inverse s (key_set right);
                 assert (FS.equal (FS.union (FS.singleton s) (FS.remove s (key_set right)))
                                 (key_set right));
                 
                 // So: key_set(delete(t, k)) = key_set(left) ∪ key_set(right)
                 assert (FS.equal (key_set (bst_delete t k))
                                 (FS.union (key_set left) (key_set right)));
                 
                 // Original: key_set(t) = key_set(left) ∪ {key} ∪ key_set(right)
                 // Need: key_set(left) ∪ key_set(right) = (key_set(left) ∪ {key} ∪ key_set(right)) \ {key}
                 // Since key ∉ left and key ∉ right, this is true
                 lemma_all_less_excludes_bound key (bst_inorder left);
                 assert (~(mem key (bst_inorder left)));
                 lemma_all_greater_excludes_bound key (bst_inorder right);
                 assert (~(mem key (bst_inorder right)));
                 lemma_list_to_set_mem key (bst_inorder left);
                 lemma_list_to_set_mem key (bst_inorder right);
                 assert (~(FS.mem key (key_set left)));
                 assert (~(FS.mem key (key_set right)));
                 
                 // Use: (s1 ∪ {k} ∪ s2) \ {k} = s1 ∪ s2 when k ∉ s1, s2
                 lemma_remove_union_no_mem_left k (key_set left) (FS.union (FS.singleton key) (key_set right));
                 lemma_remove_union_no_mem k (FS.singleton key) (key_set right);
                 lemma_remove_singleton key;
                 assert (FS.equal (FS.remove k (key_set t))
                                 (FS.union (key_set left) (key_set right)))
                 
             | None -> 
                 // Impossible case: right is not Leaf so minimum must exist
                 match right with
                 | Leaf -> ()
                 | Node _ _ _ -> 
                     // Derive contradiction: right is Node, so bst_minimum right must be Some
                     bst_minimum_exists right;
                     assert False)
      end

#pop-options
