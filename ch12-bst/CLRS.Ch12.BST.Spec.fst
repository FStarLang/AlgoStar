module CLRS.Ch12.BST.Spec

open FStar.Seq
open FStar.Classical
open FStar.Mul

(* ========================================================================
   Pure BST Predicates (copied from CLRS.Ch12.BST)
   ======================================================================== *)

// Helper lemma to prove that child indices fit
let child_indices_fit (cap: nat) (i: nat)
  : Lemma
    (requires cap < 32768 /\ i < cap)
    (ensures (
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      0 <= left /\ left < pow2 16 /\
      0 <= right /\ right < pow2 16
    ))
= // Since cap < 32768 and i < cap, we have i < 32768, so i <= 32767
  // But more precisely: i < cap <= 32767, so i <= 32766
  // Therefore: 2 * i + 2 <= 2 * 32766 + 2 = 65534
  // And 65534 < 65536 = pow2 16
  assert_norm (pow2 16 = 65536)

// Stronger BST property: all keys in subtree are bounded by lo and hi
let rec subtree_in_range 
  (keys: seq int) 
  (valid: seq bool) 
  (cap: nat) 
  (i: nat) 
  (lo hi: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then True
    else if not (index valid i) then True
    else 
      let k = index keys i in
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      lo < k /\ k < hi /\
      subtree_in_range keys valid cap left lo k /\
      subtree_in_range keys valid cap right k hi

// Key membership in subtree rooted at i
let rec key_in_subtree 
  (keys: seq int) 
  (valid: seq bool) 
  (cap: nat) 
  (i: nat) 
  (key: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = i < cap /\ i < length keys /\ i < length valid /\
    index valid i /\
    (index keys i == key \/
     key_in_subtree keys valid cap (2 * i + 1) key \/
     key_in_subtree keys valid cap (2 * i + 2) key)

// Lemma: If key is in a bounded subtree, it must be within the bounds
let rec lemma_key_in_bounded_subtree
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma 
    (requires subtree_in_range keys valid cap i lo hi /\ key_in_subtree keys valid cap i key)
    (ensures lo < key /\ key < hi)
    (decreases (if i < cap then cap - i else 0))
  = let left = 2 * i + 1 in
    let right = 2 * i + 2 in
    or_elim
      #(key_in_subtree keys valid cap left key)
      #(key_in_subtree keys valid cap right key)
      #(fun _ -> lo < key /\ key < hi)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap left lo (index keys i) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap right (index keys i) hi key)

// Lemma: If key < current_key and BST property holds, key can only be in left subtree
[@@"opaque_to_smt"]
let lemma_key_not_in_right_if_less
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires 
      subtree_in_range keys valid cap i lo hi /\
      i < cap /\ i < length keys /\ i < length valid /\
      index valid i /\
      key < index keys i /\
      key_in_subtree keys valid cap i key)
    (ensures key_in_subtree keys valid cap (2 * i + 1) key)
  = let k = index keys i in
    let right = 2 * i + 2 in
    or_elim
      #(key_in_subtree keys valid cap right key)
      #(~(key_in_subtree keys valid cap right key))
      #(fun _ -> key_in_subtree keys valid cap (2 * i + 1) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap right k hi key)
      (fun _ -> ())

// Lemma: If key > current_key and BST property holds, key can only be in right subtree  
[@@"opaque_to_smt"]
let lemma_key_not_in_left_if_greater
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires 
      subtree_in_range keys valid cap i lo hi /\
      i < cap /\ i < length keys /\ i < length valid /\
      index valid i /\
      key > index keys i /\
      key_in_subtree keys valid cap i key)
    (ensures key_in_subtree keys valid cap (2 * i + 2) key)
  = let k = index keys i in
    let left = 2 * i + 1 in
    or_elim
      #(key_in_subtree keys valid cap left key)
      #(~(key_in_subtree keys valid cap left key))
      #(fun _ -> key_in_subtree keys valid cap (2 * i + 2) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap left lo k key)
      (fun _ -> ())

(* ========================================================================
   Pure BST Search Function
   ======================================================================== *)

let rec pure_search 
  (keys: seq int) 
  (valid: seq bool) 
  (cap: nat) 
  (i: nat) 
  (key: int) 
  : Tot (option nat) (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then None
    else if not (index valid i) then None
    else let k = index keys i in
         if key = k then Some i
         else if key < k then pure_search keys valid cap (2*i+1) key
         else pure_search keys valid cap (2*i+2) key

(* ========================================================================
   Soundness Proof: If search returns Some idx, then keys[idx] == key
   ======================================================================== *)

//SNIPPET_START: pure_search_sound
let rec pure_search_sound
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (key: int)
  : Lemma
    (requires Some? (pure_search keys valid cap i key))
    (ensures (
      let idx = Some?.v (pure_search keys valid cap i key) in
      idx < length keys /\
      idx < length valid /\
      index valid idx /\
      index keys idx == key
    ))
    (decreases (if i < cap then cap - i else 0))
//SNIPPET_END: pure_search_sound
  = // Base cases: if i >= cap or out of bounds or not valid, result is None
    // So we must be in the recursive case where index valid i
    if i >= cap || i >= length keys || i >= length valid then ()
    else if not (index valid i) then ()
    else 
      let k = index keys i in
      if key = k then ()  // Result is Some i, and keys[i] == key by definition
      else if key < k then 
        pure_search_sound keys valid cap (2*i+1) key
      else 
        pure_search_sound keys valid cap (2*i+2) key

(* ========================================================================
   Completeness Proof: If search returns None and tree is ordered,
                       then key is not in the subtree
   ======================================================================== *)

//SNIPPET_START: pure_search_complete
let rec pure_search_complete
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires 
      subtree_in_range keys valid cap i lo hi /\
      None? (pure_search keys valid cap i key))
    (ensures ~(key_in_subtree keys valid cap i key))
    (decreases (if i < cap then cap - i else 0))
//SNIPPET_END: pure_search_complete
  = // If pure_search returns None, we need to show key is not in the subtree
    
    // Case 1: i >= cap or out of bounds
    if i >= cap || i >= length keys || i >= length valid then ()
    
    // Case 2: not valid[i]
    else if not (index valid i) then ()
    
    // Case 3: valid[i] is true
    else 
      let k = index keys i in
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      
      // We know pure_search returned None, so key != k
      // and both left and right searches returned None
      
      if key = k then ()  // Contradiction: search would return Some i
      else if key < k then begin
        // Search went left and returned None
        pure_search_complete keys valid cap left lo k key;
        
        // Now we need to prove key is not in the subtree at i
        // key_in_subtree i key means: key == k \/ key in left \/ key in right
        // We know key != k
        // We proved key not in left
        // We need to show key not in right
        
        // If key were in right, then by lemma_key_in_bounded_subtree,
        // we'd have k < key < hi
        // But we know key < k, contradiction
        
        // Use proof by contradiction
        let prove_not_in_right () : Lemma (~(key_in_subtree keys valid cap right key)) =
          or_elim
            #(key_in_subtree keys valid cap right key)
            #(~(key_in_subtree keys valid cap right key))
            #(fun _ -> ~(key_in_subtree keys valid cap right key))
            (fun _ -> 
              // If key in right subtree:
              lemma_key_in_bounded_subtree keys valid cap right k hi key;
              // This proves k < key, contradicting key < k
              ()
            )
            (fun _ -> ())
        in
        prove_not_in_right ();
        
        // Now prove key not in subtree at i
        let prove_not_at_i () : Lemma (~(key_in_subtree keys valid cap i key)) =
          or_elim
            #(key_in_subtree keys valid cap i key)
            #(~(key_in_subtree keys valid cap i key))
            #(fun _ -> ~(key_in_subtree keys valid cap i key))
            (fun _ -> 
              // If key in subtree at i, then by definition:
              // key == k \/ key in left \/ key in right
              // But key != k, key not in left, key not in right
              // This is a contradiction
              ()
            )
            (fun _ -> ())
        in
        prove_not_at_i ()
      end
      else begin
        // key > k, search went right and returned None
        pure_search_complete keys valid cap right k hi key;
        
        // Similar reasoning: prove key not in left
        let prove_not_in_left () : Lemma (~(key_in_subtree keys valid cap left key)) =
          or_elim
            #(key_in_subtree keys valid cap left key)
            #(~(key_in_subtree keys valid cap left key))
            #(fun _ -> ~(key_in_subtree keys valid cap left key))
            (fun _ -> 
              // If key in left subtree:
              lemma_key_in_bounded_subtree keys valid cap left lo k key;
              // This proves key < k, contradicting key > k
              ()
            )
            (fun _ -> ())
        in
        prove_not_in_left ();
        
        // Now prove key not in subtree at i
        let prove_not_at_i () : Lemma (~(key_in_subtree keys valid cap i key)) =
          or_elim
            #(key_in_subtree keys valid cap i key)
            #(~(key_in_subtree keys valid cap i key))
            #(fun _ -> ~(key_in_subtree keys valid cap i key))
            (fun _ -> ())
            (fun _ -> ())
        in
        prove_not_at_i ()
      end

(* ========================================================================
   Convenience lemma: Completeness starting from root
   ======================================================================== *)

let pure_search_complete_at_root
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires 
      subtree_in_range keys valid cap 0 lo hi /\
      None? (pure_search keys valid cap 0 key))
    (ensures ~(key_in_subtree keys valid cap 0 key))
  = pure_search_complete keys valid cap 0 lo hi key

(* ========================================================================
   Pure BST Insert Function
   ======================================================================== *)

// Walk the BST to find the insertion point for key
let rec pure_insert 
  (keys: seq int) 
  (valid: seq bool) 
  (cap: nat) 
  (i: nat) 
  (key: int) 
  : Tot (option nat) (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then None
    else if not (index valid i) then Some i  // found empty slot
    else let k = index keys i in
         if key = k then None  // already exists
         else if key < k then pure_insert keys valid cap (2*i+1) key
         else pure_insert keys valid cap (2*i+2) key

(* ========================================================================
   Soundness: If pure_insert returns Some idx, the slot is empty
   ======================================================================== *)

//SNIPPET_START: pure_insert_sound
let rec pure_insert_sound
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (key: int)
  : Lemma
    (requires Some? (pure_insert keys valid cap i key))
    (ensures (
      let idx = Some?.v (pure_insert keys valid cap i key) in
      idx < cap /\
      idx < length keys /\
      idx < length valid /\
      index valid idx == false
    ))
    (decreases (if i < cap then cap - i else 0))
//SNIPPET_END: pure_insert_sound
  = if i >= cap || i >= length keys || i >= length valid then ()
    else if not (index valid i) then ()
    else 
      let k = index keys i in
      if key = k then ()
      else if key < k then 
        pure_insert_sound keys valid cap (2*i+1) key
      else 
        pure_insert_sound keys valid cap (2*i+2) key

(* ========================================================================
   Completeness: Old keys are preserved after insertion
   ======================================================================== *)

//SNIPPET_START: pure_insert_complete
let rec pure_insert_complete
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (key: int)
  (old_key: int)
  : Lemma
    (requires 
      Some? (pure_insert keys valid cap i key) /\
      key_in_subtree keys valid cap i old_key)
    (ensures (
      let idx = Some?.v (pure_insert keys valid cap i key) in
      idx < length keys /\ idx < length valid /\
      key_in_subtree (upd keys idx key) (upd valid idx true) cap i old_key
    ))
    (decreases (if i < cap then cap - i else 0))
//SNIPPET_END: pure_insert_complete
  = if i >= cap || i >= length keys || i >= length valid then ()
    else if not (index valid i) then ()  // key_in_subtree requires valid[i], contradiction
    else begin
      let k = index keys i in
      let idx = Some?.v (pure_insert keys valid cap i key) in
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      pure_insert_sound keys valid cap i key;
      // idx is the insertion point; old key is at a different (valid) node
      // i is valid and i != idx (since valid[idx] is false but valid[i] is true)
      assert (index valid idx == false);
      assert (index valid i == true);
      assert (i <> idx);
      // keys'[i] == keys[i] and valid'[i] == valid[i] since i != idx
      assert (index (upd keys idx key) i == index keys i);
      assert (index (upd valid idx true) i == index valid i);
      if key = k then ()
      else if key < k then begin
        // pure_insert recurses left
        or_elim
          #(key_in_subtree keys valid cap left old_key)
          #(key_in_subtree keys valid cap right old_key)
          #(fun _ -> key_in_subtree (upd keys idx key) (upd valid idx true) cap i old_key)
          (fun _ -> 
            pure_insert_complete keys valid cap left key old_key)
          (fun _ ->
            // old_key is in right subtree, which doesn't contain idx (insert goes left)
            // Need: key_in_subtree keys' valid' cap right old_key
            // idx is in the left subtree path, so right subtree is unchanged
            lemma_insert_preserves_other_subtree keys valid cap right idx key old_key)
      end
      else begin
        // pure_insert recurses right
        or_elim
          #(key_in_subtree keys valid cap left old_key)
          #(key_in_subtree keys valid cap right old_key)
          #(fun _ -> key_in_subtree (upd keys idx key) (upd valid idx true) cap i old_key)
          (fun _ -> 
            lemma_insert_preserves_other_subtree keys valid cap left idx key old_key)
          (fun _ ->
            pure_insert_complete keys valid cap right key old_key)
      end
    end

// Helper: inserting at idx preserves key_in_subtree for subtrees not containing idx
and lemma_insert_preserves_other_subtree
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (root: nat)
  (idx: nat)
  (new_key: int)
  (old_key: int)
  : Lemma
    (requires
      idx < length keys /\ idx < length valid /\
      index valid idx == false /\
      key_in_subtree keys valid cap root old_key)
    (ensures
      key_in_subtree (upd keys idx new_key) (upd valid idx true) cap root old_key)
    (decreases (if root < cap then cap - root else 0))
  = if root >= cap || root >= length keys || root >= length valid then ()
    else begin
      // key_in_subtree requires valid[root] == true, so root != idx
      assert (index valid root == true);
      assert (root <> idx);
      assert (index (upd keys idx new_key) root == index keys root);
      assert (index (upd valid idx true) root == index valid root);
      let left = 2 * root + 1 in
      let right = 2 * root + 2 in
      or_elim
        #(key_in_subtree keys valid cap left old_key)
        #(key_in_subtree keys valid cap right old_key)
        #(fun _ -> key_in_subtree (upd keys idx new_key) (upd valid idx true) cap root old_key)
        (fun _ -> lemma_insert_preserves_other_subtree keys valid cap left idx new_key old_key)
        (fun _ -> lemma_insert_preserves_other_subtree keys valid cap right idx new_key old_key)
    end
