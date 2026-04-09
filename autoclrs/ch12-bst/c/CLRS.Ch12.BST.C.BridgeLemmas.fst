module CLRS.Ch12.BST.C.BridgeLemmas

(**
 * Bridge Lemma Proofs
 *
 * Connects the c2pulse-level flat array BST properties
 * to the F* mathematical BST specifications.
 *)

open FStar.Seq
open FStar.Classical
open FStar.Mul
open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BSTArray.Predicates
open CLRS.Ch12.BSTArray.Refinement

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"

(* ================================================================
   § 1. well_formed_bst implies local ordering
   ================================================================ *)

let rec wfb_implies_local_left
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat)
  (lo hi: int) (j: nat)
  : Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      cap <= length keys /\ cap <= length valid /\
      is_desc_of i j /\
      j < cap /\ index valid j /\
      2*j+1 < cap /\ index valid (2*j+1))
    (ensures index keys (2*j+1) < index keys j)
    (decreases (if i < cap then cap - i else 0))
  = if i = j then ()
    else begin
      lemma_desc_of_ge i j;
      if not (index valid i) then
        lemma_sai_desc valid cap i j
      else begin
        let k = index keys i in
        lemma_desc_split i j;
        if is_desc_of (2*i+1) j then
          wfb_implies_local_left keys valid cap (2*i+1) lo k j
        else
          wfb_implies_local_left keys valid cap (2*i+2) k hi j
      end
    end

let rec wfb_implies_local_right
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat)
  (lo hi: int) (j: nat)
  : Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      cap <= length keys /\ cap <= length valid /\
      is_desc_of i j /\
      j < cap /\ index valid j /\
      2*j+2 < cap /\ index valid (2*j+2))
    (ensures index keys j < index keys (2*j+2))
    (decreases (if i < cap then cap - i else 0))
  = if i = j then ()
    else begin
      lemma_desc_of_ge i j;
      if not (index valid i) then
        lemma_sai_desc valid cap i j
      else begin
        let k = index keys i in
        lemma_desc_split i j;
        if is_desc_of (2*i+1) j then
          wfb_implies_local_right keys valid cap (2*i+1) lo k j
        else
          wfb_implies_local_right keys valid cap (2*i+2) k hi j
      end
    end

(* ================================================================
   § 2. C search result connects to pure spec
   ================================================================ *)

let c_search_sound_bridge
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat)
  (lo hi: int) (key: int)
  : Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      cap <= length keys /\ cap <= length valid /\
      lo < key /\ key < hi /\
      key_in_subtree keys valid cap i key)
    (ensures bst_search (array_to_bst keys valid cap i) key)
  = lemma_well_formed_implies_sir keys valid cap i lo hi;
    lemma_search_refinement keys valid cap i lo hi key

let c_search_complete_bridge
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat)
  (lo hi: int) (key: int)
  : Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      cap <= length keys /\ cap <= length valid /\
      lo < key /\ key < hi /\
      ~(key_in_subtree keys valid cap i key))
    (ensures ~(bst_search (array_to_bst keys valid cap i) key))
  = lemma_well_formed_implies_sir keys valid cap i lo hi;
    lemma_search_refinement keys valid cap i lo hi key

(* ================================================================
   § 3. Insert preserves well_formed_bst
   ================================================================ *)

let c_insert_preserves_wfb
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat)
  (lo hi: int) (key: int) (idx: nat)
  : Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      length keys == length valid /\ length keys >= cap /\
      lo < key /\ key < hi /\
      idx < cap /\ idx < length keys /\ idx < length valid /\
      index valid idx == false /\
      is_desc_of i idx /\
      bst_search_reaches keys valid cap i idx key)
    (ensures
      well_formed_bst (upd keys idx key) (upd valid idx true) cap i lo hi)
  = lemma_insert_wfb keys valid cap i lo hi idx key

#pop-options
