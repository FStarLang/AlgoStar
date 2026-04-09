module CLRS.Ch12.BST.C.BridgeLemmas

(**
 * Bridge Lemmas: Connecting C-level BST properties to F* mathematical specs.
 *
 * The c2pulse-generated BST code uses flat array predicates:
 *   - Local left ordering:  forall j. keys[2*j+1] < keys[j]
 *   - Local right ordering: forall j. keys[j] < keys[2*j+2]
 *   - Soundness: search returns idx < cap ==> keys[idx] == key
 *
 * The F* mathematical spec (CLRS.Ch12.BST.Spec) uses:
 *   - bst_valid on inductive BST type
 *   - bst_search, bst_insert, bst_minimum, bst_maximum
 *
 * These bridge lemmas connect the two worlds, enabling composition
 * of verified C code with mathematical correctness proofs.
 *
 * Key lemmas:
 *   1. well_formed_bst implies local ordering (C precondition discharge)
 *   2. C search result connects to bst_search on abstraction
 *)

open FStar.Seq
open FStar.Classical
open FStar.Mul
open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BSTArray.Predicates
open CLRS.Ch12.BSTArray.Refinement

(** well_formed_bst implies local left ordering for all valid descendants.
    This discharges the bst_minimum precondition from C code. *)
val wfb_implies_local_left:
  keys:seq int -> valid:seq bool -> cap:nat -> i:nat ->
  lo:int -> hi:int -> j:nat ->
  Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      cap <= length keys /\ cap <= length valid /\
      is_desc_of i j /\
      j < cap /\ index valid j /\
      2*j+1 < cap /\ index valid (2*j+1))
    (ensures index keys (2*j+1) < index keys j)

(** well_formed_bst implies local right ordering for all valid descendants.
    This discharges the bst_maximum precondition from C code. *)
val wfb_implies_local_right:
  keys:seq int -> valid:seq bool -> cap:nat -> i:nat ->
  lo:int -> hi:int -> j:nat ->
  Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      cap <= length keys /\ cap <= length valid /\
      is_desc_of i j /\
      j < cap /\ index valid j /\
      2*j+2 < cap /\ index valid (2*j+2))
    (ensures index keys j < index keys (2*j+2))

(** If C search finds key at valid idx (its soundness postcondition),
    and the BST is well-formed, then bst_search on the abstraction agrees. *)
val c_search_sound_bridge:
  keys:seq int -> valid:seq bool -> cap:nat -> i:nat ->
  lo:int -> hi:int -> key:int ->
  Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      cap <= length keys /\ cap <= length valid /\
      lo < key /\ key < hi /\
      key_in_subtree keys valid cap i key)
    (ensures bst_search (array_to_bst keys valid cap i) key)

(** If key is not in the subtree (C search returned cap),
    then bst_search on the abstraction returns false. *)
val c_search_complete_bridge:
  keys:seq int -> valid:seq bool -> cap:nat -> i:nat ->
  lo:int -> hi:int -> key:int ->
  Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      cap <= length keys /\ cap <= length valid /\
      lo < key /\ key < hi /\
      ~(key_in_subtree keys valid cap i key))
    (ensures ~(bst_search (array_to_bst keys valid cap i) key))

(** Insert preserves well_formed_bst: connects C insert frame
    postcondition to the mathematical BST validity preservation. *)
val c_insert_preserves_wfb:
  keys:seq int -> valid:seq bool -> cap:nat -> i:nat ->
  lo:int -> hi:int -> key:int -> idx:nat ->
  Lemma
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
