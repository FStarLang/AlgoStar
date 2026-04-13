module CLRS.Ch12.BST.C.BridgeLemmas

(**
 * Bridge Lemma Proofs
 *
 * Connects the c2pulse-level flat array BST properties (option Int32.t)
 * to the F* mathematical BST specifications (Prims.int, bool).
 *)

open FStar.Seq
open FStar.Classical
open FStar.Mul
open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BSTArray.Predicates
open CLRS.Ch12.BSTArray.Refinement
module I32 = FStar.Int32

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"

// ================================================================
// § 1. Extraction helpers
// ================================================================

let to_int_seq (s: seq (option I32.t)) (len: nat{all_some s len})
  : Tot (r: seq int{
    length r == len /\
    (forall (i: nat). i < len ==> index r i == I32.v (Some?.v (index s i)))})
  = Seq.init len (fun (i: nat{i < len}) -> (I32.v (Some?.v (index s i)) <: int))

let to_bool_seq (s: seq (option I32.t)) (len: nat{all_some s len})
  : Tot (r: seq bool{
    length r == len /\
    (forall (i: nat). i < len ==> index r i == (I32.v (Some?.v (index s i)) <> 0))})
  = Seq.init len (fun (i: nat{i < len}) -> (I32.v (Some?.v (index s i)) <> 0 <: bool))

// ================================================================
// § 2. Int32 bounds
// ================================================================

let lemma_int32_in_bounds (v: I32.t)
  : Lemma (bst_lo < I32.v v /\ I32.v v < bst_hi)
  = assert_norm (FStar.Int.min_int 32 = -2147483648);
    assert_norm (FStar.Int.max_int 32 = 2147483647)

// ================================================================
// § 3. Sequence update lemmas
// ================================================================

let lemma_all_some_upd (#a: Type) (s: seq (option a)) (len: nat) (i: nat) (v: a)
  : Lemma
    (requires all_some s len /\ i < len)
    (ensures all_some (upd s i (Some v)) len)
  = ()

#push-options "--z3rlimit 80"

let lemma_to_int_seq_upd
  (s: seq (option I32.t)) (len: nat) (i: nat) (v: I32.t)
  : Lemma
    (requires all_some s len /\ i < len)
    (ensures (
      lemma_all_some_upd s len i v;
      Seq.equal (to_int_seq (upd s i (Some v)) len) (upd (to_int_seq s len) i (I32.v v))))
  = lemma_all_some_upd s len i v;
    let s' = upd s i (Some v) in
    let ints = to_int_seq s len in
    let ints' = to_int_seq s' len in
    let expected = upd ints i (I32.v v) in
    assert (forall (j: nat). j < len ==> index ints' j == index expected j)

let lemma_to_bool_seq_upd
  (s: seq (option I32.t)) (len: nat) (i: nat) (v: I32.t)
  : Lemma
    (requires all_some s len /\ i < len)
    (ensures (
      lemma_all_some_upd s len i v;
      Seq.equal (to_bool_seq (upd s i (Some v)) len) (upd (to_bool_seq s len) i (I32.v v <> 0))))
  = lemma_all_some_upd s len i v;
    let s' = upd s i (Some v) in
    let bools = to_bool_seq s len in
    let bools' = to_bool_seq s' len in
    let expected = upd bools i (I32.v v <> 0) in
    assert (forall (j: nat). j < len ==> index bools' j == index expected j)

#pop-options

// ================================================================
// § 4. well_formed_bst implies local ordering
// ================================================================

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

// c2pulse-level wrappers
let c_valid_bst_local_left
  (keys: seq (option I32.t)) (valid: seq (option I32.t)) (cap: nat) (j: nat)
  : Lemma
    (requires
      c_valid_bst keys valid cap /\
      j < cap /\ seq_vld valid j /\
      2*j+1 < cap /\ seq_vld valid (2*j+1))
    (ensures seq_key keys (2*j+1) < seq_key keys j)
  = let ks = to_int_seq keys cap in
    let vs = to_bool_seq valid cap in
    let rec desc_of_root (n: nat)
      : Lemma (ensures is_desc_of 0 n)
              (decreases n)
      = if n = 0 then ()
        else desc_of_root ((n - 1) / 2)
    in
    desc_of_root j;
    wfb_implies_local_left ks vs cap 0 bst_lo bst_hi j

let c_valid_bst_local_right
  (keys: seq (option I32.t)) (valid: seq (option I32.t)) (cap: nat) (j: nat)
  : Lemma
    (requires
      c_valid_bst keys valid cap /\
      j < cap /\ seq_vld valid j /\
      2*j+2 < cap /\ seq_vld valid (2*j+2))
    (ensures seq_key keys j < seq_key keys (2*j+2))
  = let ks = to_int_seq keys cap in
    let vs = to_bool_seq valid cap in
    let rec desc_of_root (n: nat)
      : Lemma (ensures is_desc_of 0 n)
              (decreases n)
      = if n = 0 then ()
        else desc_of_root ((n - 1) / 2)
    in
    desc_of_root j;
    wfb_implies_local_right ks vs cap 0 bst_lo bst_hi j

// ================================================================
// § 5. Insert bridge
// ================================================================

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

// ================================================================
// § 6. Search bridges
// ================================================================

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

#pop-options
