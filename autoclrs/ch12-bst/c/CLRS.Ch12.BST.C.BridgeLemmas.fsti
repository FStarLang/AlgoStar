module CLRS.Ch12.BST.C.BridgeLemmas

(**
 * Bridge Lemmas: Connecting c2pulse C-level BST properties to F* specs.
 *
 * c2pulse arrays use Seq.seq (option Int32.t); the Impl.fsti specs use
 * Seq.seq int and Seq.seq bool.  This module bridges the gap:
 *
 *   1. seq_key / seq_vld: extract int/bool from option Int32.t sequences
 *   2. to_int_seq / to_bool_seq: full sequence conversions
 *   3. c_valid_bst: top-level BST validity predicate for C code
 *   4. well_formed_bst implies local ordering (for bst_minimum/maximum)
 *   5. Insert preserves c_valid_bst
 *   6. Search soundness / completeness bridges
 *)

open FStar.Seq
open FStar.Classical
open FStar.Mul
open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BSTArray.Predicates
open CLRS.Ch12.BSTArray.Refinement
module I32 = FStar.Int32

// ================================================================
// § 1. Extraction helpers: option Int32.t → int / bool
// ================================================================

(** Extract int value from option Int32.t (total, default 0 for None) *)
let seq_key (s: seq (option I32.t)) (i: nat) : int =
  if i < length s then
    match index s i with
    | Some v -> I32.v v
    | None -> 0
  else 0

(** Extract validity from option Int32.t (nonzero → true) *)
let seq_vld (s: seq (option I32.t)) (i: nat) : bool =
  if i < length s then
    match index s i with
    | Some v -> I32.v v <> 0
    | None -> false
  else false

(** Predicate: all elements in prefix are Some *)
let all_some (#a: Type) (s: seq (option a)) (len: nat) : prop =
  len <= length s /\
  (forall (i: nat). i < len ==> Some? (index s i))

(** Convert c2pulse option Int32.t sequence to int sequence *)
val to_int_seq (s: seq (option I32.t)) (len: nat{all_some s len})
  : Tot (r: seq int{
    length r == len /\
    (forall (i: nat). i < len ==> index r i == I32.v (Some?.v (index s i)))})

(** Convert c2pulse option Int32.t sequence to bool sequence (nonzero → true) *)
val to_bool_seq (s: seq (option I32.t)) (len: nat{all_some s len})
  : Tot (r: seq bool{
    length r == len /\
    (forall (i: nat). i < len ==> index r i == (I32.v (Some?.v (index s i)) <> 0))})

// ================================================================
// § 2. Fixed bounds for Int32 keys
// ================================================================

(** Lower bound: one below Int32 minimum *)
let bst_lo : int = FStar.Int.min_int 32 - 1

(** Upper bound: one above Int32 maximum *)
let bst_hi : int = FStar.Int.max_int 32 + 1

(** Any Int32 value is within (bst_lo, bst_hi) *)
val lemma_int32_in_bounds (v: I32.t)
  : Lemma (bst_lo < I32.v v /\ I32.v v < bst_hi)

// ================================================================
// § 3. c_valid_bst: top-level BST validity
// ================================================================

(** BST validity at c2pulse level: well_formed_bst with Int32 bounds *)
let c_valid_bst (keys valid: seq (option I32.t)) (cap: nat) : prop =
  all_some keys cap /\ all_some valid cap /\
  well_formed_bst (to_int_seq keys cap) (to_bool_seq valid cap) cap 0 bst_lo bst_hi

(** key_in_subtree at c2pulse level *)
let c_key_in_subtree (keys valid: seq (option I32.t)) (cap i: nat) (key: int) : prop =
  all_some keys cap /\ all_some valid cap /\
  key_in_subtree (to_int_seq keys cap) (to_bool_seq valid cap) cap i key

// ================================================================
// § 4. Sequence update lemmas
// ================================================================

(** Updating a position preserves all_some *)
val lemma_all_some_upd (#a: Type) (s: seq (option a)) (len: nat) (i: nat) (v: a)
  : Lemma
    (requires all_some s len /\ i < len)
    (ensures all_some (upd s i (Some v)) len)

(** to_int_seq after update at position i equals upd of to_int_seq *)
val lemma_to_int_seq_upd
  (s: seq (option I32.t)) (len: nat) (i: nat) (v: I32.t)
  : Lemma
    (requires all_some s len /\ i < len)
    (ensures (
      lemma_all_some_upd s len i v;
      Seq.equal (to_int_seq (upd s i (Some v)) len) (upd (to_int_seq s len) i (I32.v v))))

(** to_bool_seq after update at position i equals upd of to_bool_seq *)
val lemma_to_bool_seq_upd
  (s: seq (option I32.t)) (len: nat) (i: nat) (v: I32.t)
  : Lemma
    (requires all_some s len /\ i < len)
    (ensures (
      lemma_all_some_upd s len i v;
      Seq.equal (to_bool_seq (upd s i (Some v)) len) (upd (to_bool_seq s len) i (I32.v v <> 0))))

// ================================================================
// § 5. well_formed_bst implies local ordering (for minimum/maximum)
// ================================================================

(** well_formed_bst implies local left ordering for all valid descendants *)
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

(** well_formed_bst implies local right ordering for all valid descendants *)
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

(** c_valid_bst implies local left ordering (c2pulse level) *)
val c_valid_bst_local_left:
  keys:seq (option I32.t) -> valid:seq (option I32.t) -> cap:nat -> j:nat ->
  Lemma
    (requires
      c_valid_bst keys valid cap /\
      j < cap /\ seq_vld valid j /\
      2*j+1 < cap /\ seq_vld valid (2*j+1))
    (ensures seq_key keys (2*j+1) < seq_key keys j)

(** c_valid_bst implies local right ordering (c2pulse level) *)
val c_valid_bst_local_right:
  keys:seq (option I32.t) -> valid:seq (option I32.t) -> cap:nat -> j:nat ->
  Lemma
    (requires
      c_valid_bst keys valid cap /\
      j < cap /\ seq_vld valid j /\
      2*j+2 < cap /\ seq_vld valid (2*j+2))
    (ensures seq_key keys j < seq_key keys (2*j+2))

// ================================================================
// § 6. Insert preserves c_valid_bst
// ================================================================

(** Insert preserves well_formed_bst *)
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

// ================================================================
// § 7. Search bridges
// ================================================================

(** If key is in subtree, bst_search on abstraction agrees *)
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

(** If key is not in subtree, bst_search on abstraction returns false *)
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
