(*
   Insertion Sort with Complexity Bound

   Proves O(n²) comparison complexity for insertion sort.
   Specifically: at most n*(n-1)/2 comparisons for an array of length n.

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each comparison gets one ghost tick (one at a time).
   Both the initial comparison and every inner loop comparison are ticked.

   Also proves functional correctness (sorted + permutation).

   NO admits. NO assumes.
*)

module CLRS.Ch02.InsertionSort.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open CLRS.Common.SortSpec

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Classical = FStar.Classical

//SNIPPET_START: ghost_tick
// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}
//SNIPPET_END: ghost_tick

// ========== Sortedness lemmas ==========

let lemma_prefix_le_key
  (s s_outer: Seq.seq int) (vi vj: nat) (key: int)
  : Lemma
    (requires
      vi <= vj /\ vj < Seq.length s /\ Seq.length s == Seq.length s_outer /\
      prefix_sorted s_outer vj /\
      prefix_sorted s vi /\
      (forall (k: nat). k < vi ==> Seq.index s k == Seq.index s_outer k) /\
      (forall (k: nat). k + 1 == vi ==> Seq.index s_outer k <= key))
    (ensures forall (k: nat). k < vi ==> Seq.index s k <= key)
  = if vi = 0 then ()
    else
      let pred = vi - 1 in
      assert (pred + 1 == vi);
      assert (Seq.index s_outer pred <= key);
      assert (forall (k: nat). k < vi ==> k <= pred);
      assert (forall (k: nat). k <= pred /\ pred < vj ==> Seq.index s_outer k <= Seq.index s_outer pred);
      ()

let lemma_combine_sorted_regions
  (s: Seq.seq int) (vi vj: nat) (key: int)
  : Lemma
    (requires vi <= vj /\ vj < Seq.length s /\
      prefix_sorted s vi /\
      Seq.index s vi == key /\
      (forall (k: nat). k < vi ==> Seq.index s k <= key) /\
      (forall (k: nat). vi < k /\ k <= vj ==> Seq.index s k > key) /\
      (forall (k1 k2: nat). vi < k1 /\ k1 <= k2 /\ k2 <= vj ==>
        Seq.index s k1 <= Seq.index s k2))
    (ensures prefix_sorted s (vj + 1))
  = ()

// ========== Complexity arithmetic helper ==========

// vj*(vj-1)/2 + vj = (vj+1)*vj/2
let lemma_triangle_step (vj: nat)
  : Lemma (requires vj >= 1)
          (ensures op_Multiply vj (vj - 1) / 2 + vj == op_Multiply (vj + 1) vj / 2)
  = assert (op_Multiply vj (vj - 1) + op_Multiply 2 vj == op_Multiply vj (vj + 1))

// ========== Main Algorithm with Complexity ==========

//SNIPPET_START: complexity_bound
// Complexity bound predicate (avoids BoundedIntegers issues in Pulse ensures)
let complexity_bounded (cf c0: nat) (n: nat) : prop =
  cf >= c0 /\
  cf - c0 <= op_Multiply n (n - 1) / 2
//SNIPPET_END: complexity_bound

//SNIPPET_START: insertion_sort_complexity_sig
fn insertion_sort_complexity
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0
  requires pure (
    SZ.v len == Seq.length s0 /\
    Seq.length s0 <= A.length a /\
    SZ.v len > 0
  )
  ensures exists* s (cf: nat). A.pts_to a s ** GR.pts_to ctr cf ** pure (
    Seq.length s == Seq.length s0 /\
    sorted s /\
    permutation s0 s /\
    complexity_bounded cf (reveal c0) (SZ.v len)
  )
//SNIPPET_END: insertion_sort_complexity_sig
{
  let mut j: SZ.t = 1sz;
  
  while (!j <^ len)
  invariant exists* vj s (vc : nat).
    R.pts_to j vj **
    A.pts_to a s **
    GR.pts_to ctr vc **
    pure (
      SZ.v vj > 0 /\
      SZ.v vj <= SZ.v len /\
      Seq.length s == Seq.length s0 /\
      Seq.length s <= A.length a /\
      permutation s0 s /\
      prefix_sorted s (SZ.v vj) /\
      // Complexity: comparisons so far <= vj*(vj-1)/2
      vc >= reveal c0 /\
      vc <= reveal c0 + op_Multiply (SZ.v vj) (SZ.v vj - 1) / 2
    )
  {
    let vj = !j;
    with s_outer. assert (A.pts_to a s_outer);
    let key = a.(vj);
    
    let mut i: SZ.t = vj;
    let mut continue: bool = true;
    
    // Initial comparison: tick for the first comparison
    if (vj >^ 0sz) {
      let prev = a.(vj - 1sz);
      continue := (prev > key);
      tick ctr;
    } else {
      continue := false;
    };
    
    // Inner loop: each iteration swaps, decrements i, and makes a comparison (with tick).
    // Invariant tracks vc + vi <= vj*(vj-1)/2 + vj + 1 (sum invariant).
    // At exit (not continue), vc <= vj*(vj-1)/2 + vj (tight bound).
    while (!continue)
    invariant exists* vi vcont s_inner (vc_inner : nat).
      R.pts_to i vi **
      R.pts_to continue vcont **
      R.pts_to j vj **
      A.pts_to a s_inner **
      GR.pts_to ctr vc_inner **
      pure (
        SZ.v vi <= SZ.v vj /\
        SZ.v vj < SZ.v len /\
        Seq.length s_inner == Seq.length s0 /\
        Seq.length s_inner <= A.length a /\
        permutation s_outer s_inner /\
        Seq.index s_inner (SZ.v vi) == key /\
        (vcont ==> (SZ.v vi > 0 /\ Seq.index s_inner (SZ.v vi - 1) > key)) /\
        ((not vcont /\ SZ.v vi > 0) ==> Seq.index s_inner (SZ.v vi - 1) <= key) /\
        prefix_sorted s_inner (SZ.v vi) /\
        (forall (k: nat). k < SZ.v vi ==> Seq.index s_inner k == Seq.index s_outer k) /\
        (forall (k: nat). SZ.v vi < k /\ k <= SZ.v vj ==> Seq.index s_inner k > key) /\
        (forall (k1 k2: nat). SZ.v vi < k1 /\ k1 <= k2 /\ k2 <= SZ.v vj ==>
          Seq.index s_inner k1 <= Seq.index s_inner k2) /\
        (forall (k1 k2: nat). k1 < SZ.v vi /\ SZ.v vi < k2 /\ k2 <= SZ.v vj ==>
          Seq.index s_inner k1 <= Seq.index s_inner k2) /\
        // Complexity: vc + vi bounded
        vc_inner >= reveal c0 /\
        vc_inner <= reveal c0 + op_Multiply (SZ.v vj) (SZ.v vj - 1) / 2 + SZ.v vj + 1 - SZ.v vi /\
        (not vcont ==> vc_inner <= reveal c0 + op_Multiply (SZ.v vj) (SZ.v vj - 1) / 2 + SZ.v vj)
      )
    {
      let vi = !i;
      with s_pre. assert (A.pts_to a s_pre);
      
      let val_prev = a.(vi - 1sz);
      let val_curr = a.(vi);
      
      a.(vi - 1sz) <- val_curr;
      a.(vi) <- val_prev;
      
      with s_post. assert (A.pts_to a s_post);
      swap_is_permutation s_pre (SZ.v vi - 1) (SZ.v vi);
      
      i := vi - 1sz;
      let new_i = vi - 1sz;
      
      if (new_i >^ 0sz) {
        let new_prev = a.(new_i - 1sz);
        continue := (new_prev > key);
        // Tick for inner comparison
        tick ctr;
      } else {
        continue := false;
      };
      
      ()
    };
    
    // After inner loop: not continue, so vc <= vj*(vj-1)/2 + vj
    with s_after. assert (A.pts_to a s_after);
    let vi_final = !i;
    
    assert (pure (forall (k: nat). k + 1 == SZ.v vi_final ==> Seq.index s_outer k <= key));
    
    lemma_prefix_le_key s_after s_outer (SZ.v vi_final) (SZ.v vj) key;
    lemma_combine_sorted_regions s_after (SZ.v vi_final) (SZ.v vj) key;
    
    // Complexity: vc <= vj*(vj-1)/2 + vj = (vj+1)*vj/2
    lemma_triangle_step (SZ.v vj);
    
    j := vj + 1sz;
  };
  
  with s_final. assert (A.pts_to a s_final);
  assert (pure (prefix_sorted s_final (Seq.length s0)));
  ()
}
