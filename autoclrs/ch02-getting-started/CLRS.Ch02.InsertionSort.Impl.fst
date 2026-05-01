(*
   Insertion Sort - Verified implementation in Pulse

   Proves:
   1. The result is sorted
   2. The result is a permutation of the input
   3. O(n^2) comparison complexity: at most n*(n-1)/2 comparisons

   Uses GhostReference.ref nat for the tick counter -- fully erased at runtime.

   NO admits. NO assumes.
*)

module CLRS.Ch02.InsertionSort.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open CLRS.Common.SortSpec
open CLRS.Ch02.InsertionSort.Spec
open CLRS.Ch02.InsertionSort.Lemmas
open CLRS.Common.Complexity

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

//SNIPPET_START: insertion_sort_sig
fn insertion_sort
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0
  requires pure (
    SZ.v len == Seq.length s0 /\
    Seq.length s0 <= A.length a
  )
  ensures exists* s (cf: nat). A.pts_to a s ** GR.pts_to ctr cf ** pure (
    Seq.length s == Seq.length s0 /\
    sorted s /\
    permutation s0 s /\
    complexity_bounded cf (reveal c0) (SZ.v len)
  )
//SNIPPET_END: insertion_sort_sig
{
  if (len = 0sz) {
    singl_sorted s0;
    permutation_refl s0;
    ()
  } else {
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
      vc <= reveal c0 + op_Star (SZ.v vj) (SZ.v vj - 1) / 2
    )
  decreases (SZ.v len `Prims.op_Subtraction` SZ.v !j)
  {
    let vj = !j;
    with s_outer. assert (A.pts_to a s_outer);
    let key = a.(vj);
    
    let mut i: SZ.t = vj;
    let mut cont: bool = true;
    
    // Initial comparison: tick for the first comparison
    if (vj >^ 0sz) {
      let prev = a.(vj - 1sz);
      cont := (Prims.op_GreaterThan prev key);
      tick ctr;
    } else {
      cont := false;
    };
    
    // Inner loop: each iteration swaps, decrements i, and makes a comparison (with tick).
    while (!cont)
    invariant exists* vi vcont s_inner (vc_inner : nat).
      R.pts_to i vi **
      R.pts_to cont vcont **
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
        vc_inner <= reveal c0 + op_Star (SZ.v vj) (SZ.v vj - 1) / 2 + SZ.v vj + 1 - SZ.v vi /\
        (not vcont ==> vc_inner <= reveal c0 + op_Star (SZ.v vj) (SZ.v vj - 1) / 2 + SZ.v vj)
      )
    decreases (SZ.v !i)
    {
      let vi = !i;
      with s_pre. assert (A.pts_to a s_pre);
      
      let val_prev = a.(vi - 1sz);
      let val_curr = a.(vi);
      
      // Swap-based insertion: CLRS shifts elements right and inserts key once,
      // but this variant swaps adjacent elements to bubble key leftward.
      // Comparison count is identical; write count is 2x CLRS's shift variant.
      a.(vi - 1sz) <- val_curr;
      a.(vi) <- val_prev;
      
      with s_post. assert (A.pts_to a s_post);
      swap_is_permutation s_pre (SZ.v vi - 1) (SZ.v vi);
      
      i := vi - 1sz;
      let new_i = vi - 1sz;
      
      if (new_i >^ 0sz) {
        let new_prev = a.(new_i - 1sz);
        cont := (Prims.op_GreaterThan new_prev key);
        // Tick for inner comparison
        tick ctr;
      } else {
        cont := false;
      };
      
      ()
    };
    
    // After inner loop
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
}

#pop-options
