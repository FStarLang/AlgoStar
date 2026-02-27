(*
   Simultaneous Min/Max Finding - Verified implementation in Pulse
   
   Implements simultaneous finding of both minimum and maximum of an array.
   
   Two implementations:
   1. Simple linear scan (2(n-1) comparisons)
   2. CLRS Section 9.1 pair-processing (⌊3n/2⌋ comparisons)
      Process elements in pairs, compare pair first, then compare smaller
      with running min and larger with running max.
   
   Both versions have complexity-tracked variants that prove their
   comparison bounds using ghost tick counters.
   
   Proves:
   1. Returns correct minimum and maximum
   2. Simple version: exactly 2(n-1) comparisons
   3. Pair version: at most ⌊3n/2⌋ comparisons
   
   NO admits. NO assumes.
*)

module CLRS.Ch09.SimultaneousMinMax
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Ghost tick for comparisons ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)
let add_nat (n: erased nat) (k: nat) : erased nat = hide (Prims.op_Addition (reveal n) k)

let add_nat_reveal (n: erased nat) (k: nat)
  : Lemma (reveal (add_nat n k) == reveal n + k)
    [SMTPat (add_nat n k)]
  = ()

let incr_nat_reveal (n: erased nat)
  : Lemma (reveal (incr_nat n) == reveal n + 1)
    [SMTPat (incr_nat n)]
  = ()

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

ghost
fn add_ticks (ctr: GR.ref nat) (#n: erased nat) (k: nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (add_nat n k)
{
  GR.(ctr := add_nat n k)
}

// ========== Result type ==========

noeq
type minmax_result = {
  min_val: int;
  max_val: int;
}

// ========== Simple linear scan version (without complexity tracking) ==========

//SNIPPET_START: find_minmax
fn find_minmax
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a #p s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    SZ.v len >= 1 /\
    SZ.v len == A.length a
  )
  returns result: minmax_result
  ensures A.pts_to a #p s0 ** pure (
    // min_val is in the array and is minimum
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
    // max_val is in the array and is maximum
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k)
  )
//SNIPPET_END: find_minmax
{
  // Initialize from first element
  let v0 = a.(0sz);
  let mut min: int = v0;
  let mut max: int = v0;
  
  // Scan remaining elements
  let mut i: SZ.t = 1sz;
  
  while (!i <^ len)
  invariant exists* vi vmin vmax.
    R.pts_to i vi **
    R.pts_to min vmin **
    R.pts_to max vmax **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v len /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmin) /\
      (forall (k:nat). k < SZ.v vi ==> vmin <= Seq.index s0 k) /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmax) /\
      (forall (k:nat). k < SZ.v vi ==> vmax >= Seq.index s0 k)
    )
  {
    let vi = !i;
    let elem = a.(vi);
    let vmin = !min;
    let vmax = !max;
    
    if (elem < vmin) {
      min := elem;
    };
    
    if (elem > vmax) {
      max := elem;
    };
    
    i := vi + 1sz;
  };
  
  let final_min = !min;
  let final_max = !max;
  
  { min_val = final_min; max_val = final_max }
}

// ========== CLRS pair-processing version (⌈3n/2⌉ - 2 comparisons) ==========

// Process elements in pairs: compare pair first, then compare smaller with
// running min and larger with running max. This gives 3 comparisons per 2
// elements instead of 2 per element.

#push-options "--z3rlimit 50 --ifuel 2 --fuel 2"
//SNIPPET_START: find_minmax_pairs
fn find_minmax_pairs
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a #p s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    SZ.v len >= 1 /\
    SZ.v len == A.length a
  )
  returns result: minmax_result
  ensures A.pts_to a #p s0 ** pure (
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k)
  )
//SNIPPET_END: find_minmax_pairs
{
  let v0 = a.(0sz);
  let mut min_ref: int = v0;
  let mut max_ref: int = v0;
  let mut i: SZ.t = 1sz;

  // For n >= 2, initialize from first pair (1 comparison)
  if (len >=^ 2sz) {
    let v1 = a.(1sz);
    if (v0 <= v1) {
      max_ref := v1;
    } else {
      min_ref := v1;
    };
    i := 2sz;
  };

  // Process remaining elements in pairs (3 comparisons per pair)
  let len_m1 = len -^ 1sz;
  while (
    let vi = !i;
    vi <^ len_m1
  )
  invariant exists* vi vmin vmax.
    R.pts_to i vi **
    R.pts_to min_ref vmin **
    R.pts_to max_ref vmax **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v len /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmin) /\
      (forall (k:nat). k < SZ.v vi ==> vmin <= Seq.index s0 k) /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmax) /\
      (forall (k:nat). k < SZ.v vi ==> vmax >= Seq.index s0 k)
    )
  {
    let vi = !i;
    let a_i = a.(vi);
    let a_next = a.(vi +^ 1sz);
    let vmin = !min_ref;
    let vmax = !max_ref;

    if (a_i <= a_next) {
      if (a_i < vmin) { min_ref := a_i; };
      if (a_next > vmax) { max_ref := a_next; };
    } else {
      if (a_next < vmin) { min_ref := a_next; };
      if (a_i > vmax) { max_ref := a_i; };
    };

    i := vi +^ 2sz;
  };

  // Handle last element if odd count remains (2 comparisons)
  let vi = !i;
  if (vi <^ len) {
    let last = a.(vi);
    let vmin = !min_ref;
    let vmax = !max_ref;
    if (last < vmin) { min_ref := last; };
    if (last > vmax) { max_ref := last; };
  };

  let final_min = !min_ref;
  let final_max = !max_ref;
  { min_val = final_min; max_val = final_max }
}
#pop-options

// ========== With complexity tracking: 2(n-1) comparisons ==========

//SNIPPET_START: complexity_bounded_minmax
let complexity_bounded_minmax (cf c0 n: nat) : prop =
  n >= 1 /\
  cf >= c0 /\
  cf - c0 == op_Multiply 2 (n - 1)
//SNIPPET_END: complexity_bounded_minmax

fn find_minmax_complexity
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len >= 1 /\
      SZ.v len == A.length a
    )
  returns result: minmax_result
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      // min_val is in the array and is minimum
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
      // max_val is in the array and is maximum
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k) /\
      // Complexity bound
      complexity_bounded_minmax cf (reveal c0) (SZ.v len)
    )
{
  // Initialize from first element
  let v0 = a.(0sz);
  let mut min: int = v0;
  let mut max: int = v0;
  
  // Scan remaining elements
  let mut i: SZ.t = 1sz;
  
  while (!i <^ len)
  invariant exists* vi vmin vmax (vc: nat).
    R.pts_to i vi **
    R.pts_to min vmin **
    R.pts_to max vmax **
    GR.pts_to ctr vc **
    A.pts_to a #p s0 **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v len /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmin) /\
      (forall (k:nat). k < SZ.v vi ==> vmin <= Seq.index s0 k) /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmax) /\
      (forall (k:nat). k < SZ.v vi ==> vmax >= Seq.index s0 k) /\
      // Comparison count: 2 comparisons per element processed
      vc >= reveal c0 /\
      vc - reveal c0 == op_Multiply 2 (SZ.v vi - 1)
    )
  {
    let vi = !i;
    let elem = a.(vi);
    let vmin = !min;
    let vmax = !max;
    
    // 1st comparison: elem < vmin
    tick ctr;
    if (elem < vmin) {
      min := elem;
    };
    
    // 2nd comparison: elem > vmax
    tick ctr;
    if (elem > vmax) {
      max := elem;
    };
    
    i := vi + 1sz;
  };
  
  let final_min = !min;
  let final_max = !max;
  
  { min_val = final_min; max_val = final_max }
}

// ========== CLRS pair-processing with complexity tracking: ⌈3n/2⌉ - 2 comparisons ==========

//SNIPPET_START: complexity_bounded_minmax_pairs
// Pair-processing uses at most ⌊3n/2⌋ comparisons (expressed without division)
let complexity_bounded_minmax_pairs (cf c0 n: nat) : prop =
  n >= 1 /\
  cf >= c0 /\
  op_Multiply 2 (cf - c0) <= op_Multiply 3 n
//SNIPPET_END: complexity_bounded_minmax_pairs

#push-options "--z3rlimit 500 --ifuel 3 --fuel 3"
fn find_minmax_pairs_complexity
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len >= 1 /\
      SZ.v len == A.length a
    )
  returns result: minmax_result
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k) /\
      complexity_bounded_minmax_pairs cf (reveal c0) (SZ.v len)
    )
{
  let v0 = a.(0sz);
  let mut min_ref: int = v0;
  let mut max_ref: int = v0;
  let mut i: SZ.t = 1sz;

  // For n >= 2, initialize from first pair (1 comparison)
  if (len >=^ 2sz) {
    let v1 = a.(1sz);
    tick ctr;
    if (v0 <= v1) {
      max_ref := v1;
    } else {
      min_ref := v1;
    };
    i := 2sz;
  };

  // Process remaining elements in pairs (3 comparisons per pair)
  let len_m1 = len -^ 1sz;
  while (
    let vi = !i;
    vi <^ len_m1
  )
  invariant exists* vi vmin vmax (vc: nat).
    R.pts_to i vi **
    R.pts_to min_ref vmin **
    R.pts_to max_ref vmax **
    GR.pts_to ctr vc **
    A.pts_to a #p s0 **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v len /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmin) /\
      (forall (k:nat). k < SZ.v vi ==> vmin <= Seq.index s0 k) /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmax) /\
      (forall (k:nat). k < SZ.v vi ==> vmax >= Seq.index s0 k) /\
      vc >= reveal c0 /\
      op_Multiply 2 (vc - reveal c0) <= op_Multiply 3 (SZ.v vi) - 2
    )
  {
    let vi = !i;
    let a_i = a.(vi);
    let a_next = a.(vi +^ 1sz);
    let vmin = !min_ref;
    let vmax = !max_ref;

    // 3 comparisons: pair + smaller vs min + larger vs max
    tick ctr; tick ctr; tick ctr;
    if (a_i <= a_next) {
      if (a_i < vmin) { min_ref := a_i; };
      if (a_next > vmax) { max_ref := a_next; };
    } else {
      if (a_next < vmin) { min_ref := a_next; };
      if (a_i > vmax) { max_ref := a_i; };
    };

    i := vi +^ 2sz;
  };

  // Handle last element if odd count remains (2 comparisons)
  let vi = !i;
  if (vi <^ len) {
    let last = a.(vi);
    let vmin = !min_ref;
    let vmax = !max_ref;
    tick ctr; tick ctr;  // 2 comparisons for last element
    if (last < vmin) { min_ref := last; };
    if (last > vmax) { max_ref := last; };
  };

  let final_min = !min_ref;
  let final_max = !max_ref;
  { min_val = final_min; max_val = final_max }
}
#pop-options
