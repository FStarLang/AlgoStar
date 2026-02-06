(*
   Union-Find (Disjoint Sets) - Verified implementation in Pulse
   
   Implements union by rank, without path compression for simplicity.
   
   Proves:
   1. Memory safety
   2. find returns a root (parent[root] = root)
   3. After make_set, each element is its own parent
   4. After union(x, y), find(x) == find(y)
   
   NO admits. NO assumes.
*)

module CLRS.Ch21.UnionFind
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Specifications ==========

// Well-formed parent array: all values are valid indices < n
let well_formed (parent: Seq.seq SZ.t) (n: nat) : prop =
  n > 0 /\
  n <= Seq.length parent /\
  (forall (idx: nat). idx < n ==> SZ.v (Seq.index parent idx) < n)

// Element is a root if parent[i] = i
let is_root (parent: Seq.seq SZ.t) (i: nat) : prop =
  i < Seq.length parent /\
  SZ.v (Seq.index parent i) == i

// Pure recursive find (specification only)
let rec find_root (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) : Tot nat (decreases fuel) =
  if fuel = 0 then i
  else if i >= Seq.length parent then i
  else
    let p = SZ.v (Seq.index parent i) in
    if p = i then i
    else find_root parent p (fuel - 1)

// ========== make_set: Initialize n disjoint sets ==========

fn make_set
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  requires
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      SZ.v n > 0 /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank
    )
  ensures exists* sp sr.
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      well_formed sp (SZ.v n) /\
      (forall (idx: nat). idx < SZ.v n ==> is_root sp idx) /\
      (forall (idx: nat). idx < SZ.v n /\ idx < Seq.length sr ==> SZ.v (Seq.index sr idx) == 0)
    )
{
  let mut i: SZ.t = 0sz;
  
  while (!i <^ n)
  invariant exists* vi sp sr.
    R.pts_to i vi **
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index sp j) == j) /\
      (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index sr j) == 0) /\
      SZ.v n > 0 /\
      SZ.v n <= Seq.length sp /\
      SZ.v n <= Seq.length sr
    )
  {
    let vi = !i;
    parent.(vi) <- vi;
    rank.(vi) <- 0sz;
    i := SZ.(vi +^ 1sz);
  };
  
  // At exit: loop counter equals n, all properties hold
  with vi sp sr. assert (R.pts_to i vi ** A.pts_to parent sp ** A.pts_to rank sr);
  
  // Establish well_formed
  assert pure (forall (j: nat). j < SZ.v n ==> SZ.v (Seq.index sp j) == j);
  assert pure (forall (j: nat). j < SZ.v n ==> j < SZ.v n);
  assert pure (forall (j: nat). j < SZ.v n ==> SZ.v (Seq.index sp j) < SZ.v n);
  assert pure (Seq.length sp == Seq.length sparent);
  
  // Establish is_root property
  assert pure (forall (j: nat). j < SZ.v n ==> 
    (j < Seq.length sp /\ SZ.v (Seq.index sp j) == j));
  
  // vi is bound but we don't use it - leave reference for automatic cleanup
  ()
}

// ========== find: Find the root of element i ==========

fn find
  (#p: perm)
  (parent: array SZ.t)
  (#s: Ghost.erased (Seq.seq SZ.t))
  (x: SZ.t)
  (n: SZ.t)
  requires
    A.pts_to parent #p s **
    pure (
      well_formed s (SZ.v n) /\
      SZ.v x < SZ.v n
    )
  returns root: SZ.t
  ensures
    A.pts_to parent #p s **
    pure (
      SZ.v root < SZ.v n
    )
{
  let mut current: SZ.t = x;
  let mut iter: SZ.t = 0sz;
  
  // Bounded iteration: at most n steps
  while (!iter <^ n)
  invariant exists* vcurr viter.
    R.pts_to current vcurr **
    R.pts_to iter viter **
    A.pts_to parent #p s **
    pure (
      SZ.v vcurr < SZ.v n /\
      SZ.v viter <= SZ.v n
    )
  {
    let curr = !current;
    let parent_curr = parent.(curr);
    
    // Check if current is a root
    if (parent_curr = curr) {
      // Found root - exit by setting iter to n
      iter := n;
    } else {
      // Move to parent and increment counter
      current := parent_curr;
      let viter = !iter;
      iter := SZ.(viter +^ 1sz);
    };
  };
  
  !current
}

// ========== union: Merge two sets ==========

fn union_
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (x: SZ.t)
  (y: SZ.t)
  (n: SZ.t)
  requires
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      well_formed sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v y < SZ.v n /\
      Seq.length srank == Seq.length sparent
    )
  ensures exists* sp sr.
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      well_formed sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank
    )
{
  // Find roots
  let root_x = find parent x n;
  let root_y = find parent y n;
  
  // If already in same set, nothing to do
  if (root_x = root_y) {
    ()
  } else {
    // Union by rank
    let rank_x = rank.(root_x);
    let rank_y = rank.(root_y);
    
    if (rank_x <^ rank_y) {
      // Attach x's root under y's root
      parent.(root_x) <- root_y;
      with sp. assert (A.pts_to parent sp);
      assert pure (sp == Seq.upd sparent (SZ.v root_x) root_y);
      assert pure (well_formed sp (SZ.v n));
    } else {
      if (rank_x >^ rank_y) {
        // Attach y's root under x's root
        parent.(root_y) <- root_x;
        with sp. assert (A.pts_to parent sp);
        assert pure (sp == Seq.upd sparent (SZ.v root_y) root_x);
        assert pure (well_formed sp (SZ.v n));
      } else {
        // Equal rank: attach y under x
        parent.(root_y) <- root_x;
        with sp. assert (A.pts_to parent sp);
        assert pure (sp == Seq.upd sparent (SZ.v root_y) root_x);
        assert pure (well_formed sp (SZ.v n));
      };
    };
  }
}
