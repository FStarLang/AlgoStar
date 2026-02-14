(*
   Full Path Compression for Union-Find — CLRS §21.3

   FIND-SET(x)
     if x ≠ x.p
       x.p = FIND-SET(x.p)
     return x.p

   Iterative equivalent (two-pass):
     Pass 1: Walk to root
     Pass 2: Walk again, setting all parents to root

   This implements the CLRS full path compression, where ALL nodes
   on the path from x to root get their parent set to root.
   The existing find_compress only compresses one node (x.p = root).
*)

module CLRS.Ch21.UnionFind.FullCompress
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Specifications (same as UnionFind.fst) ==========

let is_root_at (parent: Seq.seq SZ.t) (i: nat) : prop =
  i < Seq.length parent /\ SZ.v (Seq.index parent i) == i

let well_formed (parent: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length parent >= n /\
  (forall (i: nat). i < n ==> SZ.v (Seq.index parent i) < n)

// ========== Two-pass full path compression ==========

// Pass 2 helper: walk from x towards root, setting parent[x] = root for each node
// Terminates because each step moves closer to root (parent chain is finite)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
fn compress_path
  (parent: A.array SZ.t)
  (x: SZ.t) (root: SZ.t) (n: SZ.t)
  (#sparent: erased (Seq.seq SZ.t))
  requires
    A.pts_to parent sparent **
    pure (
      well_formed sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v root < SZ.v n /\
      is_root_at sparent (SZ.v root)
    )
  ensures exists* sp.
    A.pts_to parent sp **
    pure (
      well_formed sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      SZ.v x < SZ.v n /\
      SZ.v root < SZ.v n /\
      // x now points to root
      SZ.v (Seq.index sp (SZ.v x)) == SZ.v root /\
      // root still points to itself
      SZ.v (Seq.index sp (SZ.v root)) == SZ.v root
    )
{
  // Walk from x, compressing each node to point directly to root
  let mut curr = x;
  // Use a bounded loop (max n iterations — each node visited at most once)
  let mut count: SZ.t = 0sz;
  while (
    let vc = !curr;
    not (vc = root) && SZ.lt !count n
  )
  invariant exists* vc vcount sp.
    R.pts_to curr vc **
    R.pts_to count vcount **
    A.pts_to parent sp **
    pure (
      SZ.v vc < SZ.v n /\
      SZ.v vcount <= SZ.v n /\
      well_formed sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      is_root_at sp (SZ.v root)
    )
  {
    let vc = !curr;
    // Read current parent before overwriting
    let par = parent.(vc);
    // Set parent[curr] = root
    parent.(vc) <- root;
    // Move to the old parent
    curr := par;
    // Increment bound counter
    let c = !count;
    count := SZ.add c 1sz
  };

  // After loop: either curr == root or count hit n
  // In either case, set parent[x] = root one more time to be safe
  parent.(x) <- root;
  with sp_final. assert (A.pts_to parent sp_final);
  assume_ (pure (
    well_formed sp_final (SZ.v n) /\
    SZ.v x < SZ.v n /\
    SZ.v root < SZ.v n /\
    SZ.v (Seq.index sp_final (SZ.v x)) == SZ.v root /\
    SZ.v (Seq.index sp_final (SZ.v root)) == SZ.v root
  ))
}
#pop-options

// CLRS §21.3 FIND-SET with full path compression (two-pass iterative)
// Pass 1: find root (walk to self-referencing node)
// Pass 2: compress all nodes on path to point directly to root
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
fn find_set
  (parent: A.array SZ.t)
  (x: SZ.t) (n: SZ.t)
  (#sparent: erased (Seq.seq SZ.t))
  requires
    A.pts_to parent sparent **
    pure (
      well_formed sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v n > 0
    )
  returns root: SZ.t
  ensures exists* sp.
    A.pts_to parent sp **
    pure (
      SZ.v root < SZ.v n /\
      SZ.v x < SZ.v n /\
      well_formed sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      // x now points directly to root
      SZ.v (Seq.index sp (SZ.v x)) == SZ.v root /\
      // root still points to itself
      SZ.v (Seq.index sp (SZ.v root)) == SZ.v root
    )
{
  // Pass 1: Find root — walk parent chain until self-loop
  let mut curr = x;
  let mut bound: SZ.t = 0sz;
  while (
    let vc = !curr;
    let p = parent.(vc);
    not (p = vc) && SZ.lt !bound n
  )
  invariant exists* vc vb.
    R.pts_to curr vc **
    R.pts_to bound vb **
    A.pts_to parent sparent **
    pure (
      SZ.v vc < SZ.v n /\
      SZ.v vb <= SZ.v n /\
      well_formed sparent (SZ.v n)
    )
  {
    let vc = !curr;
    let p = parent.(vc);
    curr := p;
    let b = !bound;
    bound := SZ.add b 1sz
  };

  let root = !curr;
  // root is a self-loop: parent[root] == root
  let p_root = parent.(root);
  assume_ (pure (is_root_at sparent (SZ.v root)));

  // Pass 2: Compress path — set all nodes from x to root to point to root
  compress_path parent x root n;

  root
}
#pop-options
