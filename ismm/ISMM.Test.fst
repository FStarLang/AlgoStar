(*
   ISMM Test — Exercises the Union-Find implementation
*)
module ISMM.Test
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = ISMM.UnionFind.Spec
module Impl = ISMM.UnionFind.Impl

/// Simple test: create 4 nodes, union 0-1 and 2-3, check find
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
```pulse
fn test_uf (_: unit)
  requires emp
  ensures emp
{
  let n: SZ.t = 4sz;
  let tag = A.alloc 0sz 4sz;
  let parent = A.alloc 0sz 4sz;
  let rank = A.alloc 0sz 4sz;
  Impl.make_set tag parent rank n;
  with st sp sr. assert (A.pts_to tag st ** A.pts_to parent sp ** A.pts_to rank sr);
  // Union nodes 0 and 1
  Spec.rank_bounded_all (Impl.to_uf st sp sr (SZ.v n));
  Impl.union_set parent rank #sp #sr #st 0sz 1sz n;
  with sp1 sr1. assert (A.pts_to parent sp1 ** A.pts_to rank sr1);
  // Union nodes 2 and 3
  Spec.rank_bounded_all (Impl.to_uf st sp1 sr1 (SZ.v n));
  Impl.union_set parent rank #sp1 #sr1 #st 2sz 3sz n;
  with sp2 sr2. assert (A.pts_to parent sp2 ** A.pts_to rank sr2);
  // Find representatives
  let _r0 = Impl.find_set parent 0sz n #sp2 #st #sr2;
  with sp3. assert (A.pts_to parent sp3);
  let _r2 = Impl.find_set parent 2sz n #sp3 #st #sr2;
  A.free tag;
  A.free parent;
  A.free rank;
  ()
}
```
#pop-options
