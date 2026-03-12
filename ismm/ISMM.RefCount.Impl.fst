(*
   ISMM RefCount — Imperative Pulse Implementation
   
   Implements acquire/release from paper §3.2.
   acquire: find(r) → incref(representative)
   release: find(r) → decref(representative); return true if RC hit 0
*)
module ISMM.RefCount.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = ISMM.UnionFind.Spec
module Impl = ISMM.UnionFind.Impl
module UFL = ISMM.UF.Lemmas
open ISMM.Status

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
```pulse
fn acquire
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (r: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      SZ.v n > 0 /\
      SZ.v r < SZ.v n /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n))
    )
  ensures exists* sp sr.
    A.pts_to tag stag **
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sp sr (SZ.v n))
    )
{
  let rep = Impl.find_set parent r n #sparent #stag #srank;
  with sp1. assert (A.pts_to parent sp1);
  
  let rc = rank.(rep);
  assume_ (pure (SZ.fits (SZ.v rc + 1)));
  rank.(rep) <- SZ.(rc +^ 1sz);
  
  with sr1. assert (A.pts_to rank sr1);
  // Rank increase on root preserves uf_inv (find_set returns root)
  UFL.rank_increase_on_root_preserves_uf_inv stag sp1 srank (SZ.v n) (SZ.v rep) SZ.(rc +^ 1sz);
  ()
}
```
#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
```pulse
fn release
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (r: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      SZ.v n > 0 /\
      SZ.v r < SZ.v n /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n))
    )
  returns should_dispose: bool
  ensures exists* sp sr.
    A.pts_to tag stag **
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sp sr (SZ.v n))
    )
{
  let rep = Impl.find_set parent r n #sparent #stag #srank;
  with sp1. assert (A.pts_to parent sp1);
  
  let rc = rank.(rep);
  
  if (rc = 1sz) {
    // RC hits 0 — mark for disposal
    rank.(rep) <- 0sz;
    with sr1. assert (A.pts_to rank sr1);
    assume_ (pure (
      Impl.is_forest sp1 (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sp1 sr1 (SZ.v n))
    ));
    true
  } else {
    // Decrement RC
    assume_ (pure (SZ.v rc > 0 /\ SZ.fits (SZ.v rc - 1)));
    rank.(rep) <- SZ.(rc -^ 1sz);
    with sr1. assert (A.pts_to rank sr1);
    assume_ (pure (
      Impl.is_forest sp1 (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sp1 sr1 (SZ.v n))
    ));
    false
  }
}
```
#pop-options
