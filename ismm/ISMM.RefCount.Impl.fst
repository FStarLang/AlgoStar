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
module Arith = ISMM.Arith.Lemmas
open ISMM.Status

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
```pulse
fn acquire
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (refcount: A.array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (r: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to refcount src **
    pure (
      SZ.v n > 0 /\
      SZ.v r < SZ.v n /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      SZ.v n <= A.length refcount /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Seq.length src == A.length refcount /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index src i)} i < SZ.v n ==> SZ.fits (SZ.v (Seq.index src i) + 1))
    )
  ensures exists* sp sr src'.
    A.pts_to tag stag **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to refcount src' **
    pure (
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Seq.length src' == Seq.length src /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sp sr (SZ.v n))
    )
{
  let rep = Impl.find_set parent r n #sparent #stag #srank;
  with sp1. assert (A.pts_to parent sp1);
  
  let rc = refcount.(rep);
  // rep < n (from find_set postcondition) and forall precondition → fits(rc+1)
  refcount.(rep) <- SZ.(rc +^ 1sz);
  
  with src1. assert (A.pts_to refcount src1);
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
  (refcount: A.array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (r: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to refcount src **
    pure (
      SZ.v n > 0 /\
      SZ.v r < SZ.v n /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      SZ.v n <= A.length refcount /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Seq.length src == A.length refcount /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      // Caller must ensure: representative of r has positive refcount
      (let pf = Spec.pure_find (Impl.to_uf stag sparent srank (SZ.v n)) (SZ.v r) in
       pf < SZ.v n /\ pf < Seq.length src /\
       SZ.v (Seq.index src pf) > 0)
    )
  returns should_dispose: bool
  ensures exists* sp sr src'.
    A.pts_to tag stag **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to refcount src' **
    pure (
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Seq.length src' == Seq.length src /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sp sr (SZ.v n))
    )
{
  let rep = Impl.find_set parent r n #sparent #stag #srank;
  with sp1. assert (A.pts_to parent sp1);
  
  // rep is a root in sparent: pure_find returns a root
  Spec.pure_find_is_root (Impl.to_uf stag sparent srank (SZ.v n)) (SZ.v r);
  Impl.to_nat_seq_index sparent (SZ.v n) (SZ.v rep);
  Impl.to_int_seq_index stag (SZ.v n) (SZ.v rep);
  // Now: SZ.v (Seq.index sparent rep) == SZ.v rep (root in old parent)
  //      SZ.v (Seq.index stag rep) == Seq.index (to_uf ...).tag rep
  
  let rc = refcount.(rep);
  
  if (rc = 1sz) {
    // RC hits 0 — mark for disposal
    refcount.(rep) <- 0sz;
    with src1. assert (A.pts_to refcount src1);
    true
  } else {
    // From precondition: SZ.v (Seq.index src (pure_find ... r)) > 0
    // From find_set: SZ.v rep == pure_find ... r
    // Therefore: SZ.v (Seq.index src (SZ.v rep)) > 0, i.e., SZ.v rc > 0
    // rc != 1 and rc > 0 → rc >= 2 → fits(rc - 1) since rc fits and rc - 1 < rc
    assert (pure (SZ.v rc > 0));
    Arith.rc_dec_fits (SZ.v rc);
    refcount.(rep) <- SZ.(rc -^ 1sz);
    with src1. assert (A.pts_to refcount src1);
    false
  }
}
```
#pop-options
