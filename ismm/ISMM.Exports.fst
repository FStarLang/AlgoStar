(*
   ISMM.Exports — Public API re-export for C extraction

   Pulse fn declarations in .fsti files extract with Private visibility
   in .krml, causing KaRaMeL to dead-code-eliminate them.  This module
   (with no .fsti) re-exports the API functions as public symbols.
*)
module ISMM.Exports
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = ISMM.UnionFind.Spec
module Impl = ISMM.UnionFind.Impl
module Freeze = ISMM.Freeze.Impl
module Dispose = ISMM.Dispose.Impl
module RC = ISMM.RefCount.Impl
module Count = ISMM.Count

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"

// ── Union-Find ──────────────────────────────────────────────────

```pulse
fn ismm_make_set
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      SZ.v n > 0 /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank
    )
  ensures exists* st sp sr.
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr
{ Impl.make_set tag parent rank #stag #sparent #srank n }
```

```pulse
fn ismm_find_set
  (parent: A.array SZ.t) (x: SZ.t) (n: SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  requires
    A.pts_to parent sparent **
    pure (
      Impl.is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v n <= Seq.length sparent /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n))
    )
  returns root: SZ.t
  ensures exists* sp. A.pts_to parent sp
{ Impl.find_set parent x n #sparent #stag #srank }
```

```pulse
fn ismm_union_set
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (x: SZ.t)
  (y: SZ.t)
  (n: SZ.t)
  requires
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      Impl.is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v y < SZ.v n /\
      Seq.length srank == Seq.length sparent /\
      SZ.v n <= Seq.length sparent /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i: nat). i < SZ.v n ==> SZ.v (Seq.index srank i) < SZ.v n)
    )
  ensures exists* sp sr. A.pts_to parent sp ** A.pts_to rank sr
{ Impl.union_set parent rank #sparent #srank #stag x y n }
```

// ── Freeze ──────────────────────────────────────────────────────

```pulse
fn ismm_freeze
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (adj: A.array SZ.t)
  (refcount: A.array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#sadj: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (root: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src **
    pure (
      SZ.v n > 0 /\
      SZ.v root < SZ.v n /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      SZ.v n <= A.length refcount /\
      SZ.v n * SZ.v n <= A.length adj /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.fits (SZ.v n * (SZ.v n + 1)) /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Seq.length sadj == A.length adj /\
      Seq.length src == A.length refcount /\
      A.length parent == A.length rank /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n))
    )
  ensures exists* st sp sr src'.
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src'
{ Freeze.freeze tag parent rank adj refcount #stag #sparent #srank #sadj #src n root }
```

// ── Dispose ─────────────────────────────────────────────────────

```pulse
fn ismm_dispose
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (adj: A.array SZ.t)
  (refcount: A.array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#sadj: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (rep: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src **
    pure (
      SZ.v n > 0 /\
      SZ.v rep < SZ.v n /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      SZ.v n <= A.length refcount /\
      SZ.v n * SZ.v n <= A.length adj /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.fits (SZ.v n * (SZ.v n + 1)) /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Seq.length sadj == A.length adj /\
      Seq.length src == A.length refcount /\
      A.length parent == A.length rank /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index stag i)} i < SZ.v n /\ SZ.v (Seq.index stag i) == 3 /\ i <> SZ.v rep ==> SZ.v (Seq.index src i) > 0) /\
      Count.count_eq stag 1 (SZ.v n) == 0 /\
      SZ.v (Seq.index stag (SZ.v rep)) == 3
    )
  ensures exists* st sp sr src'.
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src'
{ Dispose.dispose tag parent rank adj refcount #stag #sparent #srank #sadj #src n rep }
```

// ── RefCount ────────────────────────────────────────────────────

```pulse
fn ismm_acquire
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
    A.pts_to refcount src'
{ RC.acquire tag parent rank refcount #stag #sparent #srank #src n r }
```

```pulse
fn ismm_release
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
      (let pf = Spec.pure_find (Impl.to_uf stag sparent srank (SZ.v n)) (SZ.v r) in
       pf < SZ.v n /\ pf < Seq.length src /\
       SZ.v (Seq.index src pf) > 0)
    )
  returns should_dispose: bool
  ensures exists* sp sr src'.
    A.pts_to tag stag **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to refcount src'
{ RC.release tag parent rank refcount #stag #sparent #srank #src n r }
```

#pop-options
