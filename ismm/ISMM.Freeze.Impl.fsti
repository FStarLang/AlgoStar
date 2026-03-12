(*
   ISMM Freeze — Imperative Pulse Implementation Interface
   
   Implements the freeze algorithm from §3.1 (Fig. 2) of:
   "Reference Counting Deeply Immutable Data Structures with Cycles"
   
   freeze(root): Iterative DFS with pending stack for SCC detection.
   Computes SCCs via Purdom's path-based algorithm fused with union-find.
   Assigns each SCC an initial external RC of 1.
*)
module ISMM.Freeze.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = ISMM.UnionFind.Spec
module Impl = ISMM.UnionFind.Impl
module FSpec = ISMM.Freeze.Spec
open ISMM.Status
open FStar.Mul

(** FREEZE: Compute SCCs of the subgraph reachable from root.
    Modifies tag, parent, rank arrays.
    Adjacency matrix adj is read-only (n*n flat array).
    
    After freeze:
    - All reachable nodes from root have tag REP or RC
    - Each SCC has exactly one RC-tagged representative
    - Unreachable nodes remain UNMARKED
    - uf_inv is maintained *)
fn freeze
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (adj: A.array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#sadj: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (root: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to adj #0.5R sadj **
    pure (
      SZ.v n > 0 /\
      SZ.v root < SZ.v n /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      SZ.v n * SZ.v n <= A.length adj /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Seq.length sadj == A.length adj /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n))
    )
  ensures exists* st sp sr.
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to adj #0.5R sadj **
    pure (
      Seq.length st == Seq.length stag /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st sp sr (SZ.v n))
    )
