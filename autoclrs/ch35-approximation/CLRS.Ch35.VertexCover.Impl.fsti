module CLRS.Ch35.VertexCover.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch35.VertexCover.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = CLRS.Ch35.VertexCover.Spec

// 2-approximation vertex cover algorithm from CLRS Chapter 35.
// Given an adjacency matrix for an undirected graph with n vertices,
// returns a cover array where cover[i] = 1 if vertex i is in the cover.
//
// NOTE: The algorithm scans only upper-triangular entries (u < v),
// which is correct for undirected graphs where adj[u*n+v] = adj[v*n+u].

//SNIPPET_START: approx_vertex_cover_sig
fn approx_vertex_cover
  (#p: perm)
  (adj: array int)
  (#s_adj: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires 
    A.pts_to adj #p s_adj ** 
    pure (
      SZ.v n > 0 /\ 
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length s_adj == SZ.v n * SZ.v n /\
      Spec.is_symmetric_adj s_adj (SZ.v n)
    )
  returns cover: V.vec int
  ensures exists* s_cover.
    A.pts_to adj #p s_adj **
    V.pts_to cover s_cover **
    pure (
      V.is_full_vec cover /\
      Seq.length s_cover == SZ.v n /\
      Spec.is_cover s_adj s_cover (SZ.v n) (SZ.v n) 0 /\
      (forall (i: nat). i < SZ.v n ==> (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
      (exists (opt: nat). Spec.min_vertex_cover_size s_adj (SZ.v n) opt) /\
      (forall (opt: nat). Spec.min_vertex_cover_size s_adj (SZ.v n) opt ==>
        Spec.count_cover (Spec.seq_to_cover_fn s_cover (SZ.v n)) (SZ.v n) <= 2 * opt) /\
      (exists (k: nat). Spec.count_cover (Spec.seq_to_cover_fn s_cover (SZ.v n)) (SZ.v n) = 2 * k)
    )
//SNIPPET_END: approx_vertex_cover_sig
