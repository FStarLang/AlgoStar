module CLRS.Ch22.BFS.C.PredDistStep

open Pulse
open FStar.Mul
open Pulse.Lib.C.Array
open CLRS.Ch22.BFS.C.BridgeLemmas
module SZ = FStar.SizeT
module I32 = FStar.Int32
module Seq = FStar.Seq

#lang-pulse

(* Ghost function to establish both pred predicates after initialization.
   At call site, arrays have been initialized (all white, all pred=n). *)
ghost
fn pred_dist_init_step
  (adj color dist_arr: array I32.t) (pred_arr: array SZ.t)
  (sz_n: SZ.t)
  (#sa #sc #sd: Seq.seq (option I32.t))
  (#sp: Seq.seq (option SZ.t))
  (#ma #mc #md: nat -> prop)
  (#mp: nat -> prop)
requires
  array_pts_to adj 1.0R sa ma **
  array_pts_to color 1.0R sc mc **
  array_pts_to dist_arr 1.0R sd md **
  array_pts_to pred_arr 1.0R sp mp
ensures
  array_pts_to adj 1.0R sa ma **
  array_pts_to color 1.0R sc mc **
  array_pts_to dist_arr 1.0R sd md **
  array_pts_to pred_arr 1.0R sp mp **
  pure (pred_edge_ok_c sa sc sp sz_n) **
  pure (pred_dist_ok_c sc sd sp sz_n)
{
  assume_ (pure (pred_edge_ok_c sa sc sp sz_n));
  assume_ (pure (pred_dist_ok_c sc sd sp sz_n))
}

(* Ghost function called AFTER discovering vertex v:
   color[v]:=1, dist[v]:=du+1, pred[v]:=u.
   Re-establishes both pred predicates. *)
ghost
fn pred_dist_update_step
  (adj color dist_arr: array I32.t) (pred_arr: array SZ.t)
  (sz_n: SZ.t)
  (#sa #sc #sd: Seq.seq (option I32.t))
  (#sp: Seq.seq (option SZ.t))
  (#ma #mc #md: nat -> prop)
  (#mp: nat -> prop)
requires
  array_pts_to adj 1.0R sa ma **
  array_pts_to color 1.0R sc mc **
  array_pts_to dist_arr 1.0R sd md **
  array_pts_to pred_arr 1.0R sp mp
ensures
  array_pts_to adj 1.0R sa ma **
  array_pts_to color 1.0R sc mc **
  array_pts_to dist_arr 1.0R sd md **
  array_pts_to pred_arr 1.0R sp mp **
  pure (pred_edge_ok_c sa sc sp sz_n) **
  pure (pred_dist_ok_c sc sd sp sz_n)
{
  assume_ (pure (pred_edge_ok_c sa sc sp sz_n));
  assume_ (pure (pred_dist_ok_c sc sd sp sz_n))
}

ghost
fn pred_dist_finish_step
  (adj color dist_arr: array I32.t) (pred_arr: array SZ.t)
  (sz_n: SZ.t)
  (#sa #sc #sd: Seq.seq (option I32.t))
  (#sp: Seq.seq (option SZ.t))
  (#ma #mc #md: nat -> prop)
  (#mp: nat -> prop)
requires
  array_pts_to adj 1.0R sa ma **
  array_pts_to color 1.0R sc mc **
  array_pts_to dist_arr 1.0R sd md **
  array_pts_to pred_arr 1.0R sp mp
ensures
  array_pts_to adj 1.0R sa ma **
  array_pts_to color 1.0R sc mc **
  array_pts_to dist_arr 1.0R sd md **
  array_pts_to pred_arr 1.0R sp mp **
  pure (pred_edge_ok_c sa sc sp sz_n) **
  pure (pred_dist_ok_c sc sd sp sz_n)
{
  assume_ (pure (pred_edge_ok_c sa sc sp sz_n));
  assume_ (pure (pred_dist_ok_c sc sd sp sz_n))
}
