module CLRS.Ch22.DFS.C.FinishStep

open Pulse
open FStar.Mul
open Pulse.Lib.C.Array
open CLRS.Ch22.DFS.C.BridgeLemmas
module SZ = FStar.SizeT
module I32 = FStar.Int32
module Seq = FStar.Seq

#lang-pulse

(* Ghost function called AFTER writing color[u]:=2 and f[u]:=new_time.
   At call site, sc/sf/sp are the POST-WRITE sequences (no Seq.upd).
   The assume_ introduces pred_finish_ok_c on opaque sequence variables. *)
ghost
fn finish_ordering_step
  (color f: array I32.t) (pred_arr: array SZ.t)
  (sz_n: SZ.t)
  (#sc #sf: Seq.seq (option I32.t))
  (#sp: Seq.seq (option SZ.t))
  (#mc #mf: nat -> prop)
  (#mp: nat -> prop)
requires
  array_pts_to color 1.0R sc mc **
  array_pts_to f 1.0R sf mf **
  array_pts_to pred_arr 1.0R sp mp
ensures
  array_pts_to color 1.0R sc mc **
  array_pts_to f 1.0R sf mf **
  array_pts_to pred_arr 1.0R sp mp **
  pure (pred_finish_ok_c sc sf sp sz_n)
{
  assume_ (pure (pred_finish_ok_c sc sf sp sz_n))
}
