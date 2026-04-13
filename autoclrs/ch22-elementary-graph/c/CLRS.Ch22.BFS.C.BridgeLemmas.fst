(**
 * Bridge lemmas for BFS C-to-Pulse verification.
 *
 * Wraps nested-array-access properties in opaque predicates using SizeT.t
 * quantifiers to match c2pulse's generated code. This prevents Z3 blowup
 * from deeply nested array_read expressions in quantifier invariants.
 *)
module CLRS.Ch22.BFS.C.BridgeLemmas

open FStar.Mul
module Seq = FStar.Seq
module I32 = FStar.Int32
module SZ  = FStar.SizeT

(* Predecessor edge validity: for all non-white vertices v with pred[v] < n,
   adj[pred[v]*n+v] != 0. Uses SizeT.t quantifiers to match c2pulse. *)
[@"opaque_to_smt"]
let pred_edge_ok_c
  (sadj scolor: Seq.seq (option I32.t))
  (spred: Seq.seq (option SZ.t))
  (sz_n: SZ.t)
  : prop
  = let n = SZ.v sz_n in
    Seq.length sadj >= n * n /\ Seq.length scolor >= n /\ Seq.length spred >= n /\
    (forall (i:SZ.t). SZ.v i < n ==> Some? (Seq.index scolor (SZ.v i))) /\
    (forall (i:SZ.t). SZ.v i < n ==> Some? (Seq.index spred (SZ.v i))) /\
    (forall (v:SZ.t). SZ.v v < n /\
      SZ.v (Some?.v (Seq.index spred (SZ.v v))) < n
    ==>
      (let pv = SZ.v (Some?.v (Seq.index spred (SZ.v v))) in
       pv * n + SZ.v v < Seq.length sadj /\
       Some? (Seq.index sadj (pv * n + SZ.v v)) /\
       not (I32.v (Some?.v (Seq.index sadj (pv * n + SZ.v v))) = 0)))

(* Predecessor distance consistency: for all non-white vertices v with pred[v] < n,
   color[pred[v]] is non-white and dist[v] == dist[pred[v]] + 1. *)
[@"opaque_to_smt"]
let pred_dist_ok_c
  (scolor sdist: Seq.seq (option I32.t))
  (spred: Seq.seq (option SZ.t))
  (sz_n: SZ.t)
  : prop
  = let n = SZ.v sz_n in
    Seq.length scolor >= n /\ Seq.length sdist >= n /\ Seq.length spred >= n /\
    (forall (i:SZ.t). SZ.v i < n ==> Some? (Seq.index scolor (SZ.v i))) /\
    (forall (i:SZ.t). SZ.v i < n ==> Some? (Seq.index sdist (SZ.v i))) /\
    (forall (i:SZ.t). SZ.v i < n ==> Some? (Seq.index spred (SZ.v i))) /\
    (forall (v:SZ.t). SZ.v v < n /\
      not (I32.v (Some?.v (Seq.index scolor (SZ.v v))) = 0) /\
      SZ.v (Some?.v (Seq.index spred (SZ.v v))) < n
    ==>
      not (I32.v (Some?.v (Seq.index scolor (SZ.v (Some?.v (Seq.index spred (SZ.v v)))))) = 0) /\
      I32.v (Some?.v (Seq.index sdist (SZ.v v))) =
        I32.v (Some?.v (Seq.index sdist (SZ.v (Some?.v (Seq.index spred (SZ.v v)))))) + 1)
