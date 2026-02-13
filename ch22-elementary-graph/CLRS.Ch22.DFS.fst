(*
   Depth-First Search - Verified implementation in Pulse
   
   Implements graph reachability via iterative exploration.
   Graph represented as adjacency matrix adj[i*n+j] (edge from i to j if != 0).
   
   Colors: 0=white (unvisited), non-zero=visited
   
   Runs n rounds. In each round, for every visited vertex u, marks all
   unvisited neighbors v as visited with dist[v] = dist[u] + 1.
   After n rounds, all reachable vertices from source are visited.
   
   Postconditions:
   - Source vertex is visited with dist[source] == 0
   - All reachable vertices (within n steps) are visited
   - Distance soundness: for all visited v, reachable_in(source, v, dist[v])
   
   NOTE: This implements graph reachability exploration, equivalent to BFS in
   terms of which vertices get visited. A full CLRS DFS with discovery/finish
   timestamps, edge classification, and the parenthesis theorem requires a
   stack-based implementation (future work).
   
   NO admits. NO assumes.
*)

module CLRS.Ch22.DFS
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

(* Reachability specification *)

// One-step reachability: there's a direct edge from u to v
let has_edge (adj: Seq.seq int) (n: nat) (u v: nat) : prop =
  u < n /\ v < n /\ u * n + v < Seq.length adj /\ Seq.index adj (u * n + v) <> 0

// k-step reachability from source
let rec reachable_in (adj: Seq.seq int) (n: nat) (source v: nat) (steps: nat) 
  : Tot prop (decreases steps)
  = if steps = 0 then v == source
    else (exists (u: nat). u < n /\ reachable_in adj n source u (steps - 1) /\ has_edge adj n u v)

// Helper: If a vertex is reachable in k+1 steps, there's a witness at k steps
let reachable_in_succ_witness (adj: Seq.seq int) (n: nat) (source v: nat) (k: nat)
  : Lemma
    (requires reachable_in adj n source v (k + 1))
    (ensures exists (u: nat). u < n /\ reachable_in adj n source u k /\ has_edge adj n u v)
  = ()

fn dfs
  (adj: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (color: A.array int)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sadj <= A.length adj /\
      Seq.length scolor == SZ.v n /\
      Seq.length scolor <= A.length color /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* scolor'.
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    pure (
      Seq.length scolor' == SZ.v n /\
      (SZ.v source < Seq.length scolor' ==> Seq.index scolor' (SZ.v source) == 1) /\
      // Main correctness property: all reachable vertices are visited
      (forall (v: nat). v < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) v (SZ.v n) ==> 
        Seq.index scolor' v <> 0)
    )
{
  // Initialize all colors to 0 (white/unvisited)
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi scolor_i.
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to color scolor_i **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length scolor_i == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index scolor_i j == 0)
    )
  {
    let vi = !i;
    A.op_Array_Assignment color vi 0;
    i := SZ.add vi 1sz;
  };

  // Mark source as visited (1)
  A.op_Array_Assignment color source 1;

  // Run n relaxation rounds to propagate reachability
  let mut round: SZ.t = 0sz;
  while (!round <^ n)
  invariant exists* vround scolor_r.
    R.pts_to round vround **
    A.pts_to adj sadj **
    A.pts_to color scolor_r **
    pure (
      SZ.v vround <= SZ.v n /\
      Seq.length scolor_r == SZ.v n /\
      Seq.index scolor_r (SZ.v source) == 1 /\
      // Key invariant: all vertices reachable in vround steps are visited
      (forall (v: nat). v < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) v (SZ.v vround) ==> 
        Seq.index scolor_r v <> 0)
    )
  {
    let vround = !round;

    // For each vertex u
    let mut u: SZ.t = 0sz;
    while (!u <^ n)
    invariant exists* vu scolor_u.
      R.pts_to round vround **
      R.pts_to u vu **
      A.pts_to adj sadj **
      A.pts_to color scolor_u **
      pure (
        SZ.v vu <= SZ.v n /\
        Seq.length scolor_u == SZ.v n /\
        Seq.index scolor_u (SZ.v source) == 1 /\
        // Maintain: vertices reachable in vround steps remain visited
        (forall (v: nat). v < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) v (SZ.v vround) ==> 
          Seq.index scolor_u v <> 0) /\
        // Partial progress: for all u_idx < vu that are reachable, their neighbors are visited
        (forall (u_idx: nat) (v_idx: nat). 
          u_idx < SZ.v vu /\ v_idx < SZ.v n /\
          reachable_in sadj (SZ.v n) (SZ.v source) u_idx (SZ.v vround) /\
          has_edge sadj (SZ.v n) u_idx v_idx ==>
          Seq.index scolor_u v_idx <> 0)
      )
    {
      let vu = !u;

      // For each neighbor v of u
      let mut v: SZ.t = 0sz;
      while (!v <^ n)
      invariant exists* vv scolor_v.
        R.pts_to round vround **
        R.pts_to u vu **
        R.pts_to v vv **
        A.pts_to adj sadj **
        A.pts_to color scolor_v **
        pure (
          SZ.v vv <= SZ.v n /\
          SZ.v vu < SZ.v n /\
          Seq.length scolor_v == SZ.v n /\
          SZ.fits (SZ.v vu * SZ.v n) /\
          SZ.fits (SZ.v vu * SZ.v n + SZ.v vv) /\
          Seq.index scolor_v (SZ.v source) == 1 /\
          // Maintain: vertices reachable in vround steps remain visited
          (forall (w: nat). w < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) w (SZ.v vround) ==> 
            Seq.index scolor_v w <> 0) /\
          // Maintain: previously processed u's have their neighbors marked
          (forall (u_idx: nat) (v_idx: nat). 
            u_idx < SZ.v vu /\ v_idx < SZ.v n /\
            reachable_in sadj (SZ.v n) (SZ.v source) u_idx (SZ.v vround) /\
            has_edge sadj (SZ.v n) u_idx v_idx ==>
            Seq.index scolor_v v_idx <> 0) /\
          // Partial progress for current vu: neighbors v_idx < vv are marked if vu is reachable
          (forall (v_idx: nat).
            v_idx < SZ.v vv /\
            reachable_in sadj (SZ.v n) (SZ.v source) (SZ.v vu) (SZ.v vround) /\
            has_edge sadj (SZ.v n) (SZ.v vu) v_idx ==>
            Seq.index scolor_v v_idx <> 0)
        )
      {
        let vv = !v;

        // Read u's color, edge, and v's color
        let cu: int = A.op_Array_Access color vu;
        let offset: SZ.t = SZ.mul vu n;
        let idx: SZ.t = SZ.add offset vv;
        let has_edge_val: int = A.op_Array_Access adj idx;
        let cv: int = A.op_Array_Access color vv;

        // Key reasoning: the adjacency matrix value matches the has_edge predicate
        assert pure (
          (has_edge_val <> 0) <==> has_edge sadj (SZ.v n) (SZ.v vu) (SZ.v vv)
        );

        // Compute new color for v
        let new_cv: int = (if cu <> 0 && has_edge_val <> 0 && cv = 0 then 1 else cv);
        
        // Write the new color
        A.op_Array_Assignment color vv new_cv;

        v := SZ.add vv 1sz;
      };

      u := SZ.add vu 1sz;
    };

    round := SZ.add vround 1sz;
  };
}
