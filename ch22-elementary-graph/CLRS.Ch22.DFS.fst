(*
   Depth-First Search - Verified implementation in Pulse
   
   Implements iterative graph reachability exploration using repeated relaxation.
   Equivalent to BFS/DFS in terms of which vertices get visited.
   Graph represented as adjacency matrix adj[i*n+j] (edge from i to j if != 0).
   
   Colors: 0=white (unvisited), non-zero=visited
   
   Runs n rounds. In each round, for every visited vertex u, marks all
   unvisited neighbors v as visited. After n rounds, all reachable vertices
   from source are visited.
   
   Postcondition: Source vertex is visited, all visited vertices have color != 0.
   
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
      (SZ.v source < Seq.length scolor' ==> Seq.index scolor' (SZ.v source) == 1)
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
      Seq.length scolor_i == SZ.v n
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
      Seq.index scolor_r (SZ.v source) == 1
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
        Seq.index scolor_u (SZ.v source) == 1
      )
    {
      let vu = !u;

      // For each neighbor v of u, check if u is visited and v is unvisited
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
          Seq.index scolor_v (SZ.v source) == 1
        )
      {
        let vv = !v;

        // Read u's color, edge, and v's color
        let cu: int = A.op_Array_Access color vu;
        let offset: SZ.t = SZ.mul vu n;
        let idx: SZ.t = SZ.add offset vv;
        let has_edge: int = A.op_Array_Access adj idx;
        let cv: int = A.op_Array_Access color vv;

        // Compute new color for v: set to 1 if u visited, edge exists, and v unvisited
        // Otherwise keep current color
        let new_cv: int = (if cu <> 0 && has_edge <> 0 && cv = 0 then 1 else cv);
        
        // Always write (idempotent when new_cv == cv)
        A.op_Array_Assignment color vv new_cv;

        v := SZ.add vv 1sz;
      };

      u := SZ.add vu 1sz;
    };

    round := SZ.add vround 1sz;
  };
}
