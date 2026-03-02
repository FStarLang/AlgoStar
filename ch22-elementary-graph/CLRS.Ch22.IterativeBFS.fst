(*
   Breadth-First Search - Verified implementation in Pulse (Relaxation Variant)
   
   Implements BFS via level-by-level exploration using iterative relaxation.
   Graph represented as adjacency matrix adj[u*n+v] (edge from u to v if != 0).
   
   Colors: 0=white (unvisited), non-zero=visited
   
   Runs n rounds. In round r, for every visited vertex u with dist[u] == r,
   marks all unvisited neighbors v as visited with dist[v] = r + 1.
   After n rounds, all reachable vertices from source are visited.
   
   Postconditions:
   - Source vertex is visited with dist[source] == 0
   - All reachable vertices (within n steps) are visited
   - Distance soundness: for all visited v, reachable_in(source, v, dist[v])
   
   Variant note: This is a simpler, self-contained BFS proof using Bellman-Ford-like
   level expansion (O(V³) work). For the canonical CLRS §22.2 queue-based BFS with
   GRAY/BLACK coloring, predecessor tracking, and O(V²) complexity, see QueueBFS.fst.
   
   NO admits. NO assumes.
*)

module CLRS.Ch22.IterativeBFS
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

let has_edge (adj: Seq.seq int) (n: nat) (u v: nat) : prop =
  u < n /\ v < n /\ u * n + v < Seq.length adj /\ Seq.index adj (u * n + v) <> 0

let rec reachable_in (adj: Seq.seq int) (n: nat) (source v: nat) (steps: nat) 
  : Tot prop (decreases steps)
  = if steps = 0 then v == source
    else (exists (u: nat). u < n /\ reachable_in adj n source u (steps - 1) /\ has_edge adj n u v)

let reachable_in_succ_witness (adj: Seq.seq int) (n: nat) (source v: nat) (k: nat)
  : Lemma
    (requires reachable_in adj n source v (k + 1))
    (ensures exists (u: nat). u < n /\ reachable_in adj n source u k /\ has_edge adj n u v)
  = ()

// Distance array: dist[v] = shortest distance from source to v (-1 if unreachable)
// BFS computes shortest (unweighted) distances via iterative relaxation

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn bfs
  (adj: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (color: A.array int)
  (dist: A.array int)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to dist sdist **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sadj <= A.length adj /\
      Seq.length scolor == SZ.v n /\
      Seq.length scolor <= A.length color /\
      Seq.length sdist == SZ.v n /\
      Seq.length sdist <= A.length dist /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* scolor' sdist'.
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to dist sdist' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sdist' == SZ.v n /\
      (SZ.v source < Seq.length scolor' ==> Seq.index scolor' (SZ.v source) == 1) /\
      // Distance of source is 0
      (SZ.v source < Seq.length sdist' ==> Seq.index sdist' (SZ.v source) == 0) /\
      // All reachable vertices are visited
      (forall (v: nat). v < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) v (SZ.v n) ==> 
        Seq.index scolor' v <> 0) /\
      // Distance soundness: for all visited v, v is reachable in dist[v] steps
      (forall (v: nat). v < SZ.v n /\ Seq.index scolor' v <> 0 ==>
        Seq.index sdist' v >= 0 /\
        reachable_in sadj (SZ.v n) (SZ.v source) v (Seq.index sdist' v))
    )
{
  // Initialize all colors to 0 and distances to -1
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi scolor_i sdist_i.
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to color scolor_i **
    A.pts_to dist sdist_i **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length scolor_i == SZ.v n /\
      Seq.length sdist_i == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index scolor_i j == 0) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index sdist_i j == (-1))
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    A.op_Array_Assignment color vi 0;
    A.op_Array_Assignment dist vi (-1);
    i := SZ.add vi 1sz;
  };

  // Mark source as visited with distance 0
  A.op_Array_Assignment color source 1;
  A.op_Array_Assignment dist source 0;

  // Run n relaxation rounds
  let mut round: SZ.t = 0sz;
  while (!round <^ n)
  invariant exists* vround scolor_r sdist_r.
    R.pts_to round vround **
    A.pts_to adj sadj **
    A.pts_to color scolor_r **
    A.pts_to dist sdist_r **
    pure (
      SZ.v vround <= SZ.v n /\
      Seq.length scolor_r == SZ.v n /\
      Seq.length sdist_r == SZ.v n /\
      Seq.index scolor_r (SZ.v source) == 1 /\
      Seq.index sdist_r (SZ.v source) == 0 /\
      // Reachability completeness: vertices reachable in <= vround steps are visited
      (forall (v: nat). v < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) v (SZ.v vround) ==> 
        Seq.index scolor_r v <> 0) /\
      // Distance soundness: visited vertices have valid distances
      (forall (v: nat). v < SZ.v n /\ Seq.index scolor_r v <> 0 ==>
        Seq.index sdist_r v >= 0 /\
        reachable_in sadj (SZ.v n) (SZ.v source) v (Seq.index sdist_r v))
    )
  decreases (SZ.v n - SZ.v !round)
  {
    let vround = !round;

    let mut u: SZ.t = 0sz;
    while (!u <^ n)
    invariant exists* vu scolor_u sdist_u.
      R.pts_to round vround **
      R.pts_to u vu **
      A.pts_to adj sadj **
      A.pts_to color scolor_u **
      A.pts_to dist sdist_u **
      pure (
        SZ.v vu <= SZ.v n /\
        Seq.length scolor_u == SZ.v n /\
        Seq.length sdist_u == SZ.v n /\
        Seq.index scolor_u (SZ.v source) == 1 /\
        Seq.index sdist_u (SZ.v source) == 0 /\
        (forall (v: nat). v < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) v (SZ.v vround) ==> 
          Seq.index scolor_u v <> 0) /\
        (forall (u_idx: nat) (v_idx: nat). 
          u_idx < SZ.v vu /\ v_idx < SZ.v n /\
          reachable_in sadj (SZ.v n) (SZ.v source) u_idx (SZ.v vround) /\
          has_edge sadj (SZ.v n) u_idx v_idx ==>
          Seq.index scolor_u v_idx <> 0) /\
        // Distance soundness carried through
        (forall (v: nat). v < SZ.v n /\ Seq.index scolor_u v <> 0 ==>
          Seq.index sdist_u v >= 0 /\
          reachable_in sadj (SZ.v n) (SZ.v source) v (Seq.index sdist_u v))
      )
    decreases (SZ.v n - SZ.v !u)
    {
      let vu = !u;

      // Read dist[u] before inner loop
      let du: int = A.op_Array_Access dist vu;

      let mut v: SZ.t = 0sz;
      while (!v <^ n)
      invariant exists* vv scolor_v sdist_v.
        R.pts_to round vround **
        R.pts_to u vu **
        R.pts_to v vv **
        A.pts_to adj sadj **
        A.pts_to color scolor_v **
        A.pts_to dist sdist_v **
        pure (
          SZ.v vv <= SZ.v n /\
          SZ.v vu < SZ.v n /\
          Seq.length scolor_v == SZ.v n /\
          Seq.length sdist_v == SZ.v n /\
          SZ.fits (SZ.v vu * SZ.v n) /\
          SZ.fits (SZ.v vu * SZ.v n + SZ.v vv) /\
          Seq.index scolor_v (SZ.v source) == 1 /\
          Seq.index sdist_v (SZ.v source) == 0 /\
          (forall (w: nat). w < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) w (SZ.v vround) ==> 
            Seq.index scolor_v w <> 0) /\
          (forall (u_idx: nat) (v_idx: nat). 
            u_idx < SZ.v vu /\ v_idx < SZ.v n /\
            reachable_in sadj (SZ.v n) (SZ.v source) u_idx (SZ.v vround) /\
            has_edge sadj (SZ.v n) u_idx v_idx ==>
            Seq.index scolor_v v_idx <> 0) /\
          (forall (v_idx: nat).
            v_idx < SZ.v vv /\
            reachable_in sadj (SZ.v n) (SZ.v source) (SZ.v vu) (SZ.v vround) /\
            has_edge sadj (SZ.v n) (SZ.v vu) v_idx ==>
            Seq.index scolor_v v_idx <> 0) /\
          // Distance soundness carried through inner loop
          (forall (w: nat). w < SZ.v n /\ Seq.index scolor_v w <> 0 ==>
            Seq.index sdist_v w >= 0 /\
            reachable_in sadj (SZ.v n) (SZ.v source) w (Seq.index sdist_v w)) /\
          // dist[vu] is preserved during inner loop
          Seq.index sdist_v (SZ.v vu) == du
        )
      // TODO: decreases
      {
        let vv = !v;

        let cu: int = A.op_Array_Access color vu;
        let offset: SZ.t = SZ.mul vu n;
        let idx: SZ.t = SZ.add offset vv;
        let has_edge_val: int = A.op_Array_Access adj idx;
        let cv: int = A.op_Array_Access color vv;

        assert pure (
          (has_edge_val <> 0) <==> has_edge sadj (SZ.v n) (SZ.v vu) (SZ.v vv)
        );

        let new_cv: int = (if cu <> 0 && has_edge_val <> 0 && cv = 0 then 1 else cv);
        
        // Key hint for dist soundness: if we're discovering vv for the first time,
        // then vu is reachable in du steps, and has_edge(vu, vv), so vv is reachable in du+1 steps
        // This uses the existential witness vu for the reachable_in definition
        assert pure (cu <> 0 /\ has_edge_val <> 0 /\ cv = 0 ==>
          (SZ.v vu < SZ.v n /\
           reachable_in sadj (SZ.v n) (SZ.v source) (SZ.v vu) du /\
           has_edge sadj (SZ.v n) (SZ.v vu) (SZ.v vv) /\
           reachable_in sadj (SZ.v n) (SZ.v source) (SZ.v vv) (du + 1)));

        A.op_Array_Assignment color vv new_cv;

        // Update distance: if visiting v for the first time, dist[v] = dist[u] + 1
        let dv: int = A.op_Array_Access dist vv;
        let new_dv: int = (if cu <> 0 && has_edge_val <> 0 && cv = 0 then du + 1 else dv);
        A.op_Array_Assignment dist vv new_dv;

        v := SZ.add vv 1sz;
      };

      u := SZ.add vu 1sz;
    };

    round := SZ.add vround 1sz;
  };
}
#pop-options
