(*
   ISSUE: SMT scalability cliff in Pulse nested loops with extra existentials.

   DESCRIPTION:
   When a Pulse `while` loop (the "outer" loop) has a nested `while` loop
   (the "inner" loop), and the inner loop's invariant has many quantified
   conjuncts that reference `with`-bound variables from the outer scope,
   adding an extra existential to the outer loop's invariant can cause
   the inner loop's SMT queries to become unsolvable — even at very high
   z3rlimit (tested up to 800).

   The extra existential (e.g., a ghost counter for complexity tracking)
   need not be referenced by the inner loop at all. Its mere presence in
   the outer scope increases the inner loop's SMT context enough to tip
   Z3 past a scalability cliff.

   REPRODUCTION:
   - The `works` function below (3 outer existentials + complex inner loop
     invariant with ~15 quantified conjuncts) verifies at z3rlimit 40.
   - The `breaks` function is identical except the outer loop invariant
     has one additional existential `(gv: nat)` with `GR.pts_to gctr gv`.
     This causes "Assertion failed" in the inner loop body at z3rlimit 800.

   This is NOT a Pulse elaboration bug — the encoding is well-typed.
   It is an SMT scalability issue: the extra existential pollutes the
   inner loop's proof context, making otherwise-tractable queries fail.

   WORKAROUND (used in CLRS.Ch24.Dijkstra.fst):
   Extract the outer loop body (containing the inner loop + bridge lemma
   calls) into a separate top-level `fn`. This gives the inner loop its
   own Pulse elaboration scope, so the extra existential is a function
   parameter rather than an outer-loop existential, keeping SMT queries
   tractable.

   STATUS: open — affects ch24-sssp Dijkstra implementation.
   Worked around by extracting `dijkstra_relax_round` as separate fn.
*)

module ISSUE_03_nested_loop_existential
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Vec
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// Predicates similar to the Dijkstra proof
let mono_decreasing (s_old s_new: Seq.seq int) (n: nat) : prop =
  Seq.length s_old == n /\ Seq.length s_new == n /\
  (forall (j: nat). j < n ==> Seq.index s_new j <= Seq.index s_old j)

let all_nonneg (s: Seq.seq int) (n: nat) : prop =
  Seq.length s == n /\ (forall (j: nat). j < n ==> Seq.index s j >= 0)

let all_bounded (s: Seq.seq int) (n: nat) : prop =
  Seq.length s == n /\ (forall (j: nat). j < n ==> Seq.index s j >= 0 /\ Seq.index s j <= 1000000)

let tri_prop (ws s sv: Seq.seq int) (n: nat) : prop =
  Seq.length s == n /\ Seq.length ws >= n * n /\ Seq.length sv == n /\
  (forall (u v: nat). u < n /\ v < n /\ u * n + v < Seq.length ws /\ Seq.index sv u = 1 ==>
    (let w = Seq.index ws (u * n + v) in
     let du = Seq.index s u in let dv = Seq.index s v in
     (w < 1000000 /\ du < 1000000) ==> dv <= du + w))

let vis_le (s sv: Seq.seq int) (n: nat) : prop =
  Seq.length s == n /\ Seq.length sv == n /\
  (forall (x u: nat). x < n /\ u < n /\ Seq.index sv x = 1 /\ Seq.index sv u = 0 ==>
    Seq.index s x <= Seq.index s u)

// Bridge lemma: re-establish invariants after relaxation (simplified)
let bridge
  (ws s_old s_new sv_old: Seq.seq int) (n u: nat)
  : Lemma
    (requires
      Seq.length s_old == n /\ Seq.length s_new == n /\
      Seq.length ws == n * n /\ Seq.length sv_old == n /\
      n > 0 /\ u < n /\
      Seq.index sv_old u = 0 /\
      tri_prop ws s_old sv_old n /\
      vis_le s_old sv_old n /\
      (forall (x:nat). x < n /\ Seq.index sv_old x = 1 ==>
        Seq.index s_new x == Seq.index s_old x) /\
      Seq.index s_new u == Seq.index s_old u /\
      mono_decreasing s_old s_new n /\
      (forall (v:nat). v < n /\ Seq.index sv_old v = 0 ==>
        Seq.index s_new v >= Seq.index s_old u) /\
      (forall (v:nat). v < n /\ u * n + v < Seq.length ws ==>
        (let w = Seq.index ws (u * n + v) in
         let du = Seq.index s_new u in
         (w < 1000000 /\ du < 1000000) ==> Seq.index s_new v <= du + w)))
    (ensures
      (let sv_new = Seq.upd sv_old u 1 in
       tri_prop ws s_new sv_new n /\ vis_le s_new sv_new n))
  = ()

let lemma_2d (u v n: nat)
  : Lemma (requires u < n /\ v < n /\ SZ.fits (n * n))
          (ensures SZ.fits (u * n + v) /\ SZ.fits (u * n) /\ u * n + v < n * n)
  = assert (u * n <= (n-1) * n); assert ((n-1) * n + v < n * n)

// ========== THIS WORKS — outer loop has 3 existentials ==========
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries always"
fn works
  (ws: A.array int) (arr: A.array int) (vis: V.vec int) (n: SZ.t)
  (#sws: erased (Seq.seq int)) (#s0: erased (Seq.seq int))
  requires
    A.pts_to ws sws ** A.pts_to arr s0 **
    pure (SZ.v n > 0 /\ Seq.length sws == SZ.v n * SZ.v n /\ Seq.length s0 == SZ.v n /\
          SZ.fits (SZ.v n * SZ.v n))
  ensures exists* sf.
    A.pts_to ws sws ** A.pts_to arr sf **
    pure (Seq.length sf == SZ.v n)
{
  let visited = V.alloc 0 n;
  let mut round: SZ.t = 0sz;
  while (let vr = !round; vr <^ n)
  invariant exists* vr s_cur sv_cur.
    R.pts_to round vr ** A.pts_to arr s_cur ** V.pts_to visited sv_cur **
    A.pts_to ws sws **
    pure (SZ.v vr <= SZ.v n /\ Seq.length s_cur == SZ.v n /\
          Seq.length sv_cur == SZ.v n /\
          all_nonneg s_cur (SZ.v n) /\ all_bounded s_cur (SZ.v n) /\
          tri_prop sws s_cur sv_cur (SZ.v n) /\
          vis_le s_cur sv_cur (SZ.v n) /\
          (forall (j:nat). j < SZ.v n ==> (Seq.index sv_cur j = 0 \/ Seq.index sv_cur j = 1)))
  decreases (SZ.v n - SZ.v !round)
  {
    let vr = !round;
    with s_pre. assert (A.pts_to arr s_pre);
    with sv_pre. assert (V.pts_to visited sv_pre);
    let u = 0sz;  // simplified: always pick vertex 0
    V.op_Array_Assignment visited u 1;

    let du = A.op_Array_Access arr u;

    // Inner relax loop
    let mut j: SZ.t = 0sz;
    while (let vj = !j; vj <^ n)
    invariant exists* vj s_inner sv_inner.
      R.pts_to j vj ** A.pts_to arr s_inner ** V.pts_to visited sv_inner **
      A.pts_to ws sws **
      pure (
        SZ.v vj <= SZ.v n /\
        Seq.length s_inner == SZ.v n /\ Seq.length sv_inner == SZ.v n /\
        Seq.length s_pre == SZ.v n /\ Seq.length sv_pre == SZ.v n /\
        Seq.index sv_pre (SZ.v u) = 0 /\
        tri_prop sws s_pre sv_pre (SZ.v n) /\
        vis_le s_pre sv_pre (SZ.v n) /\
        all_nonneg s_inner (SZ.v n) /\ all_bounded s_inner (SZ.v n) /\
        sv_inner == Seq.upd sv_pre (SZ.v u) 1 /\
        (forall (x:nat). x < SZ.v n /\ (Seq.index sv_pre x = 1 \/ x = SZ.v u) ==>
          Seq.index s_inner x == Seq.index s_pre x) /\
        mono_decreasing s_pre s_inner (SZ.v n) /\
        (forall (v':nat). v' < SZ.v vj /\ v' < SZ.v n /\
          SZ.v u * SZ.v n + v' < Seq.length sws ==>
          (let w = Seq.index sws (SZ.v u * SZ.v n + v') in
           let d = Seq.index s_inner (SZ.v u) in
           (w < 1000000 /\ d < 1000000) ==> Seq.index s_inner v' <= d + w)) /\
        (forall (v':nat). v' < SZ.v n /\ Seq.index sv_pre v' = 0 ==>
          Seq.index s_inner v' >= Seq.index s_pre (SZ.v u)) /\
        (forall (v':nat). v' < SZ.v vj /\ v' < SZ.v n ==>
          Seq.index s_inner v' == Seq.index s_pre v' \/
          (Seq.index s_inner v' == Seq.index s_pre (SZ.v u) + Seq.index sws (SZ.v u * SZ.v n + v') /\
           Seq.index sws (SZ.v u * SZ.v n + v') < 1000000 /\
           Seq.index s_pre (SZ.v u) < 1000000)) /\
        (forall (v':nat). v' >= SZ.v vj /\ v' < SZ.v n ==>
          Seq.index s_inner v' == Seq.index s_pre v')
      )
    decreases (SZ.v n - SZ.v !j)
    {
      let vj = !j;
      lemma_2d (SZ.v u) (SZ.v vj) (SZ.v n);
      let widx = u *^ n +^ vj;
      let w = A.op_Array_Access ws widx;
      let vis_j = V.op_Array_Access visited vj;
      let old_d = A.op_Array_Access arr vj;
      let can = (vis_j = 0 && w < 1000000 && du < 1000000);
      let s = du + w;
      let upd = (can && s < old_d);
      let nd: int = (if upd then s else old_d);
      A.op_Array_Assignment arr vj nd;
      j := vj +^ 1sz;
    };
    let _ = !j;

    // Bridge lemma — uses s_pre and sv_pre (with-bound from outer scope)
    with s_post. assert (A.pts_to arr s_post);
    bridge sws s_pre s_post sv_pre (SZ.v n) (SZ.v u);

    round := vr +^ 1sz;
  };
  let _ = !round;
  V.free visited;
  ()
}
#pop-options

// ========== THIS SHOULD BREAK — outer loop has 4 existentials ==========
// Identical to `works` but adds (gv: nat) + GR.pts_to to outer invariant.
// Fails at z3rlimit 800 with "Assertion failed" in inner loop body.
#push-options "--z3rlimit 800 --fuel 0 --ifuel 0 --split_queries always"
fn breaks
  (ws: A.array int) (arr: A.array int) (vis: V.vec int) (n: SZ.t) (gctr: GR.ref nat)
  (#sws: erased (Seq.seq int)) (#s0: erased (Seq.seq int)) (#g0: erased nat)
  requires
    A.pts_to ws sws ** A.pts_to arr s0 ** GR.pts_to gctr g0 **
    pure (SZ.v n > 0 /\ Seq.length sws == SZ.v n * SZ.v n /\ Seq.length s0 == SZ.v n /\
          SZ.fits (SZ.v n * SZ.v n))
  ensures exists* sf (gf: nat).
    A.pts_to ws sws ** A.pts_to arr sf ** GR.pts_to gctr gf **
    pure (Seq.length sf == SZ.v n)
{
  let visited = V.alloc 0 n;
  let mut round: SZ.t = 0sz;
  while (let vr = !round; vr <^ n)
  invariant exists* vr s_cur sv_cur (gv: nat).
    R.pts_to round vr ** A.pts_to arr s_cur ** V.pts_to visited sv_cur **
    A.pts_to ws sws ** GR.pts_to gctr gv **
    pure (SZ.v vr <= SZ.v n /\ Seq.length s_cur == SZ.v n /\
          Seq.length sv_cur == SZ.v n /\
          all_nonneg s_cur (SZ.v n) /\ all_bounded s_cur (SZ.v n) /\
          tri_prop sws s_cur sv_cur (SZ.v n) /\
          vis_le s_cur sv_cur (SZ.v n) /\
          (forall (j:nat). j < SZ.v n ==> (Seq.index sv_cur j = 0 \/ Seq.index sv_cur j = 1)))
  decreases (SZ.v n - SZ.v !round)
  {
    let vr = !round;
    with s_pre. assert (A.pts_to arr s_pre);
    with sv_pre. assert (V.pts_to visited sv_pre);
    let u = 0sz;
    V.op_Array_Assignment visited u 1;

    let du = A.op_Array_Access arr u;

    // Inner relax loop — IDENTICAL to `works`
    let mut j: SZ.t = 0sz;
    while (let vj = !j; vj <^ n)
    invariant exists* vj s_inner sv_inner.
      R.pts_to j vj ** A.pts_to arr s_inner ** V.pts_to visited sv_inner **
      A.pts_to ws sws **
      pure (
        SZ.v vj <= SZ.v n /\
        Seq.length s_inner == SZ.v n /\ Seq.length sv_inner == SZ.v n /\
        Seq.length s_pre == SZ.v n /\ Seq.length sv_pre == SZ.v n /\
        Seq.index sv_pre (SZ.v u) = 0 /\
        tri_prop sws s_pre sv_pre (SZ.v n) /\
        vis_le s_pre sv_pre (SZ.v n) /\
        all_nonneg s_inner (SZ.v n) /\ all_bounded s_inner (SZ.v n) /\
        sv_inner == Seq.upd sv_pre (SZ.v u) 1 /\
        (forall (x:nat). x < SZ.v n /\ (Seq.index sv_pre x = 1 \/ x = SZ.v u) ==>
          Seq.index s_inner x == Seq.index s_pre x) /\
        mono_decreasing s_pre s_inner (SZ.v n) /\
        (forall (v':nat). v' < SZ.v vj /\ v' < SZ.v n /\
          SZ.v u * SZ.v n + v' < Seq.length sws ==>
          (let w = Seq.index sws (SZ.v u * SZ.v n + v') in
           let d = Seq.index s_inner (SZ.v u) in
           (w < 1000000 /\ d < 1000000) ==> Seq.index s_inner v' <= d + w)) /\
        (forall (v':nat). v' < SZ.v n /\ Seq.index sv_pre v' = 0 ==>
          Seq.index s_inner v' >= Seq.index s_pre (SZ.v u)) /\
        (forall (v':nat). v' < SZ.v vj /\ v' < SZ.v n ==>
          Seq.index s_inner v' == Seq.index s_pre v' \/
          (Seq.index s_inner v' == Seq.index s_pre (SZ.v u) + Seq.index sws (SZ.v u * SZ.v n + v') /\
           Seq.index sws (SZ.v u * SZ.v n + v') < 1000000 /\
           Seq.index s_pre (SZ.v u) < 1000000)) /\
        (forall (v':nat). v' >= SZ.v vj /\ v' < SZ.v n ==>
          Seq.index s_inner v' == Seq.index s_pre v')
      )
    decreases (SZ.v n - SZ.v !j)
    {
      let vj = !j;
      lemma_2d (SZ.v u) (SZ.v vj) (SZ.v n);
      let widx = u *^ n +^ vj;
      let w = A.op_Array_Access ws widx;
      let vis_j = V.op_Array_Access visited vj;
      let old_d = A.op_Array_Access arr vj;
      let can = (vis_j = 0 && w < 1000000 && du < 1000000);
      let s = du + w;
      let upd = (can && s < old_d);
      let nd: int = (if upd then s else old_d);
      A.op_Array_Assignment arr vj nd;
      j := vj +^ 1sz;
    };
    let _ = !j;

    // Bridge lemma — FAILS with "Ill-typed term" / "Assertion failed"
    with s_post. assert (A.pts_to arr s_post);
    bridge sws s_pre s_post sv_pre (SZ.v n) (SZ.v u);

    round := vr +^ 1sz;
  };
  let _ = !round;
  V.free visited;
  ()
}
#pop-options
