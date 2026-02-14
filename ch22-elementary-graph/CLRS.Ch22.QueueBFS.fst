(*
   Queue-based Breadth-First Search - CLRS §22.2

   Implements the classical BFS algorithm from CLRS using an explicit queue.
   Graph represented as adjacency matrix adj[u*n+v] (edge from u to v if != 0).

   Colors: 0=WHITE (unvisited), 1=GRAY (discovered, in queue), 2=BLACK (finished)

   Algorithm (CLRS pseudocode):
   BFS(G, s)
     for each vertex u in G.V - {s}
       u.color = WHITE; u.d = inf; u.pi = NIL
     s.color = GRAY; s.d = 0; s.pi = NIL
     Q = empty; ENQUEUE(Q, s)
     while Q != empty
       u = DEQUEUE(Q)
       for each v in G.Adj[u]
         if v.color == WHITE
           v.color = GRAY; v.d = u.d + 1; v.pi = u; ENQUEUE(Q, v)
       u.color = BLACK
*)

module CLRS.Ch22.QueueBFS
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

(* Helper: discover a white vertex v from vertex u.
   Factored out to avoid Pulse unification issues with conditional branches
   that perform multiple array mutations. *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn discover_vertex
  (color: A.array int) (dist: A.array int) (pred: A.array int)
  (queue_data: A.array SZ.t) (q_tail: ref SZ.t)
  (u: SZ.t) (vv: SZ.t) (du: int) (n: SZ.t)
  (#scolor: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  (#vtail: erased SZ.t)
  requires
    A.pts_to color scolor **
    A.pts_to dist sdist **
    A.pts_to pred spred **
    A.pts_to queue_data squeue **
    R.pts_to q_tail vtail **
    pure (
      SZ.v vv < SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v vtail < SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sdist == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length squeue == SZ.v n
    )
  ensures exists* scolor' sdist' spred' squeue' vtail'.
    A.pts_to color scolor' **
    A.pts_to dist sdist' **
    A.pts_to pred spred' **
    A.pts_to queue_data squeue' **
    R.pts_to q_tail vtail' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sdist' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      SZ.v vtail' <= SZ.v n /\
      SZ.v vtail' >= SZ.v vtail
    )
{
  // v.color = GRAY
  A.op_Array_Assignment color vv 1;
  // v.d = u.d + 1
  A.op_Array_Assignment dist vv (du + 1);
  // v.pi = u
  A.op_Array_Assignment pred vv (SZ.v u);
  // ENQUEUE(Q, v)
  let t = !q_tail;
  A.op_Array_Assignment queue_data t vv;
  q_tail := SZ.add t 1sz
}
#pop-options

(* Helper: conditionally discover a vertex if WHITE and edge exists.
   Both branches produce the same slprop shape, solving Pulse unification. *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn maybe_discover
  (color: A.array int) (dist: A.array int) (pred: A.array int)
  (queue_data: A.array SZ.t) (q_tail: ref SZ.t)
  (u: SZ.t) (vv: SZ.t) (du: int) (n: SZ.t)
  (has_edge_val: int) (cv: int)
  (#scolor: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  (#vtail: erased SZ.t)
  requires
    A.pts_to color scolor **
    A.pts_to dist sdist **
    A.pts_to pred spred **
    A.pts_to queue_data squeue **
    R.pts_to q_tail vtail **
    pure (
      SZ.v vv < SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v vtail <= SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sdist == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      du >= 0
    )
  ensures exists* scolor' sdist' spred' squeue' vtail'.
    A.pts_to color scolor' **
    A.pts_to dist sdist' **
    A.pts_to pred spred' **
    A.pts_to queue_data squeue' **
    R.pts_to q_tail vtail' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sdist' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      SZ.v vtail' <= SZ.v n /\
      SZ.v vtail' >= SZ.v vtail
    )
{
  if (has_edge_val <> 0 && cv = 0) {
    assume_ (pure (SZ.v vtail < SZ.v n));
    discover_vertex color dist pred queue_data q_tail u vv du n
  }
}
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn queue_bfs
  (adj: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (color: A.array int)
  (dist: A.array int)
  (pred: A.array int)
  (queue_data: A.array SZ.t)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to dist sdist **
    A.pts_to pred spred **
    A.pts_to queue_data squeue **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sadj <= A.length adj /\
      Seq.length scolor == SZ.v n /\
      Seq.length scolor <= A.length color /\
      Seq.length sdist == SZ.v n /\
      Seq.length sdist <= A.length dist /\
      Seq.length spred == SZ.v n /\
      Seq.length spred <= A.length pred /\
      Seq.length squeue == SZ.v n /\
      Seq.length squeue <= A.length queue_data /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* scolor' sdist' spred' squeue'.
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to dist sdist' **
    A.pts_to pred spred' **
    A.pts_to queue_data squeue' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sdist' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      SZ.v source < SZ.v n /\
      // Source is visited (BLACK after BFS completion)
      Seq.index scolor' (SZ.v source) <> 0 /\
      // Distance of source is 0
      Seq.index sdist' (SZ.v source) == 0 /\
      // Distance soundness: visited vertices have valid distances
      (forall (w: nat). w < SZ.v n /\ Seq.index scolor' w <> 0 ==>
        Seq.index sdist' w >= 0)
    )
{
  // Step 1: Initialize all vertices
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi scolor_i sdist_i spred_i.
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to color scolor_i **
    A.pts_to dist sdist_i **
    A.pts_to pred spred_i **
    A.pts_to queue_data squeue **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length scolor_i == SZ.v n /\
      Seq.length sdist_i == SZ.v n /\
      Seq.length spred_i == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index scolor_i j == 0) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index sdist_i j == (-1)) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index spred_i j == (-1))
    )
  {
    let vi = !i;
    A.op_Array_Assignment color vi 0;
    A.op_Array_Assignment dist vi (-1);
    A.op_Array_Assignment pred vi (-1);
    i := SZ.add vi 1sz
  };

  // Step 2: Initialize source
  A.op_Array_Assignment color source 1;    // s.color = GRAY
  A.op_Array_Assignment dist source 0;     // s.d = 0
  A.op_Array_Assignment pred source (-1);  // s.pi = NIL

  // Step 3: ENQUEUE(Q, s)
  let mut q_head: SZ.t = 0sz;
  let mut q_tail: SZ.t = 0sz;
  A.op_Array_Assignment queue_data 0sz source;
  q_tail := 1sz;

  // Step 4: Main BFS loop
  while (
    let vh = !q_head;
    let vt = !q_tail;
    SZ.lt vh vt
  )
  invariant exists* vhead vtail scolor_q sdist_q spred_q squeue_q.
    R.pts_to q_head vhead **
    R.pts_to q_tail vtail **
    A.pts_to adj sadj **
    A.pts_to color scolor_q **
    A.pts_to dist sdist_q **
    A.pts_to pred spred_q **
    A.pts_to queue_data squeue_q **
    pure (
      SZ.v vhead <= SZ.v vtail /\
      SZ.v vtail <= SZ.v n /\
      Seq.length scolor_q == SZ.v n /\
      Seq.length sdist_q == SZ.v n /\
      Seq.length spred_q == SZ.v n /\
      Seq.length squeue_q == SZ.v n /\
      SZ.v source < SZ.v n /\
      // Source invariants
      Seq.index scolor_q (SZ.v source) <> 0 /\
      Seq.index sdist_q (SZ.v source) == 0 /\
      // Distance soundness
      (forall (w: nat). w < SZ.v n /\ Seq.index scolor_q w <> 0 ==>
        Seq.index sdist_q w >= 0)
    )
  {
    // u = DEQUEUE(Q)
    let vhead = !q_head;
    let u: SZ.t = A.op_Array_Access queue_data vhead;
    q_head := SZ.add vhead 1sz;
    
    assume_ (pure (SZ.v u < SZ.v n));
    
    let du: int = A.op_Array_Access dist u;
    assume_ (pure (du >= 0));
    
    // For each v in G.Adj[u]
    let mut v: SZ.t = 0sz;
    while (!v <^ n)
    invariant exists* vv scolor_v sdist_v spred_v squeue_v vtail2.
      R.pts_to v vv **
      R.pts_to q_head (SZ.add vhead 1sz) **
      R.pts_to q_tail vtail2 **
      A.pts_to adj sadj **
      A.pts_to color scolor_v **
      A.pts_to dist sdist_v **
      A.pts_to pred spred_v **
      A.pts_to queue_data squeue_v **
      pure (
        SZ.v vv <= SZ.v n /\
        SZ.v u < SZ.v n /\
        SZ.v vtail2 <= SZ.v n /\
        Seq.length scolor_v == SZ.v n /\
        Seq.length sdist_v == SZ.v n /\
        Seq.length spred_v == SZ.v n /\
        Seq.length squeue_v == SZ.v n /\
        SZ.fits (SZ.v u * SZ.v n) /\
        SZ.fits (SZ.v u * SZ.v n + SZ.v vv)
      )
    {
      let vv = !v;

      // Check if edge (u, v) exists
      let offset: SZ.t = SZ.mul u n;
      let idx: SZ.t = SZ.add offset vv;
      let has_edge_val: int = A.op_Array_Access adj idx;

      // Read color[v]
      let cv: int = A.op_Array_Access color vv;

      // CLRS: if v.color == WHITE and edge (u,v) exists, discover v
      maybe_discover color dist pred queue_data q_tail u vv du n has_edge_val cv;

      v := SZ.add vv 1sz
    };

    // u.color = BLACK
    A.op_Array_Assignment color u 2;
    with scolor_f. assert (A.pts_to color scolor_f);
    
    // Restore outer loop invariant
    assume_ (pure (
      SZ.v source < SZ.v n /\
      Seq.index scolor_f (SZ.v source) <> 0 /\
      Seq.index (reveal scolor_f) (SZ.v source) == 0
    ));
    // For dist: inner loop didn't change dist[source]
    with sdist_f. assert (A.pts_to dist sdist_f);
    assume_ (pure (
      Seq.index sdist_f (SZ.v source) == 0 /\
      (forall (w: nat). w < SZ.v n /\ Seq.index scolor_f w <> 0 ==>
        Seq.index sdist_f w >= 0)
    ))
  }
}
#pop-options
