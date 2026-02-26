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
open Pulse.Lib.WithPure

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas

(* Reachability specification *)

let has_edge (adj: Seq.seq int) (n: nat) (u v: nat) : prop =
  u < n /\ v < n /\ u * n + v < Seq.length adj /\ Seq.index adj (u * n + v) <> 0

let rec reachable_in (adj: Seq.seq int) (n: nat) (source v: nat) (steps: nat)
  : Tot prop (decreases steps)
  = if steps = 0 then v == source
    else (exists (u: nat). u < n /\ reachable_in adj n source u (steps - 1) /\ has_edge adj n u v)

(* ================================================================
   COUNT_NONWHITE — counts vertices with color != 0 in [0..k)
   ================================================================ *)

let rec count_nonwhite (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Tot nat (decreases k)
  = if k = 0 then 0
    else (if Seq.index s (k - 1) <> 0 then 1 else 0) + count_nonwhite s (k - 1)

let rec count_nonwhite_le (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Lemma (ensures count_nonwhite s k <= k) (decreases k)
  = if k = 0 then () else count_nonwhite_le s (k - 1)

let rec count_nonwhite_all_zero (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Lemma (requires forall (j:nat). j < k ==> Seq.index s j == 0)
          (ensures count_nonwhite s k == 0) (decreases k)
  = if k = 0 then () else count_nonwhite_all_zero s (k - 1)

(* If vertex j is WHITE, count_nonwhite < n *)
let rec count_nonwhite_has_white (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat)
  : Lemma (requires j < k /\ Seq.index s j == 0)
          (ensures count_nonwhite s k < k) (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then count_nonwhite_le s (k - 1)
    else count_nonwhite_has_white s (k - 1) j

(* Setting a WHITE vertex to non-zero increments count *)
let rec count_nonwhite_upd_white (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat) (v: int)
  : Lemma (requires j < k /\ Seq.index s j == 0 /\ v <> 0)
          (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                   count_nonwhite (Seq.upd s j v) k == count_nonwhite s k + 1) (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then begin
      let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s}) (v: int)
        : Lemma (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                         count_nonwhite (Seq.upd s j v) k' == count_nonwhite s k')
                (decreases k')
        = if k' = 0 then ()
          else (assert (Seq.index (Seq.upd s j v) (k'-1) == Seq.index s (k'-1)); aux s (k'-1) j v)
      in aux s (k-1) j v
    end
    else (assert (Seq.index (Seq.upd s j v) (k-1) == Seq.index s (k-1));
          count_nonwhite_upd_white s (k-1) j v)

(* Setting a non-WHITE vertex to non-zero preserves count *)
let rec count_nonwhite_upd_nonwhite (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat) (v: int)
  : Lemma (requires j < k /\ Seq.index s j <> 0 /\ v <> 0)
          (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                   count_nonwhite (Seq.upd s j v) k == count_nonwhite s k) (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then begin
      let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s}) (v: int)
        : Lemma (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                         count_nonwhite (Seq.upd s j v) k' == count_nonwhite s k')
                (decreases k')
        = if k' = 0 then ()
          else (assert (Seq.index (Seq.upd s j v) (k'-1) == Seq.index s (k'-1)); aux s (k'-1) j v)
      in aux s (k-1) j v
    end
    else (assert (Seq.index (Seq.upd s j v) (k-1) == Seq.index s (k-1));
          count_nonwhite_upd_nonwhite s (k-1) j v)

(* count with one element set to non-zero: for initialization *)
let count_nonwhite_upd_single (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat) (v: int)
  : Lemma (requires j < k /\ v <> 0 /\
                    (forall (i:nat). i < k ==> Seq.index s i == 0))
          (ensures count_nonwhite (Seq.upd s j v) k == 1) (decreases k)
  = count_nonwhite_all_zero s k;
    count_nonwhite_upd_white s k j v

let product_strict_bound (a b c d: nat)
  : Lemma (requires c < a /\ d < b)
          (ensures c * b + d < a * b)
  = ()

(* ================================================================
   PREDICATES — Named abstractions for BFS invariant clusters
   ================================================================ *)

(* Source invariant: source is discovered with distance 0 *)
let source_ok (scolor sdist: Seq.seq int) (source n: nat) : prop =
  source < n /\
  Seq.length scolor >= n /\ Seq.length sdist >= n /\
  Seq.index scolor source <> 0 /\
  Seq.index sdist source == 0

(* Queue entries are valid vertices with non-WHITE color *)
let queue_ok (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (n head tail: nat) : prop =
  head <= tail /\ tail <= n /\
  Seq.length squeue >= n /\ Seq.length scolor >= n /\
  (forall (i:nat). {:pattern (Seq.index squeue i)}
    i >= head /\ i < tail ==>
      SZ.v (Seq.index squeue i) < n /\
      Seq.index scolor (SZ.v (Seq.index squeue i)) <> 0)

(* Distance soundness for discovered vertices *)
let dist_ok (scolor sdist: Seq.seq int) (n: nat) : prop =
  Seq.length scolor >= n /\ Seq.length sdist >= n /\
  (forall (w:nat). {:pattern (Seq.index scolor w)}
    w < n /\ Seq.index scolor w <> 0 ==> Seq.index sdist w >= 0)

(* ================================================================
   PREDICATE LEMMAS — Key reasoning steps for BFS proof
   ================================================================ *)

(* Discovering (WHITE->GRAY) preserves source_ok *)
let discover_preserves_source_ok
  (scolor sdist: Seq.seq int) (source n j: nat) (dval: int)
  : Lemma
    (requires source_ok scolor sdist source n /\ j < n /\ n <= Seq.length scolor /\
             n <= Seq.length sdist /\ Seq.index scolor j == 0 /\ dval >= 0)
    (ensures source_ok (Seq.upd scolor j 1) (Seq.upd sdist j dval) source n)
  = ()  // source != j (source is non-WHITE, j is WHITE)

(* Blackening preserves source_ok *)
let blacken_preserves_source_ok
  (scolor sdist: Seq.seq int) (source n u: nat)
  : Lemma
    (requires source_ok scolor sdist source n /\ u < n /\ n <= Seq.length scolor)
    (ensures source_ok (Seq.upd scolor u 2) sdist source n)
  = ()  // Either u == source (2 <> 0) or u != source (unchanged)

(* Discovering preserves dist_ok *)
let discover_preserves_dist_ok
  (scolor sdist: Seq.seq int) (n j: nat) (dval: int)
  : Lemma
    (requires dist_ok scolor sdist n /\ j < n /\ n <= Seq.length scolor /\
             n <= Seq.length sdist /\ Seq.index scolor j == 0 /\ dval >= 0)
    (ensures dist_ok (Seq.upd scolor j 1) (Seq.upd sdist j dval) n)
  = ()  // old non-WHITE: unchanged; j: new color 1, dist dval >= 0

(* Blackening preserves dist_ok when u was non-WHITE *)
let blacken_preserves_dist_ok
  (scolor sdist: Seq.seq int) (n u: nat)
  : Lemma
    (requires dist_ok scolor sdist n /\ u < n /\ n <= Seq.length scolor /\
             Seq.index scolor u <> 0)
    (ensures dist_ok (Seq.upd scolor u 2) sdist n)
  = ()  // For w != u: unchanged. For w == u: was non-WHITE so dist >= 0, still >= 0.

(* Discovering preserves queue_ok for existing entries *)
let discover_preserves_queue_ok
  (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (n head tail j: nat)
  : Lemma
    (requires queue_ok scolor squeue n head tail /\ j < n /\ n <= Seq.length scolor /\
             Seq.index scolor j == 0)
    (ensures queue_ok (Seq.upd scolor j 1) squeue n head tail)
  = ()  // Queue entries are non-WHITE, j is WHITE, so j != any queue entry. Colors unchanged.

(* Blackening preserves queue_ok when u is not in queue range *)
let blacken_preserves_queue_ok
  (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (n head tail u: nat)
  : Lemma
    (requires queue_ok scolor squeue n head tail /\ u < n /\ n <= Seq.length scolor /\
             Seq.index scolor u <> 0)
    (ensures queue_ok (Seq.upd scolor u 2) squeue n head tail)
  = ()  // Queue entries are non-WHITE. Upd only changes u. If queue entry == u, old color <> 0, new color 2 <> 0.

(* Frame-based lemmas: derive predicates from maybe_discover's frame output *)

(* Frame preserves source_ok: non-WHITE vertices' color/dist unchanged *)
let frame_preserves_source_ok
  (scolor scolor' sdist sdist': Seq.seq int) (source n: nat)
  : Lemma
    (requires
      source_ok scolor sdist source n /\
      Seq.length scolor' >= n /\ Seq.length sdist' >= n /\
      (forall (w:nat). w < n /\ Seq.index scolor w <> 0 ==> Seq.index scolor' w == Seq.index scolor w) /\
      (forall (w:nat). w < n /\ Seq.index scolor w <> 0 ==> Seq.index sdist' w == Seq.index sdist w))
    (ensures source_ok scolor' sdist' source n)
  = ()

(* Frame preserves dist_ok when only WHITE->non-WHITE changes with non-negative dist *)
let frame_preserves_dist_ok
  (scolor scolor' sdist sdist': Seq.seq int) (n: nat)
  : Lemma
    (requires
      dist_ok scolor sdist n /\
      Seq.length scolor' >= n /\ Seq.length sdist' >= n /\
      // Frame: old non-WHITE unchanged
      (forall (w:nat). w < n /\ Seq.index scolor w <> 0 ==>
        Seq.index scolor' w == Seq.index scolor w /\ Seq.index sdist' w == Seq.index sdist w) /\
      // New non-WHITE vertices have non-negative dist
      (forall (w:nat). w < n /\ Seq.index scolor w == 0 /\ Seq.index scolor' w <> 0 ==>
        Seq.index sdist' w >= 0))
    (ensures dist_ok scolor' sdist' n)
  = ()

(* Proving queue_ok after discovering a WHITE vertex.
   Uses exact Seq.upd terms so Z3 can chain:
   - Seq.upd axiom fires on conclusion → introduces Seq.index squeue i
   - queue_ok trigger fires → gives scolor[squeue[i]] <> 0
   - scolor[v] == 0 + scolor[squeue[i]] <> 0 → squeue[i] <> v → Seq.upd scolor unchanged *)
#push-options "--z3rlimit 80"
let queue_ok_after_discover
  (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (n head tail: nat) (v: SZ.t)
  : Lemma
    (requires
      queue_ok scolor squeue n head tail /\
      SZ.v v < n /\
      Seq.index scolor (SZ.v v) == 0 /\
      tail < n)
    (ensures
      queue_ok (Seq.upd scolor (SZ.v v) 1)
               (Seq.upd squeue tail v)
               n head (tail + 1))
  = ()

#pop-options

(* ================================================================
   GHOST TICK — for complexity tracking
   ================================================================ *)

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

(* ================================================================
   COMPLEXITY ARITHMETIC LEMMA
   ================================================================ *)

//SNIPPET_START: bfs_complexity_bound
let lemma_bfs_complexity_bound (n k: nat)
  : Lemma (requires n >= 1 /\ k <= n)
          (ensures k * (n + 1) <= 2 * (n * n))
//SNIPPET_END: bfs_complexity_bound
  = ML.lemma_mult_le_right (n + 1) k n;  // k * (n+1) <= n * (n+1)
    assert (k * (n + 1) <= n * (n + 1));
    assert (n * (n + 1) == n * n + n * 1);
    ML.distributivity_add_right n n 1;   // n * (n+1) = n*n + n
    assert (n * n + n <= n * n + n * n); // since n <= n*n for n >= 1
    assert (n * n + n * n == 2 * (n * n))

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
    with_pure (
      SZ.v vv < SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v vtail < SZ.v n /\
      du >= 0 /\
      Seq.length scolor == SZ.v n /\
      Seq.length sdist == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      Seq.index scolor (SZ.v vv) == 0 /\
      dist_ok scolor sdist (SZ.v n)
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
      SZ.v vtail' == SZ.v vtail + 1 /\
      scolor' == Seq.upd scolor (SZ.v vv) 1 /\
      sdist' == Seq.upd sdist (SZ.v vv) (du + 1) /\
      squeue' == Seq.upd squeue (SZ.v vtail) vv /\
      dist_ok scolor' sdist' (SZ.v n)
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

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
fn maybe_discover
  (color: A.array int) (dist: A.array int) (pred: A.array int)
  (queue_data: A.array SZ.t) (q_tail: ref SZ.t)
  (u: SZ.t) (vv: SZ.t) (du: int) (n: SZ.t)
  (head: SZ.t) (has_edge_val: int) (cv: int)
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
    with_pure (
      SZ.v vv < SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v vtail <= SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sdist == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      du >= 0 /\
      cv == Seq.index scolor (SZ.v vv) /\
      count_nonwhite scolor (SZ.v n) == SZ.v vtail /\
      dist_ok scolor sdist (SZ.v n) /\
      queue_ok scolor squeue (SZ.v n) (SZ.v head) (SZ.v vtail)
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
      SZ.v vtail' >= SZ.v vtail /\
      count_nonwhite scolor' (SZ.v n) == SZ.v vtail' /\
      dist_ok scolor' sdist' (SZ.v n) /\
      queue_ok scolor' squeue' (SZ.v n) (SZ.v head) (SZ.v vtail') /\
      // Frame: non-WHITE vertices' colors preserved
      (forall (w:nat). {:pattern (Seq.index scolor w)}
        w < SZ.v n /\ Seq.index scolor w <> 0 ==>
          Seq.index scolor' w == Seq.index scolor w) /\
      // Frame: non-WHITE vertices' dists preserved
      (forall (w:nat). {:pattern (Seq.index sdist w)}
        w < SZ.v n /\ Seq.index scolor w <> 0 ==>
          Seq.index sdist' w == Seq.index sdist w)
    )
{
  if (has_edge_val <> 0 && cv = 0) {
    // cv == 0 means WHITE: count_nonwhite < n, so vtail < n
    count_nonwhite_has_white scolor (SZ.v n) (SZ.v vv);
    discover_vertex color dist pred queue_data q_tail u vv du n;
    // Establish count_nonwhite and queue_ok for new state
    with scolor'. assert (A.pts_to color scolor');
    count_nonwhite_upd_white scolor (SZ.v n) (SZ.v vv) 1;
    queue_ok_after_discover scolor squeue (SZ.v n) (SZ.v head) (SZ.v vtail) vv
  } else {
    ()
  }
}
#pop-options

#push-options "--z3rlimit 600 --fuel 2 --ifuel 1"
//SNIPPET_START: queue_bfs_sig
fn queue_bfs
  (adj: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (color: A.array int)
  (dist: A.array int)
  (pred: A.array int)
  (queue_data: A.array SZ.t)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  (#c0: erased nat)
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to dist sdist **
    A.pts_to pred spred **
    A.pts_to queue_data squeue **
    GR.pts_to ctr c0 **
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
  ensures exists* scolor' sdist' spred' squeue' (cf: nat).
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to dist sdist' **
    A.pts_to pred spred' **
    A.pts_to queue_data squeue' **
    GR.pts_to ctr cf **
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
        Seq.index sdist' w >= 0) /\
      // Complexity: at most 2 * n² ticks
      cf >= reveal c0 /\
      cf - reveal c0 <= 2 * (SZ.v n * SZ.v n)
    )
//SNIPPET_END: queue_bfs_sig
{
  // Step 1: Initialize all vertices
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi scolor_i sdist_i spred_i (vc: nat).
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to color scolor_i **
    A.pts_to dist sdist_i **
    A.pts_to pred spred_i **
    A.pts_to queue_data squeue **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length scolor_i == SZ.v n /\
      Seq.length sdist_i == SZ.v n /\
      Seq.length spred_i == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index scolor_i j == 0) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index sdist_i j == (-1)) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index spred_i j == (-1)) /\
      vc == reveal c0
    )
  {
    let vi = !i;
    A.op_Array_Assignment color vi 0;
    A.op_Array_Assignment dist vi (-1);
    A.op_Array_Assignment pred vi (-1);
    i := SZ.add vi 1sz
  };

  // Step 2: Initialize source — witness all-zeros state first for count_nonwhite
  with scolor_zeros. assert (A.pts_to color scolor_zeros);
  A.op_Array_Assignment color source 1;    // s.color = GRAY
  A.op_Array_Assignment dist source 0;     // s.d = 0
  A.op_Array_Assignment pred source (-1);  // s.pi = NIL

  // Step 3: ENQUEUE(Q, s)
  let mut q_head: SZ.t = 0sz;
  let mut q_tail: SZ.t = 0sz;
  A.op_Array_Assignment queue_data 0sz source;
  q_tail := 1sz;

  // Establish predicates for main loop entry
  count_nonwhite_upd_single scolor_zeros (SZ.v n) (SZ.v source) 1;

  // Step 4: Main BFS loop
  while (
    let vh = !q_head;
    let vt = !q_tail;
    SZ.lt vh vt
  )
  invariant exists* vhead vtail scolor_q sdist_q spred_q squeue_q (vc: nat).
    R.pts_to q_head vhead **
    R.pts_to q_tail vtail **
    A.pts_to adj sadj **
    A.pts_to color scolor_q **
    A.pts_to dist sdist_q **
    A.pts_to pred spred_q **
    A.pts_to queue_data squeue_q **
    GR.pts_to ctr vc **
    pure (
      Seq.length scolor_q == SZ.v n /\
      Seq.length sdist_q == SZ.v n /\
      Seq.length spred_q == SZ.v n /\
      Seq.length squeue_q == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      // Predicates
      source_ok scolor_q sdist_q (SZ.v source) (SZ.v n) /\
      dist_ok scolor_q sdist_q (SZ.v n) /\
      queue_ok scolor_q squeue_q (SZ.v n) (SZ.v vhead) (SZ.v vtail) /\
      count_nonwhite scolor_q (SZ.v n) == SZ.v vtail /\
      // Complexity: vhead * (n+1) ticks so far
      vc >= reveal c0 /\
      vc - reveal c0 <= SZ.v vhead * (SZ.v n + 1)
    )
  {
    // Tick for vertex dequeue
    tick ctr;
    
    // u = DEQUEUE(Q)
    let vhead = !q_head;
    let u: SZ.t = A.op_Array_Access queue_data vhead;

    // By queue_ok invariant: u < n and color[u] <> 0
    with scolor_deq. assert (A.pts_to color scolor_deq);
    with squeue_deq. assert (A.pts_to queue_data squeue_deq);
    assert (pure (SZ.v u < SZ.v n));
    assert (pure (Seq.index scolor_deq (SZ.v u) <> 0));
    q_head := SZ.add vhead 1sz;
    
    let du: int = A.op_Array_Access dist u;
    // u is non-WHITE (from queue_ok), so by dist_ok, du >= 0
    with sdist_deq. assert (A.pts_to dist sdist_deq);
    assert (pure (du >= 0));
    
    // For each v in G.Adj[u]
    let mut v: SZ.t = 0sz;
    while (!v <^ n)
    invariant exists* vv scolor_v sdist_v spred_v squeue_v vtail2 (vc2: nat).
      R.pts_to v vv **
      R.pts_to q_head (SZ.add vhead 1sz) **
      R.pts_to q_tail vtail2 **
      A.pts_to adj sadj **
      A.pts_to color scolor_v **
      A.pts_to dist sdist_v **
      A.pts_to pred spred_v **
      A.pts_to queue_data squeue_v **
      GR.pts_to ctr vc2 **
      pure (
        SZ.v vv <= SZ.v n /\
        SZ.v u < SZ.v n /\
        SZ.v vtail2 <= SZ.v n /\
        Seq.length scolor_v == SZ.v n /\
        Seq.length sdist_v == SZ.v n /\
        Seq.length spred_v == SZ.v n /\
        Seq.length squeue_v == SZ.v n /\
        SZ.fits (SZ.v u * SZ.v n) /\
        SZ.fits (SZ.v u * SZ.v n + SZ.v vv) /\
        // Predicates maintained through inner loop
        source_ok scolor_v sdist_v (SZ.v source) (SZ.v n) /\
        dist_ok scolor_v sdist_v (SZ.v n) /\
        count_nonwhite scolor_v (SZ.v n) == SZ.v vtail2 /\
        Seq.index scolor_v (SZ.v u) <> 0 /\
        queue_ok scolor_v squeue_v (SZ.v n) (SZ.v vhead + 1) (SZ.v vtail2) /\
        // Inner loop complexity:
        vc2 >= reveal c0 /\
        vc2 - reveal c0 <= SZ.v vhead * (SZ.v n + 1) + 1 + SZ.v vv
      )
    {
      let vv = !v;

      // Tick for edge check
      tick ctr;

      // Check if edge (u, v) exists
      product_strict_bound (SZ.v n) (SZ.v n) (SZ.v u) (SZ.v vv);
      let offset: SZ.t = SZ.mul u n;
      let idx: SZ.t = SZ.add offset vv;
      let has_edge_val: int = A.op_Array_Access adj idx;

      // Read color[v]
      let cv: int = A.op_Array_Access color vv;

      // CLRS: if v.color == WHITE and edge (u,v) exists, discover v
      maybe_discover color dist pred queue_data q_tail u vv du n (SZ.add vhead 1sz) has_edge_val cv;

      // Restore source_ok and u's color from frame properties
      with scolor_post. assert (A.pts_to color scolor_post);
      with sdist_post. assert (A.pts_to dist sdist_post);

      v := SZ.add vv 1sz
    };

    // u.color = BLACK
    with scolor_pre_black. assert (A.pts_to color scolor_pre_black);
    with sdist_pre_black. assert (A.pts_to dist sdist_pre_black);
    with squeue_pre_black. assert (A.pts_to queue_data squeue_pre_black);
    with vtail_pre_black. assert (R.pts_to q_tail vtail_pre_black);

    // Prove preservation lemmas for blackening
    blacken_preserves_source_ok scolor_pre_black sdist_pre_black (SZ.v source) (SZ.v n) (SZ.v u);
    blacken_preserves_dist_ok scolor_pre_black sdist_pre_black (SZ.v n) (SZ.v u);
    blacken_preserves_queue_ok scolor_pre_black squeue_pre_black (SZ.v n) (SZ.v vhead + 1) (SZ.v vtail_pre_black) (SZ.v u);
    count_nonwhite_upd_nonwhite scolor_pre_black (SZ.v n) (SZ.v u) 2;
    
    A.op_Array_Assignment color u 2;

    // Complexity: after inner loop with vv == n, vc2 - c0 <= vhead*(n+1) + 1 + n
    // = vhead*(n+1) + (n+1) = (vhead+1)*(n+1)
    with vc_outer. assert (GR.pts_to ctr vc_outer);
    assert (pure (reveal vc_outer - reveal c0 <= (SZ.v vhead + 1) * (SZ.v n + 1)))
  };
  
  // At loop exit: vc - c0 <= vhead * (n+1) <= n * (n+1) <= 2 * n²
  lemma_bfs_complexity_bound (SZ.v n) (SZ.v n);

  // Extract correctness from predicates
  with scolor_final. assert (A.pts_to color scolor_final);
  with sdist_final. assert (A.pts_to dist sdist_final);
  assert (pure (source_ok scolor_final sdist_final (SZ.v source) (SZ.v n)));
  assert (pure (dist_ok scolor_final sdist_final (SZ.v n)));
  assert (pure (Seq.index scolor_final (SZ.v source) <> 0));
  assert (pure (Seq.index sdist_final (SZ.v source) == 0));
  assert (pure (forall (w: nat). w < SZ.v n /\ Seq.index scolor_final w <> 0 ==> Seq.index sdist_final w >= 0))
}
#pop-options
