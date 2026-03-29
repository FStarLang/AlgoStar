(*
   Queue-based Breadth-First Search - CLRS §22.2 (Canonical BFS Implementation)

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

module CLRS.Ch22.BFS.Impl
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

open CLRS.Ch22.Graph.Common

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

// product_strict_bound imported from CLRS.Ch22.Graph.Common

(* ================================================================
   COUNT_GRAY — counts vertices with color == 1 in [0..k)
   ================================================================ *)

let rec count_gray (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Tot nat (decreases k)
  = if k = 0 then 0
    else count_gray s (k - 1) + (if Seq.index s (k - 1) = 1 then 1 else 0)

let rec count_gray_all_zero (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Lemma (requires forall (j:nat). j < k ==> Seq.index s j == 0)
          (ensures count_gray s k == 0) (decreases k)
  = if k = 0 then () else count_gray_all_zero s (k - 1)

let rec count_gray_upd_to_gray (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat)
  : Lemma (requires j < k /\ Seq.index s j == 0)
          (ensures count_gray (Seq.upd s j 1) k == count_gray s k + 1) (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then begin
      let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s})
        : Lemma (ensures count_gray (Seq.upd s j 1) k' == count_gray s k') (decreases k')
        = if k' = 0 then ()
          else (assert (Seq.index (Seq.upd s j 1) (k'-1) == Seq.index s (k'-1)); aux s (k'-1) j)
      in aux s (k-1) j
    end
    else (assert (Seq.index (Seq.upd s j 1) (k-1) == Seq.index s (k-1));
          count_gray_upd_to_gray s (k-1) j)

let rec count_gray_upd_from_gray (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat)
  : Lemma (requires j < k /\ Seq.index s j == 1)
          (ensures count_gray (Seq.upd s j 2) k == count_gray s k - 1) (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then begin
      let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s})
        : Lemma (ensures count_gray (Seq.upd s j 2) k' == count_gray s k') (decreases k')
        = if k' = 0 then ()
          else (assert (Seq.index (Seq.upd s j 2) (k'-1) == Seq.index s (k'-1)); aux s (k'-1) j)
      in aux s (k-1) j
    end
    else (assert (Seq.index (Seq.upd s j 2) (k-1) == Seq.index s (k-1));
          count_gray_upd_from_gray s (k-1) j)

let rec count_gray_zero_no_gray (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Lemma (requires count_gray s k == 0)
          (ensures forall (j:nat). j < k ==> Seq.index s j <> 1) (decreases k)
  = if k = 0 then () else count_gray_zero_no_gray s (k - 1)

let rec count_gray_upd_nonwhite_to_nonwhite (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat) (v: int)
  : Lemma (requires j < k /\ Seq.index s j <> 1 /\ v <> 1)
          (ensures count_gray (Seq.upd s j v) k == count_gray s k) (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then begin
      let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s}) (v: int)
        : Lemma (ensures count_gray (Seq.upd s j v) k' == count_gray s k') (decreases k')
        = if k' = 0 then ()
          else (assert (Seq.index (Seq.upd s j v) (k'-1) == Seq.index s (k'-1)); aux s (k'-1) j v)
      in aux s (k-1) j v
    end
    else (assert (Seq.index (Seq.upd s j v) (k-1) == Seq.index s (k-1));
          count_gray_upd_nonwhite_to_nonwhite s (k-1) j v)

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

(* Queue entries are GRAY (color 1) and unique *)
let queue_gray_unique (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (n head tail: nat) : prop =
  Seq.length squeue >= n /\ Seq.length scolor >= n /\
  head <= tail /\ tail <= n /\
  (forall (i:nat). {:pattern (Seq.index squeue i)}
    i >= head /\ i < tail ==>
      SZ.v (Seq.index squeue i) < n /\
      Seq.index scolor (SZ.v (Seq.index squeue i)) == 1) /\
  (forall (i j: nat). {:pattern (Seq.index squeue i); (Seq.index squeue j)}
    i >= head /\ i < tail /\ j >= head /\ j < tail /\
    Seq.index squeue i == Seq.index squeue j ==> i == j)

(* Scanned-all: every non-WHITE, non-GRAY vertex has all neighbors non-WHITE *)
let scanned_all (sadj: Seq.seq int) (n: nat) (scolor: Seq.seq int) : prop =
  Seq.length scolor >= n /\ Seq.length sadj >= n * n /\
  (forall (u v: nat). {:pattern (Seq.index scolor u); (Seq.index sadj (u * n + v))}
    u < n /\ v < n /\ Seq.index scolor u <> 0 /\ Seq.index scolor u <> 1 /\ Seq.index sadj (u * n + v) <> 0 ==>
      Seq.index scolor v <> 0)

(* Scanned partial: for vertex u, neighbors 0..k are non-WHITE *)
let scanned_partial (sadj: Seq.seq int) (n: nat) (scolor: Seq.seq int) (u k: nat) : prop =
  Seq.length scolor >= n /\ Seq.length sadj >= n * n /\ u < n /\
  (forall (v: nat). v < k /\ v < n /\ Seq.index sadj (u * n + v) <> 0 ==>
    Seq.index scolor v <> 0)

(* Distance soundness for discovered vertices *)
let dist_ok (scolor sdist: Seq.seq int) (n: nat) : prop =
  Seq.length scolor >= n /\ Seq.length sdist >= n /\
  (forall (w:nat). {:pattern (Seq.index scolor w)}
    w < n /\ Seq.index scolor w <> 0 ==> Seq.index sdist w >= 0)

(* Reachability correctness: every discovered vertex is reachable from source,
   and its distance is a witness — reachable_in adj n source v (dist[v]) *)
let dist_reachable (adj: Seq.seq int) (n: nat) (scolor sdist: Seq.seq int) (source: nat) : prop =
  Seq.length scolor >= n /\ Seq.length sdist >= n /\
  Seq.length adj == n * n /\
  (forall (w:nat). {:pattern (Seq.index scolor w)}
    w < n /\ Seq.index scolor w <> 0 ==>
      Seq.index sdist w >= 0 /\
      reachable_in adj n source w (Seq.index sdist w))

(* Predecessor distance consistency: dist[v] = dist[pred[v]] + 1 for discovered vertices with valid preds *)
let pred_dist_ok (scolor sdist spred: Seq.seq int) (n: nat) : prop =
  Seq.length scolor >= n /\ Seq.length sdist >= n /\ Seq.length spred >= n /\
  (forall (v:nat). {:pattern (Seq.index spred v)}
    v < n /\ Seq.index scolor v <> 0 /\ Seq.index spred v >= 0 /\ Seq.index spred v < n ==>
    Seq.index scolor (Seq.index spred v) <> 0 /\
    Seq.index sdist v == Seq.index sdist (Seq.index spred v) + 1)

(* Source initialization preserves pred_dist_ok (no non-WHITE vertex has valid pred yet) *)
let init_pred_dist_ok (scolor sdist spred: Seq.seq int) (n source: nat)
  : Lemma
    (requires n <= Seq.length scolor /\ n <= Seq.length sdist /\ n <= Seq.length spred /\
              source < n /\
              (forall (j:nat). j < n ==> Seq.index scolor j == 0) /\
              (forall (j:nat). j < n ==> Seq.index spred j == (-1)))
    (ensures pred_dist_ok (Seq.upd scolor source 1) (Seq.upd sdist source 0)
                          (Seq.upd spred source (-1)) n)
  = ()  // source has pred = -1 (< 0), so the implication is vacuously true for source.
        // All other vertices are WHITE, so the implication is vacuously true for them.

(* Discovering vertex j from u preserves pred_dist_ok *)
let discover_preserves_pred_dist_ok
  (scolor sdist spred: Seq.seq int) (n u j: nat) (du: int)
  : Lemma
    (requires
      pred_dist_ok scolor sdist spred n /\
      j < n /\ u < n /\ n <= Seq.length scolor /\ n <= Seq.length sdist /\ n <= Seq.length spred /\
      Seq.index scolor j == 0 /\ Seq.index scolor u <> 0 /\
      Seq.index sdist u == du /\ du >= 0)
    (ensures
      pred_dist_ok (Seq.upd scolor j 1) (Seq.upd sdist j (du + 1)) (Seq.upd spred j u) n)
  = ()  // For w != j: color, dist, pred unchanged. Pred's color unchanged. All equalities preserved.
        // For w == j: pred[j] = u (non-WHITE), dist[j] = du+1 = dist[u]+1 = dist[pred[j]]+1. ✓

(* Blackening preserves pred_dist_ok — only changes color, not dist or pred *)
let blacken_preserves_pred_dist_ok
  (scolor sdist spred: Seq.seq int) (n u: nat)
  : Lemma
    (requires pred_dist_ok scolor sdist spred n /\ u < n /\ n <= Seq.length scolor /\
              Seq.index scolor u <> 0)
    (ensures pred_dist_ok (Seq.upd scolor u 2) sdist spred n)
  = ()

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

(* Discovering vertex j from u preserves dist_reachable.
   Precondition: u is discovered (color[u] <> 0) with dist[u] = du,
   edge (u, j) exists, j is WHITE, and we set dist[j] = du + 1.
   Then reachable_in source j (du+1) follows from reachable_in source u du + has_edge u j. *)
let discover_preserves_dist_reachable
  (adj: Seq.seq int) (n: nat) (scolor sdist: Seq.seq int) (source u j: nat) (du: int)
  : Lemma
    (requires
      dist_reachable adj n scolor sdist source /\
      j < n /\ u < n /\ n <= Seq.length scolor /\ n <= Seq.length sdist /\
      Seq.length adj == n * n /\
      Seq.index scolor j == 0 /\    // j is WHITE
      Seq.index scolor u <> 0 /\    // u is discovered
      Seq.index sdist u == du /\
      du >= 0 /\
      has_edge adj n u j)           // edge (u, j) exists
    (ensures
      dist_reachable adj n (Seq.upd scolor j 1) (Seq.upd sdist j (du + 1)) source)
  = // For any w that was already non-WHITE: color and dist unchanged (w != j since j is WHITE)
    // For w == j: new dist is du + 1, and reachable_in source j (du + 1)
    //   because reachable_in source u du (from dist_reachable) and has_edge u j
    assert (reachable_in adj n source u du);  // from dist_reachable, u is non-WHITE
    assert (reachable_in adj n source j (du + 1))  // unfold: exists u. reachable_in source u du /\ has_edge u j

(* Blackening preserves dist_reachable — only changes color, not dist *)
let blacken_preserves_dist_reachable
  (adj: Seq.seq int) (n: nat) (scolor sdist: Seq.seq int) (source u: nat)
  : Lemma
    (requires
      dist_reachable adj n scolor sdist source /\
      u < n /\ n <= Seq.length scolor /\ Seq.index scolor u <> 0)
    (ensures dist_reachable adj n (Seq.upd scolor u 2) sdist source)
  = ()  // For w != u: unchanged. For w == u: was non-WHITE, dist unchanged, reachability unchanged.

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
#push-options "--z3rlimit 10 --split_queries always"
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

(* Establishing dist_reachable after source initialization.
   After init: only source is non-WHITE with dist=0.
   reachable_in adj n source source 0 = (source == source) = True *)
let init_dist_reachable
  (adj: Seq.seq int) (n: nat) (scolor_zeros sdist_zeros: Seq.seq int) (source: nat)
  : Lemma
    (requires
      source < n /\ n <= Seq.length scolor_zeros /\ n <= Seq.length sdist_zeros /\
      Seq.length adj == n * n /\
      (forall (j:nat). j < n ==> Seq.index scolor_zeros j == 0))
    (ensures
      dist_reachable adj n
        (Seq.upd scolor_zeros source 1)
        (Seq.upd sdist_zeros source 0)
        source)
  = // Only source is non-WHITE (color 1). All others are WHITE (color 0, unchanged by upd since j != source).
    // For source: dist = 0, reachable_in adj n source source 0 = (source == source) = True.
    ()

(* ================================================================
   SCANNED_ALL / SCANNED_PARTIAL PRESERVATION LEMMAS
   ================================================================ *)

let init_scanned_all (sadj scolor: Seq.seq int) (n: nat)
  : Lemma (requires n <= Seq.length scolor /\ n * n <= Seq.length sadj /\
                    (forall (j:nat). j < n ==> Seq.index scolor j == 0))
          (ensures scanned_all sadj n scolor)
  = ()

let discover_preserves_scanned_all (sadj scolor: Seq.seq int) (n j: nat)
  : Lemma (requires scanned_all sadj n scolor /\ j < n /\ Seq.index scolor j == 0)
          (ensures scanned_all sadj n (Seq.upd scolor j 1))
  = ()

let blacken_preserves_scanned_all (sadj scolor: Seq.seq int) (n u: nat)
  : Lemma (requires scanned_all sadj n scolor /\ u < n /\ n <= Seq.length scolor /\
                    Seq.index scolor u <> 0 /\
                    scanned_partial sadj n scolor u n)
          (ensures scanned_all sadj n (Seq.upd scolor u 2))
  = ()

let init_scanned_partial (sadj scolor: Seq.seq int) (n u: nat)
  : Lemma (requires n <= Seq.length scolor /\ n * n <= Seq.length sadj /\ u < n)
          (ensures scanned_partial sadj n scolor u 0)
  = ()

let discover_preserves_scanned_partial (sadj scolor: Seq.seq int) (n u k j: nat)
  : Lemma (requires scanned_partial sadj n scolor u k /\ j < n /\ Seq.index scolor j == 0)
          (ensures scanned_partial sadj n (Seq.upd scolor j 1) u k)
  = ()

let extend_scanned_partial_discover (sadj scolor: Seq.seq int) (n u vv: nat)
  : Lemma
    (requires scanned_partial sadj n scolor u vv /\ vv < n /\ u < n /\
              n <= Seq.length scolor /\ n * n <= Seq.length sadj /\ Seq.index scolor vv == 0)
    (ensures scanned_partial sadj n (Seq.upd scolor vv 1) u (vv + 1))
  = ()

let extend_scanned_partial_skip (sadj scolor: Seq.seq int) (n u vv: nat)
  : Lemma
    (requires scanned_partial sadj n scolor u vv /\ vv < n /\ u < n /\
              n <= Seq.length scolor /\ n * n <= Seq.length sadj /\
              (Seq.index sadj (u * n + vv) = 0 \/ Seq.index scolor vv <> 0))
    (ensures scanned_partial sadj n scolor u (vv + 1))
  = ()

let blacken_preserves_scanned_partial (sadj scolor: Seq.seq int) (n u k: nat)
  : Lemma (requires scanned_partial sadj n scolor u k /\ u < n /\ n <= Seq.length scolor /\
                    Seq.index scolor u <> 0)
          (ensures scanned_partial sadj n (Seq.upd scolor u 2) u k)
  = ()

(* ================================================================
   COMPLETENESS LEMMA — induction on reachability steps
   ================================================================ *)

let rec completeness_lemma
  (sadj: Seq.seq int) (n: nat) (scolor: Seq.seq int) (source v: nat) (steps: nat)
  : Lemma
    (requires
      scanned_all sadj n scolor /\
      n <= Seq.length scolor /\ n * n <= Seq.length sadj /\
      source < n /\ v < n /\
      Seq.index scolor source <> 0 /\
      (forall (u:nat). u < n ==> Seq.index scolor u <> 1) /\
      reachable_in sadj n source v steps)
    (ensures Seq.index scolor v <> 0)
    (decreases steps)
  = if steps = 0 then ()
    else
      let aux (u: nat)
        : Lemma (requires u < n /\ reachable_in sadj n source u (steps - 1) /\ has_edge sadj n u v)
                (ensures Seq.index scolor v <> 0)
        = completeness_lemma sadj n scolor source u (steps - 1)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(* Wrapper for completeness: universally quantified version *)
let bfs_completeness_all (sadj: Seq.seq int) (n: nat) (scolor: Seq.seq int) (source: nat)
  : Lemma
    (requires
      scanned_all sadj n scolor /\
      n <= Seq.length scolor /\ n * n <= Seq.length sadj /\
      source < n /\
      Seq.index scolor source <> 0 /\
      (forall (u:nat). u < n ==> Seq.index scolor u <> 1))
    (ensures
      forall (v: nat) (k: nat). v < n /\ reachable_in sadj n source v k ==>
        Seq.index scolor v <> 0)
  = let aux (v: nat) (k: nat)
      : Lemma (v < n /\ reachable_in sadj n source v k ==>
                  Seq.index scolor v <> 0)
      = if v < n then
          FStar.Classical.move_requires (completeness_lemma sadj n scolor source v) k
        else ()
    in
    FStar.Classical.forall_intro_2 aux

(* ================================================================
   QUEUE_GRAY_UNIQUE PRESERVATION LEMMAS
   ================================================================ *)

let discover_preserves_queue_gray_unique
  (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (n head tail j: nat)
  : Lemma
    (requires queue_gray_unique scolor squeue n head tail /\ j < n /\
             n <= Seq.length scolor /\ Seq.index scolor j == 0)
    (ensures queue_gray_unique (Seq.upd scolor j 1) squeue n head tail)
  = ()

#push-options "--z3rlimit 10 --split_queries always"
let queue_gray_unique_after_discover
  (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (n head tail: nat) (v: SZ.t)
  : Lemma
    (requires queue_gray_unique scolor squeue n head tail /\
             SZ.v v < n /\ Seq.index scolor (SZ.v v) == 0 /\ tail < n)
    (ensures queue_gray_unique (Seq.upd scolor (SZ.v v) 1) (Seq.upd squeue tail v) n head (tail + 1))
  = ()
#pop-options

let blacken_preserves_queue_gray_unique
  (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (n head tail u: nat)
  : Lemma
    (requires queue_gray_unique scolor squeue n head tail /\
             u < n /\ n <= Seq.length scolor /\
             Seq.index scolor u == 1 /\
             (forall (i:nat). i >= head /\ i < tail ==> SZ.v (Seq.index squeue i) <> u))
    (ensures queue_gray_unique (Seq.upd scolor u 2) squeue n head tail)
  = ()

(* Helper: u-not-in-queue is preserved through maybe_discover *)
let u_not_in_queue_after_discover
  (scolor_pre: Seq.seq int)
  (squeue_pre squeue_post: Seq.seq SZ.t)
  (n vhead vtail_pre vtail_post u: nat)
  : Lemma
    (requires
      Seq.length squeue_pre >= n /\ Seq.length squeue_post >= n /\
      Seq.length scolor_pre >= n /\
      vtail_pre <= n /\ vtail_post <= n /\ u < n /\
      // u was not in old queue [vhead+1, vtail_pre)
      (forall (i:nat). {:pattern (Seq.index squeue_pre i)}
        i >= vhead + 1 /\ i < vtail_pre ==> SZ.v (Seq.index squeue_pre i) <> u) /\
      // queue frame: old entries preserved
      (forall (i:nat). {:pattern (Seq.index squeue_post i)}
        i < vtail_pre ==> Seq.index squeue_post i == Seq.index squeue_pre i) /\
      // new entry was WHITE, u was GRAY
      (vtail_post > vtail_pre ==>
        (vtail_pre < Seq.length squeue_post /\
         SZ.v (Seq.index squeue_post vtail_pre) < Seq.length scolor_pre /\
         Seq.index scolor_pre (SZ.v (Seq.index squeue_post vtail_pre)) == 0)) /\
      Seq.index scolor_pre u == 1 /\
      vtail_post >= vtail_pre /\ vtail_post <= vtail_pre + 1)
    (ensures
      forall (i:nat). {:pattern (Seq.index squeue_post i)}
        i >= vhead + 1 /\ i < vtail_post ==> SZ.v (Seq.index squeue_post i) <> u)
  = ()

(* ================================================================
   GHOST TICK — for complexity tracking
   ================================================================ *)

// incr_nat and tick imported from CLRS.Ch22.Graph.Common

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

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
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
      spred' == Seq.upd spred (SZ.v vv) (SZ.v u) /\
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

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
fn maybe_discover
  (adj: A.array int)
  (color: A.array int) (dist: A.array int) (pred: A.array int)
  (queue_data: A.array SZ.t) (q_tail: ref SZ.t)
  (u: SZ.t) (vv: SZ.t) (du: int) (n: SZ.t)
  (head: SZ.t) (has_edge_val: int) (cv: int)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  (#vtail: erased SZ.t)
  (source: SZ.t)
  requires
    A.pts_to adj sadj **
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
      Seq.length sadj == SZ.v n * SZ.v n /\
      du >= 0 /\
      Seq.index sdist (SZ.v u) == du /\
      Seq.index scolor (SZ.v u) <> 0 /\
      cv == Seq.index scolor (SZ.v vv) /\
      (has_edge_val == Seq.index sadj (SZ.v u * SZ.v n + SZ.v vv)) /\
      count_nonwhite scolor (SZ.v n) == SZ.v vtail /\
      dist_ok scolor sdist (SZ.v n) /\
      dist_reachable sadj (SZ.v n) scolor sdist (SZ.v source) /\
      queue_ok scolor squeue (SZ.v n) (SZ.v head) (SZ.v vtail) /\
      // Completeness predicates
      queue_gray_unique scolor squeue (SZ.v n) (SZ.v head) (SZ.v vtail) /\
      scanned_all sadj (SZ.v n) scolor /\
      scanned_partial sadj (SZ.v n) scolor (SZ.v u) (SZ.v vv) /\
      pred_dist_ok scolor sdist spred (SZ.v n)
    )
  ensures exists* scolor' sdist' spred' squeue' vtail'.
    A.pts_to adj sadj **
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
      dist_reachable sadj (SZ.v n) scolor' sdist' (SZ.v source) /\
      queue_ok scolor' squeue' (SZ.v n) (SZ.v head) (SZ.v vtail') /\
      // Frame: non-WHITE vertices' colors preserved
      (forall (w:nat). {:pattern (Seq.index scolor w)}
        w < SZ.v n /\ Seq.index scolor w <> 0 ==>
          Seq.index scolor' w == Seq.index scolor w) /\
      // Frame: non-WHITE vertices' dists preserved
      (forall (w:nat). {:pattern (Seq.index sdist w)}
        w < SZ.v n /\ Seq.index scolor w <> 0 ==>
          Seq.index sdist' w == Seq.index sdist w) /\
      // Completeness postconditions
      queue_gray_unique scolor' squeue' (SZ.v n) (SZ.v head) (SZ.v vtail') /\
      scanned_all sadj (SZ.v n) scolor' /\
      scanned_partial sadj (SZ.v n) scolor' (SZ.v u) (SZ.v vv + 1) /\
      pred_dist_ok scolor' sdist' spred' (SZ.v n) /\
      count_gray scolor' (SZ.v n) == count_gray scolor (SZ.v n) + (SZ.v vtail' - SZ.v vtail) /\
      // Queue frame: entries below vtail unchanged
      (forall (i:nat). {:pattern (Seq.index squeue' i)}
        i < SZ.v vtail ==> Seq.index squeue' i == Seq.index squeue i) /\
      // New entry info: if a new entry was added, it was WHITE in pre-state
      (SZ.v vtail' > SZ.v vtail ==>
        Seq.index scolor (SZ.v (Seq.index squeue' (SZ.v vtail))) == 0) /\
      // At most one new entry
      SZ.v vtail' <= SZ.v vtail + 1
    )
{
  if (has_edge_val <> 0 && cv = 0) {
    // cv == 0 means WHITE: count_nonwhite < n, so vtail < n
    count_nonwhite_has_white scolor (SZ.v n) (SZ.v vv);
    // Edge exists and vv is WHITE: discover vv from u
    product_strict_bound (SZ.v n) (SZ.v n) (SZ.v u) (SZ.v vv);
    discover_preserves_dist_reachable sadj (SZ.v n) scolor sdist (SZ.v source) (SZ.v u) (SZ.v vv) du;
    discover_preserves_pred_dist_ok scolor sdist spred (SZ.v n) (SZ.v u) (SZ.v vv) du;

    // Completeness lemma calls (before mutation)
    discover_preserves_scanned_all sadj scolor (SZ.v n) (SZ.v vv);
    extend_scanned_partial_discover sadj scolor (SZ.v n) (SZ.v u) (SZ.v vv);
    count_gray_upd_to_gray scolor (SZ.v n) (SZ.v vv);
    discover_preserves_queue_gray_unique scolor squeue (SZ.v n) (SZ.v head) (SZ.v vtail) (SZ.v vv);
    queue_gray_unique_after_discover scolor squeue (SZ.v n) (SZ.v head) (SZ.v vtail) vv;

    discover_vertex color dist pred queue_data q_tail u vv du n;
    // Establish count_nonwhite and queue_ok for new state
    with scolor'. assert (A.pts_to color scolor');
    count_nonwhite_upd_white scolor (SZ.v n) (SZ.v vv) 1;
    queue_ok_after_discover scolor squeue (SZ.v n) (SZ.v head) (SZ.v vtail) vv
  } else {
    // No discovery: extend scanned_partial
    extend_scanned_partial_skip sadj scolor (SZ.v n) (SZ.v u) (SZ.v vv)
  }
}
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
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
      // Reachability: every discovered vertex is reachable from source,
      // witnessed by dist[v] steps
      (forall (w: nat). w < SZ.v n /\ Seq.index scolor' w <> 0 ==>
        reachable_in sadj (SZ.v n) (SZ.v source) w (Seq.index sdist' w)) /\
      // Completeness: every reachable vertex is discovered
      (forall (v: nat) (k: nat). v < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) v k ==>
        Seq.index scolor' v <> 0) /\
      // Predecessor distance consistency: for discovered non-source vertices,
      // dist[v] = dist[pred[v]] + 1 and pred[v] is also discovered
      (forall (v: nat). v < SZ.v n /\ Seq.index scolor' v <> 0 /\
        Seq.index spred' v >= 0 /\ Seq.index spred' v < SZ.v n ==>
        Seq.index scolor' (Seq.index spred' v) <> 0 /\
        Seq.index sdist' v == Seq.index sdist' (Seq.index spred' v) + 1) /\
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
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    A.op_Array_Assignment color vi 0;
    A.op_Array_Assignment dist vi (-1);
    A.op_Array_Assignment pred vi (-1);
    i := SZ.add vi 1sz
  };

  // Step 2: Initialize source — witness all-zeros state first for count_nonwhite
  with scolor_zeros. assert (A.pts_to color scolor_zeros);
  with sdist_zeros. assert (A.pts_to dist sdist_zeros);
  with spred_zeros. assert (A.pts_to pred spred_zeros);
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
  init_dist_reachable sadj (SZ.v n) scolor_zeros sdist_zeros (SZ.v source);

  // Establish completeness predicates for main loop entry
  init_scanned_all sadj scolor_zeros (SZ.v n);
  discover_preserves_scanned_all sadj scolor_zeros (SZ.v n) (SZ.v source);
  count_gray_all_zero scolor_zeros (SZ.v n);
  count_gray_upd_to_gray scolor_zeros (SZ.v n) (SZ.v source);
  init_pred_dist_ok scolor_zeros sdist_zeros spred_zeros (SZ.v n) (SZ.v source);

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
      dist_reachable sadj (SZ.v n) scolor_q sdist_q (SZ.v source) /\
      queue_ok scolor_q squeue_q (SZ.v n) (SZ.v vhead) (SZ.v vtail) /\
      count_nonwhite scolor_q (SZ.v n) == SZ.v vtail /\
      // Completeness predicates
      queue_gray_unique scolor_q squeue_q (SZ.v n) (SZ.v vhead) (SZ.v vtail) /\
      scanned_all sadj (SZ.v n) scolor_q /\
      pred_dist_ok scolor_q sdist_q spred_q (SZ.v n) /\
      count_gray scolor_q (SZ.v n) == SZ.v vtail - SZ.v vhead /\
      // Complexity: vhead * (n+1) ticks so far
      vc >= reveal c0 /\
      vc - reveal c0 <= SZ.v vhead * (SZ.v n + 1)
    )
  decreases (SZ.v n - SZ.v !q_head)
  {
    // Tick for vertex dequeue
    tick ctr;
    
    // u = DEQUEUE(Q)
    let vhead = !q_head;
    let u: SZ.t = A.op_Array_Access queue_data vhead;

    // By queue_ok invariant: u < n and color[u] <> 0
    // By queue_gray_unique: color[u] == 1 (GRAY)
    with scolor_deq. assert (A.pts_to color scolor_deq);
    with squeue_deq. assert (A.pts_to queue_data squeue_deq);
    assert (pure (SZ.v u < SZ.v n));
    assert (pure (Seq.index scolor_deq (SZ.v u) <> 0));
    assert (pure (Seq.index scolor_deq (SZ.v u) == 1));
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
        dist_reachable sadj (SZ.v n) scolor_v sdist_v (SZ.v source) /\
        count_nonwhite scolor_v (SZ.v n) == SZ.v vtail2 /\
        Seq.index scolor_v (SZ.v u) == 1 /\
        Seq.index sdist_v (SZ.v u) == du /\
        queue_ok scolor_v squeue_v (SZ.v n) (SZ.v vhead + 1) (SZ.v vtail2) /\
        // Completeness predicates for inner loop
        queue_gray_unique scolor_v squeue_v (SZ.v n) (SZ.v vhead + 1) (SZ.v vtail2) /\
        scanned_all sadj (SZ.v n) scolor_v /\
        scanned_partial sadj (SZ.v n) scolor_v (SZ.v u) (SZ.v vv) /\
        pred_dist_ok scolor_v sdist_v spred_v (SZ.v n) /\
        count_gray scolor_v (SZ.v n) == SZ.v vtail2 - SZ.v vhead /\
        // u not in active queue [vhead+1, vtail2)
        (forall (i:nat). {:pattern (Seq.index squeue_v i)}
          i >= SZ.v vhead + 1 /\ i < SZ.v vtail2 ==> SZ.v (Seq.index squeue_v i) <> SZ.v u) /\
        // Inner loop complexity:
        vc2 >= reveal c0 /\
        vc2 - reveal c0 <= SZ.v vhead * (SZ.v n + 1) + 1 + SZ.v vv
      )
    decreases (SZ.v n - SZ.v !v)
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

      // Capture pre-state for assertions after maybe_discover
      with scolor_pre. assert (A.pts_to color scolor_pre);
      with sdist_pre. assert (A.pts_to dist sdist_pre);
      with squeue_pre. assert (A.pts_to queue_data squeue_pre);
      with vtail_pre. assert (R.pts_to q_tail vtail_pre);

      // CLRS: if v.color == WHITE and edge (u,v) exists, discover v
      maybe_discover adj color dist pred queue_data q_tail u vv du n (SZ.add vhead 1sz) has_edge_val cv source;

      // Witness post-state
      with scolor_post. assert (A.pts_to color scolor_post);
      with sdist_post. assert (A.pts_to dist sdist_post);
      with squeue_post. assert (A.pts_to queue_data squeue_post);
      with vtail_post. assert (R.pts_to q_tail vtail_post);

      // Re-establish source_ok from frame
      frame_preserves_source_ok scolor_pre scolor_post sdist_pre sdist_post (SZ.v source) (SZ.v n);

      // Re-establish u's color from frame (u was non-WHITE, so color unchanged)
      assert (pure (Seq.index scolor_post (SZ.v u) == Seq.index scolor_pre (SZ.v u)));
      assert (pure (Seq.index scolor_post (SZ.v u) == 1));
      assert (pure (Seq.index sdist_post (SZ.v u) == du));

      // count_gray: from postcondition and invariant
      assert (pure (count_gray scolor_post (SZ.v n) == count_gray scolor_pre (SZ.v n) + (SZ.v vtail_post - SZ.v vtail_pre)));
      assert (pure (count_gray scolor_pre (SZ.v n) == SZ.v vtail_pre - SZ.v vhead));
      assert (pure (count_gray scolor_post (SZ.v n) == SZ.v vtail_post - SZ.v vhead));

      // u not in queue: helper lemma chains queue frame + new entry info
      u_not_in_queue_after_discover scolor_pre squeue_pre squeue_post
        (SZ.v n) (SZ.v vhead) (SZ.v vtail_pre) (SZ.v vtail_post) (SZ.v u);

      v := SZ.add vv 1sz
    };

    // u.color = BLACK
    with scolor_pre_black. assert (A.pts_to color scolor_pre_black);
    with sdist_pre_black. assert (A.pts_to dist sdist_pre_black);
    with squeue_pre_black. assert (A.pts_to queue_data squeue_pre_black);
    with spred_pre_black. assert (A.pts_to pred spred_pre_black);
    with vtail_pre_black. assert (R.pts_to q_tail vtail_pre_black);

    // Prove preservation lemmas for blackening
    blacken_preserves_source_ok scolor_pre_black sdist_pre_black (SZ.v source) (SZ.v n) (SZ.v u);
    blacken_preserves_dist_ok scolor_pre_black sdist_pre_black (SZ.v n) (SZ.v u);
    blacken_preserves_dist_reachable sadj (SZ.v n) scolor_pre_black sdist_pre_black (SZ.v source) (SZ.v u);
    blacken_preserves_queue_ok scolor_pre_black squeue_pre_black (SZ.v n) (SZ.v vhead + 1) (SZ.v vtail_pre_black) (SZ.v u);
    count_nonwhite_upd_nonwhite scolor_pre_black (SZ.v n) (SZ.v u) 2;

    // Completeness: blacken preserves queue_gray_unique, scanned_all, count_gray
    // scolor_pre_black[u] == 1 from inner loop invariant
    assert (pure (Seq.index scolor_pre_black (SZ.v u) == 1));
    // scanned_partial at n from inner loop invariant
    assert (pure (scanned_partial sadj (SZ.v n) scolor_pre_black (SZ.v u) (SZ.v n)));
    // u not in active queue from inner loop invariant
    blacken_preserves_queue_gray_unique scolor_pre_black squeue_pre_black (SZ.v n) (SZ.v vhead + 1) (SZ.v vtail_pre_black) (SZ.v u);
    blacken_preserves_scanned_all sadj scolor_pre_black (SZ.v n) (SZ.v u);
    count_gray_upd_from_gray scolor_pre_black (SZ.v n) (SZ.v u);
    blacken_preserves_pred_dist_ok scolor_pre_black sdist_pre_black spred_pre_black (SZ.v n) (SZ.v u);
    
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
  assert (pure (dist_reachable sadj (SZ.v n) scolor_final sdist_final (SZ.v source)));
  with spred_final. assert (A.pts_to pred spred_final);
  assert (pure (pred_dist_ok scolor_final sdist_final spred_final (SZ.v n)));
  assert (pure (Seq.index scolor_final (SZ.v source) <> 0));
  assert (pure (Seq.index sdist_final (SZ.v source) == 0));
  assert (pure (forall (w: nat). w < SZ.v n /\ Seq.index scolor_final w <> 0 ==> Seq.index sdist_final w >= 0));
  assert (pure (forall (w: nat). w < SZ.v n /\ Seq.index scolor_final w <> 0 ==>
    reachable_in sadj (SZ.v n) (SZ.v source) w (Seq.index sdist_final w)));

  // Completeness: at loop exit, head == tail so count_gray == 0, meaning no GRAY vertices
  // Combined with scanned_all and source being non-WHITE, reachable vertices must be non-WHITE
  assert (pure (count_gray scolor_final (SZ.v n) == 0));
  count_gray_zero_no_gray scolor_final (SZ.v n);
  assert (pure (forall (u:nat). u < SZ.v n ==> Seq.index scolor_final u <> 1));
  assert (pure (scanned_all sadj (SZ.v n) scolor_final));
  assert (pure (SZ.v n <= Seq.length scolor_final));
  assert (pure (SZ.v n * SZ.v n <= Seq.length sadj));

  // Apply completeness_lemma for all reachable vertices
  bfs_completeness_all sadj (SZ.v n) scolor_final (SZ.v source);
  assert (pure (forall (v: nat) (k: nat). v < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) v k ==>
    Seq.index scolor_final v <> 0));
  assert (pure (forall (v: nat). v < SZ.v n /\ Seq.index scolor_final v <> 0 /\
    Seq.index spred_final v >= 0 /\ Seq.index spred_final v < SZ.v n ==>
    Seq.index scolor_final (Seq.index spred_final v) <> 0 /\
    Seq.index sdist_final v == Seq.index sdist_final (Seq.index spred_final v) + 1))
}
#pop-options
