(*
   Stack-based Depth-First Search - CLRS §22.3 (Canonical DFS Implementation)

   Implements the classical DFS algorithm from CLRS using an explicit stack.
   Graph represented as flat adjacency matrix adj[u*n+v] (edge from u to v if != 0).

   Relationship to DFS.Spec: The pure functional specification in DFS.Spec.fst uses
   a 2D adjacency matrix (seq (seq int)), while this imperative implementation uses
   a flat 1D matrix (seq int). The representations are equivalent: adj2d[u][v] ↔
   adj1d[u*n+v]. DFS.Spec proves the parenthesis theorem, white-path theorem, and
   edge classification; this file proves the imperative implementation correct with
   verified O(V²) complexity.

   Colors: 0=WHITE (unvisited), 1=GRAY (discovered, on stack), 2=BLACK (finished)

   Algorithm (CLRS pseudocode):
   DFS(G)
     for each vertex u in G.V
       u.color = WHITE; u.pi = NIL
     time = 0
     for each vertex u in G.V
       if u.color == WHITE
         DFS-VISIT(G, u)

   DFS-VISIT(G, u)
     time = time + 1
     u.d = time        // discovery time
     u.color = GRAY
     for each v in G.Adj[u]
       if v.color == WHITE
         v.pi = u
         DFS-VISIT(G, v)
     u.color = BLACK
     time = time + 1
     u.f = time        // finish time

   Iterative implementation with explicit stack:
   - Push vertex onto stack and mark GRAY
   - For each vertex on stack, find next WHITE neighbor
   - If found, push neighbor (recursive case)
   - If none, pop vertex and mark BLACK (finish)
   - Use scan_idx[] to track how far we've scanned each vertex's neighbors
*)

module CLRS.Ch22.DFS.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.WithPure
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas

open CLRS.Ch22.Graph.Common

(* Arithmetic helpers for SZ.fits *)
let fits_product_smaller (a b c d: nat)
  : Lemma (requires c < a /\ d <= b /\ SZ.fits (a * b))
          (ensures SZ.fits (c * b) /\ SZ.fits (c * b + d))
  = assert (c * b <= a * b);
    assert (c * b + d <= a * b)

(* Safe index for int sequences - avoids refinement issues with nested Seq.index in postconditions *)
let safe_index_int (s: Seq.seq int) (i: nat) : int =
  if i < Seq.length s then Seq.index s i else 0

let fits_le (x y: nat)
  : Lemma (requires x <= y /\ SZ.fits y)
          (ensures SZ.fits x)
  = ()

(* Count GRAY (==1) vertices in s[0..k) *)
let rec count_ones (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Tot (r: nat{r <= k}) (decreases k)
  = if k = 0 then 0
    else (if Seq.index s (k - 1) = 1 then 1 else 0) + count_ones s (k - 1)

(* If any element in [0..k) is not 1, count < k *)
let rec count_ones_lt (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat)
  : Lemma (requires j < k /\ Seq.index s j <> 1)
          (ensures count_ones s k < k)
          (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then ()
    else count_ones_lt s (k - 1) j

(* Updating index j to 1 when it wasn't 1: count goes up by 1 *)
let rec count_ones_upd_to_one (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat)
  : Lemma (requires j < k /\ Seq.index s j <> 1)
          (ensures Seq.length (Seq.upd s j 1) == Seq.length s /\
                   count_ones (Seq.upd s j 1) k == count_ones s k + 1)
          (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then begin
      let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s})
        : Lemma (ensures Seq.length (Seq.upd s j 1) == Seq.length s /\
                         count_ones (Seq.upd s j 1) k' == count_ones s k')
                (decreases k')
        = if k' = 0 then ()
          else (assert (Seq.index (Seq.upd s j 1) (k'-1) == Seq.index s (k'-1)); aux s (k'-1) j)
      in aux s (k-1) j
    end
    else (assert (Seq.index (Seq.upd s j 1) (k-1) == Seq.index s (k-1));
          count_ones_upd_to_one s (k-1) j)

(* Updating index j from 1 to non-1: count goes down by 1 *)
let rec count_ones_upd_from_one (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat) (v: int)
  : Lemma (requires j < k /\ Seq.index s j = 1 /\ v <> 1)
          (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                   count_ones (Seq.upd s j v) k == count_ones s k - 1)
          (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then begin
      let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s}) (v: int)
        : Lemma (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                         count_ones (Seq.upd s j v) k' == count_ones s k')
                (decreases k')
        = if k' = 0 then ()
          else (assert (Seq.index (Seq.upd s j v) (k'-1) == Seq.index s (k'-1)); aux s (k'-1) j v)
      in aux s (k-1) j v
    end
    else (assert (Seq.index (Seq.upd s j v) (k-1) == Seq.index s (k-1));
          count_ones_upd_from_one s (k-1) j v)

(* Updating out of range doesn't change count *)
let rec count_ones_upd_out (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat) (v: int)
  : Lemma (requires j >= k /\ j < Seq.length s)
          (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                   count_ones (Seq.upd s j v) k == count_ones s k)
          (decreases k)
  = if k = 0 then ()
    else (assert (Seq.index (Seq.upd s j v) (k-1) == Seq.index s (k-1));
          count_ones_upd_out s (k-1) j v)

(* If all elements in [0..k) are 0, count_ones is 0 *)
let rec count_ones_all_zero (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Lemma (requires forall (j:nat). j < k ==> Seq.index s j == 0)
          (ensures count_ones s k == 0)
          (decreases k)
  = if k = 0 then ()
    else count_ones_all_zero s (k - 1)

(* If count_ones == 0, no element in [0..k) is 1 (GRAY) *)
let rec count_ones_zero_no_gray (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Lemma (requires count_ones s k == 0)
          (ensures forall (j:nat). j < k ==> Seq.index s j <> 1)
          (decreases k)
  = if k = 0 then ()
    else count_ones_zero_no_gray s (k - 1)

(* Count BLACK (==2) vertices in s[0..k) *)
let rec count_twos (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Tot (r: nat{r <= k}) (decreases k)
  = if k = 0 then 0
    else (if Seq.index s (k - 1) = 2 then 1 else 0) + count_twos s (k - 1)

(* If all elements in [0..k) are 0, count_twos is 0 *)
let rec count_twos_all_zero (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Lemma (requires forall (j:nat). j < k ==> Seq.index s j == 0)
          (ensures count_twos s k == 0)
          (decreases k)
  = if k = 0 then ()
    else count_twos_all_zero s (k - 1)

(* Updating from non-2 to non-2 preserves count_twos *)
let rec count_twos_upd_non_two (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat) (v: int)
  : Lemma (requires j < k /\ Seq.index s j <> 2 /\ v <> 2)
          (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                   count_twos (Seq.upd s j v) k == count_twos s k)
          (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then begin
      let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s}) (v: int)
        : Lemma (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                         count_twos (Seq.upd s j v) k' == count_twos s k')
                (decreases k')
        = if k' = 0 then ()
          else (assert (Seq.index (Seq.upd s j v) (k'-1) == Seq.index s (k'-1)); aux s (k'-1) j v)
      in aux s (k-1) j v
    end
    else (assert (Seq.index (Seq.upd s j v) (k-1) == Seq.index s (k-1));
          count_twos_upd_non_two s (k-1) j v)

(* Updating from non-2 to 2 increases count_twos by 1 *)
let rec count_twos_upd_to_two (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat)
  : Lemma (requires j < k /\ Seq.index s j <> 2)
          (ensures Seq.length (Seq.upd s j 2) == Seq.length s /\
                   count_twos (Seq.upd s j 2) k == count_twos s k + 1)
          (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then begin
      let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s})
        : Lemma (ensures Seq.length (Seq.upd s j 2) == Seq.length s /\
                         count_twos (Seq.upd s j 2) k' == count_twos s k')
                (decreases k')
        = if k' = 0 then ()
          else (assert (Seq.index (Seq.upd s j 2) (k'-1) == Seq.index s (k'-1)); aux s (k'-1) j)
      in aux s (k-1) j
    end
    else (assert (Seq.index (Seq.upd s j 2) (k-1) == Seq.index s (k-1));
          count_twos_upd_to_two s (k-1) j)

(* If all colors in {0,1,2}, then count_ones + count_twos <= k *)
let rec count_ones_twos_le (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Lemma (requires forall (i:nat). i < k ==> (Seq.index s i == 0 \/ Seq.index s i == 1 \/ Seq.index s i == 2))
          (ensures count_ones s k + count_twos s k <= k)
          (decreases k)
  = if k = 0 then ()
    else count_ones_twos_le s (k - 1)

// product_strict_bound imported from CLRS.Ch22.Graph.Common

(* ================================================================
   PREDICATES — Named abstractions for repeated invariant clusters
   ================================================================ *)

(* Stack-color consistency: the explicit stack mirrors the GRAY vertices *)
let stack_ok (scolor: Seq.seq int) (sstack: Seq.seq SZ.t) (n top: nat)
  : prop
  = top <= n /\
    Seq.length scolor >= n /\
    Seq.length sstack >= n /\
    count_ones scolor n == top /\
    (forall (i:nat). {:pattern (Seq.index sstack i)} i < top ==> SZ.v (Seq.index sstack i) < n) /\
    (forall (i:nat). {:pattern (Seq.index sstack i)} i < top ==> safe_index_int scolor (SZ.v (Seq.index sstack i)) == 1) /\
    (forall (i:nat) (j:nat). {:pattern (Seq.index sstack i); (Seq.index sstack j)}
      i < top /\ j < top /\ i <> j ==> SZ.v (Seq.index sstack i) <> SZ.v (Seq.index sstack j))

(* DFS tracking: colors are valid, BLACK vertices have valid timestamps *)
let dfs_ok (scolor sd sf: Seq.seq int) (n: nat)
  : prop
  = Seq.length scolor >= n /\ Seq.length sd >= n /\ Seq.length sf >= n /\
    (forall (i:nat). {:pattern (Seq.index scolor i)} i < n ==>
      (Seq.index scolor i == 0 \/ Seq.index scolor i == 1 \/ Seq.index scolor i == 2)) /\
    (forall (i:nat). {:pattern (Seq.index scolor i)} i < n ==>
      (Seq.index scolor i == 2 ==> Seq.index sd i > 0 /\ Seq.index sf i > 0 /\ Seq.index sd i < Seq.index sf i))

(* Strengthening: GRAY vertices discovered at known time *)
let gray_ok (scolor sd: Seq.seq int) (n: nat) (time: int)
  : prop
  = Seq.length scolor >= n /\ Seq.length sd >= n /\
    (forall (i:nat). {:pattern (Seq.index scolor i)} i < n ==>
      (Seq.index scolor i == 1 ==> Seq.index sd i > 0 /\ Seq.index sd i <= time))

(* All vertices below k are non-WHITE *)
let nonwhite_below (scolor: Seq.seq int) (k: nat)
  : prop
  = Seq.length scolor >= k /\
    (forall (j:nat). {:pattern (Seq.index scolor j)} j < k ==> Seq.index scolor j <> 0)

(* Scan indices are in bounds *)
let scan_ok (sscan: Seq.seq SZ.t) (n: nat)
  : prop
  = Seq.length sscan >= n /\
    (forall (uu:nat). {:pattern (Seq.index sscan uu)} uu < n ==> SZ.v (Seq.index sscan uu) <= n)

(* Timestamp bound: all timestamps of discovered vertices are bounded by current time *)
let timestamps_bounded (scolor sd sf: Seq.seq int) (n: nat) (time: int)
  : prop
  = Seq.length scolor >= n /\ Seq.length sd >= n /\ Seq.length sf >= n /\
    (forall (i:nat). {:pattern (Seq.index scolor i)} i < n ==>
      (Seq.index scolor i == 1 ==> Seq.index sd i <= time) /\
      (Seq.index scolor i == 2 ==> Seq.index sd i <= time /\ Seq.index sf i <= time))

(* Stack forms a DFS tree path: bottom element has pred < 0 (root),
   each non-bottom element's predecessor is the element below.
   Requires stack_ok-compatible bounds: stack elements are < n. *)
[@"opaque_to_smt"]
let stack_is_path (sstack: Seq.seq SZ.t) (spred: Seq.seq int) (n top: nat)
  : prop
  = Seq.length sstack >= n /\ Seq.length spred >= n /\ top <= n /\
    (forall (i:nat). i < top ==> SZ.v (Seq.index sstack i) < n) /\
    (top > 0 /\ SZ.v (Seq.index sstack 0) < n ==>
      Seq.index spred (SZ.v (Seq.index sstack 0)) < 0) /\
    (forall (i:nat). {:pattern (Seq.index sstack i)}
      0 < i /\ i < top /\ SZ.v (Seq.index sstack i) < n ==>
      Seq.index spred (SZ.v (Seq.index sstack i)) == SZ.v (Seq.index sstack (i - 1)))

(* Predecessor finish ordering: children finish before parents in DFS tree *)
let pred_finish_ok (scolor sf spred: Seq.seq int) (n: nat) : prop =
  Seq.length scolor >= n /\ Seq.length sf >= n /\ Seq.length spred >= n /\
  (forall (v:nat). {:pattern (Seq.index spred v)}
    v < n /\ Seq.index scolor v == 2 /\ Seq.index spred v >= 0 /\ Seq.index spred v < n /\
    Seq.index scolor (Seq.index spred v) == 2 ==>
    Seq.index sf v < Seq.index sf (Seq.index spred v))

(* ================================================================
   PREDICATE LEMMAS — Key reasoning steps isolated as lemmas
   ================================================================ *)

(* Discovering preserves dfs_ok and gray_ok *)
let discover_preserves_tracking
  (scolor sd sf: Seq.seq int) (n j: nat) (time: int)
  : Lemma
    (requires
      j < n /\ n <= Seq.length scolor /\ n <= Seq.length sd /\ n <= Seq.length sf /\
      Seq.index scolor j == 0 /\ time >= 0 /\
      dfs_ok scolor sd sf n /\ gray_ok scolor sd n time)
    (ensures (
      let scolor' = Seq.upd scolor j 1 in
      let sd' = Seq.upd sd j (time + 1) in
      dfs_ok scolor' sd' sf n /\ gray_ok scolor' sd' n (time + 1)))
  = ()

(* Discovering preserves nonwhite_below *)
let discover_preserves_nonwhite
  (scolor: Seq.seq int) (j k: nat)
  : Lemma
    (requires j < Seq.length scolor /\ nonwhite_below scolor k)
    (ensures nonwhite_below (Seq.upd scolor j 1) k)
  = ()

(* Finishing preserves dfs_ok and gray_ok *)
let finish_preserves_tracking
  (scolor sd sf: Seq.seq int) (n j: nat) (time: int)
  : Lemma
    (requires
      j < n /\ n <= Seq.length scolor /\ n <= Seq.length sd /\ n <= Seq.length sf /\
      Seq.index scolor j == 1 /\ Seq.index sd j > 0 /\
      Seq.index sd j <= time /\ time >= 0 /\
      dfs_ok scolor sd sf n /\ gray_ok scolor sd n time)
    (ensures (
      let scolor' = Seq.upd scolor j 2 in
      let sf' = Seq.upd sf j (time + 1) in
      dfs_ok scolor' sd sf' n /\ gray_ok scolor' sd n (time + 1)))
  = ()

(* Finishing preserves nonwhite_below *)
let finish_preserves_nonwhite
  (scolor: Seq.seq int) (j k: nat)
  : Lemma
    (requires j < Seq.length scolor /\ nonwhite_below scolor k)
    (ensures nonwhite_below (Seq.upd scolor j 2) k)
  = ()

(* When no GRAY vertices exist (count_ones == 0), gray_ok holds vacuously *)
let no_gray_implies_gray_ok
  (scolor sd: Seq.seq int) (n: nat) (time: int)
  : Lemma
    (requires n <= Seq.length scolor /\ n <= Seq.length sd /\ count_ones scolor n == 0)
    (ensures gray_ok scolor sd n time)
  = count_ones_zero_no_gray scolor n

(* Discovering from parent u preserves pred_edge_ok *)
let discover_preserves_pred_edge_ok
  (sadj scolor sd spred: Seq.seq int) (n j u: nat) (time: int)
  : Lemma
    (requires
      j < n /\ u < n /\
      n <= Seq.length scolor /\ n <= Seq.length sd /\ n <= Seq.length spred /\
      n * n <= Seq.length sadj /\
      Seq.index scolor j == 0 /\
      Seq.index scolor u == 1 /\
      Seq.index sadj (u * n + j) <> 0 /\
      Seq.index sd u > 0 /\
      Seq.index sd u <= time /\
      time >= 0 /\
      pred_edge_ok sadj n scolor sd spred)
    (ensures
      pred_edge_ok sadj n
        (Seq.upd scolor j 1)
        (Seq.upd sd j (time + 1))
        (Seq.upd spred j u))
  = reveal_opaque (`%pred_edge_ok) (pred_edge_ok sadj n scolor sd spred);
    reveal_opaque (`%pred_edge_ok)
      (pred_edge_ok sadj n (Seq.upd scolor j 1) (Seq.upd sd j (time + 1)) (Seq.upd spred j u))

(* Discovering source vertex (pred = -1) preserves pred_edge_ok *)
let discover_source_preserves_pred_edge_ok
  (sadj scolor sd spred: Seq.seq int) (n j: nat) (time: int)
  : Lemma
    (requires
      j < n /\
      n <= Seq.length scolor /\ n <= Seq.length sd /\ n <= Seq.length spred /\
      n * n <= Seq.length sadj /\
      Seq.index scolor j == 0 /\
      pred_edge_ok sadj n scolor sd spred)
    (ensures
      pred_edge_ok sadj n
        (Seq.upd scolor j 1)
        (Seq.upd sd j (time + 1))
        (Seq.upd spred j (-1)))
  = reveal_opaque (`%pred_edge_ok) (pred_edge_ok sadj n scolor sd spred);
    reveal_opaque (`%pred_edge_ok)
      (pred_edge_ok sadj n (Seq.upd scolor j 1) (Seq.upd sd j (time + 1)) (Seq.upd spred j (-1)))

(* Finishing preserves pred_edge_ok (color 1→2, both non-zero; sd/spred unchanged) *)
let finish_preserves_pred_edge_ok
  (sadj scolor sd spred: Seq.seq int) (n j: nat)
  : Lemma
    (requires
      j < n /\
      n <= Seq.length scolor /\ n <= Seq.length sd /\ n <= Seq.length spred /\
      n * n <= Seq.length sadj /\
      Seq.index scolor j == 1 /\
      pred_edge_ok sadj n scolor sd spred)
    (ensures pred_edge_ok sadj n (Seq.upd scolor j 2) sd spred)
  = reveal_opaque (`%pred_edge_ok) (pred_edge_ok sadj n scolor sd spred);
    reveal_opaque (`%pred_edge_ok) (pred_edge_ok sadj n (Seq.upd scolor j 2) sd spred)

(* Discovering preserves timestamps_bounded *)
let discover_preserves_timestamps_bounded
  (scolor sd sf: Seq.seq int) (n j: nat) (time: int)
  : Lemma
    (requires timestamps_bounded scolor sd sf n time /\
             j < n /\ n <= Seq.length scolor /\ n <= Seq.length sd /\
             Seq.index scolor j == 0)
    (ensures timestamps_bounded (Seq.upd scolor j 1) (Seq.upd sd j (time + 1)) sf n (time + 1))
  = ()

(* Finishing preserves timestamps_bounded *)
let finish_preserves_timestamps_bounded
  (scolor sd sf: Seq.seq int) (n j: nat) (time: int)
  : Lemma
    (requires timestamps_bounded scolor sd sf n time /\
             j < n /\ n <= Seq.length scolor /\ n <= Seq.length sd /\ n <= Seq.length sf /\
             Seq.index scolor j == 1)
    (ensures timestamps_bounded (Seq.upd scolor j 2) sd (Seq.upd sf j (time + 1)) n (time + 1))
  = ()

(* All-WHITE state satisfies timestamps_bounded vacuously *)
let init_timestamps_bounded
  (scolor sd sf: Seq.seq int) (n: nat) (time: int)
  : Lemma
    (requires n <= Seq.length scolor /\ n <= Seq.length sd /\ n <= Seq.length sf /\
             (forall (j:nat). j < n ==> Seq.index scolor j == 0))
    (ensures timestamps_bounded scolor sd sf n time)
  = ()

(* All-WHITE state satisfies pred_edge_ok vacuously (all non-WHITE: vacuous) *)
let init_pred_edge_ok (sadj scolor sd spred: Seq.seq int) (n: nat)
  : Lemma
    (requires
      n <= Seq.length scolor /\ n <= Seq.length sd /\ n <= Seq.length spred /\
      n * n <= Seq.length sadj /\
      (forall (j:nat). j < n ==> Seq.index scolor j == 0))
    (ensures pred_edge_ok sadj n scolor sd spred)
  = reveal_opaque (`%pred_edge_ok) (pred_edge_ok sadj n scolor sd spred)

(* Top-of-stack vertex has no BLACK predecessor *)
#push-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always"
let stack_top_pred_not_black
  (scolor: Seq.seq int) (sstack: Seq.seq SZ.t) (spred: Seq.seq int) (n top: nat)
  : Lemma
    (requires
      stack_ok scolor sstack n top /\
      stack_is_path sstack spred n top /\
      top > 0 /\ n <= Seq.length scolor /\ n <= Seq.length spred /\
      Seq.length sstack >= n)
    (ensures (
      let u = SZ.v (Seq.index sstack (top - 1)) in
      u < n /\
      (Seq.index spred u < 0 \/ Seq.index spred u >= n \/
       Seq.index scolor (Seq.index spred u) <> 2)))
  = reveal_opaque (`%stack_is_path) (stack_is_path sstack spred n top);
    let u = SZ.v (Seq.index sstack (top - 1)) in
    if top = 1 then
      // Root at bottom: pred < 0 from stack_is_path
      assert (Seq.index spred u < 0)
    else begin
      // Non-root: pred[u] = sstack[top-2], which is GRAY (from stack_ok)
      let below = SZ.v (Seq.index sstack (top - 2)) in
      assert (Seq.index spred u == below);
      assert (safe_index_int scolor below == 1);
      assert (below < n);
      assert (Seq.index scolor below == 1)
    end
#pop-options

(* stack_is_path with top=0 is vacuously true *)
let stack_is_path_empty (sstack: Seq.seq SZ.t) (spred: Seq.seq int) (n: nat)
  : Lemma
    (requires Seq.length sstack >= n /\ Seq.length spred >= n)
    (ensures stack_is_path sstack spred n 0)
  = reveal_opaque (`%stack_is_path) (stack_is_path sstack spred n 0)

(* stack_is_path for a single element with pred < 0 *)
let stack_is_path_singleton
  (sstack: Seq.seq SZ.t) (spred: Seq.seq int) (n: nat) (vs: nat)
  : Lemma
    (requires
      Seq.length sstack >= n /\ Seq.length spred >= n /\ 1 <= n /\
      vs < n /\ SZ.v (Seq.index sstack 0) == vs /\
      Seq.index spred vs < 0)
    (ensures stack_is_path sstack spred n 1)
  = reveal_opaque (`%stack_is_path) (stack_is_path sstack spred n 1)

(* Popping preserves stack_is_path *)
let stack_is_path_pop (sstack: Seq.seq SZ.t) (spred: Seq.seq int) (n top: nat)
  : Lemma
    (requires stack_is_path sstack spred n top /\ top > 0)
    (ensures stack_is_path sstack spred n (top - 1))
  = reveal_opaque (`%stack_is_path) (stack_is_path sstack spred n top);
    reveal_opaque (`%stack_is_path) (stack_is_path sstack spred n (top - 1))

(* Pushing preserves stack_is_path when pred[new] = stack[top-1] *)
#push-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always"
let stack_is_path_push
  (sstack: Seq.seq SZ.t) (spred: Seq.seq int) (n top: nat) (vv_sz: SZ.t) (u: nat)
  : Lemma
    (requires (
      let vv = SZ.v vv_sz in
      stack_is_path sstack spred n top /\
      top > 0 /\ top < n /\ vv < n /\ u < n /\
      Seq.length sstack >= n /\ Seq.length spred >= n /\
      SZ.v (Seq.index sstack (top - 1)) == u /\
      (forall (i:nat). i < top ==> SZ.v (Seq.index sstack i) <> vv)))
    (ensures (
      let vv = SZ.v vv_sz in
      stack_is_path (Seq.upd sstack top vv_sz) (Seq.upd spred vv u) n (top + 1)))
  = let vv = SZ.v vv_sz in
    reveal_opaque (`%stack_is_path) (stack_is_path sstack spred n top);
    reveal_opaque (`%stack_is_path)
      (stack_is_path (Seq.upd sstack top vv_sz) (Seq.upd spred vv u) n (top + 1));
    // New entry: pred[vv] = u = sstack[top-1]. For i = top: pred[sstack'[top]] = pred[vv] = u = sstack[top-1] = sstack'[top-1]. ✓
    // Old entries i < top: sstack'[i] = sstack[i], pred'[sstack[i]] = pred[sstack[i]] (since sstack[i] <> vv). ✓
    // Root: sstack'[0] = sstack[0], pred'[sstack[0]] = pred[sstack[0]] < 0 (since sstack[0] <> vv). ✓
    assert (Seq.index (Seq.upd spred vv u) vv == u)
#pop-options

(* Discovering preserves pred_finish_ok — no new BLACK vertex *)
let discover_preserves_pred_finish_ok
  (scolor sf spred: Seq.seq int) (n j: nat)
  : Lemma
    (requires pred_finish_ok scolor sf spred n /\ j < n /\ n <= Seq.length scolor /\
              Seq.index scolor j == 0)
    (ensures pred_finish_ok (Seq.upd scolor j 1) sf spred n)
  = ()

(* Finishing vertex u preserves pred_finish_ok.
   PRECONDITION: u's predecessor (if valid) is not BLACK.
   In DFS, u's parent is still GRAY on the stack below u. *)
#push-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always"
let finish_preserves_pred_finish_ok
  (sadj scolor sd sf spred: Seq.seq int) (n u: nat) (time: int)
  : Lemma
    (requires
      pred_finish_ok scolor sf spred n /\
      timestamps_bounded scolor sd sf n time /\
      pred_edge_ok sadj n scolor sd spred /\
      u < n /\ Seq.index scolor u == 1 /\
      n <= Seq.length scolor /\ n <= Seq.length sf /\ n <= Seq.length spred /\
      n <= Seq.length sd /\ n * n <= Seq.length sadj /\
      (Seq.index spred u >= 0 /\ Seq.index spred u < n ==>
        Seq.index scolor (Seq.index spred u) <> 2))
    (ensures
      pred_finish_ok (Seq.upd scolor u 2) (Seq.upd sf u (time + 1)) spred n)
  = reveal_opaque (`%pred_edge_ok) (pred_edge_ok sadj n scolor sd spred);
    ()
#pop-options

(* All-WHITE state satisfies pred_finish_ok vacuously *)
let init_pred_finish_ok (scolor sf spred: Seq.seq int) (n: nat)
  : Lemma
    (requires n <= Seq.length scolor /\ n <= Seq.length sf /\ n <= Seq.length spred /\
              (forall (j:nat). j < n ==> Seq.index scolor j == 0))
    (ensures pred_finish_ok scolor sf spred n)
  = ()

(* Final postcondition: from dfs_ok + nonwhite_below n + count_ones==0,
   all BLACK with d > 0, f > 0, d < f *)
let final_postcondition_lemma
  (scolor sd sf: Seq.seq int) (n: nat)
  : Lemma
    (requires
      n <= Seq.length scolor /\
      count_ones scolor n == 0 /\
      nonwhite_below scolor n /\
      dfs_ok scolor sd sf n)
    (ensures
      (forall (u:nat). {:pattern (Seq.index scolor u)} u < n ==> Seq.index scolor u == 2) /\
      (forall (u:nat). {:pattern (Seq.index sd u)} u < n ==> Seq.index sd u > 0) /\
      (forall (u:nat). {:pattern (Seq.index sf u)} u < n ==> Seq.index sf u > 0) /\
      (forall (u:nat). {:pattern (Seq.index sd u); (Seq.index sf u)} u < n ==> Seq.index sd u < Seq.index sf u))
  = count_ones_zero_no_gray scolor n

(* Derive timestamp bounds ≤ 2*n from timestamps_bounded + count invariant *)
let final_timestamps_lemma
  (scolor sd sf: Seq.seq int) (n: nat) (vtime: int)
  : Lemma
    (requires
      n <= Seq.length scolor /\ n <= Seq.length sd /\ n <= Seq.length sf /\
      dfs_ok scolor sd sf n /\
      timestamps_bounded scolor sd sf n vtime /\
      vtime == count_ones scolor n + 2 * count_twos scolor n /\
      (forall (u:nat). u < n ==> Seq.index scolor u == 2))
    (ensures
      vtime <= 2 * n /\
      (forall (u:nat). u < n ==> Seq.index sd u <= 2 * n) /\
      (forall (u:nat). u < n ==> Seq.index sf u <= 2 * n))
  = count_ones_twos_le scolor n

(* When all vertices are BLACK, pred_finish_ok simplifies: color checks are automatic *)
let final_pred_finish_lemma
  (scolor sf spred: Seq.seq int) (n: nat)
  : Lemma
    (requires
      n <= Seq.length scolor /\ n <= Seq.length sf /\ n <= Seq.length spred /\
      pred_finish_ok scolor sf spred n /\
      (forall (u:nat). u < n ==> Seq.index scolor u == 2))
    (ensures
      (forall (v:nat). v < n /\ Seq.index spred v >= 0 /\ Seq.index spred v < n ==>
        Seq.index sf v < Seq.index sf (Seq.index spred v)))
  = ()

(* ================================================================
   GHOST TICK — for complexity tracking
   ================================================================ *)

// incr_nat and tick imported from CLRS.Ch22.Graph.Common

(* ================================================================
   COMPLEXITY ARITHMETIC LEMMA
   ================================================================ *)

let lemma_dfs_bound_correct (outer_count inner_count n: nat)
  : Lemma (requires n >= 1 /\ outer_count <= n /\ inner_count <= n * n)
          (ensures outer_count + inner_count <= 2 * (n * n))
  = assert (outer_count <= n);
    assert (n <= n * n);
    assert (outer_count + inner_count <= n + n * n);
    assert (n + n * n <= n * n + n * n);
    assert (n * n + n * n == 2 * (n * n))

(* ================================================================
   SUM_SCAN_IDX — sum of scan_idx values for complexity accounting
   ================================================================ *)

let rec sum_scan_idx (sscan: Seq.seq SZ.t) (k: nat{k <= Seq.length sscan})
  : Tot nat (decreases k)
  = if k = 0 then 0
    else SZ.v (Seq.index sscan (k - 1)) + sum_scan_idx sscan (k - 1)

let rec sum_scan_idx_bound (sscan: Seq.seq SZ.t) (k: nat{k <= Seq.length sscan}) (n: nat)
  : Lemma (requires forall (j:nat). j < k ==> SZ.v (Seq.index sscan j) <= n)
          (ensures sum_scan_idx sscan k <= k * n)
          (decreases k)
  = if k = 0 then ()
    else sum_scan_idx_bound sscan (k - 1) n

let rec sum_scan_idx_upd (sscan: Seq.seq SZ.t) (k: nat{k <= Seq.length sscan}) (j: nat) (v: SZ.t)
  : Lemma (requires j < Seq.length sscan)
          (ensures Seq.length (Seq.upd sscan j v) == Seq.length sscan /\
                   (j < k ==> sum_scan_idx (Seq.upd sscan j v) k == 
                              sum_scan_idx sscan k - SZ.v (Seq.index sscan j) + SZ.v v) /\
                   (j >= k ==> sum_scan_idx (Seq.upd sscan j v) k == sum_scan_idx sscan k))
          (decreases k)
  = if k = 0 then ()
    else begin
      assert (Seq.index (Seq.upd sscan j v) (k-1) == (if j = k-1 then v else Seq.index sscan (k-1)));
      sum_scan_idx_upd sscan (k - 1) j v
    end

let rec sum_scan_idx_all_zero (sscan: Seq.seq SZ.t) (k: nat{k <= Seq.length sscan})
  : Lemma (requires forall (j:nat). j < k ==> SZ.v (Seq.index sscan j) == 0)
          (ensures sum_scan_idx sscan k == 0)
          (decreases k)
  = if k = 0 then ()
    else sum_scan_idx_all_zero sscan (k - 1)

(* Helper: discover a WHITE vertex v from vertex u.
   Sets d[v], color[v]=GRAY, pred[v]=u, pushes v onto stack.
   Factored out to avoid Pulse unification issues with conditional branches. *)

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1 --split_queries always"
fn discover_vertex_dfs
  (color: A.array int) (d: A.array int) (pred: A.array int)
  (stack_data: A.array SZ.t) (stack_top: ref SZ.t)
  (scan_idx: A.array SZ.t)
  (time_ref: ref int)
  (ctr: GR.ref nat)
  (u: SZ.t) (vv: SZ.t) (n: SZ.t)
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
  (#vc: erased nat)
  requires
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    GR.pts_to ctr vc **
    with_pure (
      SZ.v vv < SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v vtop < SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sd == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sstack == SZ.v n /\
      Seq.length sscan == SZ.v n /\
      vtime >= 0 /\
      Seq.index scolor (SZ.v vv) == 0 /\
      SZ.v (Seq.index sscan (SZ.v vv)) == 0 /\
      stack_ok scolor sstack (SZ.v n) (SZ.v vtop) /\
      scan_ok sscan (SZ.v n)
    )
  ensures exists* scolor' sd' spred' sstack' sscan' vtop' vtime'.
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    GR.pts_to ctr vc **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sd' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\
      Seq.length sscan' == SZ.v n /\
      SZ.v vtop' <= SZ.v n /\
      SZ.v vtop' > SZ.v vtop /\
      vtime' == vtime + 1 /\
      scolor' == Seq.upd scolor (SZ.v vv) 1 /\
      sd' == Seq.upd sd (SZ.v vv) (vtime + 1) /\
      stack_ok scolor' sstack' (SZ.v n) (SZ.v vtop') /\
      scan_ok sscan' (SZ.v n) /\
      sum_scan_idx sscan' (SZ.v n) == sum_scan_idx sscan (SZ.v n)
    )
{
  // time++
  let t = !time_ref;
  time_ref := t + 1;
  // v.d = time
  A.op_Array_Assignment d vv (t + 1);
  // v.color = GRAY
  count_ones_upd_to_one scolor (SZ.v n) (SZ.v vv);
  A.op_Array_Assignment color vv 1;
  // v.pi = u
  A.op_Array_Assignment pred vv (SZ.v u);
  // scan_idx[vv] = 0 (already 0 by white_scan_zero precondition)
  sum_scan_idx_upd sscan (SZ.v n) (SZ.v vv) 0sz;
  A.op_Array_Assignment scan_idx vv 0sz;
  // PUSH(stack, v)
  let top = !stack_top;
  A.op_Array_Assignment stack_data top vv;
  stack_top := SZ.add top 1sz
}
#pop-options

(* Helper: finish a vertex u.
   Sets f[u], color[u]=BLACK, pops u from stack. *)

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1 --split_queries always"
fn finish_vertex
  (color: A.array int) (f: A.array int)
  (stack_data: A.array SZ.t)
  (stack_top: ref SZ.t)
  (time_ref: ref int)
  (u: SZ.t) (n: SZ.t)
  (#scolor: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
  requires
    A.pts_to color scolor **
    A.pts_to f sf **
    A.pts_to stack_data sstack **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    with_pure (
      SZ.v u < SZ.v n /\
      SZ.v vtop > 0 /\
      SZ.v vtop <= SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sf == SZ.v n /\
      Seq.length sstack == SZ.v n /\
      vtime >= 0 /\
      Seq.index scolor (SZ.v u) == 1 /\
      SZ.v (Seq.index sstack (SZ.v vtop - 1)) == SZ.v u /\
      stack_ok scolor sstack (SZ.v n) (SZ.v vtop)
    )
  ensures exists* scolor' sf' vtop' vtime'.
    A.pts_to color scolor' **
    A.pts_to f sf' **
    A.pts_to stack_data sstack **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sf' == SZ.v n /\
      SZ.v vtop' < SZ.v vtop /\
      SZ.v vtop' <= SZ.v n /\
      vtime' > vtime /\
      scolor' == Seq.upd scolor (SZ.v u) 2 /\
      sf' == Seq.upd sf (SZ.v u) (vtime + 1) /\
      stack_ok scolor' sstack (SZ.v n) (SZ.v vtop')
    )
{
  // u.color = BLACK
  count_ones_upd_from_one scolor (SZ.v n) (SZ.v u) 2;
  A.op_Array_Assignment color u 2;
  // time++
  let t = !time_ref;
  time_ref := t + 1;
  // u.f = time
  A.op_Array_Assignment f u (t + 1);
  // POP(stack)
  let top = !stack_top;
  stack_top := SZ.sub top 1sz
}
#pop-options

(* Time bound: when at least one vertex is GRAY, time + 1 <= 2*n *)
let dfs_time_bound (scolor: Seq.seq int) (n: nat) (vtime: int)
  : Lemma
    (requires n <= Seq.length scolor /\
      vtime == count_ones scolor n + 2 * count_twos scolor n /\
      count_ones scolor n >= 1 /\
      (forall (i:nat). i < n ==> (Seq.index scolor i == 0 \/ Seq.index scolor i == 1 \/ Seq.index scolor i == 2)))
    (ensures vtime + 1 <= 2 * n)
  = count_ones_twos_le scolor n

(* Helper: scan adjacency row for next WHITE neighbor starting from scan_pos.
   Reads adj and color; only modifies ghost counter ctr (via tick). *)

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1 --split_queries always"
fn scan_for_white_neighbor
  (adj: A.array int)
  (color: A.array int)
  (n: SZ.t)
  (u: SZ.t)
  (scan_pos: SZ.t)
  (found_ref: ref bool)
  (next_v_ref: ref SZ.t)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#vc: erased nat)
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    R.pts_to found_ref false **
    R.pts_to next_v_ref 0sz **
    GR.pts_to ctr vc **
    with_pure (
      SZ.v scan_pos <= SZ.v n /\
      SZ.v u < SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.fits (SZ.v u * SZ.v n) /\
      SZ.fits (SZ.v u * SZ.v n + SZ.v scan_pos)
    )
  returns fscan: SZ.t
  ensures exists* vfound vnext (vc': nat).
    A.pts_to adj sadj **
    A.pts_to color scolor **
    R.pts_to found_ref vfound **
    R.pts_to next_v_ref vnext **
    GR.pts_to ctr vc' **
    pure (
      SZ.v fscan <= SZ.v n /\
      SZ.v fscan >= SZ.v scan_pos /\
      (vfound ==> SZ.v vnext < SZ.v n) /\
      (vfound ==> Seq.index scolor (SZ.v vnext) == 0) /\
      (vfound ==> Seq.index sadj (SZ.v u * SZ.v n + SZ.v vnext) <> 0) /\
      vc' + SZ.v scan_pos == reveal vc + SZ.v fscan
    )
{
  let mut scan: SZ.t = scan_pos;
  while (!scan <^ n && !found_ref)
  invariant exists* vscan vfound vnext (vc_scan: nat).
    R.pts_to scan vscan **
    R.pts_to found_ref vfound **
    R.pts_to next_v_ref vnext **
    A.pts_to adj sadj **
    A.pts_to color scolor **
    GR.pts_to ctr vc_scan **
    pure (
      SZ.v vscan <= SZ.v n /\
      SZ.v u < SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      SZ.fits (SZ.v u * SZ.v n) /\
      SZ.fits (SZ.v u * SZ.v n + SZ.v vscan) /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.v vscan >= SZ.v scan_pos /\
      (vfound ==> SZ.v vnext < SZ.v n) /\
      (vfound ==> Seq.index scolor (SZ.v vnext) == 0) /\
      (vfound ==> Seq.index sadj (SZ.v u * SZ.v n + SZ.v vnext) <> 0) /\
      vc_scan + SZ.v scan_pos == reveal vc + SZ.v vscan
    )
  decreases (SZ.v n - SZ.v !scan)
  {
    let vscan = !scan;

    // Tick for edge check
    tick ctr;

    // Check edge (u, vscan) and color[vscan]
    let offset: SZ.t = SZ.mul u n;
    let idx: SZ.t = SZ.add offset vscan;
    product_strict_bound (SZ.v n) (SZ.v n) (SZ.v u) (SZ.v vscan);
    let has_edge_val: int = A.op_Array_Access adj idx;

    let cvscan: int = A.op_Array_Access color vscan;

    if (has_edge_val <> 0 && cvscan = 0) {
      found_ref := true;
      next_v_ref := vscan
    };

    fits_le (SZ.v vscan + 1) (SZ.v n * SZ.v n);
    fits_product_smaller (SZ.v n) (SZ.v n) (SZ.v u) (SZ.v vscan + 1);
    scan := SZ.add vscan 1sz
  };
  !scan
}
#pop-options

(* Helper: perform DFS-VISIT for a single white vertex *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1 --split_queries always"
fn dfs_visit
  (adj: A.array int)
  (n: SZ.t)
  (vs: SZ.t)
  (color: A.array int)
  (d: A.array int)
  (f: A.array int)
  (pred: A.array int)
  (stack_data: A.array SZ.t)
  (scan_idx: A.array SZ.t)
  (stack_top: ref SZ.t)
  (time_ref: ref int)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
  (#vc: erased nat)
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to f sf **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    GR.pts_to ctr vc **
    with_pure (
      SZ.v vs < SZ.v n /\ SZ.v n > 0 /\ SZ.v vtop == 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\ Seq.length sd == SZ.v n /\
      Seq.length sf == SZ.v n /\ Seq.length spred == SZ.v n /\
      Seq.length sstack == SZ.v n /\ Seq.length sscan == SZ.v n /\
      vtime >= 0 /\ SZ.fits (SZ.v n * SZ.v n) /\
      Seq.index scolor (SZ.v vs) == 0 /\
      stack_ok scolor sstack (SZ.v n) (SZ.v vtop) /\
      scan_ok sscan (SZ.v n) /\
      dfs_ok scolor sd sf (SZ.v n) /\
      gray_ok scolor sd (SZ.v n) vtime /\
      timestamps_bounded scolor sd sf (SZ.v n) vtime /\
      vtime == count_ones scolor (SZ.v n) + 2 * count_twos scolor (SZ.v n) /\
      nonwhite_below scolor (SZ.v vs) /\
      pred_edge_ok sadj (SZ.v n) scolor sd spred /\
      pred_finish_ok scolor sf spred (SZ.v n) /\
      stack_is_path sstack spred (SZ.v n) (SZ.v vtop) /\
      (* WHITE vertices have scan_idx == 0 *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor j == 0 ==> SZ.v (Seq.index sscan j) == 0))
    )
  ensures exists* scolor' sd' sf' spred' sstack' sscan' vtop' vtime' (vc': nat).
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to f sf' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    GR.pts_to ctr vc' **
    pure (
      Seq.length scolor' == SZ.v n /\ Seq.length sd' == SZ.v n /\
      Seq.length sf' == SZ.v n /\ Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\ Seq.length sscan' == SZ.v n /\
      SZ.v vtop' == 0 /\ vtime' >= vtime /\
      stack_ok scolor' sstack' (SZ.v n) (SZ.v vtop') /\
      scan_ok sscan' (SZ.v n) /\
      dfs_ok scolor' sd' sf' (SZ.v n) /\
      timestamps_bounded scolor' sd' sf' (SZ.v n) vtime' /\
      vtime' == count_ones scolor' (SZ.v n) + 2 * count_twos scolor' (SZ.v n) /\
      nonwhite_below scolor' (SZ.v vs + 1) /\
      pred_edge_ok sadj (SZ.v n) scolor' sd' spred' /\
      pred_finish_ok scolor' sf' spred' (SZ.v n) /\
      stack_is_path sstack' spred' (SZ.v n) (SZ.v vtop') /\
      (* Complexity: ticks == scan work done *)
      vc' + sum_scan_idx sscan (SZ.v n) == reveal vc + sum_scan_idx sscan' (SZ.v n) /\
      (* WHITE vertices still have scan_idx == 0 *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor' j == 0 ==> SZ.v (Seq.index sscan' j) == 0))
    )
{
  // Discover vs (no tick -- scan ticks suffice for complexity bound)
  let t = !time_ref;
  time_ref := t + 1;
  A.op_Array_Assignment d vs (t + 1);
  count_ones_upd_to_one scolor (SZ.v n) (SZ.v vs);
  A.op_Array_Assignment color vs 1;      // GRAY
  A.op_Array_Assignment pred vs (-1);    // NIL
  // scan_idx[vs] = 0 (already 0 since vs is WHITE, by white_scan_zero)
  sum_scan_idx_upd sscan (SZ.v n) (SZ.v vs) 0sz;
  A.op_Array_Assignment scan_idx vs 0sz;
  
  // PUSH(stack, vs)
  let top = !stack_top;
  A.op_Array_Assignment stack_data top vs;
  stack_top := SZ.add top 1sz;

  // Establish DFS tracking after inline discover
  discover_preserves_tracking scolor sd sf (SZ.v n) (SZ.v vs) t;
  discover_preserves_nonwhite scolor (SZ.v vs) (SZ.v vs);
  discover_source_preserves_pred_edge_ok sadj scolor sd spred (SZ.v n) (SZ.v vs) t;
  discover_preserves_timestamps_bounded scolor sd sf (SZ.v n) (SZ.v vs) t;
  discover_preserves_pred_finish_ok scolor sf spred (SZ.v n) (SZ.v vs);
  count_twos_upd_non_two scolor (SZ.v n) (SZ.v vs) 1;

  // Establish stack_is_path after pushing root vs with pred[vs] = -1
  with sstack_post_push. assert (A.pts_to stack_data sstack_post_push);
  with spred_post_push. assert (A.pts_to pred spred_post_push);
  stack_is_path_singleton sstack_post_push spred_post_push (SZ.v n) (SZ.v vs);

  // Process stack
  while (
    let vtop = !stack_top;
    SZ.gt vtop 0sz
  )
  invariant exists* vtop_w vtime_w scolor_w sd_w sf_w spred_w sstack_w sscan_w (vc_w: nat).
    R.pts_to stack_top vtop_w **
    R.pts_to time_ref vtime_w **
    A.pts_to adj sadj **
    A.pts_to color scolor_w **
    A.pts_to d sd_w **
    A.pts_to f sf_w **
    A.pts_to pred spred_w **
    A.pts_to stack_data sstack_w **
    A.pts_to scan_idx sscan_w **
    GR.pts_to ctr vc_w **
    pure (
      SZ.v vs < SZ.v n /\
      Seq.length scolor_w == SZ.v n /\ Seq.length sd_w == SZ.v n /\
      Seq.length sf_w == SZ.v n /\ Seq.length spred_w == SZ.v n /\
      Seq.length sstack_w == SZ.v n /\ Seq.length sscan_w == SZ.v n /\
      vtime_w >= 0 /\ vtime_w >= vtime /\
      SZ.fits (SZ.v n * SZ.v n) /\
      stack_ok scolor_w sstack_w (SZ.v n) (SZ.v vtop_w) /\
      scan_ok sscan_w (SZ.v n) /\
      dfs_ok scolor_w sd_w sf_w (SZ.v n) /\
      gray_ok scolor_w sd_w (SZ.v n) vtime_w /\
      timestamps_bounded scolor_w sd_w sf_w (SZ.v n) vtime_w /\
      vtime_w == count_ones scolor_w (SZ.v n) + 2 * count_twos scolor_w (SZ.v n) /\
      Seq.index scolor_w (SZ.v vs) <> 0 /\
      nonwhite_below scolor_w (SZ.v vs) /\
      pred_edge_ok sadj (SZ.v n) scolor_w sd_w spred_w /\
      pred_finish_ok scolor_w sf_w spred_w (SZ.v n) /\
      stack_is_path sstack_w spred_w (SZ.v n) (SZ.v vtop_w) /\
      vc_w + sum_scan_idx sscan (SZ.v n) == reveal vc + sum_scan_idx sscan_w (SZ.v n) /\
      (* WHITE vertices have scan_idx == 0 *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor_w j == 0 ==> SZ.v (Seq.index sscan_w j) == 0))
    )
  decreases (2 * SZ.v n - !time_ref)
  {
    // u = PEEK(stack)
    let top = !stack_top;
    let u_idx: SZ.t = SZ.sub top 1sz;
    let u: SZ.t = A.op_Array_Access stack_data u_idx;
    
    assert (pure (SZ.v u < SZ.v n));

    // Get current scan position for u
    let scan_pos: SZ.t = A.op_Array_Access scan_idx u;
    
    assert (pure (SZ.v scan_pos <= SZ.v n));
    fits_product_smaller (SZ.v n) (SZ.v n) (SZ.v u) (SZ.v scan_pos);

    // Try to find next WHITE neighbor starting from scan_pos
    let mut found_white: bool = false;
    let mut next_v: SZ.t = 0sz;

    let final_scan = scan_for_white_neighbor adj color n u scan_pos found_white next_v ctr;

    // Update scan_idx[u] to where we stopped
    // Record old sum for complexity accounting
    with sscan_before_upd. assert (A.pts_to scan_idx sscan_before_upd);
    with vc_after_scan. assert (GR.pts_to ctr vc_after_scan);
    sum_scan_idx_upd sscan_before_upd (SZ.v n) (SZ.v u) final_scan;
    A.op_Array_Assignment scan_idx u final_scan;

    let found = !found_white;
    if (found) {
      // Found WHITE neighbor - discover it (inlined to preserve complexity facts)
      let vv = !next_v;
      assert (pure (SZ.v vv < SZ.v n));
      // Edge fact from inner loop invariant
      assert (pure (Seq.index sadj (SZ.v u * SZ.v n + SZ.v vv) <> 0));
      
      with scolor_now. assert (A.pts_to color scolor_now);
      with sd_now. assert (A.pts_to d sd_now);
      with sf_now. assert (A.pts_to f sf_now);
      with spred_now. assert (A.pts_to pred spred_now);
      with vtime_now. assert (R.pts_to time_ref vtime_now);
      dfs_time_bound scolor_now (SZ.v n) vtime_now;
      // count_ones == top, and scolor_now[vv] == 0 (WHITE, not GRAY)
      // so count_ones < n, hence top < n
      count_ones_lt scolor_now (SZ.v n) (SZ.v vv);
      
      // Inline discover_vertex_dfs
      let td = !time_ref;
      time_ref := td + 1;
      A.op_Array_Assignment d vv (td + 1);
      count_ones_upd_to_one scolor_now (SZ.v n) (SZ.v vv);
      A.op_Array_Assignment color vv 1;
      A.op_Array_Assignment pred vv (SZ.v u);
      // scan_idx[vv] = 0 (already 0 by white_scan_zero)
      with sscan_pre_disc. assert (A.pts_to scan_idx sscan_pre_disc);
      sum_scan_idx_upd sscan_pre_disc (SZ.v n) (SZ.v vv) 0sz;
      A.op_Array_Assignment scan_idx vv 0sz;
      // Capture stack state BEFORE push
      with sstack_pre_push. assert (A.pts_to stack_data sstack_pre_push);
      let topd = !stack_top;
      A.op_Array_Assignment stack_data topd vv;
      stack_top := SZ.add topd 1sz;
      // Reestablish DFS tracking
      discover_preserves_tracking scolor_now sd_now sf_now (SZ.v n) (SZ.v vv) vtime_now;
      discover_preserves_nonwhite scolor_now (SZ.v vv) (SZ.v vs);
      // Preserve predecessor tree property
      discover_preserves_pred_edge_ok sadj scolor_now sd_now spred_now (SZ.v n) (SZ.v vv) (SZ.v u) vtime_now;
      discover_preserves_timestamps_bounded scolor_now sd_now sf_now (SZ.v n) (SZ.v vv) vtime_now;
      discover_preserves_pred_finish_ok scolor_now sf_now spred_now (SZ.v n) (SZ.v vv);
      // Preserve stack_is_path: push vv with pred[vv] = u = sstack[topd-1]
      stack_is_path_push sstack_pre_push spred_now (SZ.v n) (SZ.v topd) vv (SZ.v u);
      count_twos_upd_non_two scolor_now (SZ.v n) (SZ.v vv) 1;
      ()
    } else {
      // No more WHITE neighbors - finish u (inlined)
      with scolor_now. assert (A.pts_to color scolor_now);
      with sd_now. assert (A.pts_to d sd_now);
      with sf_now. assert (A.pts_to f sf_now);
      with spred_now. assert (A.pts_to pred spred_now);
      with vtime_now. assert (R.pts_to time_ref vtime_now);
      dfs_time_bound scolor_now (SZ.v n) vtime_now;
      with sstack_now. assert (A.pts_to stack_data sstack_now);
      // Inline finish_vertex
      count_ones_upd_from_one scolor_now (SZ.v n) (SZ.v u) 2;
      A.op_Array_Assignment color u 2;
      let tf = !time_ref;
      time_ref := tf + 1;
      A.op_Array_Assignment f u (tf + 1);
      let topf = !stack_top;
      stack_top := SZ.sub topf 1sz;
      // Reestablish DFS tracking
      finish_preserves_tracking scolor_now sd_now sf_now (SZ.v n) (SZ.v u) vtime_now;
      finish_preserves_nonwhite scolor_now (SZ.v u) (SZ.v vs);
      // Preserve predecessor tree property
      finish_preserves_pred_edge_ok sadj scolor_now sd_now spred_now (SZ.v n) (SZ.v u);
      finish_preserves_timestamps_bounded scolor_now sd_now sf_now (SZ.v n) (SZ.v u) vtime_now;
      // Derive pred[u] not BLACK from stack structure
      stack_top_pred_not_black scolor_now sstack_now spred_now (SZ.v n) (SZ.v topf);
      finish_preserves_pred_finish_ok sadj scolor_now sd_now sf_now spred_now (SZ.v n) (SZ.v u) vtime_now;
      // Preserve stack_is_path after pop
      stack_is_path_pop sstack_now spred_now (SZ.v n) (SZ.v topf);
      count_twos_upd_to_two scolor_now (SZ.v n) (SZ.v u);
      ()
    }
  };
  
  // After the while loop, restore outer invariant shape
  with scolor_after. assert (A.pts_to color scolor_after);
  with sd_after. assert (A.pts_to d sd_after);
  with sf_after. assert (A.pts_to f sf_after);
  with spred_after. assert (A.pts_to pred spred_after);
  with sstack_after. assert (A.pts_to stack_data sstack_after);
  with sscan_after. assert (A.pts_to scan_idx sscan_after);
  with vtop_after. assert (R.pts_to stack_top vtop_after);
  with vtime_after. assert (R.pts_to time_ref vtime_after);
  with vc_final. assert (GR.pts_to ctr vc_final);
  
  assert (pure (SZ.v vtop_after == 0));
  ()
}
#pop-options

(* Helper: conditionally perform DFS-VISIT if vertex is WHITE.
   Both branches produce the same slprop shape, solving Pulse unification. *)

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1 --split_queries always"
fn maybe_dfs_visit
  (adj: A.array int)
  (n: SZ.t)
  (vs: SZ.t)
  (cv: int)
  (color: A.array int)
  (d: A.array int)
  (f: A.array int)
  (pred: A.array int)
  (stack_data: A.array SZ.t)
  (scan_idx: A.array SZ.t)
  (stack_top: ref SZ.t)
  (time_ref: ref int)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
  (#vc: erased nat)
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to f sf **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    GR.pts_to ctr vc **
    with_pure (
      SZ.v vs < SZ.v n /\ SZ.v n > 0 /\ SZ.v vtop == 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\ Seq.length sd == SZ.v n /\
      Seq.length sf == SZ.v n /\ Seq.length spred == SZ.v n /\
      Seq.length sstack == SZ.v n /\ Seq.length sscan == SZ.v n /\
      vtime >= 0 /\ SZ.fits (SZ.v n * SZ.v n) /\
      cv == Seq.index scolor (SZ.v vs) /\
      stack_ok scolor sstack (SZ.v n) (SZ.v vtop) /\
      scan_ok sscan (SZ.v n) /\
      dfs_ok scolor sd sf (SZ.v n) /\
      timestamps_bounded scolor sd sf (SZ.v n) vtime /\
      vtime == count_ones scolor (SZ.v n) + 2 * count_twos scolor (SZ.v n) /\
      nonwhite_below scolor (SZ.v vs) /\
      pred_edge_ok sadj (SZ.v n) scolor sd spred /\
      pred_finish_ok scolor sf spred (SZ.v n) /\
      stack_is_path sstack spred (SZ.v n) (SZ.v vtop) /\
      (* WHITE vertices have scan_idx == 0 *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor j == 0 ==> SZ.v (Seq.index sscan j) == 0))
    )
  ensures exists* scolor' sd' sf' spred' sstack' sscan' vtop' vtime' (vc': nat).
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to f sf' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    GR.pts_to ctr vc' **
    pure (
      Seq.length scolor' == SZ.v n /\ Seq.length sd' == SZ.v n /\
      Seq.length sf' == SZ.v n /\ Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\ Seq.length sscan' == SZ.v n /\
      SZ.v vtop' == 0 /\ vtime' >= vtime /\
      stack_ok scolor' sstack' (SZ.v n) (SZ.v vtop') /\
      scan_ok sscan' (SZ.v n) /\
      dfs_ok scolor' sd' sf' (SZ.v n) /\
      timestamps_bounded scolor' sd' sf' (SZ.v n) vtime' /\
      vtime' == count_ones scolor' (SZ.v n) + 2 * count_twos scolor' (SZ.v n) /\
      nonwhite_below scolor' (SZ.v vs + 1) /\
      pred_edge_ok sadj (SZ.v n) scolor' sd' spred' /\
      pred_finish_ok scolor' sf' spred' (SZ.v n) /\
      stack_is_path sstack' spred' (SZ.v n) (SZ.v vtop') /\
      (* Complexity: ticks == scan work *)
      vc' + sum_scan_idx sscan (SZ.v n) == reveal vc + sum_scan_idx sscan' (SZ.v n) /\
      (* WHITE scan zero preserved *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor' j == 0 ==> SZ.v (Seq.index sscan' j) == 0))
    )
{
  if (cv = 0) {
    // vtop == 0 ⟹ count_ones == 0 ⟹ no GRAY vertices ⟹ gray_ok vacuously
    no_gray_implies_gray_ok scolor sd (SZ.v n) vtime;
    dfs_visit adj n vs color d f pred stack_data scan_idx stack_top time_ref ctr
  }
}
#pop-options

(* ================================================================
   Main stack-based DFS — proves both correctness and complexity
   ================================================================ *)

#push-options "--z3rlimit 15 --fuel 2 --ifuel 1 --split_queries always"
//SNIPPET_START: stack_dfs_sig
fn stack_dfs
  (adj: A.array int)
  (n: SZ.t)
  (color: A.array int)
  (d: A.array int)
  (f: A.array int)
  (pred: A.array int)
  (stack_data: A.array SZ.t)
  (scan_idx: A.array SZ.t)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#c0: erased nat)
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to f sf **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sadj <= A.length adj /\
      Seq.length scolor == SZ.v n /\
      Seq.length scolor <= A.length color /\
      Seq.length sd == SZ.v n /\
      Seq.length sd <= A.length d /\
      Seq.length sf == SZ.v n /\
      Seq.length sf <= A.length f /\
      Seq.length spred == SZ.v n /\
      Seq.length spred <= A.length pred /\
      Seq.length sstack == SZ.v n /\
      Seq.length sstack <= A.length stack_data /\
      Seq.length sscan == SZ.v n /\
      Seq.length sscan <= A.length scan_idx /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* scolor' sd' sf' spred' sstack' sscan' (cf: nat).
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to f sf' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    GR.pts_to ctr cf **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sd' == SZ.v n /\
      Seq.length sf' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\
      Seq.length sscan' == SZ.v n /\
      // All vertices eventually colored BLACK (finished)
      (forall (u: nat). u < SZ.v n ==> Seq.index scolor' u == 2) /\
      // Discovery and finish times are positive
      (forall (u: nat). u < SZ.v n ==> Seq.index sd' u > 0) /\
      (forall (u: nat). u < SZ.v n ==> Seq.index sf' u > 0) /\
      // Discovery time < finish time (parenthesis theorem)
      (forall (u: nat). u < SZ.v n ==> Seq.index sd' u < Seq.index sf' u) /\
      // Timestamp bounds: all timestamps ≤ 2*n
      (forall (u: nat). u < SZ.v n ==> Seq.index sd' u <= 2 * SZ.v n) /\
      (forall (u: nat). u < SZ.v n ==> Seq.index sf' u <= 2 * SZ.v n) /\
      // Predecessor tree: pred[v] >= 0 implies edge from pred[v] to v, d[pred[v]] < d[v]
      pred_edge_ok sadj (SZ.v n) scolor' sd' spred' /\
      // Predecessor finish ordering: children finish before parents
      (forall (v: nat). v < SZ.v n /\ Seq.index spred' v >= 0 /\ Seq.index spred' v < SZ.v n ==>
        Seq.index sf' v < Seq.index sf' (Seq.index spred' v)) /\
      // Complexity: at most 2 * n² ticks
      cf >= reveal c0 /\
      cf - reveal c0 <= 2 * (SZ.v n * SZ.v n)
    )
//SNIPPET_END: stack_dfs_sig
{
  // Step 1: Initialize all vertices
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi scolor_i sd_i sf_i spred_i (vc: nat).
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to color scolor_i **
    A.pts_to d sd_i **
    A.pts_to f sf_i **
    A.pts_to pred spred_i **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length scolor_i == SZ.v n /\
      Seq.length sd_i == SZ.v n /\
      Seq.length sf_i == SZ.v n /\
      Seq.length spred_i == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index scolor_i j == 0) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index sd_i j == (-1)) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index sf_i j == (-1)) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index spred_i j == (-1)) /\
      vc == reveal c0
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    A.op_Array_Assignment color vi 0;      // WHITE
    A.op_Array_Assignment d vi (-1);
    A.op_Array_Assignment f vi (-1);
    A.op_Array_Assignment pred vi (-1);
    i := SZ.add vi 1sz
  };

  // Step 1b: Initialize scan_idx array
  i := 0sz;
  while (!i <^ n)
  invariant exists* vi scolor_ib sd_ib sf_ib spred_ib sscan_ib (vc: nat).
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to color scolor_ib **
    A.pts_to d sd_ib **
    A.pts_to f sf_ib **
    A.pts_to pred spred_ib **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan_ib **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length scolor_ib == SZ.v n /\
      Seq.length sd_ib == SZ.v n /\
      Seq.length sf_ib == SZ.v n /\
      Seq.length spred_ib == SZ.v n /\
      Seq.length sscan_ib == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index sscan_ib j) == 0) /\
      (forall (j: nat). j < SZ.v n ==> Seq.index scolor_ib j == 0) /\
      (forall (j: nat). j < SZ.v n ==> Seq.index sd_ib j == (-1)) /\
      (forall (j: nat). j < SZ.v n ==> Seq.index sf_ib j == (-1)) /\
      (forall (j: nat). j < SZ.v n ==> Seq.index spred_ib j == (-1)) /\
      vc == reveal c0
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    A.op_Array_Assignment scan_idx vi 0sz;
    i := SZ.add vi 1sz
  };

  // Step 2: Initialize time and stack
  let mut time_ref: int = 0;
  let mut stack_top: SZ.t = 0sz;

  // Establish count_ones == 0 (all vertices are WHITE) and sum_scan_idx == 0
  with scolor_init. assert (A.pts_to color scolor_init);
  with sscan_init. assert (A.pts_to scan_idx sscan_init);
  with sd_init. assert (A.pts_to d sd_init);
  with spred_init. assert (A.pts_to pred spred_init);
  count_ones_all_zero scolor_init (SZ.v n);
  sum_scan_idx_all_zero sscan_init (SZ.v n);
  init_pred_edge_ok sadj scolor_init sd_init spred_init (SZ.v n);
  with sf_init. assert (A.pts_to f sf_init);
  count_twos_all_zero scolor_init (SZ.v n);
  init_timestamps_bounded scolor_init sd_init sf_init (SZ.v n) 0;
  init_pred_finish_ok scolor_init sf_init spred_init (SZ.v n);
  with sstack_init. assert (A.pts_to stack_data sstack_init);
  stack_is_path_empty sstack_init spred_init (SZ.v n);

  // Step 3: Main DFS loop - for each vertex s
  let mut s: SZ.t = 0sz;
  while (!s <^ n)
  invariant exists* vs vtop vtime scolor_s sd_s sf_s spred_s sstack_s sscan_s (vc_s: nat).
    R.pts_to s vs **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    A.pts_to adj sadj **
    A.pts_to color scolor_s **
    A.pts_to d sd_s **
    A.pts_to f sf_s **
    A.pts_to pred spred_s **
    A.pts_to stack_data sstack_s **
    A.pts_to scan_idx sscan_s **
    GR.pts_to ctr vc_s **
    pure (
      SZ.v vs <= SZ.v n /\ SZ.v vtop == 0 /\
      Seq.length scolor_s == SZ.v n /\ Seq.length sd_s == SZ.v n /\
      Seq.length sf_s == SZ.v n /\ Seq.length spred_s == SZ.v n /\
      Seq.length sstack_s == SZ.v n /\ Seq.length sscan_s == SZ.v n /\
      vtime >= 0 /\ SZ.fits (SZ.v n * SZ.v n) /\
      stack_ok scolor_s sstack_s (SZ.v n) (SZ.v vtop) /\
      scan_ok sscan_s (SZ.v n) /\
      dfs_ok scolor_s sd_s sf_s (SZ.v n) /\
      timestamps_bounded scolor_s sd_s sf_s (SZ.v n) vtime /\
      vtime == count_ones scolor_s (SZ.v n) + 2 * count_twos scolor_s (SZ.v n) /\
      nonwhite_below scolor_s (SZ.v vs) /\
      pred_edge_ok sadj (SZ.v n) scolor_s sd_s spred_s /\
      pred_finish_ok scolor_s sf_s spred_s (SZ.v n) /\
      stack_is_path sstack_s spred_s (SZ.v n) (SZ.v vtop) /\
      vc_s == reveal c0 + SZ.v vs + sum_scan_idx sscan_s (SZ.v n) /\
      (* WHITE vertices have scan_idx == 0 *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor_s j == 0 ==> SZ.v (Seq.index sscan_s j) == 0))
    )
  decreases (SZ.v n - SZ.v !s)
  {
    let vs = !s;

    // Tick for outer loop iteration (checking color)
    tick ctr;

    // Check if s is WHITE
    let cs: int = A.op_Array_Access color vs;
    
    // Conditionally perform DFS-VISIT
    maybe_dfs_visit adj n vs cs color d f pred stack_data scan_idx stack_top time_ref ctr;

    s := SZ.add vs 1sz
  };
  
  // Prove final postcondition
  with scolor_final. assert (A.pts_to color scolor_final);
  with sd_final. assert (A.pts_to d sd_final);
  with sf_final. assert (A.pts_to f sf_final);
  with sscan_final. assert (A.pts_to scan_idx sscan_final);
  with sstack_final. assert (A.pts_to stack_data sstack_final);
  with vc_final. assert (GR.pts_to ctr vc_final);
  
  // From loop invariant: vc_final == c0 + n + sum_scan_idx sscan_final n
  // and sum_scan_idx sscan_final n <= n * n (since each scan_idx <= n, by scan_ok)
  sum_scan_idx_bound sscan_final (SZ.v n) (SZ.v n);
  // So vc_final - c0 = n + sum_scan_idx <= n + n*n
  // And n + n*n <= 2*n*n (since n >= 1)
  lemma_dfs_bound_correct (SZ.v n) (SZ.v n * SZ.v n) (SZ.v n);
  
  // Assert complexity bound
  assert (pure (vc_final >= reveal c0));
  assert (pure (vc_final - reveal c0 <= 2 * (SZ.v n * SZ.v n)));
  
  // Extract facts from loop invariant for final_postcondition_lemma
  // stack_ok with top==0 gives count_ones == 0
  assert (pure (count_ones scolor_final (SZ.v n) == 0));
  assert (pure (nonwhite_below scolor_final (SZ.v n)));
  assert (pure (dfs_ok scolor_final sd_final sf_final (SZ.v n)));
  final_postcondition_lemma scolor_final sd_final sf_final (SZ.v n);
  // Assert each postcondition quantifier explicitly
  assert (pure (forall (u: nat). u < SZ.v n ==> Seq.index scolor_final u == 2));
  assert (pure (forall (u: nat). u < SZ.v n ==> Seq.index sd_final u > 0));
  assert (pure (forall (u: nat). u < SZ.v n ==> Seq.index sf_final u > 0));
  assert (pure (forall (u: nat). u < SZ.v n ==> Seq.index sd_final u < Seq.index sf_final u));
  // Derive timestamp bounds: vtime <= 2*n => d[u] <= 2*n, f[u] <= 2*n
  with vtime_final. assert (R.pts_to time_ref vtime_final);
  final_timestamps_lemma scolor_final sd_final sf_final (SZ.v n) vtime_final;
  assert (pure (forall (u: nat). u < SZ.v n ==> Seq.index sd_final u <= 2 * SZ.v n));
  assert (pure (forall (u: nat). u < SZ.v n ==> Seq.index sf_final u <= 2 * SZ.v n));
  with spred_final. assert (A.pts_to pred spred_final);
  assert (pure (pred_edge_ok sadj (SZ.v n) scolor_final sd_final spred_final));
  final_pred_finish_lemma scolor_final sf_final spred_final (SZ.v n)
}
#pop-options
