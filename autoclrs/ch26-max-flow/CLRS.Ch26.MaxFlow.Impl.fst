module CLRS.Ch26.MaxFlow.Impl
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
module L = FStar.List.Tot
open CLRS.Ch26.MaxFlow.Spec
module Lemmas = CLRS.Ch26.MaxFlow.Lemmas

(*
   Ford-Fulkerson (Edmonds-Karp) — Verified in Pulse
   
   Computes a maximum flow via BFS-based augmenting paths:
   1. BFS on residual graph to find shortest augmenting path
   2. Find bottleneck (min residual capacity) along the path
   3. Augment flow along the path
   4. Repeat until no augmenting path exists
   
   Termination proved without fuel:
   - Each augmentation increases flow_value by >= 1 (proved by lemma_augment_chain)
   - flow_value <= cap_sum = Σ cap[source][v] (proved from imp_valid_flow)
   - Decreasing measure: cap_sum + 1 - iteration_count
   
   Connects to the fully verified pure spec (Spec.fst, Lemmas.fst):
   - valid_flow maintained through augmentation (Lemmas.augment_preserves_valid)
   - MFMC theorem: no augmenting path => max flow
   
   Postcondition guarantees imp_valid_flow and no_augmenting_path
   (both unconditional, verified, no admits).
   
   Flow validity (imp_valid_flow) is maintained as a loop invariant:
   - Zero flow is valid (lemma_zero_flow_imp_valid)
   - After each augmentation, lemma_augment_chain statically proves
     validity is preserved (no runtime checks needed)
*)

(* ================================================================
   TOTAL WRAPPERS for sequence operations (avoid partial Seq.index)
   ================================================================ *)

(** Maximum 63-bit signed integer, used as initial bottleneck sentinel *)
let int_max : int = 2147483647

let seq_get (s: Seq.seq int) (i: nat) : int =
  if i < Seq.length s then Seq.index s i else 0

let seq_get_sz (s: Seq.seq SZ.t) (i: nat) : SZ.t =
  if i < Seq.length s then Seq.index s i else 0sz

(* ================================================================
   SPEC-LEVEL PREDICATES
   ================================================================ *)

(** Valid non-negative capacities *)
let valid_caps (cap_seq: Seq.seq int) (n: nat) : prop =
  Seq.length cap_seq == n * n /\
  (forall (i: nat). i < n * n ==> Seq.index cap_seq i >= 0)

(** Imperative flow matches spec-level valid_flow — uses total seq_get for Pulse compatibility *)
let imp_valid_flow (flow_seq cap_seq: Seq.seq int) (n source sink: nat) : prop =
  n > 0 /\
  source < n /\
  sink < n /\
  Seq.length flow_seq == n * n /\
  Seq.length cap_seq == n * n /\
  // Capacity constraint: 0 ≤ f(u,v) ≤ c(u,v)
  (forall (u: nat) (v: nat). u < n /\ v < n ==>
    (0 <= seq_get flow_seq (u * n + v) /\
     seq_get flow_seq (u * n + v) <= seq_get cap_seq (u * n + v))) /\
  // Flow conservation
  (forall (u: nat). u < n /\ u <> source /\ u <> sink ==>
    sum_flow_into flow_seq n u n == sum_flow_out flow_seq n u n)

(** Total wrapper for sum_flow_out — avoids refinement types in Pulse ensures clauses *)
let imp_sum_flow_out (s: Seq.seq int) (n v k: nat) : int =
  if n > 0 && v < n && Seq.length s = n * n then sum_flow_out s n v k else 0

(** Total wrapper for sum_flow_into — avoids refinement types in Pulse ensures clauses *)
let imp_sum_flow_into (s: Seq.seq int) (n v k: nat) : int =
  if n > 0 && v < n && Seq.length s = n * n then sum_flow_into s n v k else 0

(** Total wrapper for flow_value — avoids refinement types in Pulse ensures clauses *)
let imp_flow_value (s: Seq.seq int) (n source: nat) : int =
  if n > 0 && source < n && Seq.length s = n * n then flow_value s n source else 0

(** imp_flow_value agrees with flow_value when constraints hold *)
let lemma_imp_flow_value_eq (s: Seq.seq int) (n source: nat)
  : Lemma
    (requires n > 0 /\ source < n /\ Seq.length s == n * n)
    (ensures imp_flow_value s n source == flow_value s n source)
  = ()

(** imp_sum_flow_out agrees with sum_flow_out when constraints hold *)
let lemma_imp_sum_flow_out_eq (s: Seq.seq int) (n v k: nat)
  : Lemma
    (requires n > 0 /\ v < n /\ Seq.length s == n * n)
    (ensures imp_sum_flow_out s n v k == sum_flow_out s n v k)
  = ()

(** Zero-initialized array equals Seq.create *)
let lemma_zero_array_eq_create (s: Seq.seq int) (len: nat)
  : Lemma
    (requires Seq.length s == len /\ (forall (i: nat). i < len ==> Seq.index s i == 0))
    (ensures s == Seq.create len 0)
  = Seq.lemma_eq_intro s (Seq.create len 0)

(** Bridge lemma: imp_valid_flow implies Spec.valid_flow.
    This connects the imperative postcondition to the spec-level predicate
    used by the MFMC theorem. The two predicates are equivalent when indices
    are in range: seq_get s (u*n+v) = get s n u v = Seq.index s (u*n+v). *)
let imp_valid_flow_implies_valid_flow (flow_seq cap_seq: Seq.seq int) (n source sink: nat)
  : Lemma
    (requires imp_valid_flow flow_seq cap_seq n source sink)
    (ensures
      n > 0 /\ source < n /\ sink < n /\
      Seq.length flow_seq == n * n /\ Seq.length cap_seq == n * n /\
      valid_flow #n flow_seq cap_seq source sink)
  = // imp_valid_flow provides length constraints
    assert (Seq.length flow_seq == n * n);
    assert (Seq.length cap_seq == n * n);
    // seq_get and get are both Seq.index for in-range indices
    let aux_cap (u: nat{u < n}) (v: nat{v < n})
      : Lemma (0 <= get flow_seq n u v /\ get flow_seq n u v <= get cap_seq n u v)
      = let idx = u * n + v in
        assert (idx < n * n);
        assert (seq_get flow_seq idx == Seq.index flow_seq idx);
        assert (get flow_seq n u v == Seq.index flow_seq idx);
        assert (seq_get cap_seq idx == Seq.index cap_seq idx);
        assert (get cap_seq n u v == Seq.index cap_seq idx)
    in
    FStar.Classical.forall_intro_2 aux_cap

(** Reverse bridge: valid_flow implies imp_valid_flow.
    Together with imp_valid_flow_implies_valid_flow, the two predicates are equivalent. *)
[@"opaque_to_smt"]
let valid_flow_implies_imp_valid_flow (flow_seq cap_seq: Seq.seq int) (n source sink: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ sink < n /\
      Seq.length flow_seq == n * n /\ Seq.length cap_seq == n * n /\
      valid_flow #n flow_seq cap_seq source sink)
    (ensures imp_valid_flow flow_seq cap_seq n source sink)
  = let aux_cap (u: nat{u < n}) (v: nat{v < n})
      : Lemma (0 <= seq_get flow_seq (u * n + v) /\
               seq_get flow_seq (u * n + v) <= seq_get cap_seq (u * n + v))
      = let idx = u * n + v in
        assert (idx < n * n);
        assert (seq_get flow_seq idx == Seq.index flow_seq idx);
        assert (get flow_seq n u v == Seq.index flow_seq idx)
    in
    FStar.Classical.forall_intro_2 aux_cap

(** Queue entries are valid vertices *)
let queue_valid (squeue: Seq.seq SZ.t) (head tail: nat) (n: nat) : prop =
  forall (k: nat). k >= head /\ k < tail ==> SZ.v (seq_get_sz squeue k) < n

(** All pred entries are in valid range [-1, n) — easy to maintain through BFS *)
let preds_in_range (spred: Seq.seq int) (n: nat) : prop =
  Seq.length spred == n /\
  (forall (v: nat). v < n ==> seq_get spred v >= -1 /\ seq_get spred v < n)

(** Pred entries for discovered non-source vertices are valid *)
let pred_valid (spred scolor: Seq.seq int) (n source: nat) : prop =
  forall (v: nat). v < n /\ v <> source /\ seq_get scolor v <> 0 ==>
    seq_get spred v >= 0 /\ seq_get spred v < n

(* ================================================================
   BFS CORRECTNESS PREDICATES
   ================================================================ *)

(** BFS predecessor-tree invariant:
    - source has pred = -1, dist = 0
    - For discovered v != source: pred[v] = u is a discovered vertex with
      residual edge u->v, and dist[v] = dist[u] + 1 *)
let pred_ok (scolor spred sdist cap_seq flow_seq: Seq.seq int) (n source: nat) : prop =
  source < n /\
  Seq.length scolor == n /\ Seq.length spred == n /\ Seq.length sdist == n /\
  Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\
  seq_get spred source == -1 /\
  seq_get sdist source == 0 /\
  seq_get scolor source <> 0 /\
  (forall (v: nat). v < n /\ v <> source /\ seq_get scolor v <> 0 ==>
    (let u = seq_get spred v in
     u >= 0 /\ u < n /\
     seq_get scolor u <> 0 /\
     seq_get sdist v >= 1 /\
     seq_get sdist v < n /\
     seq_get sdist v == seq_get sdist u + 1 /\
     // Residual edge from u to v
     (seq_get cap_seq (u * n + v) - seq_get flow_seq (u * n + v) > 0 \/
      seq_get flow_seq (v * n + u) > 0)))

(** BFS pred_ok bundled with sdist < vtail bound — opaque to avoid elaboration blowup.
    Combines pred_ok (pred-tree correctness) with the distance bound needed to prove sdist < n. *)
[@"opaque_to_smt"]
let bfs_pred_ok (scolor spred sdist cap_seq flow_seq: Seq.seq int)
                (n source vtail: nat) : prop =
  pred_ok scolor spred sdist cap_seq flow_seq n source /\
  (forall (v: nat). v < n /\ v <> source /\ seq_get scolor v <> 0 ==>
    seq_get sdist v >= 0 /\ seq_get sdist v < vtail)

let mk_bfs_pred_ok (scolor spred sdist cap_seq flow_seq: Seq.seq int) (n source vtail: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      (forall (v: nat). v < n /\ v <> source /\ seq_get scolor v <> 0 ==>
        seq_get sdist v >= 0 /\ seq_get sdist v < vtail))
    (ensures bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail)
  = reveal_opaque (`%bfs_pred_ok) (bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail)

let elim_bfs_pred_ok (scolor spred sdist cap_seq flow_seq: Seq.seq int) (n source vtail: nat)
  : Lemma
    (requires bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail)
    (ensures
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      (forall (v: nat). v < n /\ v <> source /\ seq_get scolor v <> 0 ==>
        seq_get sdist v >= 0 /\ seq_get sdist v < vtail))
  = reveal_opaque (`%bfs_pred_ok) (bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail)

(** Discovery preserves bfs_pred_ok: when discovering vv from u *)
let lemma_discover_preserves_bfs_pred_ok
  (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n source u vv vtail: nat)
  : Lemma
    (requires
      n > 0 /\ u < n /\ vv < n /\ source < n /\ vtail > 0 /\ vtail < n /\
      Seq.length scolor == n /\ Seq.length spred == n /\ Seq.length sdist == n /\
      Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\
      bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail /\
      seq_get scolor vv == 0 /\
      seq_get scolor u <> 0 /\
      (seq_get cap_seq (u * n + vv) - seq_get flow_seq (u * n + vv) > 0 \/
       seq_get flow_seq (vv * n + u) > 0))
    (ensures (
      let sc' = Seq.upd scolor vv 1 in
      let sp' = Seq.upd spred vv u in
      let sd' = Seq.upd sdist vv (seq_get sdist u + 1) in
      bfs_pred_ok sc' sp' sd' cap_seq flow_seq n source (vtail + 1)))
  = elim_bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail;
    let sc' = Seq.upd scolor vv 1 in
    let sp' = Seq.upd spred vv u in
    let du = seq_get sdist u in
    let sd' = Seq.upd sdist vv (du + 1) in
    // Prove pred_ok for the new state
    let aux (v: nat)
      : Lemma
        (requires v < n /\ v <> source /\ seq_get sc' v <> 0)
        (ensures (
          let u' = seq_get sp' v in
          u' >= 0 /\ u' < n /\
          seq_get sc' u' <> 0 /\
          seq_get sd' v >= 1 /\
          seq_get sd' v < n /\
          seq_get sd' v == seq_get (Seq.upd sdist vv (du + 1)) u' + 1 /\
          (seq_get cap_seq (u' * n + v) - seq_get flow_seq (u' * n + v) > 0 \/
           seq_get flow_seq (v * n + u') > 0)))
      = if v = vv then begin
          // New vertex: pred[vv] = u, dist[vv] = du + 1
          assert (seq_get sp' vv == u);
          assert (seq_get sd' vv == du + 1);
          // u is discovered (color u <> 0), so color'[u] <> 0
          assert (seq_get sc' u <> 0);
          // du >= 0 from bfs_pred_ok (u is discovered)
          // If u = source: du = 0 < vtail (vtail > 0).
          // If u <> source: sdist_bounded gives du < vtail.
          if u = source then assert (du == 0)
          else ();
          assert (du >= 0);
          assert (du < vtail);
          assert (du + 1 <= vtail);
          assert (du + 1 < n);
          // sd'[u] = if u = vv then du+1 else sdist[u] = du (since u <> vv: u has color <> 0, vv has color = 0)
          assert (u <> vv);
          assert (seq_get sd' u == du);
          assert (du + 1 == seq_get sd' u + 1)
        end
        else begin
          // Old vertex: unchanged pred/dist, and pred's color preserved
          assert (seq_get sp' v == seq_get spred v);
          assert (seq_get sd' v == seq_get sdist v);
          let u' = seq_get spred v in
          // From old pred_ok: u' >= 0, u' < n, scolor[u'] <> 0
          assert (u' >= 0 /\ u' < n);
          assert (seq_get scolor u' <> 0);
          assert (seq_get sc' u' <> 0);
          // sd'[u'] = sdist[u'] (u' <> vv since scolor[u'] <> 0 but scolor[vv] = 0)
          assert (u' <> vv);
          assert (seq_get sd' u' == seq_get sdist u')
        end
    in
    Classical.forall_intro (Classical.move_requires aux);
    // Prove sdist_bounded for new state
    let aux2 (v: nat)
      : Lemma
        (requires v < n /\ v <> source /\ seq_get sc' v <> 0)
        (ensures seq_get sd' v >= 0 /\ seq_get sd' v < vtail + 1)
      = if v = vv then begin
          assert (seq_get sd' vv == du + 1);
          assert (du >= 0);
          assert (du < vtail);
          assert (du + 1 <= vtail)
        end
        else begin
          assert (seq_get sd' v == seq_get sdist v);
          assert (seq_get sdist v >= 0 /\ seq_get sdist v < vtail)
        end
    in
    Classical.forall_intro (Classical.move_requires aux2);
    mk_bfs_pred_ok sc' sp' sd' cap_seq flow_seq n source (vtail + 1)

(** No-discovery preserves bfs_pred_ok *)
let lemma_nodiscover_preserves_bfs_pred_ok
  (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n source vtail: nat)
  : Lemma
    (requires bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail)
    (ensures bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail)
  = ()

(** Color change from 1 to 2 preserves bfs_pred_ok *)
let lemma_color2_preserves_bfs_pred_ok
  (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n source u vtail: nat)
  : Lemma
    (requires
      n > 0 /\ u < n /\ source < n /\
      Seq.length scolor == n /\
      bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail /\
      seq_get scolor u == 1)
    (ensures bfs_pred_ok (Seq.upd scolor u 2) spred sdist cap_seq flow_seq n source vtail)
  = elim_bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail;
    let sc' = Seq.upd scolor u 2 in
    // pred_ok: scolor u was 1, now 2. Still <> 0. For v <> source with sc'[v] <> 0:
    // if v = u: sc'[u] = 2, same pred/dist conditions as before
    // if v <> u: sc'[v] = scolor[v], and sc'[pred[v]] <> 0 since scolor[pred[v]] <> 0 and
    //   pred[v] <> u (pred[v] could be u, but sc'[u] = 2 <> 0)
    mk_bfs_pred_ok sc' spred sdist cap_seq flow_seq n source vtail

(** Monotonicity: bfs_pred_ok with vtail implies bfs_pred_ok with larger vtail *)
let lemma_bfs_pred_ok_monotone
  (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n source vtail vtail': nat)
  : Lemma
    (requires
      bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail /\
      vtail' >= vtail)
    (ensures bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail')
  = elim_bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail;
    mk_bfs_pred_ok scolor spred sdist cap_seq flow_seq n source vtail'

(** BFS completeness: every residual neighbor of a colored vertex is also colored.
    This holds at BFS termination: the queue is empty, so all reachable vertices
    have been processed and all their neighbors discovered. *)
let bfs_complete (scolor cap_seq flow_seq: Seq.seq int) (n: nat) : prop =
  Seq.length scolor == n /\
  Seq.length cap_seq == n * n /\
  Seq.length flow_seq == n * n /\
  (forall (u: nat) (v: nat). u < n /\ v < n /\ seq_get scolor u <> 0 ==>
    ((seq_get cap_seq (u * n + v) - seq_get flow_seq (u * n + v) > 0 ==>
      seq_get scolor v <> 0) /\
     (seq_get flow_seq (v * n + u) > 0 ==>
      seq_get scolor v <> 0)))

(** All colors are in {0, 1, 2} — maintained by BFS operations *)
let colors_valid (scolor: Seq.seq int) (n: nat) : prop =
  forall (u: nat). u < n ==> (seq_get scolor u == 0 \/ seq_get scolor u == 1 \/ seq_get scolor u == 2)

(** Processed-complete: color-2 vertices have all residual neighbors colored.
    This is the BFS loop invariant — becomes bfs_complete when no color-1 remains. *)
let processed_complete (scolor cap_seq flow_seq: Seq.seq int) (n: nat) : prop =
  (forall (u: nat) (v: nat). u < n /\ v < n /\ seq_get scolor u == 2 ==>
    ((seq_get cap_seq (u * n + v) - seq_get flow_seq (u * n + v) > 0 ==>
      seq_get scolor v <> 0) /\
     (seq_get flow_seq (v * n + u) > 0 ==>
      seq_get scolor v <> 0)))

(** All residual neighbors of vertex u are colored (non-zero) *)
let all_nbrs_colored (scolor cap_seq flow_seq: Seq.seq int) (n: nat) (u: nat) : prop =
  u < n /\
  (forall (v: nat). v < n ==>
    ((seq_get cap_seq (u * n + v) - seq_get flow_seq (u * n + v) > 0 ==>
      seq_get scolor v <> 0) /\
     (seq_get flow_seq (v * n + u) > 0 ==>
      seq_get scolor v <> 0)))

(** Single-neighbor residual coloring: if there's positive residual from u to v, v is colored *)
let nbr_colored_if_residual (scolor cap_seq flow_seq: Seq.seq int) (n u v: nat) : prop =
  (seq_get cap_seq (u * n + v) - seq_get flow_seq (u * n + v) > 0 ==>
    seq_get scolor v <> 0) /\
  (seq_get flow_seq (v * n + u) > 0 ==>
    seq_get scolor v <> 0)

(** Partial neighbor exploration: neighbors w < bound of u are colored if residual > 0 *)
let partial_nbrs_colored (scolor cap_seq flow_seq: Seq.seq int) (n u bound: nat) : prop =
  u < n /\
  (forall (w: nat). w < n /\ w < bound ==>
    ((seq_get cap_seq (u * n + w) - seq_get flow_seq (u * n + w) > 0 ==>
      seq_get scolor w <> 0) /\
     (seq_get flow_seq (w * n + u) > 0 ==>
      seq_get scolor w <> 0)))

let lemma_partial_nbrs_zero (scolor cap_seq flow_seq: Seq.seq int) (n u: nat)
  : Lemma (requires u < n)
    (ensures partial_nbrs_colored scolor cap_seq flow_seq n u 0)
  = ()

let lemma_partial_nbrs_to_all (scolor cap_seq flow_seq: Seq.seq int) (n u: nat)
  : Lemma (requires partial_nbrs_colored scolor cap_seq flow_seq n u n)
    (ensures all_nbrs_colored scolor cap_seq flow_seq n u)
  = ()

(** Step: extend partial_nbrs_colored from bound to bound+1.
    Requires that neighbor `bound` is colored (if it has positive residual).
    Also handles the case where scolor changed (non-zero preservation). *)
#push-options "--z3rlimit 20"
let lemma_partial_nbrs_step
  (scolor scolor': Seq.seq int) (cap_seq flow_seq: Seq.seq int) (n u bound: nat)
  : Lemma
    (requires
      partial_nbrs_colored scolor cap_seq flow_seq n u bound /\
      bound < n /\
      (forall (j: nat). j < n /\ seq_get scolor j <> 0 ==> seq_get scolor' j <> 0) /\
      nbr_colored_if_residual scolor' cap_seq flow_seq n u bound)
    (ensures partial_nbrs_colored scolor' cap_seq flow_seq n u (bound + 1))
  = assert (u < n);
    let aux (w: nat) : Lemma
      (requires w < n /\ w < bound + 1)
      (ensures
        (seq_get cap_seq (u * n + w) - seq_get flow_seq (u * n + w) > 0 ==>
          seq_get scolor' w <> 0) /\
        (seq_get flow_seq (w * n + u) > 0 ==>
          seq_get scolor' w <> 0))
    = if w < bound then begin
        assert (seq_get cap_seq (u * n + w) - seq_get flow_seq (u * n + w) > 0 ==>
          seq_get scolor w <> 0);
        assert (seq_get flow_seq (w * n + u) > 0 ==>
          seq_get scolor w <> 0);
        // From preservation: scolor[w] <> 0 ==> scolor'[w] <> 0
        ()
      end else begin
        // w == bound: directly from the precondition
        ()
      end
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

(** Active queue elements have color 1 *)
let queue_color1 (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (vhead vtail n: nat) : prop =
  forall (j: nat). vhead <= j /\ j < vtail ==> seq_get scolor (SZ.v (seq_get_sz squeue j)) == 1

(** Active queue elements are colored (non-zero) — weaker, but maintained after color[u]=2 *)
let queue_nonzero (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (vhead vtail n: nat) : prop =
  forall (j: nat). vhead <= j /\ j < vtail ==> seq_get scolor (SZ.v (seq_get_sz squeue j)) <> 0

(** Updating a color to a non-zero value preserves queue_nonzero *)
let lemma_queue_nonzero_upd_color (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (vhead vtail n idx: nat) (v: int)
  : Lemma (requires queue_nonzero scolor squeue vhead vtail n /\ idx < Seq.length scolor /\ v <> 0)
    (ensures queue_nonzero (Seq.upd scolor idx v) squeue vhead vtail n)
  = ()

(** Queue entries are distinct: no vertex appears twice in [0, vtail) *)
let queue_entries_unique (squeue: Seq.seq SZ.t) (vtail: nat) : prop =
  forall (i j: nat). i < vtail /\ j < vtail /\ i <> j ==> seq_get_sz squeue i <> seq_get_sz squeue j

(** Combined: queue entries non-zero AND unique *)
let queue_ok (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (vtail n: nat) : prop =
  queue_nonzero scolor squeue 0 vtail n /\ queue_entries_unique squeue vtail

(** Queue prefix preserved: entries below a threshold are unchanged *)
let queue_prefix_preserved (sq sq': Seq.seq SZ.t) (vtail: nat) : prop =
  forall (j: nat). j < vtail ==> seq_get_sz sq' j == seq_get_sz sq j

(** Extending queue with a fresh element preserves uniqueness.
    The new element has color 0 while all existing entries have non-zero color,
    so the new element must differ from all existing entries. *)
let lemma_queue_unique_extend
  (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (vtail n: nat) (vv: SZ.t)
  : Lemma
    (requires
      vtail < Seq.length squeue /\
      SZ.v vv < n /\
      queue_entries_unique squeue vtail /\
      queue_nonzero scolor squeue 0 vtail n /\
      seq_get scolor (SZ.v vv) == 0 /\
      queue_valid squeue 0 vtail n)
    (ensures queue_entries_unique (Seq.upd squeue vtail vv) (vtail + 1))
  = let squeue' = Seq.upd squeue vtail vv in
    let aux (i j: nat)
      : Lemma (requires i < vtail + 1 /\ j < vtail + 1 /\ i <> j)
        (ensures seq_get_sz squeue' i <> seq_get_sz squeue' j)
      = if i < vtail && j < vtail then ()
        else if i = vtail then (
          assert (seq_get scolor (SZ.v vv) == 0);
          assert (seq_get scolor (SZ.v (seq_get_sz squeue j)) <> 0)
        ) else (
          assert (seq_get scolor (SZ.v vv) == 0);
          assert (seq_get scolor (SZ.v (seq_get_sz squeue i)) <> 0)
        )
    in
    assert (queue_entries_unique squeue' (vtail + 1))
      by (FStar.Tactics.norm [delta_only [`%queue_entries_unique; `%seq_get_sz]];
          FStar.Tactics.smt ())

(** Updating queue beyond vtail preserves uniqueness in [0, vtail) *)
let lemma_queue_unique_frame (squeue: Seq.seq SZ.t) (vtail: nat) (idx: nat) (v: SZ.t)
  : Lemma (requires queue_entries_unique squeue vtail /\ idx >= vtail /\ idx < Seq.length squeue)
    (ensures queue_entries_unique (Seq.upd squeue idx v) vtail)
  = ()

(** queue_color1 after setting color[u]=2, using queue uniqueness to skip position vhead *)
let lemma_queue_color1_after_set2
  (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (vhead vtail n u: nat)
  : Lemma
    (requires
      vhead < vtail /\
      queue_color1 scolor squeue vhead vtail n /\
      queue_entries_unique squeue vtail /\
      u == SZ.v (seq_get_sz squeue vhead) /\
      u < Seq.length scolor)
    (ensures queue_color1 (Seq.upd scolor u 2) squeue (vhead + 1) vtail n)
  = let scolor' = Seq.upd scolor u 2 in
    let aux (j: nat) : Lemma
      (requires vhead + 1 <= j /\ j < vtail)
      (ensures seq_get scolor' (SZ.v (seq_get_sz squeue j)) == 1)
      = // queue[j] <> queue[vhead] = u by uniqueness (j <> vhead)
        assert (j <> vhead);
        assert (seq_get_sz squeue j <> seq_get_sz squeue vhead)
    in
    Classical.forall_intro (fun j -> Classical.move_requires aux j)

(** Combined: queue_ok after discovering vertex vv (color 0→1, append to queue) *)
let lemma_queue_ok_after_discover
  (scolor: Seq.seq int) (squeue: Seq.seq SZ.t) (vtail n: nat) (vv: SZ.t)
  : Lemma
    (requires
      queue_ok scolor squeue vtail n /\
      queue_valid squeue 0 vtail n /\
      seq_get scolor (SZ.v vv) == 0 /\
      SZ.v vv < n /\
      Seq.length scolor >= n /\
      vtail < Seq.length squeue)
    (ensures
      queue_ok (Seq.upd scolor (SZ.v vv) 1) (Seq.upd squeue vtail vv) (vtail + 1) n)
  = let sc' = Seq.upd scolor (SZ.v vv) 1 in
    let sq' = Seq.upd squeue vtail vv in
    // Part 1: queue_entries_unique sq' (vtail+1)
    lemma_queue_unique_extend scolor squeue vtail n vv;
    // Part 2: queue_nonzero sc' sq' 0 (vtail+1) n
    let aux (j: nat)
      : Lemma (requires 0 <= j /\ j < vtail + 1)
        (ensures seq_get sc' (SZ.v (seq_get_sz sq' j)) <> 0) =
      if j = vtail then ()  // sq'[vtail] = vv, sc'[vv] = 1 ≠ 0
      else begin
        // j < vtail: sq'[j] = squeue[j], color was non-zero
        assert (seq_get scolor (SZ.v (seq_get_sz squeue j)) <> 0);
        // squeue[j] ≠ vv (since scolor[squeue[j]] ≠ 0 but scolor[vv] = 0)
        ()
      end
    in Classical.forall_intro (Classical.move_requires aux)

(** queue_color1 is preserved when color-1 entries stay color-1 and queue prefix is preserved.
    Also extends to new entries if they have color 1 in the new state. *)
let lemma_queue_color1_preserved
  (scolor scolor': Seq.seq int) (squeue squeue': Seq.seq SZ.t)
  (vhead vtail vtail' n: nat)
  : Lemma
    (requires
      vhead <= vtail /\ vtail <= vtail' /\
      queue_color1 scolor squeue vhead vtail n /\
      queue_valid squeue 0 vtail n /\
      queue_prefix_preserved squeue squeue' vtail /\
      (forall (j: nat). j < n /\ seq_get scolor j == 1 ==> seq_get scolor' j == 1) /\
      queue_color1 scolor' squeue' vtail vtail' n)
    (ensures queue_color1 scolor' squeue' vhead vtail' n)
  = let aux (j: nat)
      : Lemma (requires vhead <= j /\ j < vtail')
        (ensures seq_get scolor' (SZ.v (seq_get_sz squeue' j)) == 1)
      = if j < vtail then begin
          // Old entry: queue prefix preserved, color-1 preservation
          assert (seq_get_sz squeue' j == seq_get_sz squeue j);
          assert (seq_get scolor (SZ.v (seq_get_sz squeue j)) == 1);
          assert (SZ.v (seq_get_sz squeue j) < n)  // from queue_valid
        end
    in Classical.forall_intro (Classical.move_requires aux)

(** Transitivity for queue_prefix_preserved *)
let lemma_queue_prefix_trans (sq0 sq1 sq2: Seq.seq SZ.t) (n0 n1: nat)
  : Lemma
    (requires n0 <= n1 /\ queue_prefix_preserved sq0 sq1 n0 /\ queue_prefix_preserved sq1 sq2 n1)
    (ensures queue_prefix_preserved sq0 sq2 n0)
  = ()

(** Extending queue_color1 range: old [a,b) + new [b,c) = [a,c) using color-1 pres + prefix pres *)
let lemma_queue_color1_chain
  (sc0 sc1: Seq.seq int) (sq0 sq1: Seq.seq SZ.t) (a b c n: nat)
  : Lemma
    (requires
      a <= b /\ b <= c /\
      queue_color1 sc0 sq0 a b n /\
      queue_valid sq0 0 b n /\
      queue_prefix_preserved sq0 sq1 b /\
      (forall (j: nat). j < n /\ seq_get sc0 j == 1 ==> seq_get sc1 j == 1) /\
      queue_color1 sc1 sq1 b c n)
    (ensures queue_color1 sc1 sq1 a c n)
  = let aux (j: nat)
      : Lemma (requires a <= j /\ j < c)
        (ensures seq_get sc1 (SZ.v (seq_get_sz sq1 j)) == 1)
      = if j < b then begin
          assert (seq_get_sz sq1 j == seq_get_sz sq0 j);
          assert (seq_get sc0 (SZ.v (seq_get_sz sq0 j)) == 1);
          assert (SZ.v (seq_get_sz sq0 j) < n)
        end
    in Classical.forall_intro (Classical.move_requires aux)

(** Count of color-1 vertices in positions [0..k) *)
let rec count_color1 (scolor: Seq.seq int) (k: nat) : Tot nat (decreases k) =
  if k = 0 then 0
  else count_color1 scolor (k - 1) + (if seq_get scolor (k - 1) = 1 then 1 else 0)

(** Updating index >= k doesn't affect count over [0..k) *)
let rec lemma_count_color1_frame (scolor: Seq.seq int) (k: nat) (idx: nat) (v: int)
  : Lemma (requires idx < Seq.length scolor /\ idx >= k)
    (ensures count_color1 (Seq.upd scolor idx v) k == count_color1 scolor k)
    (decreases k)
  = if k = 0 then () else lemma_count_color1_frame scolor (k - 1) idx v

(** Setting a non-1 cell to 1 increases count by 1 *)
let rec lemma_count_color1_set_1 (scolor: Seq.seq int) (k: nat) (idx: nat)
  : Lemma (requires idx < Seq.length scolor /\ idx < k /\ Seq.index scolor idx <> 1)
    (ensures count_color1 (Seq.upd scolor idx 1) k == count_color1 scolor k + 1)
    (decreases k)
  = if k - 1 = idx then (if k > 1 then lemma_count_color1_frame scolor (k - 1) idx 1)
    else lemma_count_color1_set_1 scolor (k - 1) idx

(** Setting a color-1 cell to 2 decreases count by 1 *)
let rec lemma_count_color1_set_2 (scolor: Seq.seq int) (k: nat) (idx: nat)
  : Lemma (requires idx < Seq.length scolor /\ idx < k /\ Seq.index scolor idx == 1)
    (ensures count_color1 scolor k >= 1 /\
             count_color1 (Seq.upd scolor idx 2) k == count_color1 scolor k - 1)
    (decreases k)
  = if k - 1 = idx then (if k > 1 then lemma_count_color1_frame scolor (k - 1) idx 2)
    else lemma_count_color1_set_2 scolor (k - 1) idx

(** Updating a non-1 cell to a non-1 value preserves count *)
let rec lemma_count_color1_preserve (scolor: Seq.seq int) (k: nat) (idx: nat) (v: int)
  : Lemma (requires idx < Seq.length scolor /\ idx < k /\ Seq.index scolor idx <> 1 /\ v <> 1)
    (ensures count_color1 (Seq.upd scolor idx v) k == count_color1 scolor k)
    (decreases k)
  = if k - 1 = idx then (if k > 1 then lemma_count_color1_frame scolor (k - 1) idx v)
    else lemma_count_color1_preserve scolor (k - 1) idx v

(** If count_color1 is 0, no vertex has color 1 *)
let rec lemma_count_zero_no_color1 (scolor: Seq.seq int) (k: nat)
  : Lemma (requires count_color1 scolor k == 0)
    (ensures forall (u: nat). u < k ==> seq_get scolor u <> 1)
    (decreases k)
  = if k = 0 then () else lemma_count_zero_no_color1 scolor (k - 1)

(** If all entries are 0, count_color1 is 0 *)
let rec lemma_count_color1_all_zero (scolor: Seq.seq int) (k: nat)
  : Lemma (requires forall (j: nat). j < k ==> seq_get scolor j == 0)
    (ensures count_color1 scolor k == 0)
    (decreases k)
  = if k = 0 then () else lemma_count_color1_all_zero scolor (k - 1)

(** If exactly one entry has color 1 and the rest are 0, count_color1 is 1 *)
let rec lemma_count_color1_single (scolor: Seq.seq int) (k: nat) (idx: nat)
  : Lemma
    (requires
      idx < k /\
      seq_get scolor idx == 1 /\
      (forall (j: nat). j < k /\ j <> idx ==> seq_get scolor j == 0))
    (ensures count_color1 scolor k == 1)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 = idx then lemma_count_color1_all_zero scolor (k - 1)
    else lemma_count_color1_single scolor (k - 1) idx

(** Count of non-zero colored vertices in positions [0..k) *)
let rec count_nonzero (scolor: Seq.seq int) (k: nat) : Tot nat (decreases k) =
  if k = 0 then 0
  else count_nonzero scolor (k - 1) + (if seq_get scolor (k - 1) <> 0 then 1 else 0)

(** Helper for chaining addition-form count_color1 equations *)
let lemma_add_chain (a1 a2 b c d1 d2: nat)
  : Lemma (requires a1 + b == c + d1 /\ a2 + d1 == a1 + d2)
    (ensures a2 + b == c + d2)
  = ()

(** count_nonzero <= k *)
let rec lemma_count_nonzero_bound (scolor: Seq.seq int) (k: nat)
  : Lemma (ensures count_nonzero scolor k <= k)
    (decreases k)
  = if k = 0 then () else lemma_count_nonzero_bound scolor (k - 1)

(** Updating index >= k doesn't affect count_nonzero over [0..k) *)
let rec lemma_count_nonzero_frame (scolor: Seq.seq int) (k: nat) (idx: nat) (v: int)
  : Lemma (requires idx < Seq.length scolor /\ idx >= k)
    (ensures count_nonzero (Seq.upd scolor idx v) k == count_nonzero scolor k)
    (decreases k)
  = if k = 0 then () else lemma_count_nonzero_frame scolor (k - 1) idx v

(** Setting a zero cell to non-zero increases count_nonzero by 1 *)
let rec lemma_count_nonzero_set_nz (scolor: Seq.seq int) (k: nat) (idx: nat) (v: int)
  : Lemma (requires idx < Seq.length scolor /\ idx < k /\ Seq.index scolor idx == 0 /\ v <> 0)
    (ensures count_nonzero (Seq.upd scolor idx v) k == count_nonzero scolor k + 1)
    (decreases k)
  = if k - 1 = idx then (if k > 1 then lemma_count_nonzero_frame scolor (k - 1) idx v)
    else lemma_count_nonzero_set_nz scolor (k - 1) idx v

(** Setting a non-zero cell to non-zero preserves count_nonzero *)
let rec lemma_count_nonzero_preserve (scolor: Seq.seq int) (k: nat) (idx: nat) (v: int)
  : Lemma (requires idx < Seq.length scolor /\ idx < k /\ Seq.index scolor idx <> 0 /\ v <> 0)
    (ensures count_nonzero (Seq.upd scolor idx v) k == count_nonzero scolor k)
    (decreases k)
  = if k - 1 = idx then (if k > 1 then lemma_count_nonzero_frame scolor (k - 1) idx v)
    else lemma_count_nonzero_preserve scolor (k - 1) idx v

(** If count_nonzero < k, there exists a zero-colored vertex (hence vtail < k) *)
let rec lemma_count_nonzero_lt_has_zero (scolor: Seq.seq int) (k: nat) (idx: nat)
  : Lemma (requires idx < k /\ seq_get scolor idx == 0)
    (ensures count_nonzero scolor k < k)
    (decreases k)
  = if k = 0 then () 
    else begin
      lemma_count_nonzero_bound scolor (k - 1);
      if k - 1 = idx then ()
      else lemma_count_nonzero_lt_has_zero scolor (k - 1) idx
    end

(** If some entry in [0,k) is non-zero, count_nonzero >= 1 *)
let rec lemma_count_nonzero_ge_1 (scolor: Seq.seq int) (k: nat) (idx: nat)
  : Lemma (requires idx < k /\ seq_get scolor idx <> 0)
    (ensures count_nonzero scolor k >= 1)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 = idx then ()
    else lemma_count_nonzero_ge_1 scolor (k - 1) idx

(** If all entries in [0,k) are zero, count_nonzero is 0 *)
let rec lemma_count_nonzero_all_zero (scolor: Seq.seq int) (k: nat)
  : Lemma (requires forall (j: nat). j < k ==> seq_get scolor j == 0)
    (ensures count_nonzero scolor k == 0)
    (decreases k)
  = if k = 0 then () else lemma_count_nonzero_all_zero scolor (k - 1)

(** If exactly one entry in [0,k) is non-zero, count_nonzero is 1 *)
let rec lemma_count_nonzero_single (scolor: Seq.seq int) (k: nat) (idx: nat)
  : Lemma
    (requires
      idx < k /\
      seq_get scolor idx <> 0 /\
      (forall (j: nat). j < k /\ j <> idx ==> seq_get scolor j == 0))
    (ensures count_nonzero scolor k == 1)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 = idx then lemma_count_nonzero_all_zero scolor (k - 1)
    else lemma_count_nonzero_single scolor (k - 1) idx

(** processed_complete + no color-1 vertices + colors_valid => bfs_complete *)
let lemma_processed_to_bfs_complete (scolor cap_seq flow_seq: Seq.seq int) (n: nat)
  : Lemma
    (requires
      Seq.length scolor == n /\ Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\
      processed_complete scolor cap_seq flow_seq n /\
      (forall (u: nat). u < n ==> seq_get scolor u <> 1) /\
      colors_valid scolor n)
    (ensures bfs_complete scolor cap_seq flow_seq n)
  = ()

(** Setting a zero-colored cell to 1 preserves processed_complete *)
let lemma_processed_complete_set_1 (scolor cap_seq flow_seq: Seq.seq int) (n: nat) (idx: nat)
  : Lemma
    (requires idx < n /\ Seq.length scolor == n /\ seq_get scolor idx == 0 /\
              processed_complete scolor cap_seq flow_seq n)
    (ensures processed_complete (Seq.upd scolor idx 1) cap_seq flow_seq n)
  = ()

(** Setting color[u]=2 after all neighbors are colored extends processed_complete *)
let lemma_processed_complete_extend (scolor cap_seq flow_seq: Seq.seq int) (n: nat) (u: nat)
  : Lemma
    (requires u < n /\ Seq.length scolor == n /\
              processed_complete scolor cap_seq flow_seq n /\
              all_nbrs_colored scolor cap_seq flow_seq n u)
    (ensures processed_complete (Seq.upd scolor u 2) cap_seq flow_seq n)
  = ()

(** Extending queue_valid by one entry *)
let lemma_queue_valid_extend (squeue: Seq.seq SZ.t) (tail n: nat) (v: SZ.t)
  : Lemma
    (requires queue_valid squeue 0 tail n /\
              tail < Seq.length squeue /\
              SZ.v v < n)
    (ensures queue_valid (Seq.upd squeue tail v) 0 (tail + 1) n)
  = let sq' = Seq.upd squeue tail v in
    let aux (k: nat)
      : Lemma (requires k >= 0 /\ k < tail + 1) (ensures SZ.v (seq_get_sz sq' k) < n) =
      if k = tail then () else ()
    in Classical.forall_intro (Classical.move_requires aux)

(** Updating one pred entry preserves preds_in_range *)
let lemma_preds_in_range_upd (spred: Seq.seq int) (n: nat) (idx: nat) (v: int)
  : Lemma
    (requires preds_in_range spred n /\ idx < n /\ v >= -1 /\ v < n)
    (ensures preds_in_range (Seq.upd spred idx v) n)
  = let sp' = Seq.upd spred idx v in
    let aux (w: nat)
      : Lemma (requires w < n) (ensures seq_get sp' w >= -1 /\ seq_get sp' w < n) =
      if w = idx then () else ()
    in Classical.forall_intro (Classical.move_requires aux)

(** colors_valid is preserved when setting a zero cell to 1 *)
let lemma_colors_valid_set_1 (scolor: Seq.seq int) (n: nat) (idx: nat)
  : Lemma
    (requires colors_valid scolor n /\ idx < n /\ Seq.length scolor == n)
    (ensures colors_valid (Seq.upd scolor idx 1) n)
  = ()

(* ================================================================
   PATH VALIDITY LEMMAS
   Prove properties of path_from_preds given pred_ok.
   ================================================================ *)

(** Extract augmenting path from BFS predecessor array.
    Walks pred from sink back to source, building path [source, ..., sink].
    Uses fuel to ensure termination (path length bounded by n). *)
let rec path_from_preds_aux (spred: Seq.seq int) (n: nat{Seq.length spred == n})
                            (source: nat{source < n}) (current: nat{current < n})
                            (fuel: nat)
  : Tot (list nat) (decreases fuel)
  = if fuel = 0 then [current]
    else if current = source then [source]
    else
      let p = seq_get spred current in
      if p >= 0 && p < n then
        L.append (path_from_preds_aux spred n source p (fuel - 1)) [current]
      else [current]

let path_from_preds (spred: Seq.seq int) (n: nat{Seq.length spred == n})
                    (source: nat{source < n}) (sink: nat{sink < n})
  : list nat
  = path_from_preds_aux spred n source sink n

(** Depth of a vertex in the pred tree (follows pred chain to source) *)
let rec pred_chain_depth (spred: Seq.seq int) (n source: nat) (v: nat) (fuel: nat)
  : Tot int (decreases fuel)
  = if v = source then 0
    else if fuel = 0 then -1
    else
      let u = seq_get spred v in
      if u >= 0 && u < n then
        let d = pred_chain_depth spred n source u (fuel - 1) in
        if d >= 0 then d + 1 else -1
      else -1

(** pred_chain_depth agrees with sdist for discovered vertices *)
let rec lemma_depth_eq_dist (scolor spred sdist cap_seq flow_seq: Seq.seq int) (n source: nat) (v: nat) (fuel: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      v < n /\ seq_get scolor v <> 0 /\ fuel >= seq_get sdist v /\ seq_get sdist v >= 0)
    (ensures pred_chain_depth spred n source v fuel == seq_get sdist v)
    (decreases fuel)
  = if v = source then ()
    else begin
      let u = seq_get spred v in
      assert (u >= 0 /\ u < n /\ seq_get scolor u <> 0);
      assert (seq_get sdist v == seq_get sdist u + 1);
      assert (seq_get sdist u >= 0);
      if fuel > 0 then
        lemma_depth_eq_dist scolor spred sdist cap_seq flow_seq n source u (fuel - 1)
    end

(** path_from_preds_aux: if dist[current] < fuel and pred_ok holds,
    the path starts at source *)
let rec lemma_path_starts_source (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length spred == n}) (source: nat{source < n}) (current: nat{current < n})
  (fuel: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      seq_get scolor current <> 0 /\ seq_get sdist current >= 0 /\
      fuel > seq_get sdist current)
    (ensures (
      let path = path_from_preds_aux spred n source current fuel in
      Cons? path /\ L.hd path == source))
    (decreases fuel)
  = if current = source then ()
    else begin
      let u = seq_get spred current in
      assert (u >= 0 /\ u < n /\ seq_get scolor u <> 0);
      assert (seq_get sdist current == seq_get sdist u + 1);
      lemma_path_starts_source scolor spred sdist cap_seq flow_seq n source u (fuel - 1);
      let prefix = path_from_preds_aux spred n source u (fuel - 1) in
      assert (Cons? prefix /\ L.hd prefix == source);
      L.append_l_cons (L.hd prefix) (L.tl prefix) [current]
    end

(** path_from_preds_aux: last element is current *)
let rec lemma_path_ends_current (spred: Seq.seq int) (n: nat{Seq.length spred == n})
  (source: nat{source < n}) (current: nat{current < n}) (fuel: nat)
  : Lemma
    (ensures (
      let path = path_from_preds_aux spred n source current fuel in
      Cons? path /\ L.last path == current))
    (decreases fuel)
  = if fuel = 0 then ()
    else if current = source then ()
    else begin
      let u = seq_get spred current in
      if u >= 0 && u < n then begin
        lemma_path_ends_current spred n source u (fuel - 1);
        let prefix = path_from_preds_aux spred n source u (fuel - 1) in
        L.lemma_append_last prefix [current]
      end
      else ()
    end

(** All vertices in path_from_preds_aux are < n *)
let rec lemma_path_vertices_bounded (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length spred == n}) (source: nat{source < n}) (current: nat{current < n})
  (fuel: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      seq_get scolor current <> 0 /\ seq_get sdist current >= 0 /\
      fuel > seq_get sdist current)
    (ensures (
      let path = path_from_preds_aux spred n source current fuel in
      forall (v: nat). L.mem v path ==> v < n))
    (decreases fuel)
  = if current = source then ()
    else begin
      let u = seq_get spred current in
      assert (u >= 0 /\ u < n);
      lemma_path_vertices_bounded scolor spred sdist cap_seq flow_seq n source u (fuel - 1);
      let prefix = path_from_preds_aux spred n source u (fuel - 1) in
      let aux (v: nat) : Lemma (L.mem v (L.append prefix [current]) ==> v < n)
        = L.append_mem prefix [current] v
      in FStar.Classical.forall_intro aux
    end

(** All vertices on path have dist strictly decreasing from back to front *)
let rec lemma_path_depths_decreasing (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length spred == n}) (source: nat{source < n}) (current: nat{current < n})
  (fuel: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      seq_get scolor current <> 0 /\ seq_get sdist current >= 0 /\
      fuel > seq_get sdist current)
    (ensures (
      let path = path_from_preds_aux spred n source current fuel in
      forall (v: nat). L.mem v path ==>
        v < n /\ seq_get scolor v <> 0 /\
        seq_get sdist v >= 0 /\ seq_get sdist v <= seq_get sdist current))
    (decreases fuel)
  = if current = source then ()
    else begin
      let u = seq_get spred current in
      assert (u >= 0 /\ u < n);
      assert (seq_get sdist current == seq_get sdist u + 1);
      lemma_path_depths_decreasing scolor spred sdist cap_seq flow_seq n source u (fuel - 1);
      let prefix = path_from_preds_aux spred n source u (fuel - 1) in
      let aux (v: nat) : Lemma (L.mem v (L.append prefix [current]) ==>
          v < n /\ seq_get scolor v <> 0 /\ seq_get sdist v >= 0 /\ seq_get sdist v <= seq_get sdist current)
        = L.append_mem prefix [current] v
      in FStar.Classical.forall_intro aux
    end

(** Helper: appending a non-member preserves distinct_vertices *)
let rec lemma_distinct_append (prefix: list nat) (x: nat)
  : Lemma
    (requires distinct_vertices prefix /\ not (L.mem x prefix))
    (ensures distinct_vertices (L.append prefix [x]))
    (decreases prefix)
  = match prefix with
    | [] -> ()
    | hd :: tl ->
      let aux (v: nat) : Lemma (L.mem v (L.append tl [x]) ==> (L.mem v tl || v = x))
        = L.append_mem tl [x] v in
      FStar.Classical.forall_intro aux;
      lemma_distinct_append tl x

(** Key: distinct vertices from strictly decreasing dist.
    Vertices on path all have different dist values, hence are distinct. *)
let lemma_path_not_mem (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length spred == n}) (source: nat{source < n}) (current: nat{current < n})
  (fuel: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      seq_get scolor current <> 0 /\ seq_get sdist current >= 0 /\
      fuel > seq_get sdist current /\ current <> source)
    (ensures (
      let u = seq_get spred current in
      let prefix = path_from_preds_aux spred n source u (fuel - 1) in
      not (L.mem current prefix)))
    (decreases fuel)
  = let u = seq_get spred current in
    assert (u >= 0 /\ u < n);
    assert (seq_get sdist current == seq_get sdist u + 1);
    lemma_path_depths_decreasing scolor spred sdist cap_seq flow_seq n source u (fuel - 1);
    let prefix = path_from_preds_aux spred n source u (fuel - 1) in
    assert (forall (v: nat). L.mem v prefix ==> seq_get sdist v <= seq_get sdist u);
    assert (seq_get sdist current > seq_get sdist u);
    ()

let rec lemma_path_distinct (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length spred == n}) (source: nat{source < n}) (current: nat{current < n})
  (fuel: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      seq_get scolor current <> 0 /\ seq_get sdist current >= 0 /\
      fuel > seq_get sdist current)
    (ensures distinct_vertices (path_from_preds_aux spred n source current fuel))
    (decreases fuel)
  = if current = source then ()
    else begin
      let u = seq_get spred current in
      assert (u >= 0 /\ u < n);
      lemma_path_distinct scolor spred sdist cap_seq flow_seq n source u (fuel - 1);
      lemma_path_not_mem scolor spred sdist cap_seq flow_seq n source current fuel;
      let prefix = path_from_preds_aux spred n source u (fuel - 1) in
      lemma_distinct_append prefix current
    end

(** Path length ≥ 2 when source ≠ sink *)
let lemma_path_length_ge_2 (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length spred == n}) (source: nat{source < n}) (sink: nat{sink < n})
  (fuel: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      source <> sink /\
      seq_get scolor sink <> 0 /\ seq_get sdist sink >= 0 /\
      fuel > seq_get sdist sink)
    (ensures L.length (path_from_preds_aux spred n source sink fuel) >= 2)
  = // sink ≠ source, so path = prefix ++ [sink], prefix = path to pred[sink]
    // prefix is non-empty (at least [source]), so length ≥ 2
    let u = seq_get spred sink in
    assert (u >= 0 /\ u < n);
    lemma_path_ends_current spred n source u (fuel - 1);
    let prefix = path_from_preds_aux spred n source u (fuel - 1) in
    assert (Cons? prefix);
    L.append_length prefix [sink]

(* ================================================================
   PRED-BASED BOTTLENECK AND AUGMENT: PURE FUNCTIONAL VERSIONS
   These match the imperative find_bottleneck_imp / augment_imp logic.
   ================================================================ *)

(** Edge residual: effective residual capacity of edge (u,v).
    Uses forward residual if positive, otherwise backward. *)
let edge_residual (cap_seq flow_seq: Seq.seq int)
                  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n})
                  (u: nat{u < n}) (v: nat{v < n}) : int =
  let fwd = residual_capacity cap_seq flow_seq n u v in
  if fwd > 0 then fwd else residual_capacity_backward flow_seq n u v

(** Pure bottleneck via pred walk: walks pred from current to source,
    computing min of edge_residual along the path. Matches find_bottleneck_imp. *)
let rec bottleneck_via_pred (spred cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\ Seq.length spred == n /\ n > 0})
  (source: nat{source < n}) (current: nat{current < n}) (fuel: nat)
  : Tot int (decreases fuel)
  = if fuel = 0 || current = source then int_max
    else
      let u = seq_get spred current in
      if u >= 0 && u < n then
        let er = edge_residual cap_seq flow_seq n u current in
        let rest = bottleneck_via_pred spred cap_seq flow_seq n source u (fuel - 1) in
        if er < rest then er else rest
      else int_max

(** Bottleneck of (prefix ++ [x]) = min(bottleneck(prefix), edge_residual(last prefix, x)) *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec lemma_bottleneck_append
  (cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\ n > 0})
  (prefix: list nat{Cons? prefix /\ (forall (v: nat). L.mem v prefix ==> v < n)})
  (x: nat{x < n})
  : Lemma
    (ensures (
      let path = L.append prefix [x] in
      Cons? path /\
      (forall (v: nat). L.mem v path ==> v < n) /\
      L.last prefix < n /\
      bottleneck_aux cap_seq flow_seq n path ==
        (let last_v = L.last prefix in
         let er = edge_residual cap_seq flow_seq n last_v x in
         let br = bottleneck_aux cap_seq flow_seq n prefix in
         if er < br then er else br)))
    (decreases prefix)
  = let aux (v: nat) : Lemma (L.mem v (L.append prefix [x]) ==> v < n)
      = L.append_mem prefix [x] v in
    FStar.Classical.forall_intro aux;
    match prefix with
    | [a] ->
      // prefix ++ [x] = [a, x]
      // bottleneck_aux [a, x] = min(edge_residual(a,x), bottleneck_aux [x]) = min(edge_residual(a,x), int_max)
      // min(bottleneck_aux [a], edge_residual(a,x)) = min(int_max, edge_residual(a,x))
      // Both equal edge_residual(a,x) (or int_max if edge_residual >= int_max)
      ()
    | a :: b :: rest ->
      // prefix ++ [x] = a :: (b :: rest ++ [x])
      let suffix = b :: rest in
      let aux2 (v: nat) : Lemma (L.mem v suffix ==> v < n) = () in
      FStar.Classical.forall_intro aux2;
      lemma_bottleneck_append cap_seq flow_seq n suffix x;
      // bottleneck_aux (a :: (suffix ++ [x])) = min(edge(a,b), bottleneck_aux (suffix ++ [x]))
      // By IH: bottleneck_aux (suffix ++ [x]) = min(bottleneck_aux suffix, edge(last suffix, x))
      // bottleneck_aux prefix = min(edge(a,b), bottleneck_aux suffix)
      // Need: min(edge(a,b), min(bottleneck_aux suffix, edge(last,x)))
      //      = min(min(edge(a,b), bottleneck_aux suffix), edge(last,x))
      // This is min associativity — SMT should handle it
      L.append_assoc [a] suffix [x];
      // L.last of prefix = L.last of suffix (since prefix = a :: suffix and suffix is non-empty)
      assert (L.last prefix == L.last suffix)
#pop-options

(** Bottleneck via pred equals bottleneck on the path from preds.
    Requires pred_ok with sufficient fuel. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec lemma_bottleneck_via_pred_eq (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\ Seq.length spred == n /\ n > 0})
  (source: nat{source < n}) (current: nat{current < n}) (fuel: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      Seq.length scolor == n /\ Seq.length sdist == n /\
      seq_get scolor current <> 0 /\ seq_get sdist current >= 0 /\
      fuel > seq_get sdist current)
    (ensures (
      let path = path_from_preds_aux spred n source current fuel in
      Cons? path /\
      (forall (v: nat). L.mem v path ==> v < n) /\
      bottleneck_via_pred spred cap_seq flow_seq n source current fuel ==
      bottleneck_aux cap_seq flow_seq n path))
    (decreases fuel)
  = if current = source then ()
    else begin
      let u = seq_get spred current in
      assert (u >= 0 /\ u < n);
      assert (seq_get scolor u <> 0);
      assert (seq_get sdist current == seq_get sdist u + 1);
      lemma_bottleneck_via_pred_eq scolor spred sdist cap_seq flow_seq n source u (fuel - 1);
      let prefix = path_from_preds_aux spred n source u (fuel - 1) in
      lemma_path_ends_current spred n source u (fuel - 1);
      assert (L.last prefix == u);
      lemma_path_vertices_bounded scolor spred sdist cap_seq flow_seq n source u (fuel - 1);
      lemma_path_starts_source scolor spred sdist cap_seq flow_seq n source u (fuel - 1);
      lemma_bottleneck_append cap_seq flow_seq n prefix current;
      // Prove path properties for the full path
      let path = L.append prefix [current] in
      let aux (v: nat) : Lemma (L.mem v path ==> v < n)
        = L.append_mem prefix [current] v in
      FStar.Classical.forall_intro aux
    end
#pop-options

(** Each edge on path from preds has positive residual capacity *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let lemma_path_edges_positive (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\ Seq.length spred == n /\ n > 0})
  (source: nat{source < n}) (current: nat{current < n}) (fuel: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      Seq.length scolor == n /\ Seq.length sdist == n /\
      seq_get scolor current <> 0 /\ seq_get sdist current >= 0 /\
      fuel > seq_get sdist current /\ current <> source)
    (ensures edge_residual cap_seq flow_seq n (seq_get spred current) current > 0)
  = let u = seq_get spred current in
    assert (u >= 0 /\ u < n);
    // From pred_ok: residual(u, current) > 0 or backward(u, current) > 0
    // edge_residual uses forward if positive, else backward
    ()
#pop-options

(** Bottleneck via pred is positive when pred_ok holds and current ≠ source *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec lemma_bottleneck_via_pred_positive (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\ Seq.length spred == n /\ n > 0})
  (source: nat{source < n}) (current: nat{current < n}) (fuel: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      Seq.length scolor == n /\ Seq.length sdist == n /\
      seq_get scolor current <> 0 /\ seq_get sdist current >= 0 /\
      fuel > seq_get sdist current /\ current <> source)
    (ensures bottleneck_via_pred spred cap_seq flow_seq n source current fuel > 0)
    (decreases fuel)
  = let u = seq_get spred current in
    assert (u >= 0 /\ u < n);
    lemma_path_edges_positive scolor spred sdist cap_seq flow_seq n source current fuel;
    let er = edge_residual cap_seq flow_seq n u current in
    assert (er > 0);
    if u = source then ()
    else begin
      assert (seq_get scolor u <> 0);
      assert (seq_get sdist current == seq_get sdist u + 1);
      lemma_bottleneck_via_pred_positive scolor spred sdist cap_seq flow_seq n source u (fuel - 1);
      let rest = bottleneck_via_pred spred cap_seq flow_seq n source u (fuel - 1) in
      assert (rest > 0);
      assert (if er < rest then er else rest) > 0
    end
#pop-options

(** Fuel monotonicity: bottleneck_via_pred gives the same result with any sufficient fuel *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec lemma_bottleneck_fuel_mono (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\ Seq.length spred == n /\ n > 0})
  (source: nat{source < n}) (current: nat{current < n}) (fuel1 fuel2: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      Seq.length scolor == n /\ Seq.length sdist == n /\
      seq_get scolor current <> 0 /\ seq_get sdist current >= 0 /\
      fuel1 > seq_get sdist current /\ fuel2 > seq_get sdist current)
    (ensures
      bottleneck_via_pred spred cap_seq flow_seq n source current fuel1 ==
      bottleneck_via_pred spred cap_seq flow_seq n source current fuel2)
    (decreases fuel1)
  = if current = source then ()
    else begin
      let u = seq_get spred current in
      assert (u >= 0 /\ u < n);
      assert (seq_get scolor u <> 0);
      assert (seq_get sdist current == seq_get sdist u + 1);
      lemma_bottleneck_fuel_mono scolor spred sdist cap_seq flow_seq n source u (fuel1 - 1) (fuel2 - 1)
    end
#pop-options

(** bottleneck_via_pred always returns a value <= int_max (since int_max is the base case
    and we only take min) *)
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rec lemma_bottleneck_via_pred_le_int_max (spred cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\ Seq.length spred == n /\ n > 0})
  (source: nat{source < n}) (current: nat{current < n}) (fuel: nat)
  : Lemma
    (ensures bottleneck_via_pred spred cap_seq flow_seq n source current fuel <= int_max)
    (decreases fuel)
  = if fuel = 0 || current = source then ()
    else
      let u = seq_get spred current in
      if u >= 0 && u < n then
        lemma_bottleneck_via_pred_le_int_max spred cap_seq flow_seq n source u (fuel - 1)
      else ()
#pop-options

(** One step of the bottleneck loop: given the invariant holds for (vc, vbn),
    after computing new_vbn via the code's branching, the invariant holds for (u, new_vbn).
    This encapsulates all the case analysis + fuel mono + min associativity. *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let lemma_bottleneck_step
  (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\ Seq.length spred == n /\ n > 0
           /\ Seq.length scolor == n /\ Seq.length sdist == n})
  (source: nat{source < n}) (sink: nat{sink < n}) (current: nat{current < n /\ current <> source})
  (vbn: int)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      seq_get scolor current <> 0 /\
      vbn >= 0 /\ vbn <= int_max /\
      bottleneck_via_pred spred cap_seq flow_seq n source sink n ==
        (if vbn < bottleneck_via_pred spred cap_seq flow_seq n source current n
         then vbn
         else bottleneck_via_pred spred cap_seq flow_seq n source current n))
    (ensures (
      let u = seq_get spred current in
      u >= 0 /\ u < n /\
      seq_get scolor u <> 0 /\
      (let res_fwd = seq_get cap_seq (u * n + current) - seq_get flow_seq (u * n + current) in
       let flow_bwd = seq_get flow_seq (current * n + u) in
       let new_vbn =
         if res_fwd > 0 then (if res_fwd < vbn then res_fwd else vbn)
         else (if flow_bwd > 0 && flow_bwd < vbn then flow_bwd else vbn) in
       new_vbn >= 0 /\ new_vbn <= int_max /\
       bottleneck_via_pred spred cap_seq flow_seq n source sink n ==
         (if new_vbn < bottleneck_via_pred spred cap_seq flow_seq n source u n
          then new_vbn
          else bottleneck_via_pred spred cap_seq flow_seq n source u n))))
  = let u = seq_get spred current in
    // From pred_ok: u is valid predecessor
    assert (u >= 0 /\ u < n /\ seq_get scolor u <> 0);
    // Residual condition: res_fwd > 0 \/ flow_bwd > 0
    let res_fwd = seq_get cap_seq (u * n + current) - seq_get flow_seq (u * n + current) in
    let flow_bwd = seq_get flow_seq (current * n + u) in
    assert (res_fwd > 0 \/ flow_bwd > 0);
    // Fuel mono: BVP(u, n-1) = BVP(u, n)
    lemma_bottleneck_fuel_mono scolor spred sdist cap_seq flow_seq n source u (n - 1) n;
    // Now BVP(current, n) = min(edge_res, BVP(u, n)) by definition unfolding
    // (since current ≠ source, fuel = n > 0, u = seq_get spred current, u >= 0 && u < n)
    // edge_res = if res_fwd > 0 then res_fwd else flow_bwd
    let bvp_u = bottleneck_via_pred spred cap_seq flow_seq n source u n in
    let bvp_cur = bottleneck_via_pred spred cap_seq flow_seq n source current n in
    let edge_res = if res_fwd > 0 then res_fwd else flow_bwd in
    assert (bvp_cur == (if edge_res < bvp_u then edge_res else bvp_u));
    // Old invariant: BVP(sink) = min(vbn, bvp_cur) = min(vbn, min(edge_res, bvp_u))
    // Code computes new_vbn = min(vbn, edge_res) [using pred_ok: res_fwd > 0 \/ flow_bwd > 0]
    let new_vbn =
      if res_fwd > 0 then (if res_fwd < vbn then res_fwd else vbn)
      else (if flow_bwd > 0 && flow_bwd < vbn then flow_bwd else vbn) in
    // Case analysis to show new_vbn = min(vbn, edge_res)
    assert (new_vbn == (if edge_res < vbn then edge_res else vbn));
    // min associativity: min(vbn, min(edge_res, bvp_u)) = min(min(vbn, edge_res), bvp_u)
    // = min(new_vbn, bvp_u)
    assert (
      (if vbn < (if edge_res < bvp_u then edge_res else bvp_u)
       then vbn
       else (if edge_res < bvp_u then edge_res else bvp_u)) ==
      (if (if edge_res < vbn then edge_res else vbn) < bvp_u
       then (if edge_res < vbn then edge_res else vbn)
       else bvp_u))
#pop-options

(** Pure augment via pred walk: walks pred from current to source,
    augmenting each edge. Matches augment_imp. *)
let rec augment_via_pred (spred: Seq.seq int) (flow_seq cap_seq: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\ Seq.length spred == n /\ n > 0})
  (source: nat{source < n}) (current: nat{current < n}) (bn: int) (fuel: nat)
  : Tot (s: Seq.seq int{Seq.length s == n * n}) (decreases fuel)
  = if fuel = 0 || current = source then flow_seq
    else
      let u = seq_get spred current in
      if u >= 0 && u < n then
        let flow' = augment_edge flow_seq cap_seq n u current bn in
        augment_via_pred spred flow' cap_seq n source u bn (fuel - 1)
      else flow_seq

(** Fuel monotonicity for augment_via_pred *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec lemma_augment_fuel_mono (scolor spred sdist cap_seq flow_seq flow_comp: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\ 
          Seq.length flow_comp == n * n /\ Seq.length spred == n /\ n > 0})
  (source: nat{source < n}) (current: nat{current < n}) (bn: int) (fuel1 fuel2: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      Seq.length scolor == n /\ Seq.length sdist == n /\
      seq_get scolor current <> 0 /\ seq_get sdist current >= 0 /\
      fuel1 > seq_get sdist current /\ fuel2 > seq_get sdist current)
    (ensures
      augment_via_pred spred flow_comp cap_seq n source current bn fuel1 ==
      augment_via_pred spred flow_comp cap_seq n source current bn fuel2)
    (decreases fuel1)
  = if current = source then ()
    else begin
      let u = seq_get spred current in
      assert (u >= 0 /\ u < n);
      assert (seq_get scolor u <> 0);
      assert (seq_get sdist current == seq_get sdist u + 1);
      let flow' = augment_edge flow_comp cap_seq n u current bn in
      lemma_augment_fuel_mono scolor spred sdist cap_seq flow_seq flow' n source u bn (fuel1 - 1) (fuel2 - 1)
    end
#pop-options

(** One step of augment loop: AVP(fs, vc, n) == AVP(augment_edge(fs, ..., u, vc, bn), u, n)
    when u = pred[vc] and pred_ok holds. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let lemma_augment_step
  (scolor spred sdist cap_seq flow_pred fs: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_pred == n * n /\
          Seq.length fs == n * n /\ Seq.length spred == n /\ n > 0
          /\ Seq.length scolor == n /\ Seq.length sdist == n})
  (source: nat{source < n}) (current: nat{current < n /\ current <> source}) (bn: int)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_pred n source /\
      seq_get scolor current <> 0)
    (ensures (
      let u = seq_get spred current in
      u >= 0 /\ u < n /\
      seq_get scolor u <> 0 /\
      (let fs' = augment_edge fs cap_seq n u current bn in
       Seq.length fs' == n * n /\
       augment_via_pred spred fs cap_seq n source current bn n ==
       augment_via_pred spred fs' cap_seq n source u bn n)))
  = let u = seq_get spred current in
    assert (u >= 0 /\ u < n /\ seq_get scolor u <> 0);
    let fs' = augment_edge fs cap_seq n u current bn in
    // By unfolding (fuel = n > 0, current ≠ source, u valid):
    // AVP(fs, vc, n) = AVP(augment_edge(fs, ..., u, vc, bn), u, n-1)
    // By fuel mono: AVP(fs', u, n-1) = AVP(fs', u, n)
    lemma_augment_fuel_mono scolor spred sdist cap_seq flow_pred fs' n source u bn (n - 1) n
#pop-options

(** augment_edge when forward residual > 0: just Seq.upd at u*n+v *)
let lemma_augment_edge_fwd (flow cap: Seq.seq int)
  (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
  (u: nat{u < n}) (v: nat{v < n}) (delta: int)
  : Lemma
    (requires residual_capacity cap flow n u v > 0)
    (ensures augment_edge flow cap n u v delta ==
             Seq.upd flow (u * n + v) (Seq.index flow (u * n + v) + delta))
  = ()

(** augment_edge when forward residual <= 0: Seq.upd at v*n+u *)
let lemma_augment_edge_bwd (flow cap: Seq.seq int)
  (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
  (u: nat{u < n}) (v: nat{v < n}) (delta: int)
  : Lemma
    (requires residual_capacity cap flow n u v <= 0)
    (ensures augment_edge flow cap n u v delta ==
             Seq.upd flow (v * n + u) (Seq.index flow (v * n + u) - delta))
  = ()

(** init of (l ++ [x]) == l when l is non-empty *)
let rec lemma_init_append_singleton (l: list nat{Cons? l}) (x: nat)
  : Lemma (ensures L.init (L.append l [x]) == l)
    (decreases l)
  = match l with
    | [_] -> ()
    | _ :: b :: rest -> lemma_init_append_singleton (b :: rest) x

(** Augment via pred equals augment_aux on the path from preds.
    flow_pred is the original BFS flow (for pred_ok), flow_comp is the computation flow. *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let rec lemma_augment_via_pred_eq (scolor spred sdist cap_seq flow_pred: Seq.seq int)
  (flow_comp: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_pred == n * n /\
          Seq.length flow_comp == n * n /\ Seq.length spred == n /\ n > 0})
  (source: nat{source < n}) (current: nat{current < n}) (bn: int) (fuel: nat)
  : Lemma
    (requires
      pred_ok scolor spred sdist cap_seq flow_pred n source /\
      Seq.length scolor == n /\ Seq.length sdist == n /\
      seq_get scolor current <> 0 /\ seq_get sdist current >= 0 /\
      fuel > seq_get sdist current)
    (ensures (
      let path = path_from_preds_aux spred n source current fuel in
      Cons? path /\
      (forall (v: nat). L.mem v path ==> v < n) /\
      distinct_vertices path /\
      augment_via_pred spred flow_comp cap_seq n source current bn fuel ==
      augment_aux flow_comp cap_seq n path bn))
    (decreases fuel)
  = lemma_path_starts_source scolor spred sdist cap_seq flow_pred n source current fuel;
    lemma_path_vertices_bounded scolor spred sdist cap_seq flow_pred n source current fuel;
    lemma_path_distinct scolor spred sdist cap_seq flow_pred n source current fuel;
    if current = source then ()
    else begin
      let u = seq_get spred current in
      assert (u >= 0 /\ u < n);
      assert (seq_get scolor u <> 0);
      assert (seq_get sdist current == seq_get sdist u + 1);
      let prefix = path_from_preds_aux spred n source u (fuel - 1) in
      let path = path_from_preds_aux spred n source current fuel in
      let flow' = augment_edge flow_comp cap_seq n u current bn in
      // IH: augment_via_pred with flow' for u
      lemma_augment_via_pred_eq scolor spred sdist cap_seq flow_pred flow' n source u bn (fuel - 1);
      // IH gives: augment_via_pred spred flow' cap n source u bn (fuel-1) == augment_aux flow' cap n prefix bn
      // So: augment_via_pred spred flow_comp cap n source current bn fuel == augment_aux flow' cap n prefix bn
      
      // Now show: augment_aux flow_comp cap n path bn == augment_aux flow' cap n prefix bn
      // Using lemma_augment_aux_last_first
      lemma_path_ends_current spred n source current fuel;
      lemma_path_ends_current spred n source u (fuel - 1);
      assert (L.last prefix == u);
      
      let path_len = L.length path in
      lemma_path_length_ge_2 scolor spred sdist cap_seq flow_pred n source current fuel;
      assert (path_len >= 2);
      
      if path_len = 2 then begin
        // path = prefix ++ [current], length = 2, so length prefix = 1
        L.append_length prefix [current];
        assert (L.length prefix == 1);
        // prefix = [source] (starts at source and has length 1)
        assert (L.hd prefix == source);
        assert (L.last prefix == source);
        assert (u = source);
        ()
      end
      else begin
        // path_len >= 3, so init has >= 2 elements
        // Use lemma_augment_aux_last_first
        Lemmas.lemma_augment_aux_last_first flow_comp cap_seq n path bn;
        // Gives: augment_aux flow_comp cap n path bn ==
        //   augment_aux (ae flow_comp cap n (L.last (L.init path)) (L.last path) bn) cap n (L.init path) bn
        // L.last path = current, L.init path = prefix
        lemma_init_append_singleton prefix current;
        assert (L.init path == prefix);
        // L.last (L.init path) = L.last prefix = u
        assert (L.last (L.init path) == u);
        // ae flow_comp cap n u current bn = flow'
        // So: augment_aux flow_comp cap n path bn == augment_aux flow' cap n prefix bn ✓
        ()
      end
    end
#pop-options

(** Master augmentation lemma: chains all the pieces together.
    Given imp_valid_flow + BFS pred_ok + bottleneck + augment results,
    proves that the augmented flow is still imp_valid and flow value increased. *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 1"
let lemma_augment_chain
  (scolor spred sdist cap_seq flow_seq: Seq.seq int)
  (n: nat{Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\ Seq.length spred == n /\ n > 0
           /\ Seq.length scolor == n /\ Seq.length sdist == n})
  (source: nat{source < n}) (sink: nat{sink < n /\ source <> sink}) (bn: int)
  : Lemma
    (requires
      imp_valid_flow flow_seq cap_seq n source sink /\
      valid_caps cap_seq n /\
      pred_ok scolor spred sdist cap_seq flow_seq n source /\
      seq_get scolor sink <> 0 /\
      bn > 0 /\
      bn == bottleneck_via_pred spred cap_seq flow_seq n source sink n)
    (ensures (
      let flow' = augment_via_pred spred flow_seq cap_seq n source sink bn n in
      Seq.length flow' == n * n /\
      imp_valid_flow flow' cap_seq n source sink /\
      imp_flow_value flow' n source > imp_flow_value flow_seq n source))
  = // 1. Bridge: imp_valid_flow → valid_flow
    imp_valid_flow_implies_valid_flow flow_seq cap_seq n source sink;
    // 2. Get the path and its properties
    lemma_augment_via_pred_eq scolor spred sdist cap_seq flow_seq flow_seq n source sink bn n;
    let path = path_from_preds_aux spred n source sink n in
    assert (Cons? path /\ distinct_vertices path);
    assert (forall (v: nat). L.mem v path ==> v < n);
    // 3. Path starts at source, ends at sink
    lemma_path_starts_source scolor spred sdist cap_seq flow_seq n source sink n;
    lemma_path_ends_current spred n source sink n;
    assert (L.hd path == source /\ L.last path == sink);
    // 4. Bottleneck: bn == bottleneck_aux on path
    lemma_bottleneck_via_pred_eq scolor spred sdist cap_seq flow_seq n source sink n;
    assert (bn == bottleneck_aux cap_seq flow_seq n path);
    // 5. augment_preserves_valid: valid_flow (augment_aux ...) 
    Lemmas.augment_preserves_valid #n cap_seq flow_seq source sink path bn;
    // 6. augment_via_pred == augment_aux
    let flow' = augment_via_pred spred flow_seq cap_seq n source sink bn n in
    assert (flow' == augment_aux flow_seq cap_seq n path bn);
    assert (valid_flow #n flow' cap_seq source sink);
    // 7. Reverse bridge: valid_flow → imp_valid_flow
    valid_flow_implies_imp_valid_flow flow' cap_seq n source sink;
    // 8. Flow value increases
    assert (Seq.length flow' == n * n);
    Lemmas.augment_increases_value #n cap_seq flow_seq source sink path bn;
    lemma_imp_flow_value_eq flow_seq n source;
    lemma_imp_flow_value_eq flow' n source
#pop-options

(** Zero flow satisfies imp_valid_flow when capacities are valid.
    Used to establish the loop invariant after zero_init_flow. *)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let lemma_zero_flow_imp_valid (flow_seq cap_seq: Seq.seq int) (n source sink: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ sink < n /\
      Seq.length flow_seq == n * n /\
      Seq.length cap_seq == n * n /\
      valid_caps cap_seq n /\
      (forall (i: nat). i < n * n ==> Seq.index flow_seq i == 0))
    (ensures imp_valid_flow flow_seq cap_seq n source sink)
  = lemma_zero_array_eq_create flow_seq (n * n);
    // Capacity constraint: 0 <= 0 <= cap[u*n+v]
    let aux_cap (u: nat{u < n}) (v: nat{v < n}) : Lemma
      (0 <= seq_get flow_seq (u * n + v) /\
       seq_get flow_seq (u * n + v) <= seq_get cap_seq (u * n + v))
      = FStar.Math.Lemmas.lemma_mult_le_right n u (n - 1);
        assert (u * n + v < n * n);
        assert (seq_get flow_seq (u * n + v) == 0)
    in
    Classical.forall_intro_2 (Classical.move_requires_2 aux_cap);
    // Conservation: sum_flow_into = 0 = sum_flow_out for all intermediate vertices
    let aux_cons (w: nat{w < n /\ w <> source /\ w <> sink}) : Lemma
      (sum_flow_into flow_seq n w n == sum_flow_out flow_seq n w n)
      = lemma_sum_flow_into_zero n w n;
        lemma_sum_flow_out_zero n w n
    in
    Classical.forall_intro (Classical.move_requires aux_cons)
#pop-options

(** Zero flow has imp_flow_value 0. *)
let lemma_zero_flow_value (flow_seq: Seq.seq int) (n: nat{n > 0}) (source: nat{source < n})
  : Lemma
    (requires
      Seq.length flow_seq == n * n /\
      (forall (i: nat). i < n * n ==> Seq.index flow_seq i == 0))
    (ensures imp_flow_value flow_seq n source == 0)
  = lemma_zero_array_eq_create flow_seq (n * n);
    lemma_sum_flow_out_zero n source n;
    lemma_sum_flow_into_zero n source n

(** sum_flow_out is monotone: if flow[v][u] <= cap[v][u] for all u, then
    sum_flow_out(flow, v, k) <= sum_flow_out(cap, v, k). *)
let rec lemma_sum_flow_out_mono
  (flow cap: Seq.seq int) (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
  (v: nat{v < n}) (k: nat)
  : Lemma
    (requires forall (u: nat). u < n ==> get flow n v u <= get cap n v u)
    (ensures sum_flow_out flow n v k <= sum_flow_out cap n v k)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then lemma_sum_flow_out_mono flow cap n v (k - 1)
    else lemma_sum_flow_out_mono flow cap n v (k - 1)

(** sum_flow_into is non-negative when all flows are non-negative. *)
let rec lemma_sum_flow_into_nonneg
  (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
  (v: nat{v < n}) (k: nat)
  : Lemma
    (requires forall (u: nat). u < n ==> get flow n u v >= 0)
    (ensures sum_flow_into flow n v k >= 0)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then lemma_sum_flow_into_nonneg flow n v (k - 1)
    else lemma_sum_flow_into_nonneg flow n v (k - 1)

(** sum_flow_out is non-negative when all flows are non-negative. *)
let rec lemma_sum_flow_out_nonneg
  (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
  (v: nat{v < n}) (k: nat)
  : Lemma
    (requires forall (u: nat). u < n ==> get flow n v u >= 0)
    (ensures sum_flow_out flow n v k >= 0)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then lemma_sum_flow_out_nonneg flow n v (k - 1)
    else lemma_sum_flow_out_nonneg flow n v (k - 1)

(** For a valid flow, imp_flow_value <= imp_sum_flow_out(cap, source, n). *)
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let lemma_flow_value_le_cap_sum
  (flow_seq cap_seq: Seq.seq int) (n source sink: nat)
  : Lemma
    (requires imp_valid_flow flow_seq cap_seq n source sink)
    (ensures imp_flow_value flow_seq n source <= imp_sum_flow_out cap_seq n source n)
  = // From imp_valid_flow: 0 <= flow[u][v] <= cap[u][v]
    // So sum_flow_out(flow, source) <= sum_flow_out(cap, source)
    let aux_le (u: nat{u < n}) : Lemma (get flow_seq n source u <= get cap_seq n source u)
      = FStar.Math.Lemmas.lemma_mult_le_right n source (n - 1);
        assert (source * n + u < n * n);
        assert (seq_get flow_seq (source * n + u) <= seq_get cap_seq (source * n + u))
    in
    Classical.forall_intro (Classical.move_requires aux_le);
    lemma_sum_flow_out_mono flow_seq cap_seq n source n;
    // sum_flow_into(flow, source) >= 0
    let aux_nonneg (u: nat{u < n}) : Lemma (get flow_seq n u source >= 0)
      = FStar.Math.Lemmas.lemma_mult_le_right n u (n - 1);
        assert (u * n + source < n * n);
        assert (seq_get flow_seq (u * n + source) >= 0)
    in
    Classical.forall_intro (Classical.move_requires aux_nonneg);
    lemma_sum_flow_into_nonneg flow_seq n source n
    // flow_value = sum_out - sum_in <= sum_out(cap) - 0 = sum_out(cap)
    // imp_flow_value = flow_value, imp_sum_flow_out = sum_flow_out (under constraints)
#pop-options

(** imp_sum_flow_out(cap, source, n) >= 0 when capacities are non-negative. *)
let lemma_cap_sum_nonneg
  (cap_seq: Seq.seq int) (n: nat{n > 0}) (source: nat{source < n})
  : Lemma
    (requires Seq.length cap_seq == n * n /\ valid_caps cap_seq n)
    (ensures imp_sum_flow_out cap_seq n source n >= 0)
  = let aux (u: nat{u < n}) : Lemma (get cap_seq n source u >= 0)
      = FStar.Math.Lemmas.lemma_mult_le_right n source (n - 1);
        assert (source * n + u < n * n);
        assert (Seq.index cap_seq (source * n + u) >= 0)
    in
    Classical.forall_intro (Classical.move_requires aux);
    lemma_sum_flow_out_nonneg cap_seq n source n

(** Bottleneck ≤ 0 when BFS colored/uncolored crossing exists.
    Key lemma: any path from a colored source to an uncolored sink must
    cross from colored to uncolored; at that edge, both forward and backward
    residual capacity are ≤ 0 (by bfs_complete), giving bottleneck ≤ 0. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec lemma_bottleneck_crossing
  (scolor cap flow: Seq.seq int)
  (n: nat)
  (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
  : Lemma
    (requires
      n > 0 /\
      Seq.length scolor >= n /\
      Seq.length cap == n * n /\ Seq.length flow == n * n /\
      bfs_complete scolor cap flow n /\
      seq_get scolor (L.hd path) <> 0 /\
      seq_get scolor (L.last path) == 0)
    (ensures bottleneck cap flow n path <= 0)
    (decreases path)
  = match path with
    | [_] -> () // impossible: hd == last, colored and uncolored. False.
    | u :: v :: rest ->
      assert (u < n /\ v < n);
      if seq_get scolor v = 0 then begin
        // Crossing edge: u colored, v uncolored
        // bfs_complete: colored u => residual neighbors colored. v uncolored => not a residual nbr.
        assert (seq_get cap (u * n + v) - seq_get flow (u * n + v) <= 0);
        assert (seq_get flow (v * n + u) <= 0);
        // These equal residual_capacity and residual_capacity_backward
        // edge_capacity: if rc > 0 then rc else rcb, both ≤ 0 ⟹ edge_capacity ≤ 0
        // bottleneck = min(edge_capacity, rest_cap) ≤ edge_capacity ≤ 0
        ()
      end else begin
        // v is colored. Recurse on (v :: rest).
        // L.last (v :: rest) == L.last path == uncolored.
        // If rest = []: L.last [v] = v, but v is colored. Contradiction. False.
        if Nil? rest then ()
        else begin
          lemma_bottleneck_crossing scolor cap flow n (v :: rest);
          // bottleneck (v :: rest) ≤ 0
          // bottleneck path = min(edge(u,v), bottleneck(v::rest))
          // In both cases of min, result ≤ 0
          ()
        end
      end
    | [] -> () // impossible: Cons? path
#pop-options

(** BFS completeness lemma — replaces axiom_bfs_complete.
    When BFS terminates with all residual neighbors of discovered vertices
    also discovered, and sink is undiscovered, no augmenting path exists. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let lemma_bfs_complete
  (cap_seq flow_seq scolor: Seq.seq int)
  (n source sink: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ sink < n /\ source <> sink /\
      Seq.length cap_seq == n * n /\
      Seq.length flow_seq == n * n /\
      seq_get scolor source <> 0 /\
      seq_get scolor sink == 0 /\
      bfs_complete scolor cap_seq flow_seq n)
    (ensures no_augmenting_path #n cap_seq flow_seq source sink)
  = let aux (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
      : Lemma
        (requires L.hd path = source /\ L.last path = sink)
        (ensures bottleneck cap_seq flow_seq n path <= 0)
      = lemma_bottleneck_crossing scolor cap_seq flow_seq n path
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

(* ================================================================
   BFS ON RESIDUAL GRAPH
   ================================================================ *)

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
fn bfs_init
  (color pred dist: A.array int)
  (n source: SZ.t)
  (#scolor: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  requires
    A.pts_to color scolor **
    A.pts_to pred spred **
    A.pts_to dist sdist **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sdist == SZ.v n
    )
  ensures exists* scolor' spred' sdist'.
    A.pts_to color scolor' **
    A.pts_to pred spred' **
    A.pts_to dist sdist' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sdist' == SZ.v n /\
      (forall (j: nat). j < SZ.v n /\ j <> SZ.v source ==> seq_get scolor' j == 0) /\
      seq_get scolor' (SZ.v source) == 1 /\
      (forall (j: nat). j < SZ.v n ==> seq_get spred' j == -1) /\
      seq_get sdist' (SZ.v source) == 0 /\
      (forall (j: nat). j < SZ.v n /\ j <> SZ.v source ==> seq_get sdist' j == -1)
    )
{
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi sc sp sd.
    R.pts_to i vi **
    A.pts_to color sc **
    A.pts_to pred sp **
    A.pts_to dist sd **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sc == SZ.v n /\
      Seq.length sp == SZ.v n /\
      Seq.length sd == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> seq_get sc j == 0) /\
      (forall (j: nat). j < SZ.v vi ==> seq_get sp j == -1) /\
      (forall (j: nat). j < SZ.v vi ==> seq_get sd j == -1)
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    A.op_Array_Assignment color vi 0;
    A.op_Array_Assignment pred vi (-1);
    A.op_Array_Assignment dist vi (-1);
    i := vi +^ 1sz
  };
  A.op_Array_Assignment color source 1;
  A.op_Array_Assignment dist source 0;
  ()
}
#pop-options

(** BFS invariant properties — opaque to SMT to prevent Pulse elaboration blowup *)
[@"opaque_to_smt"]
let bfs_inv_props (scolor: Seq.seq int) (spred: Seq.seq int)
  (squeue: Seq.seq SZ.t) (cap_seq flow_seq: Seq.seq int)
  (n source vtail: nat) : prop =
  queue_valid squeue 0 vtail n /\
  preds_in_range spred n /\
  seq_get scolor source <> 0 /\
  processed_complete scolor cap_seq flow_seq n /\
  colors_valid scolor n /\
  count_nonzero scolor n == vtail /\
  queue_ok scolor squeue vtail n

let mk_bfs_inv_props (scolor: Seq.seq int) (spred: Seq.seq int)
  (squeue: Seq.seq SZ.t) (cap_seq flow_seq: Seq.seq int)
  (n source vtail: nat)
  : Lemma
    (requires
      queue_valid squeue 0 vtail n /\
      preds_in_range spred n /\
      seq_get scolor source <> 0 /\
      processed_complete scolor cap_seq flow_seq n /\
      colors_valid scolor n /\
      count_nonzero scolor n == vtail /\
      queue_ok scolor squeue vtail n)
    (ensures bfs_inv_props scolor spred squeue cap_seq flow_seq n source vtail)
  = reveal_opaque (`%bfs_inv_props) (bfs_inv_props scolor spred squeue cap_seq flow_seq n source vtail)

let elim_bfs_inv_props (scolor: Seq.seq int) (spred: Seq.seq int)
  (squeue: Seq.seq SZ.t) (cap_seq flow_seq: Seq.seq int)
  (n source vtail: nat)
  : Lemma
    (requires bfs_inv_props scolor spred squeue cap_seq flow_seq n source vtail)
    (ensures
      queue_valid squeue 0 vtail n /\
      preds_in_range spred n /\
      seq_get scolor source <> 0 /\
      processed_complete scolor cap_seq flow_seq n /\
      colors_valid scolor n /\
      count_nonzero scolor n == vtail /\
      queue_ok scolor squeue vtail n)
  = reveal_opaque (`%bfs_inv_props) (bfs_inv_props scolor spred squeue cap_seq flow_seq n source vtail)

(** Discover-specific postcondition delta — opaque to SMT *)
[@"opaque_to_smt"]
let discover_delta
  (scolor scolor': Seq.seq int) (spred': Seq.seq int)
  (squeue squeue': Seq.seq SZ.t) (cap_seq flow_seq: Seq.seq int)
  (n u vv source: nat) (vtail vtail': nat) : prop =
  bfs_inv_props scolor' spred' squeue' cap_seq flow_seq n source vtail' /\
  vtail' >= vtail /\
  nbr_colored_if_residual scolor' cap_seq flow_seq n u vv /\
  count_color1 scolor' n + vtail == count_color1 scolor n + vtail' /\
  (forall (j: nat). j < n /\ seq_get scolor j <> 0 ==> seq_get scolor' j <> 0) /\
  (forall (j: nat). j < n /\ seq_get scolor j == 1 ==> seq_get scolor' j == 1) /\
  queue_prefix_preserved squeue squeue' vtail /\
  queue_color1 scolor' squeue' vtail vtail' n

let mk_discover_delta
  (scolor scolor': Seq.seq int) (spred': Seq.seq int)
  (squeue squeue': Seq.seq SZ.t) (cap_seq flow_seq: Seq.seq int)
  (n u vv source: nat) (vtail vtail': nat)
  : Lemma
    (requires
      bfs_inv_props scolor' spred' squeue' cap_seq flow_seq n source vtail' /\
      vtail' >= vtail /\
      nbr_colored_if_residual scolor' cap_seq flow_seq n u vv /\
      count_color1 scolor' n + vtail == count_color1 scolor n + vtail' /\
      (forall (j: nat). j < n /\ seq_get scolor j <> 0 ==> seq_get scolor' j <> 0) /\
      (forall (j: nat). j < n /\ seq_get scolor j == 1 ==> seq_get scolor' j == 1) /\
      queue_prefix_preserved squeue squeue' vtail /\
      queue_color1 scolor' squeue' vtail vtail' n)
    (ensures discover_delta scolor scolor' spred' squeue squeue' cap_seq flow_seq n u vv source vtail vtail')
  = reveal_opaque (`%discover_delta) (discover_delta scolor scolor' spred' squeue squeue' cap_seq flow_seq n u vv source vtail vtail')

let elim_discover_delta
  (scolor scolor': Seq.seq int) (spred': Seq.seq int)
  (squeue squeue': Seq.seq SZ.t) (cap_seq flow_seq: Seq.seq int)
  (n u vv source: nat) (vtail vtail': nat)
  : Lemma
    (requires discover_delta scolor scolor' spred' squeue squeue' cap_seq flow_seq n u vv source vtail vtail')
    (ensures
      bfs_inv_props scolor' spred' squeue' cap_seq flow_seq n source vtail' /\
      vtail' >= vtail /\
      nbr_colored_if_residual scolor' cap_seq flow_seq n u vv /\
      count_color1 scolor' n + vtail == count_color1 scolor n + vtail' /\
      (forall (j: nat). j < n /\ seq_get scolor j <> 0 ==> seq_get scolor' j <> 0) /\
      (forall (j: nat). j < n /\ seq_get scolor j == 1 ==> seq_get scolor' j == 1) /\
      queue_prefix_preserved squeue squeue' vtail /\
      queue_color1 scolor' squeue' vtail vtail' n)
  = reveal_opaque (`%discover_delta) (discover_delta scolor scolor' spred' squeue squeue' cap_seq flow_seq n u vv source vtail vtail')

(** Proof helper for maybe_discover then-branch: packs discover_delta without Seq.upd in call *)
#restart-solver
#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
let maybe_discover_then_proof
  (scolor spred: Seq.seq int) (squeue: Seq.seq SZ.t)
  (cap_seq flow_seq: Seq.seq int)
  (n u source vtail: nat) (vv: SZ.t)
  : Lemma
    (requires
      n > 0 /\ u < n /\ SZ.v vv < n /\ source < n /\ vtail < n /\
      Seq.length scolor == n /\ Seq.length spred == n /\ Seq.length squeue == n /\
      Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\
      bfs_inv_props scolor spred squeue cap_seq flow_seq n source vtail /\
      seq_get scolor (SZ.v vv) == 0 /\
      (seq_get cap_seq (u * n + SZ.v vv) - seq_get flow_seq (u * n + SZ.v vv) > 0 \/
       seq_get flow_seq (SZ.v vv * n + u) > 0))
    (ensures
      discover_delta scolor (Seq.upd scolor (SZ.v vv) 1) (Seq.upd spred (SZ.v vv) u)
        squeue (Seq.upd squeue vtail vv)
        cap_seq flow_seq n u (SZ.v vv) source vtail (vtail + 1) /\
      Seq.length (Seq.upd scolor (SZ.v vv) 1) == n /\
      Seq.length (Seq.upd spred (SZ.v vv) u) == n /\
      Seq.length (Seq.upd squeue vtail vv) == n)
  = elim_bfs_inv_props scolor spred squeue cap_seq flow_seq n source vtail;
    lemma_count_nonzero_lt_has_zero scolor n (SZ.v vv);
    lemma_queue_ok_after_discover scolor squeue vtail n vv;
    lemma_queue_valid_extend squeue vtail n vv;
    lemma_processed_complete_set_1 scolor cap_seq flow_seq n (SZ.v vv);
    lemma_count_nonzero_set_nz scolor n (SZ.v vv) 1;
    lemma_count_color1_set_1 scolor n (SZ.v vv);
    lemma_colors_valid_set_1 scolor n (SZ.v vv);
    lemma_preds_in_range_upd spred n (SZ.v vv) u;
    let sc' = Seq.upd scolor (SZ.v vv) 1 in
    let sp' = Seq.upd spred (SZ.v vv) u in
    let sq' = Seq.upd squeue vtail vv in
    mk_bfs_inv_props sc' sp' sq' cap_seq flow_seq n source (vtail + 1);
    // Help SMT with each conjunct of mk_discover_delta's precondition
    assert (bfs_inv_props sc' sp' sq' cap_seq flow_seq n source (vtail + 1));
    assert (vtail + 1 >= vtail);
    assert (nbr_colored_if_residual sc' cap_seq flow_seq n u (SZ.v vv));
    assert (SZ.v vv < Seq.length scolor);
    assert (Seq.index scolor (SZ.v vv) == 0);
    assert (count_color1 sc' n == count_color1 scolor n + 1);
    let c1 = count_color1 sc' n in
    let c0 = count_color1 scolor n in
    assert (c1 == c0 + 1);
    assert (c1 + vtail == c0 + 1 + vtail);
    assert (c0 + 1 + vtail == c0 + (vtail + 1));
    // Queue prefix: writing at position vtail doesn't affect positions < vtail
    assert (Seq.length sq' == n);
    assert (forall (j: nat). j < vtail ==> j < Seq.length sq' /\ Seq.index sq' j == Seq.index squeue j);
    assert (queue_prefix_preserved squeue sq' vtail);
    // New entry at position vtail has color 1: sq'[vtail]=vv and sc'[vv]=1
    assert (Seq.index sq' vtail == vv);
    assert (Seq.index sc' (SZ.v vv) == 1);
    assert (queue_color1 sc' sq' vtail (vtail + 1) n);
    mk_discover_delta scolor sc' sp' squeue sq'
      cap_seq flow_seq n u (SZ.v vv) source vtail (vtail + 1)
#pop-options

(** Proof helper for maybe_discover else-branch: trivial delta *)
let maybe_discover_else_proof
  (scolor spred: Seq.seq int) (squeue: Seq.seq SZ.t)
  (cap_seq flow_seq: Seq.seq int)
  (n u vv source vtail: nat)
  : Lemma
    (requires
      n > 0 /\ u < n /\ vv < n /\ source < n /\ vtail <= n /\
      Seq.length scolor == n /\ Seq.length cap_seq == n * n /\ Seq.length flow_seq == n * n /\
      bfs_inv_props scolor spred squeue cap_seq flow_seq n source vtail /\
      (seq_get scolor vv <> 0 \/
       (seq_get cap_seq (u * n + vv) - seq_get flow_seq (u * n + vv) <= 0 /\
        seq_get flow_seq (vv * n + u) <= 0)))
    (ensures
      discover_delta scolor scolor spred squeue squeue
        cap_seq flow_seq n u vv source vtail vtail)
  = mk_discover_delta scolor scolor spred squeue squeue
      cap_seq flow_seq n u vv source vtail vtail

(** Try to discover vertex vv from u in the residual graph *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
fn maybe_discover
  (capacity flow color pred dist: A.array int)
  (queue: A.array SZ.t)
  (n u vv source: SZ.t)
  (q_tail: R.ref SZ.t)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  (#vtail: erased SZ.t)
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor **
    A.pts_to pred spred **
    A.pts_to dist sdist **
    A.pts_to queue squeue **
    R.pts_to q_tail vtail **
    pure (
      SZ.v n > 0 /\
      SZ.v u < SZ.v n /\
      SZ.v vv < SZ.v n /\
      SZ.v source < SZ.v n /\
      SZ.v vtail <= SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sdist == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      seq_get scolor (SZ.v u) <> 0 /\
      bfs_inv_props scolor spred squeue cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v vtail) /\
      bfs_pred_ok scolor spred sdist cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v vtail)
    )
  ensures exists* scolor' spred' sdist' squeue' vtail'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor' **
    A.pts_to pred spred' **
    A.pts_to dist sdist' **
    A.pts_to queue squeue' **
    R.pts_to q_tail vtail' **
    pure (
      SZ.v vtail' <= SZ.v n /\
      Seq.length scolor' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sdist' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      discover_delta scolor scolor' spred' squeue squeue'
        cap_seq flow_seq (SZ.v n) (SZ.v u) (SZ.v vv) (SZ.v source)
        (SZ.v vtail) (SZ.v vtail') /\
      bfs_pred_ok scolor' spred' sdist' cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v vtail')
    )
{
  let vt = !q_tail;
  let cv: int = A.op_Array_Access color vv;
  let idx_fwd: SZ.t = u *^ n +^ vv;
  let idx_bwd: SZ.t = vv *^ n +^ u;
  let cap_val: int = A.op_Array_Access capacity idx_fwd;
  let flow_fwd: int = A.op_Array_Access flow idx_fwd;
  let flow_bwd: int = A.op_Array_Access flow idx_bwd;
  let res_fwd: int = cap_val - flow_fwd;
  // Reveal BFS invariant facts (AFTER array reads to avoid Ill-typed elaboration)
  elim_bfs_inv_props scolor spred squeue cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v vtail);
  if (cv = 0 && (res_fwd > 0 || flow_bwd > 0))
  {
    // Establish vtail < n from the zero-colored vertex, vtail > 0 from source discovered
    lemma_count_nonzero_lt_has_zero scolor (SZ.v n) (SZ.v vv);
    lemma_count_nonzero_ge_1 scolor (SZ.v n) (SZ.v source);
    // Use pure proof helper (avoids Seq.upd terms in Pulse elaboration)
    maybe_discover_then_proof scolor spred squeue cap_seq flow_seq
      (SZ.v n) (SZ.v u) (SZ.v source) (SZ.v vtail) vv;
    // Perform stateful updates
    let du: int = A.op_Array_Access dist u;
    // Prove bfs_pred_ok preserved through discovery
    // Assert residual condition explicitly (connects runtime values to seq_get)
    assert (pure (
      seq_get cap_seq (SZ.v u * SZ.v n + SZ.v vv) - seq_get flow_seq (SZ.v u * SZ.v n + SZ.v vv) > 0 \/
      seq_get flow_seq (SZ.v vv * SZ.v n + SZ.v u) > 0));
    lemma_discover_preserves_bfs_pred_ok scolor spred sdist cap_seq flow_seq
      (SZ.v n) (SZ.v source) (SZ.v u) (SZ.v vv) (SZ.v vtail);
    A.op_Array_Assignment color vv 1;
    A.op_Array_Assignment pred vv (SZ.v u);
    A.op_Array_Assignment dist vv (du + 1);
    A.op_Array_Assignment queue vt vv;
    q_tail := vt +^ 1sz;
    ()
  }
  else {
    // No change — use else proof helper
    maybe_discover_else_proof scolor spred squeue cap_seq flow_seq
      (SZ.v n) (SZ.v u) (SZ.v vv) (SZ.v source) (SZ.v vtail);
    ()
  }
}
#pop-options

(** Explore all neighbors of vertex u in the residual graph *)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
fn bfs_explore_neighbors
  (capacity flow color pred dist: A.array int)
  (queue: A.array SZ.t)
  (n u source: SZ.t)
  (q_tail: R.ref SZ.t)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  (#vtail: erased SZ.t)
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor **
    A.pts_to pred spred **
    A.pts_to dist sdist **
    A.pts_to queue squeue **
    R.pts_to q_tail vtail **
    pure (
      SZ.v n > 0 /\
      SZ.v u < SZ.v n /\
      SZ.v source < SZ.v n /\
      SZ.v vtail <= SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sdist == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      queue_valid squeue 0 (SZ.v vtail) (SZ.v n) /\
      preds_in_range spred (SZ.v n) /\
      seq_get scolor (SZ.v source) <> 0 /\
      processed_complete scolor cap_seq flow_seq (SZ.v n) /\
      colors_valid scolor (SZ.v n) /\
      count_nonzero scolor (SZ.v n) == SZ.v vtail /\
      queue_ok scolor squeue (SZ.v vtail) (SZ.v n) /\
      seq_get scolor (SZ.v u) <> 0 /\
      bfs_pred_ok scolor spred sdist cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v vtail)
    )
  ensures exists* scolor' spred' sdist' squeue' vtail'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor' **
    A.pts_to pred spred' **
    A.pts_to dist sdist' **
    A.pts_to queue squeue' **
    R.pts_to q_tail vtail' **
    pure (
      SZ.v vtail' <= SZ.v n /\
      SZ.v vtail' >= SZ.v vtail /\
      Seq.length scolor' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sdist' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      queue_valid squeue' 0 (SZ.v vtail') (SZ.v n) /\
      preds_in_range spred' (SZ.v n) /\
      seq_get scolor' (SZ.v source) <> 0 /\
      processed_complete scolor' cap_seq flow_seq (SZ.v n) /\
      colors_valid scolor' (SZ.v n) /\
      count_nonzero scolor' (SZ.v n) == SZ.v vtail' /\
      queue_ok scolor' squeue' (SZ.v vtail') (SZ.v n) /\
      count_color1 scolor' (SZ.v n) + SZ.v vtail == count_color1 scolor (SZ.v n) + SZ.v vtail' /\
      all_nbrs_colored scolor' cap_seq flow_seq (SZ.v n) (SZ.v u) /\
      (forall (j: nat). j < SZ.v n /\ seq_get scolor j <> 0 ==> seq_get scolor' j <> 0) /\
      (forall (j: nat). j < SZ.v n /\ seq_get scolor j == 1 ==> seq_get scolor' j == 1) /\
      queue_prefix_preserved squeue squeue' (SZ.v vtail) /\
      queue_color1 scolor' squeue' (SZ.v vtail) (SZ.v vtail') (SZ.v n) /\
      bfs_pred_ok scolor' spred' sdist' cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v vtail')
    )
{
  let mut v: SZ.t = 0sz;
  while (!v <^ n)
  invariant exists* vi sc sp sd sq vt.
    R.pts_to v vi **
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color sc **
    A.pts_to pred sp **
    A.pts_to dist sd **
    A.pts_to queue sq **
    R.pts_to q_tail vt **
    pure (
      SZ.v vi <= SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v vt <= SZ.v n /\
      SZ.v vt >= SZ.v vtail /\
      Seq.length sc == SZ.v n /\
      Seq.length sp == SZ.v n /\
      Seq.length sd == SZ.v n /\
      Seq.length sq == SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      queue_valid sq 0 (SZ.v vt) (SZ.v n) /\
      preds_in_range sp (SZ.v n) /\
      seq_get sc (SZ.v source) <> 0 /\
      processed_complete sc cap_seq flow_seq (SZ.v n) /\
      colors_valid sc (SZ.v n) /\
      count_nonzero sc (SZ.v n) == SZ.v vt /\
      queue_ok sc sq (SZ.v vt) (SZ.v n) /\
      count_color1 sc (SZ.v n) + SZ.v vtail == count_color1 scolor (SZ.v n) + SZ.v vt /\
      partial_nbrs_colored sc cap_seq flow_seq (SZ.v n) (SZ.v u) (SZ.v vi) /\
      (forall (j: nat). j < SZ.v n /\ seq_get scolor j <> 0 ==> seq_get sc j <> 0) /\
      (forall (j: nat). j < SZ.v n /\ seq_get scolor j == 1 ==> seq_get sc j == 1) /\
      queue_prefix_preserved squeue sq (SZ.v vtail) /\
      queue_color1 sc sq (SZ.v vtail) (SZ.v vt) (SZ.v n) /\
      bfs_pred_ok sc sp sd cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v vt)
    )
  decreases (SZ.v n - SZ.v !v)
  {
    let vv = !v;
    with sc_before. assert (A.pts_to color sc_before);
    with sp_before. assert (A.pts_to pred sp_before);
    with sd_before. assert (A.pts_to dist sd_before);
    with sq_before. assert (A.pts_to queue sq_before);
    with vt_before. assert (R.pts_to q_tail vt_before);
    // Pack BFS invariant for maybe_discover's precondition
    mk_bfs_inv_props sc_before sp_before sq_before cap_seq flow_seq
      (SZ.v n) (SZ.v source) (SZ.v vt_before);
    maybe_discover capacity flow color pred dist queue n u vv source q_tail;
    with sc_after. assert (A.pts_to color sc_after);
    with sp_after. assert (A.pts_to pred sp_after);
    with sq_after. assert (A.pts_to queue sq_after);
    with vt_after. assert (R.pts_to q_tail vt_after);
    // Unpack discover_delta to get individual facts
    elim_discover_delta sc_before sc_after sp_after sq_before sq_after
      cap_seq flow_seq (SZ.v n) (SZ.v u) (SZ.v vv) (SZ.v source) (SZ.v vt_before) (SZ.v vt_after);
    elim_bfs_inv_props sc_after sp_after sq_after cap_seq flow_seq
      (SZ.v n) (SZ.v source) (SZ.v vt_after);
    lemma_add_chain
      (count_color1 sc_before (SZ.v n)) (count_color1 sc_after (SZ.v n))
      (SZ.v vtail) (count_color1 scolor (SZ.v n))
      (SZ.v vt_before) (SZ.v vt_after);
    lemma_partial_nbrs_step sc_before sc_after cap_seq flow_seq (SZ.v n) (SZ.v u) (SZ.v vv);
    // Queue prefix transitivity: squeue → sq_before → sq_after
    lemma_queue_prefix_trans squeue sq_before sq_after (SZ.v vtail) (SZ.v vt_before);
    // queue_color1 chain: old [vtail, vt_before) + new [vt_before, vt_after) = [vtail, vt_after)
    lemma_queue_color1_chain sc_before sc_after sq_before sq_after
      (SZ.v vtail) (SZ.v vt_before) (SZ.v vt_after) (SZ.v n);
    v := vv +^ 1sz
  };
  with sc_done. assert (A.pts_to color sc_done);
  lemma_partial_nbrs_to_all sc_done cap_seq flow_seq (SZ.v n) (SZ.v u);
  ()
}
#pop-options

(** Main BFS: returns whether sink was reached *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1 --split_queries always"
fn bfs_residual
  (capacity flow color pred dist: A.array int)
  (queue: A.array SZ.t)
  (n source sink: SZ.t)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#scolor0: erased (Seq.seq int))
  (#spred0: erased (Seq.seq int))
  (#sdist0: erased (Seq.seq int))
  (#squeue0: erased (Seq.seq SZ.t))
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor0 **
    A.pts_to pred spred0 **
    A.pts_to dist sdist0 **
    A.pts_to queue squeue0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length scolor0 == SZ.v n /\
      Seq.length spred0 == SZ.v n /\
      Seq.length sdist0 == SZ.v n /\
      Seq.length squeue0 == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns found: bool
  ensures exists* scolor' spred' sdist' squeue'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor' **
    A.pts_to pred spred' **
    A.pts_to dist sdist' **
    A.pts_to queue squeue' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sdist' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      found == (seq_get scolor' (SZ.v sink) <> 0) /\
      preds_in_range spred' (SZ.v n) /\
      // Source is always discovered by BFS
      seq_get scolor' (SZ.v source) <> 0 /\
      // BFS completeness: all residual neighbors of discovered vertices are discovered
      bfs_complete scolor' cap_seq flow_seq (SZ.v n) /\
      // Predecessor tree correctness with dist witness
      pred_ok scolor' spred' sdist' cap_seq flow_seq (SZ.v n) (SZ.v source)
    )
{
  bfs_init color pred dist n source;
  A.op_Array_Assignment queue 0sz source;
  // Establish invariant preconditions for the BFS loop
  with scolor_init. assert (A.pts_to color scolor_init);
  with squeue_init. assert (A.pts_to queue squeue_init);
  with spred_init. assert (A.pts_to pred spred_init);
  with sdist_init. assert (A.pts_to dist sdist_init);
  lemma_count_nonzero_single scolor_init (SZ.v n) (SZ.v source);
  lemma_count_color1_single scolor_init (SZ.v n) (SZ.v source);
  // Establish bfs_pred_ok for initial state (vtail = 1)
  mk_bfs_pred_ok scolor_init spred_init sdist_init cap_seq flow_seq
    (SZ.v n) (SZ.v source) 1;
  let mut q_head: SZ.t = 0sz;
  let mut q_tail: SZ.t = 1sz;

  while (
    let vh = !q_head;
    let vt = !q_tail;
    vh <^ vt
  )
  invariant exists* vhead vtail scolor_q spred_q sdist_q squeue_q.
    R.pts_to q_head vhead **
    R.pts_to q_tail vtail **
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor_q **
    A.pts_to pred spred_q **
    A.pts_to dist sdist_q **
    A.pts_to queue squeue_q **
    pure (
      SZ.v vhead <= SZ.v vtail /\
      SZ.v vtail <= SZ.v n /\
      Seq.length scolor_q == SZ.v n /\
      Seq.length spred_q == SZ.v n /\
      Seq.length sdist_q == SZ.v n /\
      Seq.length squeue_q == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      queue_valid squeue_q 0 (SZ.v vtail) (SZ.v n) /\
      preds_in_range spred_q (SZ.v n) /\
      seq_get scolor_q (SZ.v source) <> 0 /\
      processed_complete scolor_q cap_seq flow_seq (SZ.v n) /\
      colors_valid scolor_q (SZ.v n) /\
      count_nonzero scolor_q (SZ.v n) == SZ.v vtail /\
      queue_ok scolor_q squeue_q (SZ.v vtail) (SZ.v n) /\
      count_color1 scolor_q (SZ.v n) == SZ.v vtail - SZ.v vhead /\
      queue_color1 scolor_q squeue_q (SZ.v vhead) (SZ.v vtail) (SZ.v n) /\
      bfs_pred_ok scolor_q spred_q sdist_q cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v vtail)
    )
  decreases (SZ.v n - SZ.v !q_head)
  {
    let vh = !q_head;
    with sc_cur. assert (A.pts_to color sc_cur);
    with sq_cur. assert (A.pts_to queue sq_cur);
    with vt_cur. assert (R.pts_to q_tail vt_cur);
    let u: SZ.t = A.op_Array_Access queue vh;
    ();
    q_head := vh +^ 1sz;
    bfs_explore_neighbors capacity flow color pred dist queue n u source q_tail;
    with sc_post. assert (A.pts_to color sc_post);
    with sq_post. assert (A.pts_to queue sq_post);
    with vtail_post. assert (R.pts_to q_tail vtail_post);
    // u has color 1 (from queue_color1 + color-1 preservation)
    // So count_color1 decreases by 1 after color[u]=2, and processed_complete extends
    lemma_count_nonzero_preserve sc_post (SZ.v n) (SZ.v u) 2;
    lemma_processed_complete_extend sc_post cap_seq flow_seq (SZ.v n) (SZ.v u);
    lemma_queue_nonzero_upd_color sc_post sq_post 0 (SZ.v vtail_post) (SZ.v n) (SZ.v u) 2;
    // queue_color1 for full range [vhead, vtail_post)
    lemma_queue_color1_preserved sc_cur sc_post sq_cur sq_post
      (SZ.v vh) (SZ.v vt_cur) (SZ.v vtail_post) (SZ.v n);
    // After color[u]=2: shift queue_color1 to [vhead+1, vtail_post)
    lemma_queue_color1_after_set2 sc_post sq_post (SZ.v vh) (SZ.v vtail_post) (SZ.v n) (SZ.v u);
    // count_color1 decreases by 1
    lemma_count_color1_set_2 sc_post (SZ.v n) (SZ.v u);
    // Preserve bfs_pred_ok through color[u] := 2
    with sd_post. assert (A.pts_to dist sd_post);
    with sp_post. assert (A.pts_to pred sp_post);
    lemma_color2_preserves_bfs_pred_ok sc_post sp_post sd_post cap_seq flow_seq
      (SZ.v n) (SZ.v source) (SZ.v u) (SZ.v vtail_post);
    A.op_Array_Assignment color u 2;
    ()
  };
  let sink_color: int = A.op_Array_Access color sink;

  // Extract pred_ok from bfs_pred_ok
  with sd_final. assert (A.pts_to dist sd_final);
  with sp_final. assert (A.pts_to pred sp_final);
  with sc_pre. assert (A.pts_to color sc_pre);
  with vtail_final. assert (R.pts_to q_tail vtail_final);
  elim_bfs_pred_ok sc_pre sp_final sd_final cap_seq flow_seq
    (SZ.v n) (SZ.v source) (SZ.v vtail_final);

  // BFS completeness: at termination, queue is empty → count_color1 == 0 → no color-1 vertices
  // → processed_complete = bfs_complete
  with sc_final. assert (A.pts_to color sc_final);
  lemma_count_zero_no_color1 sc_final (SZ.v n);
  lemma_processed_to_bfs_complete sc_final cap_seq flow_seq (SZ.v n);

  (sink_color <> 0)
}
#pop-options

(* ================================================================
   BOTTLENECK AND AUGMENTATION VIA PRED ARRAY
   ================================================================ *)

(** Find bottleneck: walk pred array from sink to source *)
#restart-solver
#push-options "--z3rlimit 800 --fuel 2 --ifuel 1"
fn find_bottleneck_imp
  (capacity flow pred: A.array int)
  (n source sink: SZ.t)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to pred spred **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sdist == SZ.v n /\
      preds_in_range spred (SZ.v n) /\
      SZ.fits (SZ.v n * SZ.v n) /\
      pred_ok scolor spred sdist cap_seq flow_seq (SZ.v n) (SZ.v source) /\
      seq_get scolor (SZ.v sink) <> 0
    )
  returns bn: int
  ensures
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to pred spred **
    pure (
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length spred == SZ.v n /\
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      bn > 0 /\
      bn == bottleneck_via_pred spred cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v sink) (SZ.v n)
    )
{
  lemma_bottleneck_via_pred_le_int_max spred cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v sink) (SZ.v n);
  let mut current: SZ.t = sink;
  let mut bottleneck: int = int_max;

  while (
    let c = !current;
    not (c = source)
  )
  invariant exists* vc vbn.
    R.pts_to current vc **
    R.pts_to bottleneck vbn **
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to pred spred **
    pure (
      SZ.v vc < SZ.v n /\
      vbn >= 0 /\
      vbn <= int_max /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      preds_in_range spred (SZ.v n) /\
      SZ.fits (SZ.v n * SZ.v n) /\
      // Ghost tracking: current vertex is discovered, bottleneck invariant
      seq_get scolor (SZ.v vc) <> 0 /\
      bottleneck_via_pred spred cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v sink) (SZ.v n) ==
        (if vbn < bottleneck_via_pred spred cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v vc) (SZ.v n)
         then vbn
         else bottleneck_via_pred spred cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v vc) (SZ.v n))
    )
  {
    let vc = !current;
    let u_int: int = A.op_Array_Access pred vc;
    // From pred_ok: vc is discovered and vc ≠ source, so pred[vc] >= 0 and pred[vc] < n
    if (u_int >= 0)
    {
      let u: SZ.t = SZ.uint_to_t u_int;
      assert (pure (SZ.v u < SZ.v n));
      let idx_fwd: SZ.t = u *^ n +^ vc;
      let idx_bwd: SZ.t = vc *^ n +^ u;
      assert (pure (SZ.v idx_fwd < SZ.v n * SZ.v n /\ SZ.v idx_bwd < SZ.v n * SZ.v n));
      let cap_val: int = A.op_Array_Access capacity idx_fwd;
      let flow_fwd: int = A.op_Array_Access flow idx_fwd;
      let flow_bwd: int = A.op_Array_Access flow idx_bwd;
      let res_fwd: int = cap_val - flow_fwd;
      let vbn = !bottleneck;
      // Pure lemma: does all the case analysis + fuel mono
      lemma_bottleneck_step scolor spred sdist cap_seq flow_seq
        (SZ.v n) (SZ.v source) (SZ.v sink) (SZ.v vc) vbn;
      if (res_fwd > 0)
      {
        if (res_fwd < vbn) { bottleneck := res_fwd } else { () }
      }
      else
      {
        if (flow_bwd > 0 && flow_bwd < vbn) { bottleneck := flow_bwd } else { () }
      };
      current := u
    }
    else
    {
      // Unreachable on valid BFS paths — defensive: exit loop
      current := source
    }
  };
  // At loop exit: vc = source
  // BVP(source, n) = int_max by definition (current = source)
  assert (pure (
    bottleneck_via_pred spred cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v source) (SZ.v n) == int_max
  ));
  // From invariant: BVP(sink, n) == min(vbn, int_max)
  // Since vbn <= int_max: min(vbn, int_max) = vbn
  // So BVP(sink, n) = vbn
  // Also prove bn > 0
  lemma_bottleneck_via_pred_positive scolor spred sdist cap_seq flow_seq
    (SZ.v n) (SZ.v source) (SZ.v sink) (SZ.v n);
  !bottleneck
}
#pop-options

(** Augment flow: walk pred array from sink to source, update flow *)
#restart-solver
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn augment_imp
  (capacity flow pred: A.array int)
  (n source sink: SZ.t)
  (bn: int)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to pred spred **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      bn > 0 /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sdist == SZ.v n /\
      preds_in_range spred (SZ.v n) /\
      SZ.fits (SZ.v n * SZ.v n) /\
      pred_ok scolor spred sdist cap_seq flow_seq (SZ.v n) (SZ.v source) /\
      seq_get scolor (SZ.v sink) <> 0
    )
  ensures exists* flow_seq'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq' **
    A.pts_to pred spred **
    pure (
      Seq.length flow_seq' == SZ.v n * SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length spred == SZ.v n /\
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      flow_seq' == augment_via_pred spred flow_seq cap_seq (SZ.v n) (SZ.v source) (SZ.v sink) bn (SZ.v n)
    )
{
  let mut current: SZ.t = sink;

  while (
    let c = !current;
    not (c = source)
  )
  invariant exists* vc fs.
    R.pts_to current vc **
    A.pts_to capacity cap_seq **
    A.pts_to flow fs **
    A.pts_to pred spred **
    pure (
      SZ.v vc < SZ.v n /\
      Seq.length fs == SZ.v n * SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      preds_in_range spred (SZ.v n) /\
      SZ.fits (SZ.v n * SZ.v n) /\
      seq_get scolor (SZ.v vc) <> 0 /\
      augment_via_pred spred flow_seq cap_seq (SZ.v n) (SZ.v source) (SZ.v sink) bn (SZ.v n) ==
      augment_via_pred spred fs cap_seq (SZ.v n) (SZ.v source) (SZ.v vc) bn (SZ.v n)
    )
  {
    let vc = !current;
    let u_int: int = A.op_Array_Access pred vc;
    if (u_int >= 0)
    {
      let u: SZ.t = SZ.uint_to_t u_int;
      assert (pure (SZ.v u < SZ.v n));
      let idx_fwd: SZ.t = u *^ n +^ vc;
      let idx_bwd: SZ.t = vc *^ n +^ u;
      assert (pure (SZ.v idx_fwd < SZ.v n * SZ.v n /\ SZ.v idx_bwd < SZ.v n * SZ.v n));
      let cap_val: int = A.op_Array_Access capacity idx_fwd;
      let flow_fwd: int = A.op_Array_Access flow idx_fwd;
      // Call step lemma to get: AVP(fs, vc, n) == AVP(augment_edge(fs, ..., u, vc, bn), u, n)
      with _fs. assert (A.pts_to flow _fs);
      lemma_augment_step scolor spred sdist cap_seq flow_seq _fs
        (SZ.v n) (SZ.v source) (SZ.v vc) bn;
      if (cap_val - flow_fwd > 0)
      {
        // residual_capacity > 0 → augment_edge = Seq.upd at u*n+v
        lemma_augment_edge_fwd _fs cap_seq (SZ.v n) (SZ.v u) (SZ.v vc) bn;
        A.op_Array_Assignment flow idx_fwd (flow_fwd + bn);
        current := u
      }
      else
      {
        let flow_bwd: int = A.op_Array_Access flow idx_bwd;
        // residual_capacity <= 0 → augment_edge = Seq.upd at v*n+u
        lemma_augment_edge_bwd _fs cap_seq (SZ.v n) (SZ.v u) (SZ.v vc) bn;
        A.op_Array_Assignment flow idx_bwd (flow_bwd - bn);
        current := u
      }
    }
    else
    {
      // Unreachable on valid BFS paths — defensive: exit loop
      current := source
    }
  };
  // At loop exit: vc = source
  // AVP(flow_seq, ..., source, ..., n) = flow_seq (by definition, current = source)
  // Wait no: AVP(spred, fs, ..., source, bn, n) = fs
  // So: AVP(flow_seq, ..., sink, ..., n) = fs = flow_seq'
  ()
}
#pop-options

(* ================================================================
   VALIDITY CHECK — dynamic verification of imp_valid_flow
   ================================================================ *)

(** Check valid_caps: all capacity entries are non-negative *)
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
fn check_valid_caps_fn
  (capacity: A.array int)
  (nn: SZ.t)
  (#cap_seq: erased (Seq.seq int))
  requires
    A.pts_to capacity cap_seq **
    pure (Seq.length cap_seq == SZ.v nn)
  returns ok: bool
  ensures
    A.pts_to capacity cap_seq **
    pure (
      Seq.length cap_seq == SZ.v nn /\
      (ok ==> (forall (i: nat). i < SZ.v nn ==> Seq.index cap_seq i >= 0)))
{
  let mut i = 0sz;
  let mut result = true;
  while (
    let vi = !i;
    let vr = !result;
    vr && vi <^ nn
  )
  invariant exists* vi vr.
    R.pts_to i vi **
    R.pts_to result vr **
    A.pts_to capacity cap_seq **
    pure (
      SZ.v vi <= SZ.v nn /\
      Seq.length cap_seq == SZ.v nn /\
      (vr ==> (forall (idx: nat). idx < SZ.v vi ==> Seq.index cap_seq idx >= 0))
    )
  decreases (SZ.v nn - SZ.v !i)
  {
    let vi = !i;
    let c: int = A.op_Array_Access capacity vi;
    if (c < 0) { result := false } else { () };
    i := vi +^ 1sz
  };
  !result
}
#pop-options

(* ================================================================
   MAIN FORD-FULKERSON LOOP
   ================================================================ *)

(** Compute sum_flow_out from an array: Σ_{j<n} arr[v*n + j] *)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
fn compute_sum_out_fn
  (arr: A.array int)
  (n: SZ.t)
  (v: SZ.t)
  (#arr_seq: erased (Seq.seq int))
  requires
    A.pts_to arr arr_seq **
    pure (
      SZ.v n > 0 /\ SZ.v v < SZ.v n /\
      Seq.length arr_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n))
  returns result: int
  ensures
    A.pts_to arr arr_seq **
    pure (result == imp_sum_flow_out arr_seq (SZ.v n) (SZ.v v) (SZ.v n))
{
  let mut acc = 0;
  let mut j: SZ.t = 0sz;
  while (!j <^ n)
  invariant exists* jv s.
    R.pts_to j jv **
    R.pts_to acc s **
    A.pts_to arr arr_seq **
    pure (
      SZ.v jv <= SZ.v n /\
      Seq.length arr_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.v v < SZ.v n /\
      s == imp_sum_flow_out arr_seq (SZ.v n) (SZ.v v) (SZ.v jv))
  decreases (SZ.v n - SZ.v !j)
  {
    let jv = !j;
    let idx = v *^ n +^ jv;
    let fval = A.op_Array_Access arr idx;
    acc := !acc + fval;
    j := jv +^ 1sz
  };
  !acc
}
#pop-options

(** Compute sum_flow_into from an array: Σ_{u<n} arr[u*n + v] *)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
fn compute_sum_in_fn
  (arr: A.array int)
  (n: SZ.t)
  (v: SZ.t)
  (#arr_seq: erased (Seq.seq int))
  requires
    A.pts_to arr arr_seq **
    pure (
      SZ.v n > 0 /\ SZ.v v < SZ.v n /\
      Seq.length arr_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n))
  returns result: int
  ensures
    A.pts_to arr arr_seq **
    pure (result == imp_sum_flow_into arr_seq (SZ.v n) (SZ.v v) (SZ.v n))
{
  let mut acc = 0;
  let mut u: SZ.t = 0sz;
  while (!u <^ n)
  invariant exists* uv s.
    R.pts_to u uv **
    R.pts_to acc s **
    A.pts_to arr arr_seq **
    pure (
      SZ.v uv <= SZ.v n /\
      Seq.length arr_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.v v < SZ.v n /\
      s == imp_sum_flow_into arr_seq (SZ.v n) (SZ.v v) (SZ.v uv))
  decreases (SZ.v n - SZ.v !u)
  {
    let uv = !u;
    let idx = uv *^ n +^ v;
    let fval = A.op_Array_Access arr idx;
    acc := !acc + fval;
    u := uv +^ 1sz
  };
  !acc
}
#pop-options

(** Compute flow_value = sum_flow_out(source) - sum_flow_into(source) *)
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
fn compute_flow_value_fn
  (flow: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (#flow_seq: erased (Seq.seq int))
  requires
    A.pts_to flow flow_seq **
    pure (
      SZ.v n > 0 /\ SZ.v source < SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n))
  returns result: int
  ensures
    A.pts_to flow flow_seq **
    pure (result == imp_flow_value flow_seq (SZ.v n) (SZ.v source))
{
  let sum_out = compute_sum_out_fn flow n source;
  let sum_in = compute_sum_in_fn flow n source;
  (sum_out - sum_in)
}
#pop-options

(** Initialize flow to zero *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
fn zero_init_flow
  (flow: A.array int)
  (nn: SZ.t)
  (#flow_seq: erased (Seq.seq int))
  requires
    A.pts_to flow flow_seq **
    pure (Seq.length flow_seq == SZ.v nn)
  ensures exists* flow_seq'.
    A.pts_to flow flow_seq' **
    pure (
      Seq.length flow_seq' == SZ.v nn /\
      (forall (i: nat). i < SZ.v nn ==> Seq.index flow_seq' i == 0)
    )
{
  let mut i: SZ.t = 0sz;
  while (!i <^ nn)
  invariant exists* vi fs.
    R.pts_to i vi **
    A.pts_to flow fs **
    pure (
      SZ.v vi <= SZ.v nn /\
      Seq.length fs == SZ.v nn /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index fs j == 0)
    )
  decreases (SZ.v nn - SZ.v !i)
  {
    let vi = !i;
    A.op_Array_Assignment flow vi 0;
    i := vi +^ 1sz
  };
  ()
}
#pop-options

(** Main max flow: Ford-Fulkerson with BFS (Edmonds-Karp)

    Termination proof (no fuel needed):
    - cap_sum = sum of outgoing capacities from source (constant)
    - flow_value is bounded: 0 <= flow_value <= cap_sum (from imp_valid_flow)
    - Each augmentation where we continue increases flow_value by >= 1
    - Iteration counter iters is bounded by flow_value + 1
    - Measure: cap_sum + 1 - iters (non-negative, decreases by 1 each iteration) *)
#push-options "--z3rlimit 600 --fuel 1 --ifuel 1"
fn max_flow
  (capacity: A.array int)
  (#cap_seq: Ghost.erased (Seq.seq int))
  (flow: A.array int)
  (#flow_contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (source: SZ.t)
  (sink: SZ.t)
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_contents **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      valid_caps cap_seq (SZ.v n)
    )
  ensures exists* flow_seq'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq' **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq' == SZ.v n * SZ.v n /\
      imp_valid_flow flow_seq' cap_seq (SZ.v n) (SZ.v source) (SZ.v sink) /\
      no_augmenting_path #(SZ.v n) cap_seq flow_seq' (SZ.v source) (SZ.v sink)
    )
{
  let nn: SZ.t = n *^ n;

  // Phase 1: Initialize flow to zero
  zero_init_flow flow nn;

  // Establish imp_valid_flow for the zero flow (loop invariant initialization)
  with flow_zero. assert (A.pts_to flow flow_zero);
  lemma_zero_flow_imp_valid flow_zero cap_seq (SZ.v n) (SZ.v source) (SZ.v sink);

  // Zero flow has flow_value 0
  lemma_zero_flow_value flow_zero (SZ.v n) (SZ.v source);

  // Compute termination bound: sum of outgoing capacities from source
  let cap_sum = compute_sum_out_fn capacity n source;
  // cap_sum == sum_flow_out cap_seq n source n >= 0
  lemma_cap_sum_nonneg cap_seq (SZ.v n) (SZ.v source);

  // Phase 2: Allocate BFS workspace
  let color = A.alloc 0 n;
  let pred = A.alloc (-1) n;
  let dist = A.alloc (-1) n;
  let queue = A.alloc 0sz n;

  // Phase 3: Main Ford-Fulkerson loop
  let mut continue_loop: bool = true;
  let mut iters: int = 0;
  let mut flow_val: int = 0;

  while (!continue_loop)
  invariant exists* cont itr fv flow_s sc sp sd sq.
    R.pts_to continue_loop cont **
    R.pts_to iters itr **
    R.pts_to flow_val fv **
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_s **
    A.pts_to color sc **
    A.pts_to pred sp **
    A.pts_to dist sd **
    A.pts_to queue sq **
    pure (
      Seq.length flow_s == SZ.v n * SZ.v n /\
      Seq.length sc == SZ.v n /\
      Seq.length sp == SZ.v n /\
      Seq.length sd == SZ.v n /\
      Seq.length sq == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      valid_caps cap_seq (SZ.v n) /\
      imp_valid_flow flow_s cap_seq (SZ.v n) (SZ.v source) (SZ.v sink) /\
      fv == imp_flow_value flow_s (SZ.v n) (SZ.v source) /\
      fv <= cap_sum /\
      itr >= 0 /\
      (cont ==> itr <= fv) /\
      (cont ==> fv >= 0) /\
      // When loop exits (cont = false): no augmenting path
      (not cont ==> no_augmenting_path #(SZ.v n) cap_seq flow_s (SZ.v source) (SZ.v sink))
    )
  decreases (cap_sum + 1 - !iters)
  {
    iters := !iters + 1;

    let found = bfs_residual capacity flow color pred dist queue n source sink;

    if found
    {
      // Bind ghost witnesses from bfs_residual
      with _scolor' _spred' _sdist' _squeue'. assert (
        A.pts_to color _scolor' **
        A.pts_to pred _spred' **
        A.pts_to dist _sdist' **
        A.pts_to queue _squeue'
      );
      with _flow_s. assert (A.pts_to flow _flow_s);
      // find_bottleneck_imp: proven bn > 0 and bn == bottleneck_via_pred
      let bn = find_bottleneck_imp capacity flow pred n source sink
        #cap_seq #_flow_s #_spred' #_scolor' #_sdist';
      // augment_imp: proven flow' == augment_via_pred
      augment_imp capacity flow pred n source sink bn
        #cap_seq #_flow_s #_spred' #_scolor' #_sdist';
      // Chain: imp_valid_flow preserved, flow value increases
      lemma_augment_chain _scolor' _spred' _sdist' cap_seq _flow_s
        (SZ.v n) (SZ.v source) (SZ.v sink) bn;
      // Get augmented flow and update flow_val
      with flow_s'. assert (A.pts_to flow flow_s');
      lemma_flow_value_le_cap_sum flow_s' cap_seq (SZ.v n) (SZ.v source) (SZ.v sink);
      let new_fv = compute_flow_value_fn flow n source;
      flow_val := new_fv;
      ()
    }
    else
    {
      // BFS found no augmenting path — we have the max flow
      with flow_s. assert (A.pts_to flow flow_s);
      with sc. assert (A.pts_to color sc);
      lemma_bfs_complete cap_seq flow_s sc (SZ.v n) (SZ.v source) (SZ.v sink);
      continue_loop := false
    }
  };

  // Cleanup BFS workspace
  A.free color;
  A.free pred;
  A.free dist;
  A.free queue
}
#pop-options
