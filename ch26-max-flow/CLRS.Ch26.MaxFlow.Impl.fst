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
   4. Repeat until no augmenting path exists (or fuel exhausted)
   
   Connects to the fully verified pure spec (Spec.fst, Lemmas.fst):
   - valid_flow maintained through augmentation (Lemmas.augment_preserves_valid)
   - MFMC theorem: no augmenting path => max flow
   
   Postcondition guarantees imp_valid_flow (static proof, no runtime check).
   
   Remaining proof obligations (admit in lemma_augment_imp_preserves_valid):
   - BFS produces a valid augmenting path (distinct vertices, bounded, source to sink)
   - find_bottleneck_imp computes bn <= spec bottleneck
   - augment_imp refines augment_aux (operations commute on distinct paths)
   Pure lemmas for BFS path correctness (pred_ok => path properties) are proved.
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

(** Augmentation preserves imp_valid_flow.
    Proof obligation: follows from BFS path correctness + Lemmas.augment_preserves_valid.
    TODO: discharge once BFS + augment correspondence proofs are complete. *)
let lemma_augment_imp_preserves_valid (flow_seq cap_seq: Seq.seq int) (n source sink: nat)
  : Lemma (ensures imp_valid_flow flow_seq cap_seq n source sink)
  = admit ()

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
#push-options "--z3rlimit 120 --fuel 1 --ifuel 1"
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
      bfs_inv_props scolor spred squeue cap_seq flow_seq (SZ.v n) (SZ.v source) (SZ.v vtail)
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
        (SZ.v vtail) (SZ.v vtail')
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
    // Establish vtail < n from the zero-colored vertex
    lemma_count_nonzero_lt_has_zero scolor (SZ.v n) (SZ.v vv);
    // Use pure proof helper (avoids Seq.upd terms in Pulse elaboration)
    maybe_discover_then_proof scolor spred squeue cap_seq flow_seq
      (SZ.v n) (SZ.v u) (SZ.v source) (SZ.v vtail) vv;
    // Perform stateful updates
    let du: int = A.op_Array_Access dist u;
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
      queue_ok scolor squeue (SZ.v vtail) (SZ.v n)
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
      queue_color1 scolor' squeue' (SZ.v vtail) (SZ.v vtail') (SZ.v n)
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
      queue_color1 sc sq (SZ.v vtail) (SZ.v vt) (SZ.v n)
    )
  decreases (SZ.v n - SZ.v !v)
  {
    let vv = !v;
    with sc_before. assert (A.pts_to color sc_before);
    with sp_before. assert (A.pts_to pred sp_before);
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
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
fn bfs_residual
  (capacity flow color pred: A.array int)
  (queue: A.array SZ.t)
  (n source sink: SZ.t)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#scolor0: erased (Seq.seq int))
  (#spred0: erased (Seq.seq int))
  (#squeue0: erased (Seq.seq SZ.t))
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor0 **
    A.pts_to pred spred0 **
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
      Seq.length squeue0 == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns found: bool
  ensures exists* scolor' spred' squeue'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color scolor' **
    A.pts_to pred spred' **
    A.pts_to queue squeue' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      found == (seq_get scolor' (SZ.v sink) <> 0) /\
      preds_in_range spred' (SZ.v n) /\
      // Source is always discovered by BFS
      seq_get scolor' (SZ.v source) <> 0 /\
      // BFS completeness: all residual neighbors of discovered vertices are discovered
      bfs_complete scolor' cap_seq flow_seq (SZ.v n)
    )
{
  // Allocate dist array for BFS tree depth tracking
  let dist = A.alloc (-1) n;

  bfs_init color pred dist n source;
  A.op_Array_Assignment queue 0sz source;
  // Establish invariant preconditions for the BFS loop
  with scolor_init. assert (A.pts_to color scolor_init);
  with squeue_init. assert (A.pts_to queue squeue_init);
  lemma_count_nonzero_single scolor_init (SZ.v n) (SZ.v source);
  lemma_count_color1_single scolor_init (SZ.v n) (SZ.v source);
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
      queue_color1 scolor_q squeue_q (SZ.v vhead) (SZ.v vtail) (SZ.v n)
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
    A.op_Array_Assignment color u 2;
    ()
  };
  let sink_color: int = A.op_Array_Access color sink;

  // Free dist array (local to BFS)
  A.free dist;

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
#push-options "--z3rlimit 160 --fuel 1 --ifuel 1"
fn find_bottleneck_imp
  (capacity flow pred: A.array int)
  (n source sink: SZ.t)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
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
      preds_in_range spred (SZ.v n) /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns bn: int
  ensures
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to pred spred **
    pure (bn >= 0)
{
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
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      preds_in_range spred (SZ.v n) /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  // TODO: decreases
  {
    let vc = !current;
    let u_int: int = A.op_Array_Access pred vc;
    // From preds_in_range: u_int >= -1 /\ u_int < SZ.v n
    // On a valid BFS path, u_int >= 0 (only -1 for undiscovered vertices)
    if (u_int >= 0)
    {
      let u: SZ.t = SZ.uint_to_t u_int;
      let idx_fwd: SZ.t = u *^ n +^ vc;
      let idx_bwd: SZ.t = vc *^ n +^ u;
      let cap_val: int = A.op_Array_Access capacity idx_fwd;
      let flow_fwd: int = A.op_Array_Access flow idx_fwd;
      let flow_bwd: int = A.op_Array_Access flow idx_bwd;
      let res_fwd: int = cap_val - flow_fwd;
      let vbn = !bottleneck;
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
  !bottleneck
}
#pop-options

(** Augment flow: walk pred array from sink to source, update flow *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
fn augment_imp
  (capacity flow pred: A.array int)
  (n source sink: SZ.t)
  (bn: int)
  (#cap_seq: erased (Seq.seq int))
  (#flow_seq: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
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
      preds_in_range spred (SZ.v n) /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* flow_seq'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq' **
    A.pts_to pred spred **
    pure (
      Seq.length flow_seq' == SZ.v n * SZ.v n
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
      SZ.fits (SZ.v n * SZ.v n)
    )
  // TODO: decreases
  {
    let vc = !current;
    let u_int: int = A.op_Array_Access pred vc;
    // From preds_in_range: u_int >= -1 /\ u_int < SZ.v n
    if (u_int >= 0)
    {
      let u: SZ.t = SZ.uint_to_t u_int;
      let idx_fwd: SZ.t = u *^ n +^ vc;
      let idx_bwd: SZ.t = vc *^ n +^ u;
      let cap_val: int = A.op_Array_Access capacity idx_fwd;
      let flow_fwd: int = A.op_Array_Access flow idx_fwd;
      if (cap_val - flow_fwd > 0)
      {
        A.op_Array_Assignment flow idx_fwd (flow_fwd + bn);
        current := u
      }
      else
      {
        let flow_bwd: int = A.op_Array_Access flow idx_bwd;
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
  ()
}
#pop-options

(* ================================================================
   VALIDITY CHECK — dynamic verification of imp_valid_flow
   ================================================================ *)

(** Helper: u*n+v < n*n when u < n and v < n *)
let lemma_idx_lt_nn (n u v: nat)
  : Lemma (requires u < n /\ v < n) (ensures u * n + v < n * n)
  = FStar.Math.Lemmas.lemma_mult_le_right n u (n - 1)

(** Establish imp_valid_flow from capacity + conservation checks *)
#push-options "--z3rlimit 40"
let lemma_checks_imply_valid_flow 
  (flow_s cap_s: Seq.seq int) (n source sink: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ sink < n /\
      Seq.length flow_s == n * n /\ Seq.length cap_s == n * n /\
      (forall (idx: nat). idx < n * n ==> 0 <= Seq.index flow_s idx /\ Seq.index flow_s idx <= Seq.index cap_s idx) /\
      (forall (w: nat). w < n /\ w <> source /\ w <> sink ==>
        sum_flow_into flow_s n w n == sum_flow_out flow_s n w n))
    (ensures imp_valid_flow flow_s cap_s n source sink)
  = let aux (u v: nat)
        : Lemma (requires u < n /\ v < n)
                (ensures u * n + v < n * n)
        = FStar.Math.Lemmas.lemma_mult_le_right n u (n - 1);
          FStar.Math.Lemmas.distributivity_sub_left n 1 n
    in
    FStar.Classical.forall_intro_2 (fun u v -> FStar.Classical.move_requires_2 aux u v)
#pop-options

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

(** Check capacity constraint: 0 <= flow[i] <= cap[i] for all i *)
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
fn check_capacity_fn
  (flow capacity: A.array int)
  (nn: SZ.t)
  (#flow_seq #cap_seq: erased (Seq.seq int))
  requires
    A.pts_to flow flow_seq **
    A.pts_to capacity cap_seq **
    pure (
      Seq.length flow_seq == SZ.v nn /\
      Seq.length cap_seq == SZ.v nn
    )
  returns ok: bool
  ensures
    A.pts_to flow flow_seq **
    A.pts_to capacity cap_seq **
    pure (
      Seq.length flow_seq == SZ.v nn /\
      Seq.length cap_seq == SZ.v nn /\
      (ok ==> (forall (idx: nat). idx < SZ.v nn ==>
        0 <= Seq.index flow_seq idx /\ Seq.index flow_seq idx <= Seq.index cap_seq idx)))
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
    A.pts_to flow flow_seq **
    A.pts_to capacity cap_seq **
    pure (
      SZ.v vi <= SZ.v nn /\
      Seq.length flow_seq == SZ.v nn /\
      Seq.length cap_seq == SZ.v nn /\
      (vr ==> (forall (idx: nat). idx < SZ.v vi ==>
        0 <= Seq.index flow_seq idx /\ Seq.index flow_seq idx <= Seq.index cap_seq idx))
    )
  decreases (SZ.v nn - SZ.v !i)
  {
    let vi = !i;
    let f: int = A.op_Array_Access flow vi;
    let c: int = A.op_Array_Access capacity vi;
    if (f < 0 || f > c) { result := false } else { () };
    i := vi +^ 1sz
  };
  !result
}
#pop-options

(** Check conservation at a single vertex: sum_flow_into == sum_flow_out *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
fn check_vertex_conservation
  (flow: A.array int)
  (n u: SZ.t)
  (#flow_seq: erased (Seq.seq int))
  requires
    A.pts_to flow flow_seq **
    pure (
      SZ.v u < SZ.v n /\
      SZ.v n > 0 /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns ok: bool
  ensures
    A.pts_to flow flow_seq **
    pure (
      SZ.v u < SZ.v n /\ SZ.v n > 0 /\ Seq.length flow_seq == SZ.v n * SZ.v n /\
      (ok ==> sum_flow_into flow_seq (SZ.v n) (SZ.v u) (SZ.v n) == sum_flow_out flow_seq (SZ.v n) (SZ.v u) (SZ.v n)))
{
  let mut sum_in: int = 0;
  let mut sum_out: int = 0;
  let mut v = 0sz;
  while (!v <^ n)
  invariant exists* vv si so.
    R.pts_to v vv **
    R.pts_to sum_in si **
    R.pts_to sum_out so **
    A.pts_to flow flow_seq **
    pure (
      SZ.v vv <= SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v n > 0 /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      si == sum_flow_into flow_seq (SZ.v n) (SZ.v u) (SZ.v vv) /\
      so == sum_flow_out flow_seq (SZ.v n) (SZ.v u) (SZ.v vv)
    )
  decreases (SZ.v n - SZ.v !v)
  {
    let vv = !v;
    let idx_in: SZ.t = vv *^ n +^ u;
    let idx_out: SZ.t = u *^ n +^ vv;
    let f_in: int = A.op_Array_Access flow idx_in;
    let f_out: int = A.op_Array_Access flow idx_out;
    let si = !sum_in;
    let so = !sum_out;
    sum_in := si + f_in;
    sum_out := so + f_out;
    v := vv +^ 1sz
  };
  let si = !sum_in;
  let so = !sum_out;
  (si = so)
}
#pop-options

(** Check conservation for all non-source, non-sink vertices *)
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
fn check_all_conservation
  (flow: A.array int)
  (n source sink: SZ.t)
  (#flow_seq: erased (Seq.seq int))
  requires
    A.pts_to flow flow_seq **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns ok: bool
  ensures
    A.pts_to flow flow_seq **
    pure (
      SZ.v n > 0 /\ Seq.length flow_seq == SZ.v n * SZ.v n /\
      (ok ==> (forall (w: nat). w < SZ.v n /\ w <> SZ.v source /\ w <> SZ.v sink ==>
        sum_flow_into flow_seq (SZ.v n) w (SZ.v n) == sum_flow_out flow_seq (SZ.v n) w (SZ.v n))))
{
  let mut u_idx = 0sz;
  let mut result = true;
  while (
    let vu = !u_idx;
    let vr = !result;
    vr && vu <^ n
  )
  invariant exists* vu vr.
    R.pts_to u_idx vu **
    R.pts_to result vr **
    A.pts_to flow flow_seq **
    pure (
      SZ.v vu <= SZ.v n /\
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      (vr ==> (forall (w: nat). w < SZ.v vu /\ w <> SZ.v source /\ w <> SZ.v sink ==>
        sum_flow_into flow_seq (SZ.v n) w (SZ.v n) == sum_flow_out flow_seq (SZ.v n) w (SZ.v n)))
    )
  decreases (SZ.v n - SZ.v !u_idx)
  {
    let vu = !u_idx;
    let ok_v = check_vertex_conservation flow n vu;
    if (not (vu = source) && not (vu = sink) && not ok_v)
    {
      result := false
    } else { () };
    u_idx := vu +^ 1sz
  };
  !result
}
#pop-options

(** Combined validity check with imp_valid_flow postcondition *)
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
fn check_imp_valid_flow_fn
  (flow capacity: A.array int)
  (n source sink: SZ.t)
  (#flow_seq #cap_seq: erased (Seq.seq int))
  requires
    A.pts_to flow flow_seq **
    A.pts_to capacity cap_seq **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns valid: bool
  ensures
    A.pts_to flow flow_seq **
    A.pts_to capacity cap_seq **
    pure (valid ==> imp_valid_flow flow_seq cap_seq (SZ.v n) (SZ.v source) (SZ.v sink))
{
  let nn = n *^ n;
  let cap_ok = check_capacity_fn flow capacity nn;
  let cons_ok = check_all_conservation flow n source sink;
  if (cap_ok && cons_ok) {
    lemma_checks_imply_valid_flow flow_seq cap_seq (SZ.v n) (SZ.v source) (SZ.v sink);
    true
  } else {
    false
  }
}
#pop-options

(* ================================================================
   MAIN FORD-FULKERSON LOOP
   ================================================================ *)

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

(** Main max flow: Ford-Fulkerson with BFS (Edmonds-Karp) *)
#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
fn max_flow
  (capacity: A.array int)
  (#cap_seq: Ghost.erased (Seq.seq int))
  (flow: A.array int)
  (#flow_contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (source: SZ.t)
  (sink: SZ.t)
  (fuel: SZ.t)
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
  returns completed: bool
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
      // When completed = true, BFS found no augmenting path:
      // the flow is maximum and MFMC theorem applies
      (completed ==> no_augmenting_path #(SZ.v n) cap_seq flow_seq' (SZ.v source) (SZ.v sink))
    )
{
  let nn: SZ.t = n *^ n;

  // Phase 1: Initialize flow to zero
  zero_init_flow flow nn;

  // Phase 2: Allocate BFS workspace
  let color = A.alloc 0 n;
  let pred = A.alloc (-1) n;
  let queue = A.alloc 0sz n;

  // Phase 3: Main Ford-Fulkerson loop
  let mut continue_loop: bool = true;
  let mut iters: SZ.t = 0sz;
  // Tracks whether we terminated because BFS found no path (vs fuel exhaustion)
  let mut is_completed: bool = false;

  (* Termination argument (CLRS §26.2):
     Each augmentation strictly increases the flow value by ≥1 (integer capacities).
     The maximum flow is bounded by the sum of outgoing capacities from source.
     For Edmonds-Karp: at most O(VE) augmentations (Theorem 26.8).
     With n×n adjacency matrix (E ≤ n²): at most n³ augmentations.
     Caller should provide fuel ≥ n³ for guaranteed complete execution. *)
  while (!continue_loop && !iters <^ fuel)
  invariant exists* cont itr flow_s sc sp sq completed_v.
    R.pts_to continue_loop cont **
    R.pts_to iters itr **
    R.pts_to is_completed completed_v **
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_s **
    A.pts_to color sc **
    A.pts_to pred sp **
    A.pts_to queue sq **
    pure (
      Seq.length flow_s == SZ.v n * SZ.v n /\
      Seq.length sc == SZ.v n /\
      Seq.length sp == SZ.v n /\
      Seq.length sq == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.v itr <= SZ.v fuel /\
      valid_caps cap_seq (SZ.v n) /\
      // completed is only set to true when the loop is about to exit
      (cont ==> completed_v == false) /\
      // When loop stops with completed=true, no_augmenting_path holds
      (completed_v ==> no_augmenting_path #(SZ.v n) cap_seq flow_s (SZ.v source) (SZ.v sink))
    )
  decreases (SZ.v fuel - SZ.v !iters)
  {
    iters := !iters +^ 1sz;

    let found = bfs_residual capacity flow color pred queue n source sink;

    if found
    {
      let bn = find_bottleneck_imp capacity flow pred n source sink;
      if (bn > 0) {
        augment_imp capacity flow pred n source sink bn
      } else {
        continue_loop := false
      }
    }
    else
    {
      // BFS found no augmenting path — we have the max flow
      // Use BFS completeness to establish no_augmenting_path
      with flow_s. assert (A.pts_to flow flow_s);
      with sc. assert (A.pts_to color sc);
      lemma_bfs_complete cap_seq flow_s sc (SZ.v n) (SZ.v source) (SZ.v sink);
      is_completed := true;
      continue_loop := false
    }
  };

  let result = !is_completed;

  // Establish imp_valid_flow for postcondition
  // Proof relies on: zero flow is valid, and each augment_imp preserves validity
  // (via BFS path correctness + Lemmas.augment_preserves_valid)
  with flow_end. assert (A.pts_to flow flow_end);
  lemma_augment_imp_preserves_valid flow_end cap_seq (SZ.v n) (SZ.v source) (SZ.v sink);

  // Cleanup BFS workspace
  A.free color;
  A.free pred;
  A.free queue;
  result
}
#pop-options
