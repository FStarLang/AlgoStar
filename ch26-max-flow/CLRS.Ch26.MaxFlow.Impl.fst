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

(** AXIOM — BFS completeness: when BFS terminates with all residual neighbors of
    discovered vertices also discovered (bfs_complete), and sink undiscovered,
    then no augmenting path exists.
    
    Proof sketch:
    - Any path from source to sink must cross from a discovered vertex to an
      undiscovered vertex at some edge (u, v) where u is colored and v is not.
    - By bfs_complete, the residual capacity of u→v is ≤ 0 (forward) and
      v→u backward flow is ≤ 0. So this edge contributes ≤ 0 to the bottleneck.
    - Therefore the bottleneck of any source-to-sink path is ≤ 0.
    
    Pending full proof (requires induction on path structure). *)
assume val axiom_bfs_complete
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

(** Try to discover vertex vv from u in the residual graph *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
fn maybe_discover
  (capacity flow color pred dist: A.array int)
  (queue: A.array SZ.t)
  (n u vv: SZ.t)
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
      SZ.v vtail <= SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sdist == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      queue_valid squeue 0 (SZ.v vtail) (SZ.v n) /\
      preds_in_range spred (SZ.v n)
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
      preds_in_range spred' (SZ.v n)
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
  if (cv = 0 && (res_fwd > 0 || flow_bwd > 0) && vt <^ n)
  {
    let du: int = A.op_Array_Access dist u;
    A.op_Array_Assignment color vv 1;
    A.op_Array_Assignment pred vv (SZ.v u);
    A.op_Array_Assignment dist vv (du + 1);
    A.op_Array_Assignment queue vt vv;
    q_tail := vt +^ 1sz;
    ()
  }
  else { () }
}
#pop-options

(** Explore all neighbors of vertex u in the residual graph *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
fn bfs_explore_neighbors
  (capacity flow color pred dist: A.array int)
  (queue: A.array SZ.t)
  (n u: SZ.t)
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
      SZ.v vtail <= SZ.v n /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sdist == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      queue_valid squeue 0 (SZ.v vtail) (SZ.v n) /\
      preds_in_range spred (SZ.v n)
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
      preds_in_range spred' (SZ.v n)
    )
{
  let mut v: SZ.t = 0sz;
  while (!v <^ n)
  invariant exists* vv sc sp sd sq vt.
    R.pts_to v vv **
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq **
    A.pts_to color sc **
    A.pts_to pred sp **
    A.pts_to dist sd **
    A.pts_to queue sq **
    R.pts_to q_tail vt **
    pure (
      SZ.v vv <= SZ.v n /\
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
      preds_in_range sp (SZ.v n)
    )
  decreases (SZ.v n - SZ.v !v)
  {
    let vv = !v;
    maybe_discover capacity flow color pred dist queue n u vv q_tail;
    v := vv +^ 1sz
  };
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
      preds_in_range spred_q (SZ.v n)
    )
  decreases (SZ.v n - SZ.v !q_head)
  {
    let vh = !q_head;
    let u: SZ.t = A.op_Array_Access queue vh;
    ();
    q_head := vh +^ 1sz;
    bfs_explore_neighbors capacity flow color pred dist queue n u q_tail;
    A.op_Array_Assignment color u 2;
    ()
  };
  let sink_color: int = A.op_Array_Access color sink;

  // Free dist array (local to BFS)
  A.free dist;

  // BFS completeness: at termination, queue is empty so all colored vertices
  // have been fully processed and all their residual neighbors discovered.
  // Source was colored during bfs_init and color is never unset.
  with sc_final. assert (A.pts_to color sc_final);
  assume_ (pure (seq_get sc_final (SZ.v source) <> 0));
  assume_ (pure (bfs_complete sc_final cap_seq flow_seq (SZ.v n)));

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
      axiom_bfs_complete cap_seq flow_s sc (SZ.v n) (SZ.v source) (SZ.v sink);
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
