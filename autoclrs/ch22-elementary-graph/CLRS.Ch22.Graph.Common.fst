(**
 * CLRS Chapter 22: Common Graph Definitions
 *
 * Shared definitions used across Ch22 Pulse implementations.
 * Consolidates previously duplicated definitions:
 * - has_edge: edge predicate for flat adjacency matrix
 * - reachable_in: k-step reachability from a source vertex
 * - incr_nat / tick: ghost counter for complexity tracking
 * - product_strict_bound: arithmetic helper for index bounds
 * - fits_product_smaller: SZ.fits preservation for smaller products
 *
 * Graph representation: flat adjacency matrix (Seq.seq int) of size n*n,
 * where adj[u*n+v] <> 0 indicates an edge from u to v.
 *
 * Migration status:
 * - QueueBFS: migrated (uses these shared definitions)
 * - StackDFS: migrated (uses these shared definitions)
 * - IterativeBFS: local copies retained (Z3 proof sensitivity)
 * - TopologicalSort.Impl: local copies retained (Z3 proof sensitivity)
 *
 * New Pulse implementations should use these shared definitions via:
 *   open CLRS.Ch22.Graph.Common
 *)
module CLRS.Ch22.Graph.Common
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas

(*** Graph Representation ***)

/// Edge predicate for flat adjacency matrix: adj[u*n+v] <> 0 means edge u→v
let has_edge (adj: Seq.seq int) (n: nat) (u v: nat) : prop =
  u < n /\ v < n /\ u * n + v < Seq.length adj /\ Seq.index adj (u * n + v) <> 0

/// k-step reachability: source can reach v in exactly `steps` hops
let rec reachable_in (adj: Seq.seq int) (n: nat) (source v: nat) (steps: nat)
  : Tot prop (decreases steps)
  = if steps = 0 then v == source
    else (exists (u: nat). u < n /\ reachable_in adj n source u (steps - 1) /\ has_edge adj n u v)

/// Predecessor tree validity: for every non-WHITE vertex v with pred[v] in [0,n),
/// pred[v] is also non-WHITE, there is an edge from pred[v] to v, and d[pred[v]] < d[v].
/// Vertices with pred[v] < 0 are DFS tree roots (unconstrained).
[@"opaque_to_smt"]
let pred_edge_ok (sadj: Seq.seq int) (n: nat) (scolor sd spred: Seq.seq int) : prop =
  Seq.length scolor >= n /\ Seq.length sd >= n /\ Seq.length spred >= n /\ Seq.length sadj >= n * n /\
  (forall (v:nat). v < n /\ Seq.index scolor v <> 0 /\ Seq.index spred v >= 0 ==>
    Seq.index spred v < n) /\
  (forall (v:nat). {:pattern (Seq.index spred v)}
    v < n /\ Seq.index scolor v <> 0 /\ Seq.index spred v >= 0 /\ Seq.index spred v < n ==>
    Seq.index scolor (Seq.index spred v) <> 0 /\
    Seq.index sadj (Seq.index spred v * n + v) <> 0 /\
    Seq.index sd (Seq.index spred v) > 0 /\
    Seq.index sd (Seq.index spred v) < Seq.index sd v)

(*** Arithmetic Helpers ***)

/// Strict product bound: c < a ∧ d < b ⟹ c*b + d < a*b
let product_strict_bound (a b c d: nat)
  : Lemma (requires c < a /\ d < b)
          (ensures c * b + d < a * b)
  = ()

/// SZ.fits preservation for smaller products
let fits_product_smaller (a b c d: nat)
  : Lemma (requires c < a /\ d <= b /\ SZ.fits (a * b))
          (ensures SZ.fits (c * b) /\ SZ.fits (c * b + d))
  = assert (c * b <= a * b);
    assert (c * b + d <= a * b)

(*** Ghost Tick Counter for Complexity Tracking ***)

/// Increment an erased nat (ghost-only, erased at extraction)
let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

/// Ghost tick: increment a ghost counter (for complexity accounting)
ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

(*** Edge Classification Predicates ***)

/// Classify edge (u,v) as a BACK edge based on timestamps.
/// Back edge: u's interval [d[u], f[u]] is nested inside v's [d[v], f[v]].
/// (CLRS §22.3: v is an ancestor of u in the DFS tree)
let is_back_edge (sd sf: Seq.seq int) (u v: nat) : bool =
  u < Seq.length sd && v < Seq.length sd &&
  u < Seq.length sf && v < Seq.length sf &&
  Seq.index sd u >= Seq.index sd v && Seq.index sf u <= Seq.index sf v

/// Classify edge (u,v) as a TREE or FORWARD edge based on timestamps.
/// v's interval [d[v], f[v]] is strictly nested inside u's [d[u], f[u]].
/// (CLRS §22.3: v is a descendant of u; tree edge if pred[v]=u)
let is_tree_or_forward_edge (sd sf: Seq.seq int) (u v: nat) : bool =
  u < Seq.length sd && v < Seq.length sd &&
  u < Seq.length sf && v < Seq.length sf &&
  Seq.index sd u < Seq.index sd v && Seq.index sf v < Seq.index sf u

/// Classify edge (u,v) as a CROSS edge based on timestamps.
/// v's interval finishes before u's begins (disjoint, v first).
/// (CLRS §22.3: v is neither ancestor nor descendant of u)
let is_cross_edge (sd sf: Seq.seq int) (u v: nat) : bool =
  u < Seq.length sd && v < Seq.length sd &&
  u < Seq.length sf && v < Seq.length sf &&
  Seq.index sf v < Seq.index sd u

(*** White-Path Theorem Definitions (flat-array) ***)
(*
 * These are flat-array (Seq.seq int) versions of the definitions from
 * CLRS.Ch22.DFS.WhitePath, which uses 2D adjacency (Seq.seq (Seq.seq int))
 * and Seq.seq nat timestamps. These flat versions use the same
 * adjacency representation and int timestamps as the implementation
 * (CLRS.Ch22.DFS.Impl), making the white-path theorem vocabulary
 * available to callers of the implementation interface.
 *
 * The White-Path Theorem itself is fully proven in DFS.WhitePath.fst
 * for the spec representation. Connecting it to the implementation
 * requires a simulation proof (proving impl computes the same d/f
 * as the spec), which is left as future work.
 *)

/// DFS ancestor relation for flat int arrays.
/// Equivalent to is_tree_or_forward_edge — included for theorem vocabulary.
/// Mirrors DFS.WhitePath.dfs_ancestor (Seq.seq nat version).
let dfs_ancestor_flat (sd sf: Seq.seq int) (u v: nat) : prop =
  u < Seq.length sd /\ v < Seq.length sd /\
  u < Seq.length sf /\ v < Seq.length sf /\
  Seq.index sd u < Seq.index sd v /\
  Seq.index sf v < Seq.index sf u

/// Vertex v is white (undiscovered) at time t.
/// Mirrors DFS.WhitePath.white_at_time.
let white_at_time_flat (sd: Seq.seq int) (v: nat) (time: int) : prop =
  v < Seq.length sd /\
  (Seq.index sd v <= 0 \/ time < Seq.index sd v)

/// All intermediate vertices on a path are white at time t.
/// Uses flat adjacency matrix. Mirrors DFS.WhitePath.path_all_white.
let rec path_all_white_flat
  (adj: Seq.seq int) (n: nat) (sd: Seq.seq int)
  (u v: nat) (time: int) (steps: nat)
  : Tot prop (decreases steps)
  = if steps = 0 then u == v /\ white_at_time_flat sd v time
    else if steps = 1 then has_edge adj n u v /\ white_at_time_flat sd v time
    else u < n /\ v < n /\
      (exists (w: nat). w < n /\ has_edge adj n u w /\ white_at_time_flat sd w time /\
        path_all_white_flat adj n sd w v time (steps - 1))

/// There exists a white path from u to v at time t.
/// Mirrors DFS.WhitePath.white_path_exists.
let white_path_exists_flat (adj: Seq.seq int) (n: nat) (sd: Seq.seq int)
  (u v: nat) (time: int) : prop =
  exists (k: nat). k <= n /\ path_all_white_flat adj n sd u v time k

(*** Lemma: Predecessor implies DFS tree/forward edge ***)

/// From the DFS postcondition properties (all-BLACK + pred_edge_ok + pred_finish_ok),
/// any vertex with a valid predecessor is a descendant of that predecessor in the
/// DFS forest. That is, pred[v] = u implies d[u] < d[v] and f[v] < f[u].
///
/// This connects the predecessor array to the DFS ancestor relation, and
/// is the implementation-level analog of the white-path theorem's forward
/// direction: if v was discovered from u, then v is a descendant of u.
let pred_implies_tree_or_forward
  (sadj: Seq.seq int) (n: nat) (scolor sd sf spred: Seq.seq int) (v: nat)
  : Lemma
    (requires
      v < n /\
      Seq.length scolor >= n /\ Seq.length sd >= n /\
      Seq.length sf >= n /\ Seq.length spred >= n /\
      Seq.length sadj >= n * n /\
      (forall (u: nat). u < n ==> Seq.index scolor u == 2) /\
      pred_edge_ok sadj n scolor sd spred /\
      Seq.index spred v >= 0 /\ Seq.index spred v < n /\
      Seq.index sf v < Seq.index sf (Seq.index spred v))
    (ensures
      is_tree_or_forward_edge sd sf (Seq.index spred v) v == true)
  = reveal_opaque (`%pred_edge_ok) (pred_edge_ok sadj n scolor sd spred)
