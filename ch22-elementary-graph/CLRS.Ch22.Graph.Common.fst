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
 * - KahnTopologicalSort: local copies retained (Z3 proof sensitivity)
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
