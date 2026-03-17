(*
   CLRS Chapter 35: Vertex Cover 2-Approximation — Spec Validation Test

   Adapted from:
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   Tests that the approx_vertex_cover API's postcondition
   (is_cover + binary + 2-approximation) is satisfiable and sufficiently
   precise to constrain the output for a concrete triangle graph K₃.

   Test instance: K₃ (complete graph on 3 vertices)
     Vertices: {0, 1, 2}
     Edges: {(0,1), (0,2), (1,2)}
     Adjacency matrix (row-major, 3×3): [0,1,1, 1,0,1, 1,1,0]

   The postcondition proves the output is one of exactly 4 admissible
   binary covers: [1,1,0], [1,0,1], [0,1,1], [1,1,1] — ruling out
   all 0-vertex and 1-vertex covers.
*)
module CLRS.Ch35.VertexCover.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch35.VertexCover.Spec
open CLRS.Ch35.VertexCover.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = CLRS.Ch35.VertexCover.Spec

(*** Pure helper lemmas ***)

(* Extract a single-edge constraint from the is_cover postcondition.
   Helps Z3 instantiate the universal quantifier for specific (u, v). *)
let is_cover_edge (s_adj s_cover: Seq.seq int) (n u v: nat)
  : Lemma
    (requires
      Spec.is_cover s_adj s_cover n n 0 /\
      u < n /\ v < n /\ u < v /\
      Seq.index s_adj (u * n + v) <> 0)
    (ensures
      Seq.index s_cover u <> 0 \/ Seq.index s_cover v <> 0)
  = ()

(* For K₃, is_cover + binary implies at least 2 vertices are covered.
   Edges (0,1), (0,2), (1,2) each require at least one endpoint in the cover.
   By case analysis on 3 binary variables, at least 2 must be 1. *)
let triangle_cover_at_least_two
  (s_adj s_cover: Seq.seq int)
  : Lemma
    (requires
      Seq.length s_adj == 9 /\
      Seq.length s_cover == 3 /\
      Seq.index s_adj 1 <> 0 /\
      Seq.index s_adj 2 <> 0 /\
      Seq.index s_adj 5 <> 0 /\
      Spec.is_cover s_adj s_cover 3 3 0 /\
      (forall (i: nat). i < 3 ==> (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)))
    (ensures
      (Seq.index s_cover 0 = 1 \/ Seq.index s_cover 1 = 1) /\
      (Seq.index s_cover 0 = 1 \/ Seq.index s_cover 2 = 1) /\
      (Seq.index s_cover 1 = 1 \/ Seq.index s_cover 2 = 1))
  = is_cover_edge s_adj s_cover 3 0 1;
    is_cover_edge s_adj s_cover 3 0 2;
    is_cover_edge s_adj s_cover 3 1 2

(* Completeness: the postcondition (is_cover + binary) admits exactly 4 covers
   for K₃ and excludes the other 4.
   Admissible:  [1,1,0], [1,0,1], [0,1,1], [1,1,1]
   Excluded:    [0,0,0], [1,0,0], [0,1,0], [0,0,1] *)
let triangle_cover_enumeration
  (s_adj s_cover: Seq.seq int)
  : Lemma
    (requires
      Seq.length s_adj == 9 /\
      Seq.length s_cover == 3 /\
      Seq.index s_adj 1 <> 0 /\
      Seq.index s_adj 2 <> 0 /\
      Seq.index s_adj 5 <> 0 /\
      Spec.is_cover s_adj s_cover 3 3 0 /\
      (forall (i: nat). i < 3 ==> (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)))
    (ensures
      (Seq.index s_cover 0 = 1 /\ Seq.index s_cover 1 = 1 /\ Seq.index s_cover 2 = 0) \/
      (Seq.index s_cover 0 = 1 /\ Seq.index s_cover 1 = 0 /\ Seq.index s_cover 2 = 1) \/
      (Seq.index s_cover 0 = 0 /\ Seq.index s_cover 1 = 1 /\ Seq.index s_cover 2 = 1) \/
      (Seq.index s_cover 0 = 1 /\ Seq.index s_cover 1 = 1 /\ Seq.index s_cover 2 = 1))
  = triangle_cover_at_least_two s_adj s_cover

(*** Pulse test: triangle graph K₃ ***)

#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"

```pulse
fn test_vertex_cover_triangle ()
  requires emp
  returns _: unit
  ensures emp
{
  // --- Setup: adjacency matrix for K₃ (3 vertices, all pairs connected) ---
  // Layout (row-major 3×3): [0,1,1, 1,0,1, 1,1,0]
  let adj_v = V.alloc 0 9sz;
  V.to_array_pts_to adj_v;
  let adj = V.vec_to_array adj_v;
  rewrite (A.pts_to (V.vec_to_array adj_v) (Seq.create 9 0))
       as (A.pts_to adj (Seq.create 9 0));

  // Set edge entries (symmetric): (0,1), (0,2), (1,2) and transposes
  adj.(1sz) <- 1;   // adj[0*3+1] — edge (0,1)
  adj.(2sz) <- 1;   // adj[0*3+2] — edge (0,2)
  adj.(3sz) <- 1;   // adj[1*3+0] — edge (1,0)
  adj.(5sz) <- 1;   // adj[1*3+2] — edge (1,2)
  adj.(6sz) <- 1;   // adj[2*3+0] — edge (2,0)
  adj.(7sz) <- 1;   // adj[2*3+1] — edge (2,1)

  // Bind ghost sequence of adjacency matrix
  with s_adj. assert (A.pts_to adj s_adj);

  // --- Precondition satisfiability ---
  // Z3 verifies all preconditions from the concrete array values:
  //   SZ.v 3sz > 0, SZ.fits 9, Seq.length == 9, is_symmetric_adj

  // --- Call the 2-approximation vertex cover algorithm ---
  let cover = approx_vertex_cover adj 3sz;

  // --- Postcondition validation ---
  with s_cover. assert (V.pts_to cover s_cover);

  // Assert concrete adjacency values (trigger for lemma preconditions)
  assert (pure (Seq.index s_adj 1 <> 0));
  assert (pure (Seq.index s_adj 2 <> 0));
  assert (pure (Seq.index s_adj 5 <> 0));

  // Prove: at least 2 vertices must be in the cover
  triangle_cover_at_least_two s_adj s_cover;

  // Prove: output is one of exactly 4 valid covers
  triangle_cover_enumeration s_adj s_cover;

  // --- Cleanup ---
  V.free cover;

  with s_a. assert (A.pts_to adj s_a);
  rewrite (A.pts_to adj s_a)
       as (A.pts_to (V.vec_to_array adj_v) s_a);
  V.to_vec_pts_to adj_v;
  V.free adj_v;
}
```

#pop-options
