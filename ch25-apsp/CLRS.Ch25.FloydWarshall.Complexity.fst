(*
   Floyd-Warshall with Complexity Bound

   Proves O(n³) complexity for the Floyd-Warshall all-pairs shortest paths algorithm.
   Specifically: exactly n³ relaxation operations (three nested loops each 0..n-1).

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each relaxation (compute via_k, update d[i][j]) gets one ghost tick.

   Also proves functional correctness (result == fw_outer contents n 0).

   NO admits. NO assumes.
*)

module CLRS.Ch25.FloydWarshall.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

#set-options "--z3rlimit 40"

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Pure Specification (same as FloydWarshall.fst) ==========

let inf : int = 1000000

let rec fw_inner_j (d: Seq.seq int) (n k i j: nat) (d_ik: int)
  : Tot (Seq.seq int) (decreases (n - j)) =
  if j >= n || i >= n || k >= n || Seq.length d <> n * n then d
  else
    let d_ij = Seq.index d (i * n + j) in
    let d_kj = Seq.index d (k * n + j) in
    let via_k = d_ik + d_kj in
    let new_val = if via_k < d_ij then via_k else d_ij in
    fw_inner_j (Seq.upd d (i * n + j) new_val) n k i (j + 1) d_ik

let rec fw_inner_i (d: Seq.seq int) (n k i: nat)
  : Tot (Seq.seq int) (decreases (n - i)) =
  if i >= n || k >= n || Seq.length d <> n * n then d
  else
    let d_ik = Seq.index d (i * n + k) in
    fw_inner_i (fw_inner_j d n k i 0 d_ik) n k (i + 1)

let rec fw_outer (d: Seq.seq int) (n k: nat)
  : Tot (Seq.seq int) (decreases (n - k)) =
  if k >= n || Seq.length d <> n * n then d
  else fw_outer (fw_inner_i d n k 0) n (k + 1)

let rec lemma_fw_inner_j_len (d: Seq.seq int) (n k i j: nat) (d_ik: int)
  : Lemma (ensures Seq.length (fw_inner_j d n k i j d_ik) == Seq.length d)
          (decreases (n - j))
  = if j >= n || i >= n || k >= n || Seq.length d <> n * n then ()
    else
      let d_ij = Seq.index d (i * n + j) in
      let d_kj = Seq.index d (k * n + j) in
      let via_k = d_ik + d_kj in
      let new_val = if via_k < d_ij then via_k else d_ij in
      lemma_fw_inner_j_len (Seq.upd d (i * n + j) new_val) n k i (j + 1) d_ik

let rec lemma_fw_inner_i_len (d: Seq.seq int) (n k i: nat)
  : Lemma (ensures Seq.length (fw_inner_i d n k i) == Seq.length d)
          (decreases (n - i))
  = if i >= n || k >= n || Seq.length d <> n * n then ()
    else begin
      let d_ik = Seq.index d (i * n + k) in
      lemma_fw_inner_j_len d n k i 0 d_ik;
      lemma_fw_inner_i_len (fw_inner_j d n k i 0 d_ik) n k (i + 1)
    end

let rec lemma_fw_outer_len (d: Seq.seq int) (n k: nat)
  : Lemma (ensures Seq.length (fw_outer d n k) == Seq.length d)
          (decreases (n - k))
  = if k >= n || Seq.length d <> n * n then ()
    else begin
      lemma_fw_inner_i_len d n k 0;
      lemma_fw_outer_len (fw_inner_i d n k 0) n (k + 1)
    end

open Pulse.Lib.BoundedIntegers

// ========== Main Algorithm with Complexity ==========

// Complexity bound predicate
let fw_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n * n * n

fn floyd_warshall_complexity
  (dist: array int)
  (#contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to dist contents **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      Seq.length contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _:unit
  ensures exists* contents' (cf: nat).
    A.pts_to dist contents' **
    GR.pts_to ctr cf **
    pure (
      Seq.length contents' == SZ.v n * SZ.v n /\
      contents' == fw_outer contents (SZ.v n) 0 /\
      fw_complexity_bounded cf (reveal c0) (SZ.v n)
    )
{
  let mut k : SZ.t = 0sz;

  while (!k <^ n)
  invariant exists* vk contents_k (vc : nat).
    R.pts_to k vk **
    A.pts_to dist contents_k **
    GR.pts_to ctr vc **
    pure (
      SZ.v vk <= SZ.v n /\
      Seq.length contents_k == SZ.v n * SZ.v n /\
      fw_outer contents_k (SZ.v n) (SZ.v vk) == fw_outer contents (SZ.v n) 0 /\
      // Complexity: vc - c0 == vk * n * n
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vk * SZ.v n * SZ.v n
    )
  {
    let vk = !k;
    let mut i : SZ.t = 0sz;

    while (!i <^ n)
    invariant exists* vi contents_i (vc_i : nat).
      R.pts_to i vi **
      A.pts_to dist contents_i **
      GR.pts_to ctr vc_i **
      pure (
        SZ.v vi <= SZ.v n /\
        Seq.length contents_i == SZ.v n * SZ.v n /\
        fw_outer (fw_inner_i contents_i (SZ.v n) (SZ.v vk) (SZ.v vi)) (SZ.v n) (SZ.v vk + 1)
          == fw_outer contents (SZ.v n) 0 /\
        // Complexity: vc_i - c0 == vk*n*n + vi*n
        vc_i >= reveal c0 /\
        vc_i - reveal c0 == SZ.v vk * SZ.v n * SZ.v n + SZ.v vi * SZ.v n
      )
    {
      let vi = !i;
      let mut j : SZ.t = 0sz;

      let idx_ik = vi *^ n +^ vk;
      let d_ik = A.op_Array_Access dist idx_ik;

      while (!j <^ n)
      invariant exists* vj contents_j (vc_j : nat).
        R.pts_to j vj **
        A.pts_to dist contents_j **
        GR.pts_to ctr vc_j **
        pure (
          SZ.v vj <= SZ.v n /\
          Seq.length contents_j == SZ.v n * SZ.v n /\
          fw_outer
            (fw_inner_i (fw_inner_j contents_j (SZ.v n) (SZ.v vk) (SZ.v vi) (SZ.v vj) d_ik)
                        (SZ.v n) (SZ.v vk) (SZ.v vi + 1))
            (SZ.v n) (SZ.v vk + 1)
            == fw_outer contents (SZ.v n) 0 /\
          // Complexity: vc_j - c0 == vk*n*n + vi*n + vj
          vc_j >= reveal c0 /\
          vc_j - reveal c0 == SZ.v vk * SZ.v n * SZ.v n + SZ.v vi * SZ.v n + SZ.v vj
        )
      {
        let vj = !j;

        let idx_ij = vi *^ n +^ vj;
        let idx_kj = vk *^ n +^ vj;
        let d_ij = A.op_Array_Access dist idx_ij;
        let d_kj = A.op_Array_Access dist idx_kj;
        let via_k = d_ik + d_kj;
        let new_val = (if via_k < d_ij then via_k else d_ij);
        A.op_Array_Assignment dist idx_ij new_val;

        // Count the relaxation — one ghost tick
        tick ctr;

        j := vj +^ 1sz;
      };

      i := vi +^ 1sz;
    };

    k := vk +^ 1sz;
  };

  // At exit: cf - c0 == n³
  ()
}
