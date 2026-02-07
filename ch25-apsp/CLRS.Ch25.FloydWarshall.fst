module CLRS.Ch25.FloydWarshall
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

#set-options "--z3rlimit 20"

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// Sentinel value for "infinity" (no edge)
let inf : int = 1000000

(*** Pure imperative-mirroring specification ***)

// fw_inner_j: process columns j..n-1 for row i with intermediate vertex k
// d_ik is cached (read once before the j-loop in the imperative code)
let rec fw_inner_j (d: Seq.seq int) (n k i j: nat) (d_ik: int) 
  : Tot (Seq.seq int) (decreases (n - j)) =
  if j >= n || i >= n || k >= n || Seq.length d <> n * n then d
  else
    let d_ij = Seq.index d (i * n + j) in
    let d_kj = Seq.index d (k * n + j) in
    let via_k = d_ik + d_kj in
    let new_val = if via_k < d_ij then via_k else d_ij in
    fw_inner_j (Seq.upd d (i * n + j) new_val) n k i (j + 1) d_ik

// fw_inner_i: process rows i..n-1 for intermediate vertex k
let rec fw_inner_i (d: Seq.seq int) (n k i: nat) 
  : Tot (Seq.seq int) (decreases (n - i)) =
  if i >= n || k >= n || Seq.length d <> n * n then d
  else
    let d_ik = Seq.index d (i * n + k) in
    fw_inner_i (fw_inner_j d n k i 0 d_ik) n k (i + 1)

// fw_outer: process intermediate vertices k..n-1
let rec fw_outer (d: Seq.seq int) (n k: nat) 
  : Tot (Seq.seq int) (decreases (n - k)) =
  if k >= n || Seq.length d <> n * n then d
  else fw_outer (fw_inner_i d n k 0) n (k + 1)

// Length preservation lemmas
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

fn floyd_warshall
  (dist: array int)
  (#contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires 
    A.pts_to dist contents **
    pure (
      SZ.v n > 0 /\
      Seq.length contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _:unit
  ensures exists* contents'. 
    A.pts_to dist contents' **
    pure (
      Seq.length contents' == SZ.v n * SZ.v n /\
      // Functional correctness: output == pure Floyd-Warshall computation
      contents' == fw_outer contents (SZ.v n) 0
    )
{
  let mut k : SZ.t = 0sz;
  
  while (!k <^ n)
  invariant exists* vk contents_k.
    R.pts_to k vk **
    A.pts_to dist contents_k **
    pure (
      SZ.v vk <= SZ.v n /\
      Seq.length contents_k == SZ.v n * SZ.v n /\
      // Remaining work: processing k..n-1 from current state = processing 0..n-1 from initial
      fw_outer contents_k (SZ.v n) (SZ.v vk) == fw_outer contents (SZ.v n) 0
    )
  {
    let vk = !k;
    let mut i : SZ.t = 0sz;
    
    while (!i <^ n)
    invariant exists* vi contents_i.
      R.pts_to i vi **
      A.pts_to dist contents_i **
      pure (
        SZ.v vi <= SZ.v n /\
        Seq.length contents_i == SZ.v n * SZ.v n /\
        // Remaining i-work then remaining k-work = total
        fw_outer (fw_inner_i contents_i (SZ.v n) (SZ.v vk) (SZ.v vi)) (SZ.v n) (SZ.v vk + 1) 
          == fw_outer contents (SZ.v n) 0
      )
    {
      let vi = !i;
      let mut j : SZ.t = 0sz;
      
      // Read d_ik once (cached for entire j-loop, matching pure spec)
      let idx_ik = vi *^ n +^ vk;
      let d_ik = A.op_Array_Access dist idx_ik;
      
      while (!j <^ n)
      invariant exists* vj contents_j.
        R.pts_to j vj **
        A.pts_to dist contents_j **
        pure (
          SZ.v vj <= SZ.v n /\
          Seq.length contents_j == SZ.v n * SZ.v n /\
          // Remaining j-work then remaining i-work then remaining k-work = total
          fw_outer 
            (fw_inner_i (fw_inner_j contents_j (SZ.v n) (SZ.v vk) (SZ.v vi) (SZ.v vj) d_ik)
                        (SZ.v n) (SZ.v vk) (SZ.v vi + 1))
            (SZ.v n) (SZ.v vk + 1)
            == fw_outer contents (SZ.v n) 0
        )
      {
        let vj = !j;
        
        // Compute indices
        let idx_ij = vi *^ n +^ vj;
        let idx_kj = vk *^ n +^ vj;
        
        // Read values
        let d_ij = A.op_Array_Access dist idx_ij;
        let d_kj = A.op_Array_Access dist idx_kj;
        
        // Compute new value unconditionally
        let via_k = d_ik + d_kj;
        let new_val = (if via_k < d_ij then via_k else d_ij);
        
        // Write unconditionally (no conditional writes)
        A.op_Array_Assignment dist idx_ij new_val;
        
        j := vj +^ 1sz;
      };
      
      i := vi +^ 1sz;
    };
    
    k := vk +^ 1sz;
  }
}
