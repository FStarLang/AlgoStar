module CLRS.Ch25.FloydWarshall
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

// Sentinel value for "infinity" (no edge)
let inf : int = 1000000

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
    pure (Seq.length contents' == SZ.v n * SZ.v n)
{
  let mut k : SZ.t = 0sz;
  
  while (!k <^ n)
  invariant exists* vk contents_k.
    R.pts_to k vk **
    A.pts_to dist contents_k **
    pure (
      SZ.v vk <= SZ.v n /\
      Seq.length contents_k == SZ.v n * SZ.v n
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
        Seq.length contents_i == SZ.v n * SZ.v n
      )
    {
      let vi = !i;
      let mut j : SZ.t = 0sz;
      
      // Compute idx_ik = i * n + k once per i iteration
      let idx_ik = vi *^ n +^ vk;
      let d_ik = A.op_Array_Access dist idx_ik;
      
      while (!j <^ n)
      invariant exists* vj contents_j.
        R.pts_to j vj **
        A.pts_to dist contents_j **
        pure (
          SZ.v vj <= SZ.v n /\
          Seq.length contents_j == SZ.v n * SZ.v n
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
