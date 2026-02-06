module CLRS.Ch22.TopologicalSort
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
module V = Pulse.Lib.Vec

// Topological sort using Kahn's algorithm
// Input: adjacency matrix adj (n×n represented as flat array)
// Output: array containing topological order of vertices
fn topological_sort 
  (adj: A.array int) 
  (n: SZ.t)
  (#sadj: erased (Seq.seq int))
  requires 
    A.pts_to adj sadj **
    pure (
      SZ.v n > 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns output: V.vec int
  ensures exists* sout.
    A.pts_to adj sadj **
    V.pts_to output sout **
    pure (Seq.length sout == SZ.v n)
{
  // Step 1: Compute in-degrees
  let in_degree_v = V.alloc 0 n;
  V.to_array_pts_to in_degree_v;
  let in_degree = V.vec_to_array in_degree_v;
  rewrite (A.pts_to (V.vec_to_array in_degree_v) (Seq.create (SZ.v n) 0))
       as (A.pts_to in_degree (Seq.create (SZ.v n) 0));
  
  // For each vertex i
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi sin_degree.
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sin_degree == SZ.v n
    )
  {
    let vi = !i;
    
    // For each vertex j, check if edge vi->j exists
    let mut j: SZ.t = 0sz;
    while (!j <^ n)
    invariant exists* vj sin_degree.
      R.pts_to i vi **
      R.pts_to j vj **
      A.pts_to adj sadj **
      A.pts_to in_degree sin_degree **
      pure (
        SZ.v vi < SZ.v n /\
        SZ.v vj <= SZ.v n /\
        Seq.length sin_degree == SZ.v n
      )
    {
      let vj = !j;
      
      // Check if edge from vi to vj exists
      let idx = vi *^ n +^ vj;
      let edge_val = A.op_Array_Access adj idx;
      
      // If edge exists, increment in_degree[vj]
      let old_deg = A.op_Array_Access in_degree vj;
      let new_deg: int = (if edge_val <> 0 then old_deg + 1 else old_deg);
      A.op_Array_Assignment in_degree vj new_deg;
      
      j := vj +^ 1sz;
    };
    
    i := vi +^ 1sz;
  };
  
  // Step 2: Initialize queue with vertices having in-degree 0
  let queue_v = V.alloc 0sz n;
  V.to_array_pts_to queue_v;
  let queue = V.vec_to_array queue_v;
  rewrite (A.pts_to (V.vec_to_array queue_v) (Seq.create (SZ.v n) 0sz))
       as (A.pts_to queue (Seq.create (SZ.v n) 0sz));
  let mut queue_tail: SZ.t = 0sz;
  
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi vqt sin_degree squeue.
    R.pts_to i vi **
    R.pts_to queue_tail vqt **
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree **
    A.pts_to queue squeue **
    pure (
      SZ.v vi <= SZ.v n /\
      SZ.v vqt <= SZ.v vi /\
      SZ.v vqt <= SZ.v n /\
      Seq.length sin_degree == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      // All vertices in queue are valid (< n)
      (forall (k: nat). k < SZ.v vqt ==> SZ.v (Seq.index squeue k) < SZ.v n)
    )
  {
    let vi = !i;
    let deg = A.op_Array_Access in_degree vi;
    let vqt = !queue_tail;
    
    // Unconditionally write (might write garbage if deg != 0, but queue_tail won't advance)
    A.op_Array_Assignment queue vqt vi;
    
    // Conditionally advance queue_tail
    let new_vqt: SZ.t = (if deg = 0 then vqt +^ 1sz else vqt);
    queue_tail := new_vqt;
    
    i := vi +^ 1sz;
  };
  
  // Step 3: Process queue and build output
  let output_v = V.alloc 0 n;
  V.to_array_pts_to output_v;
  let output = V.vec_to_array output_v;
  rewrite (A.pts_to (V.vec_to_array output_v) (Seq.create (SZ.v n) 0))
       as (A.pts_to output (Seq.create (SZ.v n) 0));
  let mut queue_head: SZ.t = 0sz;
  let mut out_idx: SZ.t = 0sz;
  
  while (!queue_head <^ !queue_tail)
  invariant exists* vqh vqt vout sin_degree squeue soutput.
    R.pts_to queue_head vqh **
    R.pts_to queue_tail vqt **
    R.pts_to out_idx vout **
    A.pts_to adj sadj **
    A.pts_to in_degree sin_degree **
    A.pts_to queue squeue **
    A.pts_to output soutput **
    pure (
      SZ.v vqh <= SZ.v vqt /\
      SZ.v vqt <= SZ.v n /\
      SZ.v vout == SZ.v vqh /\
      SZ.v vout <= SZ.v n /\
      Seq.length sin_degree == SZ.v n /\
      Seq.length squeue == SZ.v n /\
      Seq.length soutput == SZ.v n /\
      // All vertices in queue are valid (< n)
      (forall (k: nat). k < SZ.v vqt ==> SZ.v (Seq.index squeue k) < SZ.v n)
    )
  {
    let vqh = !queue_head;
    
    // Dequeue vertex u
    let u = A.op_Array_Access queue vqh;
    
    // u must be a valid vertex - this should be provable from the fact that we only enqueue vertices < n
    // For now, we'll need to strengthen the invariants to track this
    // TODO: Add invariant that forall i < vqt. queue[i] < n
    
    // Add u to output
    let vout = !out_idx;
    let u_int = SZ.v u;  // Convert SZ.t to int
    A.op_Array_Assignment output vout u_int;
    let new_vout = vout +^ 1sz;
    out_idx := new_vout;
    queue_head := vqh +^ 1sz;
    
    // For each neighbor v of u, decrement in-degree
    let mut v: SZ.t = 0sz;
    while (!v <^ n)
    invariant exists* vv vqh_inner vqt vout_inner sin_degree squeue soutput.
      R.pts_to v vv **
      R.pts_to queue_head vqh_inner **
      R.pts_to queue_tail vqt **
      R.pts_to out_idx vout_inner **
      A.pts_to adj sadj **
      A.pts_to in_degree sin_degree **
      A.pts_to queue squeue **
      A.pts_to output soutput **
      pure (
        SZ.v u < SZ.v n /\
        SZ.v vv <= SZ.v n /\
        SZ.v vqh_inner == SZ.v vqh + 1 /\
        SZ.v vout_inner == SZ.v vqh + 1 /\
        SZ.v vqh_inner <= SZ.v vqt /\
        SZ.v vqt <= SZ.v n /\
        Seq.length sin_degree == SZ.v n /\
        Seq.length squeue == SZ.v n /\
        Seq.length soutput == SZ.v n /\
        // All vertices in queue are valid (< n)
        (forall (k: nat). k < SZ.v vqt ==> SZ.v (Seq.index squeue k) < SZ.v n)
      )
    {
      let vv = !v;
      
      // Check if edge from u to vv exists
      let idx = u *^ n +^ vv;
      let edge_val = A.op_Array_Access adj idx;
      
      // Read current state before any conditionals
      let old_deg = A.op_Array_Access in_degree vv;
      let vqt = !queue_tail;
      
      // Compute new degree
      let new_deg: int = (if edge_val <> 0 then old_deg - 1 else old_deg);
      
      // Always write new degree (might be same as old)
      A.op_Array_Assignment in_degree vv new_deg;
      
      // Determine if we should enqueue: edge exists, new degree is 0, and we have space
      let should_enqueue: bool = (edge_val <> 0 && new_deg = 0 && vqt <^ n);
      
      // Choose where to write: if should_enqueue and have space, write to vqt; otherwise write to position 0 (harmless)
      let write_idx: SZ.t = (if should_enqueue then vqt else 0sz);
      let queue_write_val: SZ.t = (if should_enqueue then vv else 0sz);
      
      // Unconditionally write (write_idx is always valid: either vqt < n, or 0)
      A.op_Array_Assignment queue write_idx queue_write_val;
      
      // Update queue_tail based on whether we enqueued
      let new_vqt: SZ.t = (if should_enqueue then vqt +^ 1sz else vqt);
      queue_tail := new_vqt;
      
      v := vv +^ 1sz;
    };
  };
  
  // Clean up temporary arrays
  with sin. assert (A.pts_to in_degree sin);
  rewrite (A.pts_to in_degree sin)
       as (A.pts_to (V.vec_to_array in_degree_v) sin);
  V.to_vec_pts_to in_degree_v;
  V.free in_degree_v;

  with sq. assert (A.pts_to queue sq);
  rewrite (A.pts_to queue sq)
       as (A.pts_to (V.vec_to_array queue_v) sq);
  V.to_vec_pts_to queue_v;
  V.free queue_v;
  
  // Convert output back to vec
  with so. assert (A.pts_to output so);
  rewrite (A.pts_to output so)
       as (A.pts_to (V.vec_to_array output_v) so);
  V.to_vec_pts_to output_v;

  output_v
}
