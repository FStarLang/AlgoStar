(*
   Spec validation test for Matrix Chain Multiplication (CLRS Â§15.2)

   Input: dims = [10, 30, 5, 60], n = 3 (three matrices)
   Expected: mc_result [10,30,5,60] 3 = 4500
     Optimal parenthesization: (A1*A2)*A3 = 10*30*5 + 10*5*60 = 4500

   What is proven:
   1. The precondition of matrix_chain_order is satisfiable for a concrete input.
   2. The postcondition is precise: result == 4500.
   3. No admits, no assumes.
   4. Runtime check: returns bool (true iff result == 4500), proven true.
*)

module CLRS.Ch15.MatrixChain.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch15.MatrixChain.Impl
open CLRS.Ch15.MatrixChain.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

let mc_expected ()
  : Lemma (mc_result (Seq.seq_of_list [10; 30; 5; 60]) 3 == 4500)
  = assert_norm (mc_result (Seq.seq_of_list [10; 30; 5; 60]) 3 == 4500)

let mc_pre_satisfiable ()
  : Lemma
    (ensures SZ.v 3sz > 0 /\
             SZ.fits (op_Multiply (SZ.v 3sz) (SZ.v 3sz)))
  = assert_norm (SZ.v 3sz > 0 /\
                 SZ.fits (op_Multiply (SZ.v 3sz) (SZ.v 3sz)))

#push-options "--z3rlimit 10"

fn test_matrix_chain ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let dv = V.alloc 10 4sz;
  V.to_array_pts_to dv;
  let dims = V.vec_to_array dv;
  rewrite (A.pts_to (V.vec_to_array dv) (Seq.create 4 10))
       as (A.pts_to dims (Seq.create 4 10));
  A.pts_to_len dims;
  assert (pure (A.length dims == SZ.v 4sz));

  dims.(0sz) <- 10;
  dims.(1sz) <- 30;
  dims.(2sz) <- 5;
  dims.(3sz) <- 60;

  mc_pre_satisfiable ();

  let ctr = GR.alloc #nat 0;
  let result = matrix_chain_order dims 3sz ctr;

  mc_expected ();
  assert (pure (result == 4500));

  // Runtime check that survives extraction to C
  let pass = (result = 4500);

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;

  with s1. assert (A.pts_to dims s1);
  rewrite (A.pts_to dims s1) as (A.pts_to (V.vec_to_array dv) s1);
  V.to_vec_pts_to dv;
  V.free dv;

  pass
}

#pop-options
