module CLRS.Ch32.KMP.Test
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch32.KMP

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// Helper: use the normalizer (not SMT) to establish pow2 16, then derive fits
let fits_for_kmp_5_3 () : Lemma (
  SZ.fits 4 /\ SZ.fits 6 /\ SZ.fits 10 /\ SZ.fits 16
) = 
  assert_norm (pow2 16 == 65536);
  SZ.fits_at_least_16 4;
  SZ.fits_at_least_16 6;
  SZ.fits_at_least_16 10;
  SZ.fits_at_least_16 16

#push-options "--z3rlimit 100"

fn test_kmp_basic ()
  requires emp
  returns _: unit
  ensures emp
{
  // Text: [0,1,0,1,0] (length 5)
  let tv = V.alloc 0 5sz;
  V.to_array_pts_to tv;
  let text_arr = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 5 0))
       as (A.pts_to text_arr (Seq.create 5 0));
  A.op_Array_Assignment text_arr 0sz 0;
  A.op_Array_Assignment text_arr 1sz 1;
  A.op_Array_Assignment text_arr 2sz 0;
  A.op_Array_Assignment text_arr 3sz 1;
  A.op_Array_Assignment text_arr 4sz 0;

  // Pattern: [0,1,0] (length 3)
  let pv = V.alloc 0 3sz;
  V.to_array_pts_to pv;
  let pattern_arr = V.vec_to_array pv;
  rewrite (A.pts_to (V.vec_to_array pv) (Seq.create 3 0))
       as (A.pts_to pattern_arr (Seq.create 3 0));
  A.op_Array_Assignment pattern_arr 0sz 0;
  A.op_Array_Assignment pattern_arr 1sz 1;
  A.op_Array_Assignment pattern_arr 2sz 0;

  // Ghost counter
  let ctr = GR.alloc #nat 0;

  // Provide fits facts  
  fits_for_kmp_5_3 ();

  // Call KMP: n=5, m=3
  let count = kmp_string_match text_arr pattern_arr 5sz 3sz ctr;

  // Clean up
  GR.free ctr;
  with st. assert (A.pts_to text_arr st);
  rewrite (A.pts_to text_arr st) as (A.pts_to (V.vec_to_array tv) st);
  V.to_vec_pts_to tv;
  V.free tv;
  with sp. assert (A.pts_to pattern_arr sp);
  rewrite (A.pts_to pattern_arr sp) as (A.pts_to (V.vec_to_array pv) sp);
  V.to_vec_pts_to pv;
  V.free pv;

  ()
}

#pop-options
