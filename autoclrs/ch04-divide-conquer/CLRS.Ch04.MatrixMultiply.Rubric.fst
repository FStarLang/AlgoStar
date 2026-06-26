(*
   CLRS Chapter 4: square matrix multiplication as an instance of the
   shared divide-and-conquer complexity rubric.
*)

module CLRS.Ch04.MatrixMultiply.Rubric
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open CLRS.Common.Complexity.DivideConquer.Class

module A = Pulse.Lib.Array
module DC = CLRS.Common.Complexity.DivideConquer.Class
module MR = Pulse.Lib.MonotonicGhostRef
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SZ = FStar.SizeT

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"

noeq
type square_matrices (a:Type0) = {
  sm_left: A.array a;
  sm_right: A.array a;
  sm_out: A.array a;
  sm_left_perm: perm;
  sm_right_perm: perm;
}

let owns (a:Type0) (m:square_matrices a) (sa sb sc:Seq.seq a) : slprop =
  A.pts_to m.sm_left #m.sm_left_perm sa **
  A.pts_to m.sm_right #m.sm_right_perm sb **
  A.pts_to m.sm_out sc

let index_bounds_lemma (n: nat{n > 0}) (i j k: nat) : Lemma
  (requires i < n /\ j < n /\ k < n)
  (ensures DC.flat_index n i k < n * n /\
           DC.flat_index n k j < n * n /\
           DC.flat_index n i j < n * n) =
  ()

fn matrix_multiply_poly
  (a: Type0)
  (#pa #pb: perm)
  (ma: A.array a)
  (mb: A.array a)
  (mc: A.array a)
  (n: SZ.t)
  (ctr: DC.ticks_t)
  (#ops: erased (DC.semiring a))
  (zero: a)
  (iadd: DC.instrumented_binary_op a ops.sr_add ctr)
  (imul: DC.instrumented_binary_op a ops.sr_mul ctr)
  (#sa: Ghost.erased (Seq.seq a))
  (#sb: Ghost.erased (Seq.seq a))
  (#sc: Ghost.erased (Seq.seq a))
  (#c0: erased nat)
  requires
    A.pts_to ma #pa sa **
    A.pts_to mb #pb sb **
    A.pts_to mc sc **
    MR.pts_to ctr #1.0R c0 **
    pure (
      SZ.v n > 0 /\
      zero == ops.sr_zero /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length sa == SZ.v n * SZ.v n /\
      Seq.length sb == SZ.v n * SZ.v n /\
      Seq.length sc == SZ.v n * SZ.v n
    )
  returns _: unit
  ensures exists* (sc': Seq.seq a) (ticks: nat).
    A.pts_to ma #pa sa **
    A.pts_to mb #pb sb **
    A.pts_to mc sc' **
    MR.pts_to ctr #1.0R ticks **
    pure (DC.mat_mul_correct ops sa sb sc' (SZ.v n) /\
          ticks <= reveal c0 + DC.matrix_multiply_bound (SZ.v n))
{
  let mut row: SZ.t = 0sz;

  while (!row <^ n)
  invariant exists* vi sc_i (vc : nat).
    R.pts_to row vi **
    A.pts_to ma #pa sa **
    A.pts_to mb #pb sb **
    A.pts_to mc sc_i **
    MR.pts_to ctr #1.0R vc **
    pure (
      zero == ops.sr_zero /\
      SZ.v vi <= SZ.v n /\
      Seq.length sc_i == SZ.v n * SZ.v n /\
      DC.mat_mul_partial_ij ops sa sb sc_i (SZ.v n) (SZ.v vi) 0 /\
      vc == reveal c0 + 2 * (SZ.v vi * SZ.v n * SZ.v n)
    )
  decreases (SZ.v n - SZ.v !row)
  {
    let vi = !row;

    let mut j: SZ.t = 0sz;

    while (!j <^ n)
    invariant exists* vj sc_ij (vc_ij : nat).
      R.pts_to row vi **
      R.pts_to j vj **
      A.pts_to ma #pa sa **
      A.pts_to mb #pb sb **
      A.pts_to mc sc_ij **
      MR.pts_to ctr #1.0R vc_ij **
      pure (
        zero == ops.sr_zero /\
        SZ.v vi < SZ.v n /\
        SZ.v vj <= SZ.v n /\
        Seq.length sc_ij == SZ.v n * SZ.v n /\
        DC.mat_mul_partial_ij ops sa sb sc_ij (SZ.v n) (SZ.v vi) (SZ.v vj) /\
        vc_ij == reveal c0 + 2 * (SZ.v vi * SZ.v n * SZ.v n + SZ.v vj * SZ.v n)
      )
    decreases (SZ.v n - SZ.v !j)
    {
      let vj = !j;

      index_bounds_lemma (SZ.v n) (SZ.v vi) (SZ.v vj) 0;

      assert pure (SZ.fits (SZ.v vi * SZ.v n + SZ.v vj));
      let idx_c = vi *^ n +^ vj;
      assert pure (SZ.v idx_c < SZ.v n * SZ.v n);

      A.op_Array_Assignment mc idx_c zero;

      let mut k: SZ.t = 0sz;

      while (!k <^ n)
      invariant exists* vk sc_ijk (vc_ijk : nat).
        R.pts_to row vi **
        R.pts_to j vj **
        R.pts_to k vk **
        A.pts_to ma #pa sa **
        A.pts_to mb #pb sb **
        A.pts_to mc sc_ijk **
        MR.pts_to ctr #1.0R vc_ijk **
        pure (
          zero == ops.sr_zero /\
          SZ.v vi < SZ.v n /\
          SZ.v vj < SZ.v n /\
          SZ.v vk <= SZ.v n /\
          Seq.length sc_ijk == SZ.v n * SZ.v n /\
          SZ.v idx_c == DC.flat_index (SZ.v n) (SZ.v vi) (SZ.v vj) /\
          SZ.v idx_c < SZ.v n * SZ.v n /\
          DC.mat_mul_partial_k ops sa sb sc_ijk (SZ.v n) (SZ.v vi) (SZ.v vj) (SZ.v vk) /\
          DC.mat_mul_partial_ij ops sa sb sc_ijk (SZ.v n) (SZ.v vi) (SZ.v vj) /\
          vc_ijk == reveal c0 +
            2 * (SZ.v vi * SZ.v n * SZ.v n + SZ.v vj * SZ.v n + SZ.v vk)
        )
      decreases (SZ.v n - SZ.v !k)
      {
        let vk = !k;

        assert pure (SZ.v vk < SZ.v n);

        index_bounds_lemma (SZ.v n) (SZ.v vi) (SZ.v vj) (SZ.v vk);

        assert pure (SZ.fits (SZ.v vi * SZ.v n + SZ.v vk));
        let idx_a = vi *^ n +^ vk;

        assert pure (SZ.fits (SZ.v vk * SZ.v n + SZ.v vj));
        let idx_b = vk *^ n +^ vj;

        let a_val = A.op_Array_Access ma idx_a;
        let b_val = A.op_Array_Access mb idx_b;
        let c_val = A.op_Array_Access mc idx_c;

        let prod = imul a_val b_val;
        let new_val = iadd c_val prod;

        A.op_Array_Assignment mc idx_c new_val;

        k := vk +^ 1sz;
      };

      j := vj +^ 1sz;
    };

    row := vi +^ 1sz;
  };

  with sc_final ticks. assert (A.pts_to mc sc_final ** MR.pts_to ctr #1.0R ticks);
  assert (pure (DC.mat_mul_correct ops sa sb sc_final (SZ.v n)));
  assert (pure (ticks == reveal c0 + DC.matrix_multiply_bound (SZ.v n)));
  assert (pure (ticks <= reveal c0 + DC.matrix_multiply_bound (SZ.v n)));
  ()
}

fn matrix_multiply_poly_instance
  (a: Type0)
  (m: square_matrices a)
  (n: SZ.t)
  (ctr: DC.ticks_t)
  (#ops: erased (DC.semiring a))
  (zero: a)
  (iadd: DC.instrumented_binary_op a ops.sr_add ctr)
  (imul: DC.instrumented_binary_op a ops.sr_mul ctr)
  (#sa: Ghost.erased (Seq.seq a))
  (#sb: Ghost.erased (Seq.seq a))
  (#sc: Ghost.erased (Seq.seq a))
  (#c0: erased nat)
  requires
    owns a m sa sb sc **
    MR.pts_to ctr #1.0R c0 **
    pure (
      SZ.v n > 0 /\
      zero == ops.sr_zero /\
      SZ.fits (SZ.v n * SZ.v n) /\
      DC.matrix_lengths sa sb sc (SZ.v n))
  returns _:unit
  ensures exists* (sc': Seq.seq a) (ticks: nat).
    owns a m sa sb sc' **
    MR.pts_to ctr #1.0R ticks **
    pure (DC.mat_mul_correct ops sa sb sc' (SZ.v n) /\
          ticks <= reveal c0 + DC.matrix_multiply_bound (SZ.v n))
{
  unfold (owns a m sa sb sc);
  DC.matrix_lengths_elim sa sb sc (SZ.v n);
  matrix_multiply_poly
    a
    #m.sm_left_perm
    #m.sm_right_perm
    m.sm_left
    m.sm_right
    m.sm_out
    n
    ctr
    #ops
    zero
    iadd
    imul
    #sa
    #sb
    #sc
    #c0;
  with sc' ticks. assert (A.pts_to m.sm_out sc' ** MR.pts_to ctr #1.0R ticks);
  fold (owns a m sa sb sc');
  ()
}

instance matrix_multiply_square :
  DC.square_matrix_multiply square_matrices owns DC.matrix_multiply_bound
=
  Pulse.Lib.Core.slprop_equivs ();
  {
    multiply = matrix_multiply_poly_instance
  }

#pop-options
