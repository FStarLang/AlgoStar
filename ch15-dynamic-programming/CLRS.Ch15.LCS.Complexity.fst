(*
   LCS with Complexity Bound

   Proves O(m·n) complexity for the longest common subsequence DP algorithm.
   Specifically: exactly (m+1)*(n+1) cell evaluations (including base cases).

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each DP cell evaluation gets one ghost tick.

   Also proves functional correctness (result == lcs_length x y m n).

   NO admits. NO assumes.
*)

module CLRS.Ch15.LCS.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.Vec
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
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

// ========== Pure Specification (same as LCS.fst) ==========

let rec lcs_length (x y: Seq.seq int) (i j: nat) : Tot int (decreases i + j) =
  if i = 0 || j = 0 then 0
  else if i <= Seq.length x && j <= Seq.length y &&
          Seq.index x (i - 1) = Seq.index y (j - 1) then
    1 + lcs_length x y (i - 1) (j - 1)
  else
    let l1 = lcs_length x y (i - 1) j in
    let l2 = lcs_length x y i (j - 1) in
    if l1 >= l2 then l1 else l2

let tbl_idx (i j: nat) (n1: nat) : nat = op_Multiply i n1 + j

let lcs_table_correct (x y: Seq.seq int) (tbl: Seq.seq int) (m n: nat) (i j: nat) : prop =
  let n1 = n + 1 in
  Seq.length tbl == op_Multiply (m + 1) n1 /\
  i <= m + 1 /\ j <= n + 1 /\
  (forall (r c: nat). (r < i \/ (r == i /\ c < j)) ==> r <= m ==> c <= n ==>
    Seq.index tbl (op_Multiply r n1 + c) == lcs_length x y r c)

#push-options "--z3rlimit 20"
let lcs_table_update_preserves (x y: Seq.seq int) (tbl: Seq.seq int) (m n i j: nat) (v: int)
  : Lemma
    (requires
      lcs_table_correct x y tbl m n i j /\
      i <= m /\ j <= n /\
      v == lcs_length x y i j)
    (ensures (
      let idx = op_Multiply i (n + 1) + j in
      let tbl' = Seq.upd tbl idx v in
      lcs_table_correct x y tbl' m n i (j + 1)))
  = let n1 = n + 1 in
    let idx = op_Multiply i n1 + j in
    let tbl' = Seq.upd tbl idx v in
    assert (forall (r c: nat). ((r < i \/ (r == i /\ c < j + 1)) /\ r <= m /\ c <= n) ==>
      (let idx2 = op_Multiply r n1 + c in
       Seq.index tbl' idx2 == lcs_length x y r c))
#pop-options

let lcs_table_next_row (x y: Seq.seq int) (tbl: Seq.seq int) (m n i: nat)
  : Lemma
    (requires lcs_table_correct x y tbl m n i (n + 1) /\ i <= m)
    (ensures lcs_table_correct x y tbl m n (i + 1) 0)
  = ()

let lcs_step_correct (x y: Seq.seq int) (tbl: Seq.seq int) (m n i j: nat) (value: int)
  : Lemma
    (requires
      i <= m /\ j <= n /\
      m == Seq.length x /\ n == Seq.length y /\
      lcs_table_correct x y tbl m n i j /\
      (i = 0 \/ j = 0 ==> value == 0) /\
      (i > 0 /\ j > 0 ==> (
        let n1 = n + 1 in
        let val_diag = Seq.index tbl (op_Multiply (i - 1) n1 + (j - 1)) in
        let val_up = Seq.index tbl (op_Multiply (i - 1) n1 + j) in
        let val_left = Seq.index tbl (op_Multiply i n1 + (j - 1)) in
        let xi = Seq.index x (i - 1) in
        let yj = Seq.index y (j - 1) in
        value == (if xi = yj then val_diag + 1
                  else if val_up >= val_left then val_up
                  else val_left))))
    (ensures value == lcs_length x y i j)
  = if i = 0 || j = 0 then ()
    else ()

// ========== Helper Lemmas ==========

let lemma_index_in_bounds (i j m n: nat)
  : Lemma (requires i <= m /\ j <= n)
          (ensures op_Multiply i (n + 1) + j < op_Multiply (m + 1) (n + 1))
  = ()

let lemma_table_size_positive (m n: nat)
  : Lemma (op_Multiply (m + 1) (n + 1) > 0)
  = ()

open Pulse.Lib.BoundedIntegers

// Complexity bound predicate
let lcs_complexity_bounded (cf c0 m n: nat) : prop =
  cf >= c0 /\ cf - c0 == op_Multiply (m + 1) (n + 1)

// ========== Main Implementation with Complexity ==========

fn lcs_complexity
  (#px #py: perm)
  (x: A.array int)
  (y: A.array int)
  (m: SZ.t)
  (n: SZ.t)
  (#sx #sy: erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to x #px sx **
    A.pts_to y #py sy **
    GR.pts_to ctr c0 **
    pure (
      SZ.v m == Seq.length sx /\
      SZ.v m == A.length x /\
      SZ.v n == Seq.length sy /\
      SZ.v n == A.length y /\
      SZ.v m > 0 /\ SZ.v n > 0 /\
      SZ.fits (op_Multiply (SZ.v m + 1) (SZ.v n + 1))
    )
  returns result: int
  ensures exists* (cf: nat).
    A.pts_to x #px sx **
    A.pts_to y #py sy **
    GR.pts_to ctr cf **
    pure (
      result == lcs_length sx sy (SZ.v m) (SZ.v n) /\
      lcs_complexity_bounded cf (reveal c0) (SZ.v m) (SZ.v n)
    )
{
  let m_plus_1 = m + 1sz;
  let n_plus_1 = n + 1sz;
  let table_size = m_plus_1 *^ n_plus_1;
  lemma_table_size_positive (SZ.v m) (SZ.v n);
  let table = V.alloc 0 table_size;
  let mut i: SZ.t = 0sz;

  while (!i <=^ m)
  invariant exists* vi stable (vc : nat).
    R.pts_to i vi **
    V.pts_to table stable **
    GR.pts_to ctr vc **
    A.pts_to x #px sx **
    A.pts_to y #py sy **
    pure (
      SZ.v vi <= SZ.v m + 1 /\
      Seq.length stable == op_Multiply (SZ.v m + 1) (SZ.v n + 1) /\
      V.length table == Seq.length stable /\
      lcs_table_correct sx sy stable (SZ.v m) (SZ.v n) (SZ.v vi) 0 /\
      // Complexity: vc == c0 + vi * (n+1)
      vc >= reveal c0 /\
      vc - reveal c0 == op_Multiply (SZ.v vi) (SZ.v n + 1)
    )
  {
    let vi = !i;
    let mut j: SZ.t = 0sz;

    while (!j <=^ n)
    invariant exists* vj stable_inner (vc_inner : nat).
      R.pts_to i vi **
      R.pts_to j vj **
      V.pts_to table stable_inner **
      GR.pts_to ctr vc_inner **
      A.pts_to x #px sx **
      A.pts_to y #py sy **
      pure (
        SZ.v vi <= SZ.v m /\
        SZ.v vj <= SZ.v n + 1 /\
        Seq.length stable_inner == op_Multiply (SZ.v m + 1) (SZ.v n + 1) /\
        V.length table == Seq.length stable_inner /\
        lcs_table_correct sx sy stable_inner (SZ.v m) (SZ.v n) (SZ.v vi) (SZ.v vj) /\
        // Complexity: vc == c0 + vi*(n+1) + vj
        vc_inner >= reveal c0 /\
        vc_inner - reveal c0 == op_Multiply (SZ.v vi) (SZ.v n + 1) + SZ.v vj
      )
    {
      let vj = !j;
      with s_before. assert (V.pts_to table s_before);
      let idx = vi *^ (n + 1sz) + vj;
      lemma_index_in_bounds (SZ.v vi) (SZ.v vj) (SZ.v m) (SZ.v n);

      let safe_vi_m1: SZ.t = (if vi >^ 0sz then vi - 1sz else vi);
      let safe_vj_m1: SZ.t = (if vj >^ 0sz then vj - 1sz else vj);
      lemma_index_in_bounds (SZ.v safe_vi_m1) (SZ.v safe_vj_m1) (SZ.v m) (SZ.v n);
      lemma_index_in_bounds (SZ.v safe_vi_m1) (SZ.v vj) (SZ.v m) (SZ.v n);
      lemma_index_in_bounds (SZ.v vi) (SZ.v safe_vj_m1) (SZ.v m) (SZ.v n);

      let idx_diag = safe_vi_m1 *^ (n + 1sz) + safe_vj_m1;
      let idx_up = safe_vi_m1 *^ (n + 1sz) + vj;
      let idx_left = vi *^ (n + 1sz) + safe_vj_m1;
      let val_diag = V.op_Array_Access table idx_diag;
      let val_up = V.op_Array_Access table idx_up;
      let val_left = V.op_Array_Access table idx_left;
      let xi = A.op_Array_Access x safe_vi_m1;
      let yj = A.op_Array_Access y safe_vj_m1;

      let value_to_store: int =
        (if vi = 0sz || vj = 0sz then 0
         else if xi = yj then val_diag + 1
         else if val_up >= val_left then val_up
         else val_left);

      lcs_step_correct sx sy s_before (SZ.v m) (SZ.v n) (SZ.v vi) (SZ.v vj) value_to_store;
      V.op_Array_Assignment table idx value_to_store;
      with s_after. assert (V.pts_to table s_after);
      lcs_table_update_preserves sx sy s_before (SZ.v m) (SZ.v n) (SZ.v vi) (SZ.v vj) value_to_store;
      assert (pure (Seq.equal s_after (Seq.upd s_before (SZ.v idx) value_to_store)));

      // Count the cell evaluation — one ghost tick
      tick ctr;

      j := vj + 1sz;
    };

    with s_row_done. assert (V.pts_to table s_row_done);
    lcs_table_next_row sx sy s_row_done (SZ.v m) (SZ.v n) (SZ.v vi);
    i := vi + 1sz;
  };

  let result_idx = m *^ (n + 1sz) + n;
  lemma_index_in_bounds (SZ.v m) (SZ.v n) (SZ.v m) (SZ.v n);
  let result = V.op_Array_Access table result_idx;
  V.free table;
  result
}
