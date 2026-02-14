(*
   Naive String Matching with Complexity Bound

   Proves O((n-m+1)·m) comparison complexity for the naive string matching algorithm.
   Specifically: at most (n-m+1)*m character comparisons.

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each character comparison gets one ghost tick.

   Also proves functional correctness (count == count_matches_up_to).

   NO admits. NO assumes.
*)

module CLRS.Ch32.NaiveStringMatch.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

#push-options "--z3rlimit 40 --ifuel 2 --fuel 2"

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

// ========== Pure Specification (same as NaiveStringMatch.fst) ==========

let matches_at (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) : prop =
  s + Seq.length pattern <= Seq.length text /\
  (forall (j: nat). j < Seq.length pattern ==>
    Seq.index text (s + j) == Seq.index pattern j)

let rec check_match_at (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) (j: nat{j <= Seq.length pattern})
  : Tot bool (decreases (Seq.length pattern - j))
  = if j >= Seq.length pattern then true
    else if s + j >= Seq.length text then false
    else if Seq.index text (s + j) = Seq.index pattern j
         then check_match_at text pattern s (j + 1)
         else false

let matches_at_dec (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) : bool =
  s + Seq.length pattern <= Seq.length text && check_match_at text pattern s 0

let rec check_match_at_correct (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) (j: nat{j <= Seq.length pattern})
  : Lemma (requires s + Seq.length pattern <= Seq.length text)
          (ensures check_match_at text pattern s j <==>
                   (forall (k: nat). j <= k /\ k < Seq.length pattern ==>
                     Seq.index text (s + k) == Seq.index pattern k))
          (decreases (Seq.length pattern - j))
  = if j >= Seq.length pattern then ()
    else check_match_at_correct text pattern s (j + 1)

let matches_at_dec_correct (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat)
  : Lemma (requires s + Seq.length pattern <= Seq.length text)
          (ensures matches_at_dec text pattern s <==> matches_at text pattern s)
  = check_match_at_correct text pattern s 0

let rec count_matches_up_to (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (limit: nat)
  : Tot nat (decreases limit)
  = if limit = 0 then 0
    else count_matches_up_to text pattern (limit - 1) +
         (if matches_at_dec text pattern (limit - 1) then 1 else 0)

let count_matches_up_to_unfold (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (limit: nat)
  : Lemma (requires limit > 0)
          (ensures count_matches_up_to text pattern limit ==
                   count_matches_up_to text pattern (limit - 1) +
                   (if matches_at_dec text pattern (limit - 1) then 1 else 0))
  = ()

let rec count_matches_up_to_bounded (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (limit: nat)
  : Lemma (ensures count_matches_up_to text pattern limit <= limit)
          (decreases limit)
  = if limit = 0 then ()
    else count_matches_up_to_bounded text pattern (limit - 1)

// ========== Complexity bound predicate ==========
let string_match_complexity_bounded (cf c0 n m: nat) : prop =
  cf >= c0 /\ cf - c0 <= op_Multiply (n - m + 1) m

// ========== Pulse Implementation with Complexity ==========

fn naive_string_match_complexity
  (#a: eqtype)
  (#p_text: perm)
  (#p_pat: perm)
  (text: array a)
  (pattern: array a)
  (#s_text: Ghost.erased (Seq.seq a))
  (#s_pat: Ghost.erased (Seq.seq a))
  (n: SZ.t)
  (m: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s_text /\
      SZ.v m == Seq.length s_pat /\
      Seq.length s_text <= A.length text /\
      Seq.length s_pat <= A.length pattern /\
      SZ.v m > 0 /\
      SZ.v m <= SZ.v n /\
      SZ.fits (SZ.v n - SZ.v m + 2) /\
      SZ.fits (op_Multiply (SZ.v n - SZ.v m + 1) (SZ.v m))
    )
  returns result: SZ.t
  ensures exists* (cf: nat).
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    GR.pts_to ctr cf **
    pure (
      SZ.v result <= SZ.v n - SZ.v m + 1 /\
      SZ.v result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1) /\
      string_match_complexity_bounded cf (reveal c0) (SZ.v n) (SZ.v m)
    )
{
  let mut count: SZ.t = 0sz;
  let mut s: SZ.t = 0sz;

  while (!s <=^ (n -^ m))
  invariant exists* vs vcount (vc : nat).
    R.pts_to s vs **
    R.pts_to count vcount **
    GR.pts_to ctr vc **
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    pure (
      SZ.v vs <= SZ.v n - SZ.v m + 1 /\
      SZ.v vcount == count_matches_up_to s_text s_pat (SZ.v vs) /\
      SZ.v vcount <= SZ.v vs /\
      // Complexity: at most vs * m comparisons so far
      vc >= reveal c0 /\
      vc - reveal c0 <= op_Multiply (SZ.v vs) (SZ.v m)
    )
  {
    let vs = !s;
    let vcount_outer = !count;

    let mut j: SZ.t = 0sz;
    let mut all_match: bool = true;

    while (!j <^ m && !all_match)
    invariant exists* vj vall_match vcount (vc_inner : nat).
      R.pts_to s vs **
      R.pts_to count vcount **
      R.pts_to j vj **
      R.pts_to all_match vall_match **
      GR.pts_to ctr vc_inner **
      A.pts_to text #p_text s_text **
      A.pts_to pattern #p_pat s_pat **
      pure (
        SZ.v vj <= SZ.v m /\
        SZ.v vcount == SZ.v vcount_outer /\
        (vall_match == true ==> (forall (k: nat). k < SZ.v vj ==>
          Seq.index s_text (SZ.v vs + k) == Seq.index s_pat k)) /\
        (vall_match == false ==> (exists (k: nat). k < SZ.v vj /\
          Seq.index s_text (SZ.v vs + k) <> Seq.index s_pat k)) /\
        // Complexity: inner ticks track j comparisons
        vc_inner >= reveal c0 /\
        vc_inner - reveal c0 <= op_Multiply (SZ.v vs) (SZ.v m) + SZ.v vj /\
        vc_inner - reveal c0 <= op_Multiply (SZ.v vs) (SZ.v m) + SZ.v m
      )
    {
      let vj = !j;

      let text_char = text.(vs +^ vj);
      let pat_char = pattern.(vj);

      // Count the comparison — one ghost tick
      tick ctr;

      if (text_char <> pat_char) {
        all_match := false;
      };

      j := vj +^ 1sz;
    };

    let final_j = !j;
    let final_all_match = !all_match;
    let vcount_before = !count;

    matches_at_dec_correct s_text s_pat (SZ.v vs);

    if (final_j = m && final_all_match) {
      count := vcount_before +^ 1sz;
    };

    count_matches_up_to_unfold s_text s_pat (SZ.v vs + 1);
    count_matches_up_to_bounded s_text s_pat (SZ.v vs + 1);

    s := vs +^ 1sz;
  };

  // At exit: cf - c0 <= (n-m+1) * m
  let final_count = !count;
  final_count
}

#pop-options
