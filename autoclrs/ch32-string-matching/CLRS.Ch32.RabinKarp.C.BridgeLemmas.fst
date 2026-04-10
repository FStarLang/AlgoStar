module CLRS.Ch32.RabinKarp.C.BridgeLemmas
open CLRS.Ch32.RabinKarp.Spec
module Seq = FStar.Seq
module SizeT = FStar.SizeT

let count_matches_up_to_unfold text pattern limit = ()

let rec count_matches_up_to_bounded text pattern limit =
  if limit = 0 then ()
  else count_matches_up_to_bounded text pattern (limit - 1)

#push-options "--fuel 4 --z3rlimit 200"
let match_connection vt vp n m s j all_match =
  let t = unwrap_nat_seq vt n in
  let p = unwrap_nat_seq vp m in
  // Lift option-level equality to nat-level equality
  let aux (k: nat{k < j})
    : Lemma (Seq.index t (s + k) = Seq.index p k) =
    SizeT.fits_lte k n;
    let k_st = SizeT.uint_to_t k in
    assert (Seq.index vt (s + k) = Seq.index vp k);
    // Option equality + Some? implies unwrap_nat_val equality (congruence)
    assert (Some? (Seq.index vt (s + k)));
    assert (Some? (Seq.index vp k));
    assert (unwrap_nat_val (Seq.index vt (s + k)) = unwrap_nat_val (Seq.index vp k))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  // Connect to matches_at_dec via check_matches_at_aux_correct
  check_matches_at_aux_correct t p s 0;
  if j = m then ()
  else (
    assert (j < m);
    assert (all_match = 0);
    // Mismatch at position j: option inequality implies nat inequality
    assert (Seq.index vt (s + j) <> Seq.index vp j);
    assert (Some? (Seq.index vt (s + j)));
    assert (Some? (Seq.index vp j));
    // Get >= 0 from SizeT-quantified precondition
    SizeT.fits_lte (s + j) n;
    let sj_st = SizeT.uint_to_t (s + j) in
    assert (Int32.v (Some?.v (Seq.index vt (s + j))) >= 0);
    SizeT.fits_lte j m;
    let j_st = SizeT.uint_to_t j in
    assert (Int32.v (Some?.v (Seq.index vp j)) >= 0);
    // unwrap_nat_val on distinct Some values with non-negative Int32.v
    assert (unwrap_nat_val (Seq.index vt (s + j)) <> unwrap_nat_val (Seq.index vp j));
    assert (Seq.index t (s + j) <> Seq.index p j)
  )
#pop-options
