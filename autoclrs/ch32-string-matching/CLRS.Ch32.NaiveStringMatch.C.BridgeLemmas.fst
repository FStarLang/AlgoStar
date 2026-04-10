module CLRS.Ch32.NaiveStringMatch.C.BridgeLemmas
open CLRS.Ch32.NaiveStringMatch.Spec
open CLRS.Ch32.NaiveStringMatch.Lemmas
module Seq = FStar.Seq
module SizeT = FStar.SizeT

#push-options "--fuel 4 --z3rlimit 200"
let match_connection vt vp n m s j all_match =
  let t = unwrap_seq vt n in
  let p = unwrap_seq vp m in
  // Lift option-level match/mismatch to value-level
  let aux (k: nat{k < j}) : Lemma (Seq.index t (s + k) = Seq.index p k) =
    SizeT.fits_lte k m;
    let k_st = SizeT.uint_to_t k in
    assert (Seq.index vt (s + k) = Seq.index vp k)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  // Connect to matches_at_dec via check_match_at_correct
  check_match_at_correct t p s 0;
  if j = m then ()
  else (
    assert (j < m);
    assert (all_match = 0);
    assert (Seq.index vt (s + j) <> Seq.index vp j);
    assert (Seq.index t (s + j) <> Seq.index p j)
  )
#pop-options
