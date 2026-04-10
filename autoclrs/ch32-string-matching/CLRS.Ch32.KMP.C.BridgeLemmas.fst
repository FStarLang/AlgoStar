module CLRS.Ch32.KMP.C.BridgeLemmas
open CLRS.Ch32.KMP.PureDefs
open CLRS.Ch32.KMP.Spec
module Seq = FStar.Seq
module SizeT = FStar.SizeT

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

let follow_fail_step pattern pi k c =
  pi_val_bounds pattern pi (k - 1);
  ()

let is_max_prefix_below_init text pattern n m =
  assert (matched_prefix_at text pattern 0 0);
  assert (forall (k:nat). matched_prefix_at text pattern 0 k /\ k < m ==> k <= 0)

#push-options "--z3rlimit 80"
let kmp_extend_connection pattern pi q_init q_final c m =
  ()
#pop-options

let unwrap_seq_index_lemma s m q = ()

let count_finish vt vp n m =
  let t = unwrap_int_seq vt n in
  let p = unwrap_int_seq vp m in
  assert (Seq.length t == n);
  assert (Seq.length p == m);
  count_before_eq_spec t p n m

#pop-options
