module CLRS.Ch23.Prim.C.BridgeLemmas

open FStar.Mul
module Seq = FStar.Seq
module SZ = FStar.SizeT
open CLRS.Ch23.Prim.Impl

let unwrap_eq_somev o = ()

let unwrap_sizet_seq_length s n = ()

let unwrap_sizet_seq_index s n i = ()

let unwrap_upd_commutes s n i v =
  Seq.lemma_eq_intro
    (unwrap_sizet_seq (Seq.upd s i (Some v)) n)
    (Seq.upd (unwrap_sizet_seq s n) i v)

let kpc_opt_init sk sp sw n source = ()

let kpc_opt_step sk sp sw n source u v_idx w_uv =
  unwrap_upd_commutes sk n (SZ.v v_idx) w_uv;
  unwrap_upd_commutes sp n (SZ.v v_idx) u

let kpc_opt_write_source_key sk sp sw n source new_key =
  unwrap_upd_commutes sk n source new_key

let kpc_opt_write_source_parent sk sp sw n source new_parent =
  unwrap_upd_commutes sp n source new_parent

#push-options "--z3rlimit 20"
let prim_correct_assembly sk sp sw n source = ()
#pop-options

/// SZ.t → nat quantifier bridge: for any v:nat < SZ.v n, construct
/// j = SZ.uint_to_t v to instantiate the SZ.t quantifier.
#push-options "--z3rlimit 40"
let keys_bounded_nat sk n =
  let n' = SZ.v n in
  let aux (v:(i:nat{i < n' /\ i < Seq.length sk}))
    : Lemma (SZ.v (unwrap_sz_val (Seq.index sk v)) <= SZ.v infinity) =
    let j : SZ.t = SZ.uint_to_t v in
    assert (Some? (Seq.index sk (SZ.v j)));
    ()
  in
  Classical.forall_intro aux

let parents_valid_nat sp n =
  let n' = SZ.v n in
  let aux (v:(i:nat{i < n' /\ i < Seq.length sp}))
    : Lemma (SZ.v (unwrap_sz_val (Seq.index sp v)) < SZ.v n) =
    let j : SZ.t = SZ.uint_to_t v in
    assert (Some? (Seq.index sp (SZ.v j)));
    ()
  in
  Classical.forall_intro aux
#pop-options
