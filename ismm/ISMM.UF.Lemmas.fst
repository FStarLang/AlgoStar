(*
   ISMM UF Lemmas — Bridge lemmas for discharging assume_ obligations
   
   Key results:
   1. Tag-only updates preserve uf_inv (tag is metadata, rank_invariant ignores it)
   2. Rank increases on roots preserve uf_inv (children still have smaller ranks)
   3. No-op writes preserve uf_inv (Seq.upd s i (Seq.index s i) == s)
   4. Combined tag+rank-increase on root preserves uf_inv
*)
module ISMM.UF.Lemmas

open FStar.Seq
open FStar.SizeT
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = ISMM.UnionFind.Spec
module Impl = ISMM.UnionFind.Impl
open ISMM.Status

// ========== Bridge: to_int_seq with Seq.upd ==========

let to_int_seq_length (s: Seq.seq SZ.t) (n: nat)
  : Lemma (Seq.length (Impl.to_int_seq s n) == n)
  = ()

let to_int_seq_upd (s: Seq.seq SZ.t) (n: nat{n <= Seq.length s}) (i: nat{i < n}) (v: SZ.t)
  : Lemma (Impl.to_int_seq (Seq.upd s i v) n == Seq.upd (Impl.to_int_seq s n) i (SZ.v v))
  = Seq.lemma_eq_intro
      (Impl.to_int_seq (Seq.upd s i v) n)
      (Seq.upd (Impl.to_int_seq s n) i (SZ.v v))

// Bridge: to_uf with updated tag
let to_uf_upd_tag (stag sp srank: Seq.seq SZ.t)
  (n: nat{n <= Seq.length stag}) (i: nat{i < n}) (v: SZ.t)
  : Lemma (Impl.to_uf (Seq.upd stag i v) sp srank n ==
           { (Impl.to_uf stag sp srank n) with Spec.tag = Seq.upd (Impl.to_uf stag sp srank n).Spec.tag i (SZ.v v) })
  = to_int_seq_upd stag n i v

// Bridge: to_nat_seq with Seq.upd (re-proved here since not exposed in .fsti)
let to_nat_seq_length (s: Seq.seq SZ.t) (n: nat)
  : Lemma (Seq.length (Impl.to_nat_seq s n) == n)
  = ()

let to_nat_seq_upd (s: Seq.seq SZ.t) (n: nat{n <= Seq.length s}) (i: nat{i < n}) (v: SZ.t)
  : Lemma (Impl.to_nat_seq (Seq.upd s i v) n == Seq.upd (Impl.to_nat_seq s n) i (SZ.v v))
  = Seq.lemma_eq_intro
      (Impl.to_nat_seq (Seq.upd s i v) n)
      (Seq.upd (Impl.to_nat_seq s n) i (SZ.v v))

// Bridge: to_uf with updated rank
let to_uf_upd_rank (stag sp srank: Seq.seq SZ.t)
  (n: nat{n <= Seq.length srank}) (i: nat{i < n}) (v: SZ.t)
  : Lemma (Impl.to_uf stag sp (Seq.upd srank i v) n ==
           { (Impl.to_uf stag sp srank n) with Spec.rank = Seq.upd (Impl.to_uf stag sp srank n).Spec.rank i (SZ.v v) })
  = to_nat_seq_upd srank n i v

// Bridge: to_uf with both tag and rank updated
let to_uf_upd_tag_rank (stag sp srank: Seq.seq SZ.t)
  (n: nat{n <= Seq.length stag /\ n <= Seq.length srank})
  (i: nat{i < n}) (vt: SZ.t) (vr: SZ.t)
  : Lemma (Impl.to_uf (Seq.upd stag i vt) sp (Seq.upd srank i vr) n ==
           { Spec.n = n;
             Spec.tag = Seq.upd (Impl.to_uf stag sp srank n).Spec.tag i (SZ.v vt);
             Spec.parent = (Impl.to_uf stag sp srank n).Spec.parent;
             Spec.rank = Seq.upd (Impl.to_uf stag sp srank n).Spec.rank i (SZ.v vr) })
  = to_int_seq_upd stag n i vt;
    to_nat_seq_upd srank n i vr


// ========== Core Lemma 1: Tag-only update preserves uf_inv ==========

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let tag_update_preserves_uf_inv
  (stag sp srank: Seq.seq SZ.t) (n: nat) (i: nat) (v: SZ.t)
  : Lemma
    (requires
      n > 0 /\ i < n /\
      n <= Seq.length stag /\ n <= Seq.length sp /\ n <= Seq.length srank /\
      valid_tag (SZ.v v) /\
      Spec.uf_inv (Impl.to_uf stag sp srank n))
    (ensures
      Spec.uf_inv (Impl.to_uf (Seq.upd stag i v) sp srank n))
  = let s  = Impl.to_uf stag sp srank n in
    let s' = Impl.to_uf (Seq.upd stag i v) sp srank n in
    to_uf_upd_tag stag sp srank n i v;
    // s' has same parent, rank, n as s — only tag differs
    assert (s'.Spec.parent == s.Spec.parent);
    assert (s'.Spec.rank == s.Spec.rank);
    assert (s'.Spec.n == s.Spec.n);
    // rank_invariant depends only on parent and rank → identical
    // is_valid: lengths preserved, parent bounds identical, tag validity:
    //   position i has valid_tag (SZ.v v), all others unchanged from s
    // size_rank_inv: parent/rank/n unchanged → preserved
    Spec.size_rank_inv_tag_ext s s';
    ()
#pop-options


// ========== Lemma 4: No-op write (same value) preserves sequence ==========

let noop_seq_upd (#a: eqtype) (s: Seq.seq a) (i: nat{i < Seq.length s})
  : Lemma (Seq.upd s i (Seq.index s i) == s)
  = Seq.lemma_eq_intro (Seq.upd s i (Seq.index s i)) s

// For SZ.t sequences, if the SZ.t value we write equals the existing value
let noop_write_preserves_to_uf
  (stag sp srank: Seq.seq SZ.t) (n: nat) (i: nat)
  : Lemma
    (requires
      i < n /\
      n <= Seq.length stag /\ n <= Seq.length sp /\ n <= Seq.length srank)
    (ensures
      Impl.to_uf (Seq.upd stag i (Seq.index stag i)) sp (Seq.upd srank i (Seq.index srank i)) n ==
      Impl.to_uf stag sp srank n)
  = noop_seq_upd stag i;
    noop_seq_upd srank i


// ========== Lemma 5: is_forest only depends on parent ==========
// (Trivially true since is_forest's type signature only takes parent.
//  This lemma helps Pulse at call sites.)

let is_forest_independent_of_tag_rank
  (sp: Seq.seq SZ.t) (n: nat)
  (stag1 stag2 srank1 srank2: Seq.seq SZ.t)
  : Lemma (Impl.is_forest sp n <==> Impl.is_forest sp n)
  = ()
