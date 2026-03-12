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
    ()
#pop-options


// ========== Core Lemma 2: Rank increase on root preserves uf_inv ==========

// Helper: Seq.upd with index reasoning
private let seq_upd_index_same (#a:Type) (s: Seq.seq a) (i: nat{i < Seq.length s}) (v: a) (j: nat{j < Seq.length s})
  : Lemma (Seq.index (Seq.upd s i v) j == (if j = i then v else Seq.index s j))
  = ()

#push-options "--z3rlimit 120 --fuel 0 --ifuel 0"
let rank_increase_on_root_preserves_uf_inv
  (stag sp srank: Seq.seq SZ.t) (n: nat) (i: nat) (new_rank: SZ.t)
  : Lemma
    (requires
      n > 0 /\ i < n /\
      n <= Seq.length stag /\ n <= Seq.length sp /\ n <= Seq.length srank /\
      SZ.v (Seq.index sp i) == i /\
      SZ.v new_rank >= SZ.v (Seq.index srank i) /\
      Spec.uf_inv (Impl.to_uf stag sp srank n))
    (ensures
      Spec.uf_inv (Impl.to_uf stag sp (Seq.upd srank i new_rank) n))
  = let s  = Impl.to_uf stag sp srank n in
    let s' = Impl.to_uf stag sp (Seq.upd srank i new_rank) n in
    to_uf_upd_rank stag sp srank n i new_rank;
    // s' has same parent, tag, n — only rank at position i differs
    assert (s'.Spec.parent == s.Spec.parent);
    assert (s'.Spec.tag == s.Spec.tag);
    assert (s'.Spec.n == s.Spec.n);
    // is_valid: tag and parent checks identical, rank length preserved
    // rank_invariant: for all x where parent[x] != x:
    //   x != i (because parent[i] = i)
    //   rank'[x] = rank[x] (unchanged)
    //   rank'[parent[x]]: if parent[x]=i then new_rank >= old >= rank[x]+1 > rank[x]
    //                      else rank[parent[x]] (unchanged, same as before)
    // Need to help Z3 with the Seq.index through Seq.upd and to_nat_seq
    let abstract_i = SZ.v (Seq.index sp i) in
    Impl.to_nat_seq_index sp n i;
    assert (Seq.index s.Spec.parent i == abstract_i);
    assert (abstract_i == i);
    // Work with concrete sequences to avoid record field indexing issues
    let rank_old = s.Spec.rank in
    let rank_new = Seq.upd rank_old i (SZ.v new_rank) in
    let parent_seq = s.Spec.parent in
    to_nat_seq_length (Seq.upd srank i new_rank) n;
    to_nat_seq_length sp n;
    to_nat_seq_length srank n;
    to_int_seq_length stag n;
    to_nat_seq_upd srank n i new_rank;
    assert (s'.Spec.rank == rank_new);
    assert (s'.Spec.parent == parent_seq);
    assert (Seq.length rank_new == n);
    assert (Seq.length rank_old == n);
    assert (Seq.length parent_seq == n);
    // rank_invariant for s': for all x, parent[x] != x ==> rank'[x] < rank'[parent[x]]
    let aux (x: nat{x < n /\ Seq.index parent_seq x <> x})
      : Lemma (Seq.index rank_new x < Seq.index rank_new (Seq.index parent_seq x))
      = let px = Seq.index parent_seq x in
        assert (px < n);
        // x != i because parent[i] = i
        Impl.to_nat_seq_index sp n i;
        assert (Seq.index parent_seq i == i);
        assert (x <> i);
        // rank'[x] = rank[x] since x != i
        assert (Seq.index rank_new x == Seq.index rank_old x);
        if px = i then begin
          // parent[x] = i, rank'[i] = new_rank >= old_rank > rank[x]
          assert (Seq.index rank_new px == SZ.v new_rank);
          Impl.to_nat_seq_index srank n i;
          assert (Seq.index rank_old i == SZ.v (Seq.index srank i));
          assert (SZ.v new_rank >= Seq.index rank_old i);
          // From original rank_invariant: rank[x] < rank[parent[x]] = rank[i]
          assert (Seq.index rank_old x < Seq.index rank_old px)
        end else begin
          // parent[x] != i, rank'[parent[x]] = rank[parent[x]]
          assert (Seq.index rank_new px == Seq.index rank_old px);
          // From original rank_invariant: rank[x] < rank[parent[x]]
          assert (Seq.index rank_old x < Seq.index rank_old px)
        end
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options


// ========== Core Lemma 3: Combined tag + rank increase on root ==========

#push-options "--z3rlimit 120 --fuel 0 --ifuel 0"
let tag_rank_increase_on_root_preserves_uf_inv
  (stag sp srank: Seq.seq SZ.t) (n: nat) (i: nat) (new_tag new_rank: SZ.t)
  : Lemma
    (requires
      n > 0 /\ i < n /\
      n <= Seq.length stag /\ n <= Seq.length sp /\ n <= Seq.length srank /\
      valid_tag (SZ.v new_tag) /\
      SZ.v (Seq.index sp i) == i /\
      SZ.v new_rank >= SZ.v (Seq.index srank i) /\
      Spec.uf_inv (Impl.to_uf stag sp srank n))
    (ensures
      Spec.uf_inv (Impl.to_uf (Seq.upd stag i new_tag) sp (Seq.upd srank i new_rank) n))
  = // First update rank (preserves uf_inv), then update tag (preserves uf_inv)
    rank_increase_on_root_preserves_uf_inv stag sp srank n i new_rank;
    tag_update_preserves_uf_inv stag sp (Seq.upd srank i new_rank) n i new_tag
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
