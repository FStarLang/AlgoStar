(*
   Union-Find (Disjoint Sets) — Verified Pulse Implementation
   CLRS Chapter 21: union by rank with full path compression

   Single consolidated implementation:
   - make_set: initialize n-element forest
   - find_set: CLRS FIND-SET with full path compression (two-pass)
   - union: CLRS UNION by rank, returns unit

   All postconditions reference the pure specification in Spec.fst.
   NO admits. NO assumes.
*)

module CLRS.Ch21.UnionFind.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = CLRS.Ch21.UnionFind.Spec

// ========== Bridge: imperative arrays <-> pure spec ==========

// to_nat_seq and to_uf are defined in the .fsti

let to_nat_seq_index (s: Seq.seq SZ.t) (n: nat) (i: nat{i < n /\ i < Seq.length s})
  : Lemma (Seq.index (to_nat_seq s n) i == SZ.v (Seq.index s i))
  = ()

let to_nat_seq_length (s: Seq.seq SZ.t) (n: nat)
  : Lemma (Seq.length (to_nat_seq s n) == n)
  = ()

let to_nat_seq_upd (s: Seq.seq SZ.t) (n: nat{n <= Seq.length s}) (i: nat{i < n}) (v: SZ.t)
  : Lemma (to_nat_seq (Seq.upd s i v) n == Seq.upd (to_nat_seq s n) i (SZ.v v))
  = Seq.lemma_eq_intro
      (to_nat_seq (Seq.upd s i v) n)
      (Seq.upd (to_nat_seq s n) i (SZ.v v))

// Bridge: imperative parent update corresponds to spec record update
let to_uf_upd_parent (sp srank: Seq.seq SZ.t) (n: nat{n <= Seq.length sp}) (i: nat{i < n}) (v: SZ.t)
  : Lemma (to_uf (Seq.upd sp i v) srank n ==
           { (to_uf sp srank n) with Spec.parent = Seq.upd (to_uf sp srank n).Spec.parent i (SZ.v v) })
  = to_nat_seq_upd sp n i v;
    assert (to_nat_seq (Seq.upd sp i v) n == Seq.upd (to_nat_seq sp n) i (SZ.v v))

// Bridge: imperative rank update corresponds to spec record update
let to_uf_upd_rank (sp srank: Seq.seq SZ.t) (n: nat{n <= Seq.length srank}) (i: nat{i < n}) (v: SZ.t)
  : Lemma (to_uf sp (Seq.upd srank i v) n ==
           { (to_uf sp srank n) with Spec.rank = Seq.upd (to_uf sp srank n).Spec.rank i (SZ.v v) })
  = to_nat_seq_upd srank n i v

// Bridge: combined parent + rank update
let to_uf_upd_both (sp srank: Seq.seq SZ.t) (n: nat{n <= Seq.length sp /\ n <= Seq.length srank})
  (ip: nat{ip < n}) (vp: SZ.t) (ir: nat{ir < n}) (vr: SZ.t)
  : Lemma (to_uf (Seq.upd sp ip vp) (Seq.upd srank ir vr) n ==
           { Spec.parent = Seq.upd (to_uf sp srank n).Spec.parent ip (SZ.v vp);
             Spec.rank = Seq.upd (to_uf sp srank n).Spec.rank ir (SZ.v vr);
             Spec.n = n })
  = to_nat_seq_upd sp n ip vp;
    to_nat_seq_upd srank n ir vr

// ========== Imperative forest invariants (for loop termination) ==========

let well_formed (parent: Seq.seq SZ.t) (n: nat) : prop =
  n > 0 /\
  n <= Seq.length parent /\
  (forall (idx: nat). idx < n ==> SZ.v (Seq.index parent idx) < n)

let is_root_at (parent: Seq.seq SZ.t) (i: nat) : prop =
  i < Seq.length parent /\ SZ.v (Seq.index parent i) == i

let rec has_root_within (parent: Seq.seq SZ.t) (i: nat) (depth: nat)
  : Tot prop (decreases depth)
  = i < Seq.length parent /\
    (SZ.v (Seq.index parent i) == i \/
     (depth > 0 /\ has_root_within parent (SZ.v (Seq.index parent i)) (depth - 1)))

let is_forest (parent: Seq.seq SZ.t) (n: nat) : prop =
  well_formed parent n /\
  (forall (idx: nat). idx < n ==> has_root_within parent idx n)

// Weaken: more depth is always fine
let rec has_root_within_weaken (parent: Seq.seq SZ.t) (i: nat) (d d': nat)
  : Lemma (requires has_root_within parent i d /\ d' >= d)
          (ensures has_root_within parent i d')
          (decreases d)
  = if SZ.v (Seq.index parent i) = i then ()
    else has_root_within_weaken parent (SZ.v (Seq.index parent i)) (d - 1) (d' - 1)

// Setting parent[v] = root preserves has_root_within (depth + 1)
let rec upd_depth_increase
  (parent: Seq.seq SZ.t) (n: nat) (v: nat) (root_sz: SZ.t) (j: nat) (d: nat)
  : Lemma (requires well_formed parent n /\
                    v < n /\ SZ.v root_sz < n /\
                    is_root_at parent (SZ.v root_sz) /\
                    j < n /\ d <= n /\
                    has_root_within parent j d)
          (ensures has_root_within (Seq.upd parent v root_sz) j (d + 1))
          (decreases d)
  = let root = SZ.v root_sz in
    let parent' = Seq.upd parent v root_sz in
    if SZ.v (Seq.index parent j) = j then begin
      if j = v then begin
        if root = v then has_root_within_weaken parent' v 0 (d + 1)
        else begin
          assert (SZ.v (Seq.index parent' root) == root);
          has_root_within_weaken parent' v 1 (d + 1)
        end
      end
      else has_root_within_weaken parent' j 0 (d + 1)
    end
    else begin
      if j = v then begin
        if root = v then has_root_within_weaken parent' v 0 (d + 1)
        else begin
          assert (SZ.v (Seq.index parent' root) == root);
          has_root_within_weaken parent' v 1 (d + 1)
        end
      end
      else begin
        assert (SZ.v (Seq.index parent' j) == SZ.v (Seq.index parent j));
        upd_depth_increase parent n v root_sz (SZ.v (Seq.index parent j)) (d - 1)
      end
    end

// Path length for tightening
let rec path_len (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) : Tot nat (decreases fuel) =
  if fuel = 0 then 0
  else if i >= Seq.length parent then 0
  else if SZ.v (Seq.index parent i) = i then 0
  else 1 + path_len parent (SZ.v (Seq.index parent i)) (fuel - 1)

let rec path_len_le_fuel (parent: Seq.seq SZ.t) (i: nat) (fuel: nat)
  : Lemma (ensures path_len parent i fuel <= fuel) (decreases fuel)
  = if fuel = 0 then ()
    else if i >= Seq.length parent then ()
    else if SZ.v (Seq.index parent i) = i then ()
    else path_len_le_fuel parent (SZ.v (Seq.index parent i)) (fuel - 1)

let rec has_root_within_exact (parent: Seq.seq SZ.t) (i: nat) (fuel: nat)
  : Lemma (requires has_root_within parent i fuel)
          (ensures has_root_within parent i (path_len parent i fuel))
          (decreases fuel)
  = if SZ.v (Seq.index parent i) = i then ()
    else has_root_within_exact parent (SZ.v (Seq.index parent i)) (fuel - 1)

// Pigeonhole path bound
let rec path_node (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) (k: nat) : Tot nat (decreases k) =
  if k = 0 then i
  else if fuel = 0 then i
  else if i >= Seq.length parent then i
  else if SZ.v (Seq.index parent i) = i then i
  else path_node parent (SZ.v (Seq.index parent i)) (fuel - 1) (k - 1)

let rec follow (parent: Seq.seq SZ.t) (i: nat) (steps: nat) : Tot nat (decreases steps) =
  if steps = 0 then i
  else if i >= Seq.length parent then i
  else follow parent (SZ.v (Seq.index parent i)) (steps - 1)

let rec follow_split (parent: Seq.seq SZ.t) (n: nat) (i: nat) (a b: nat)
  : Lemma (requires well_formed parent n /\ i < n /\ a + b <= n)
          (ensures follow parent i (a + b) == follow parent (follow parent i a) b)
          (decreases a)
  = if a = 0 then ()
    else follow_split parent n (SZ.v (Seq.index parent i)) (a - 1) b

let rec follow_bounded (parent: Seq.seq SZ.t) (n: nat) (i: nat) (steps: nat)
  : Lemma (requires well_formed parent n /\ i < n /\ steps <= n)
          (ensures follow parent i steps < n) (decreases steps)
  = if steps = 0 then ()
    else follow_bounded parent n (SZ.v (Seq.index parent i)) (steps - 1)

let rec nonroot_cycle_false (parent: Seq.seq SZ.t) (n: nat) (v: nat) (m: pos) (d: nat)
  : Lemma (requires well_formed parent n /\ v < n /\
                    SZ.v (Seq.index parent v) <> v /\
                    follow parent v m == v /\
                    has_root_within parent v d /\ m <= n)
          (ensures False) (decreases d)
  = let p = SZ.v (Seq.index parent v) in
    assert (follow parent p (m - 1) == v);
    follow_split parent n p (m - 1) 1;
    assert (follow parent p m == p);
    if SZ.v (Seq.index parent p) = p then begin
      let rec follow_root_stays (parent: Seq.seq SZ.t) (r: nat) (k: nat)
        : Lemma (requires r < Seq.length parent /\ SZ.v (Seq.index parent r) = r)
                (ensures follow parent r k == r) (decreases k)
        = if k = 0 then () else follow_root_stays parent r (k - 1)
      in
      follow_root_stays parent p (m - 1);
      assert (v == p)
    end
    else nonroot_cycle_false parent n p m (d - 1)

let rec path_node_eq_follow (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) (k: nat)
  : Lemma (requires i < Seq.length parent /\ has_root_within parent i fuel /\ k <= path_len parent i fuel)
          (ensures path_node parent i fuel k == follow parent i k)
          (decreases k)
  = if k = 0 then ()
    else path_node_eq_follow parent (SZ.v (Seq.index parent i)) (fuel - 1) (k - 1)

let rec path_node_not_root (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) (k: nat)
  : Lemma (requires i < Seq.length parent /\ has_root_within parent i fuel /\
                    k < path_len parent i fuel)
          (ensures (let v = path_node parent i fuel k in
                    v < Seq.length parent /\ SZ.v (Seq.index parent v) <> v))
          (decreases k)
  = if k = 0 then ()
    else path_node_not_root parent (SZ.v (Seq.index parent i)) (fuel - 1) (k - 1)

let rec path_node_bounded (parent: Seq.seq SZ.t) (n: nat) (i: nat) (fuel: nat) (k: nat)
  : Lemma (requires well_formed parent n /\ i < n /\ has_root_within parent i fuel /\
                    k <= path_len parent i fuel)
          (ensures path_node parent i fuel k < n) (decreases k)
  = if k = 0 then ()
    else path_node_bounded parent n (SZ.v (Seq.index parent i)) (fuel - 1) (k - 1)

#push-options "--z3rlimit 8"
let path_len_strict_bound (parent: Seq.seq SZ.t) (n: nat) (i: nat)
  : Lemma (requires is_forest parent n /\ i < n)
          (ensures path_len parent i n < n)
  = let pl = path_len parent i n in
    path_len_le_fuel parent i n;
    if pl >= n then begin
      let mk_node (k: nat{k < pl + 1}) : FStar.Fin.under n =
        path_node_bounded parent n i n k; path_node parent i n k
      in
      let s : Seq.seq (FStar.Fin.under n) = Seq.init (pl + 1) mk_node in
      let (k1, k2) = FStar.Fin.pigeonhole #n s in
      let v = path_node parent i n k1 in
      path_node_not_root parent i n k1;
      path_node_eq_follow parent i n k1;
      path_node_eq_follow parent i n k2;
      let m = k2 - k1 in
      follow_bounded parent n i k1;
      follow_split parent n i k1 m;
      nonroot_cycle_false parent n v m n
    end
#pop-options

let has_root_within_tight (parent: Seq.seq SZ.t) (n: nat) (i: nat)
  : Lemma (requires is_forest parent n /\ i < n)
          (ensures has_root_within parent i (n - 1))
  = has_root_within_exact parent i n;
    path_len_strict_bound parent n i;
    has_root_within_weaken parent i (path_len parent i n) (n - 1)

// upd preserves is_forest
let upd_preserves_is_forest
  (parent: Seq.seq SZ.t) (n: nat) (v: nat) (root_sz: SZ.t)
  : Lemma (requires is_forest parent n /\ v < n /\ SZ.v root_sz < n /\
                    is_root_at parent (SZ.v root_sz))
          (ensures is_forest (Seq.upd parent v root_sz) n)
  = let parent' = Seq.upd parent v root_sz in
    assert (well_formed parent' n);
    let aux (idx: nat{idx < n})
      : Lemma (has_root_within parent' idx n)
      = has_root_within_tight parent n idx;
        upd_depth_increase parent n v root_sz idx (n - 1)
    in FStar.Classical.forall_intro aux

// upd a non-root to point to a root preserves all existing roots
let upd_preserves_roots
  (parent: Seq.seq SZ.t) (n: nat) (v: nat) (root_sz: SZ.t)
  : Lemma (requires is_forest parent n /\ v < n /\ SZ.v root_sz < n /\
                    is_root_at parent (SZ.v root_sz) /\ ~(is_root_at parent v))
          (ensures (forall (r: nat). r < n /\ is_root_at parent r ==>
                      is_root_at (Seq.upd parent v root_sz) r))
  = ()

// upd a root to point to a root preserves all OTHER existing roots
let upd_root_preserves_other_roots
  (parent: Seq.seq SZ.t) (n: nat) (v: nat) (root_sz: SZ.t)
  : Lemma (requires is_forest parent n /\ v < n /\ SZ.v root_sz < n /\
                    is_root_at parent (SZ.v root_sz))
          (ensures (forall (r: nat). r < n /\ r <> v /\ is_root_at parent r ==>
                      is_root_at (Seq.upd parent v root_sz) r))
  = ()

// If pure_find(f, x) == x (x is a root in the spec), then is_root_at at the imperative level
let pure_find_self_implies_root_at
  (sp srank: Seq.seq SZ.t) (n: nat) (x: nat)
  : Lemma (requires n <= Seq.length sp /\ x < n /\
                    Spec.uf_inv (to_uf sp srank n) /\
                    Spec.pure_find (to_uf sp srank n) x == x)
          (ensures is_root_at sp x)
  = Spec.pure_find_is_root (to_uf sp srank n) x;
    to_nat_seq_index sp n x

// ========== MAKE-SET ==========

// Helper: after make_set initialization, the pure spec invariant holds
let make_set_uf_inv (sp sr: Seq.seq SZ.t) (n: nat)
  : Lemma (requires
             n > 0 /\
             n <= Seq.length sp /\ n <= Seq.length sr /\
             (forall (j: nat). j < n ==> SZ.v (Seq.index sp j) == j) /\
             (forall (j: nat). j < n ==> SZ.v (Seq.index sr j) == 0))
          (ensures Spec.uf_inv (to_uf sp sr n))
  = let f = to_uf sp sr n in
    // Seq.length f.parent == n, Seq.length f.rank == n
    assert (Seq.length f.Spec.parent == n);
    assert (Seq.length f.Spec.rank == n);
    // is_valid_uf: all parents in bounds (parent[i] = i < n)
    let aux (i: nat{i < n}) : Lemma (Seq.index f.Spec.parent i < n)
      = () in FStar.Classical.forall_intro aux;
    // rank_invariant: vacuously true (all parent[i] == i, so no non-root nodes)
    let aux2 (x: nat{x < n}) : Lemma (Seq.index f.Spec.parent x == x)
      = () in FStar.Classical.forall_intro aux2

fn make_set
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  requires
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      SZ.v n > 0 /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank
    )
  ensures exists* sp sr.
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      is_forest sp (SZ.v n) /\
      Spec.uf_inv (to_uf sp sr (SZ.v n)) /\
      (forall (idx: nat). idx < SZ.v n ==> is_root_at sp idx) /\
      (forall (idx: nat). idx < SZ.v n /\ idx < Seq.length sr ==> SZ.v (Seq.index sr idx) == 0)
    )
{
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi sp sr.
    R.pts_to i vi **
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index sp j) == j) /\
      (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index sr j) == 0) /\
      SZ.v n > 0 /\
      SZ.v n <= Seq.length sp /\
      SZ.v n <= Seq.length sr
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    parent.(vi) <- vi;
    rank.(vi) <- 0sz;
    i := SZ.(vi +^ 1sz);
  };
  with vi sp sr. assert (R.pts_to i vi ** A.pts_to parent sp ** A.pts_to rank sr);
  assert pure (forall (j: nat). j < SZ.v n ==> SZ.v (Seq.index sp j) == j);
  assert pure (forall (j: nat). j < SZ.v n ==> SZ.v (Seq.index sp j) < SZ.v n);
  make_set_uf_inv sp sr (SZ.v n);
  ()
}

// ========== FIND-SET: full path compression (CLRS §21.3) ==========

// Helper: has_root_within_zero
let has_root_within_zero (parent: Seq.seq SZ.t) (i: nat)
  : Lemma (requires i < Seq.length parent /\ has_root_within parent i 0)
          (ensures SZ.v (Seq.index parent i) == i)
  = ()

// Compress path: set all nodes from x to root to point to root
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
fn compress_path
  (parent: A.array SZ.t) (x: SZ.t) (root: SZ.t) (n: SZ.t)
  (#sparent: erased (Seq.seq SZ.t))
  (#srank: erased (Seq.seq SZ.t))
  requires
    A.pts_to parent sparent **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v root < SZ.v n /\
      SZ.v n <= Seq.length sparent /\
      is_root_at sparent (SZ.v root) /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      SZ.v root == Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v x)
    )
  ensures exists* sp.
    A.pts_to parent sp **
    pure (
      Seq.length sp == Seq.length sparent /\
      SZ.v x < SZ.v n /\
      SZ.v root < SZ.v n /\
      SZ.v n <= Seq.length sp /\
      is_forest sp (SZ.v n) /\
      SZ.v (Seq.index sp (SZ.v x)) == SZ.v root /\
      SZ.v (Seq.index sp (SZ.v root)) == SZ.v root /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      Spec.uf_inv (to_uf sp srank (SZ.v n)) /\
      (forall (z: nat). z < SZ.v n ==>
        Spec.pure_find (to_uf sp srank (SZ.v n)) z ==
        Spec.pure_find (to_uf sparent srank (SZ.v n)) z)
    )
{
  let mut curr = x;
  let mut count: SZ.t = 0sz;
  while (
    let vc = !curr;
    not (vc = root) && SZ.lt !count n
  )
  invariant exists* vc vcount sp.
    R.pts_to curr vc **
    R.pts_to count vcount **
    A.pts_to parent sp **
    pure (
      SZ.v vc < SZ.v n /\
      SZ.v vcount <= SZ.v n /\
      is_forest sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      SZ.v n <= Seq.length sp /\
      is_root_at sp (SZ.v root) /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      Spec.uf_inv (to_uf sp srank (SZ.v n)) /\
      SZ.v root == Spec.pure_find (to_uf sp srank (SZ.v n)) (SZ.v vc) /\
      (forall (z: nat). z < SZ.v n ==>
        Spec.pure_find (to_uf sp srank (SZ.v n)) z ==
        Spec.pure_find (to_uf sparent srank (SZ.v n)) z)
    )
  decreases (SZ.v n - SZ.v !count)
  {
    let vc = !curr;
    with sp_pre. assert (A.pts_to parent sp_pre);
    let par = parent.(vc);
    // vc is not root, so vc is not a self-loop in the current spec forest
    to_nat_seq_index sp_pre (SZ.v n) (SZ.v vc);
    // pure_find(current, par) == pure_find(current, vc) == root
    Spec.pure_find_step (to_uf sp_pre srank (SZ.v n)) (SZ.v vc);
    // Compression: parent[vc] <- root
    parent.(vc) <- root;
    // Bridge: to_uf after upd == spec record update
    to_uf_upd_parent sp_pre srank (SZ.v n) (SZ.v vc) root;
    // Spec preservation
    Spec.compress_preserves_find_all (to_uf sp_pre srank (SZ.v n)) (SZ.v vc);
    // Structural preservation
    upd_preserves_is_forest sp_pre (SZ.v n) (SZ.v vc) root;
    curr := par;
    let c = !count;
    count := SZ.add c 1sz
  };
  let _vc_f = !curr;
  let _cnt_f = !count;
  with sp_pre2. assert (A.pts_to parent sp_pre2);
  // Final compression of x itself (harmless no-op if x == root)
  parent.(x) <- root;
  to_uf_upd_parent sp_pre2 srank (SZ.v n) (SZ.v x) root;
  Spec.compress_preserves_find_all (to_uf sp_pre2 srank (SZ.v n)) (SZ.v x);
  upd_preserves_is_forest sp_pre2 (SZ.v n) (SZ.v x) root;
  with sp_final. assert (A.pts_to parent sp_final)
}
#pop-options

// ========== FIND-SET: full path compression (CLRS §21.3) ==========

// Read-only root-finding (no path compression) for internal use
fn find_root_imp
  (#p: perm)
  (parent: A.array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (x: SZ.t)
  (n: SZ.t)
  (#srank: Ghost.erased (Seq.seq SZ.t))
  requires
    A.pts_to parent #p sparent **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v n <= Seq.length sparent /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n))
    )
  returns root: SZ.t
  ensures
    A.pts_to parent #p sparent **
    pure (
      SZ.v root < SZ.v n /\
      is_root_at sparent (SZ.v root) /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      SZ.v x < SZ.v n /\
      SZ.v root == Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v x)
    )
{
  let mut curr = x;
  let mut bound: SZ.t = 0sz;
  // Read initial parent to set up flag-based loop
  // (array reads in while conditions are incompatible with NuWhile encoding)
  let p_init = parent.(x);
  let mut go: bool = not (p_init = x);
  while (!go)
  invariant exists* vc vb vgo.
    R.pts_to curr vc **
    R.pts_to bound vb **
    R.pts_to go vgo **
    A.pts_to parent #p sparent **
    pure (
      SZ.v vc < SZ.v n /\
      SZ.v vb <= SZ.v n /\
      is_forest sparent (SZ.v n) /\
      has_root_within sparent (SZ.v vc) (SZ.v n - SZ.v vb) /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v vc) ==
        Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v x) /\
      (not vgo ==> is_root_at sparent (SZ.v vc)) /\
      (vgo ==> ~(is_root_at sparent (SZ.v vc)))
    )
  decreases (SZ.v n - SZ.v !bound)
  {
    let vc = !curr;
    let p = parent.(vc);
    to_nat_seq_index sparent (SZ.v n) (SZ.v vc);
    Spec.pure_find_step (to_uf sparent srank (SZ.v n)) (SZ.v vc);
    curr := p;
    let b = !bound;
    bound := SZ.add b 1sz;
    // Check if new position is a root
    let p2 = parent.(p);
    go := not (p2 = p)
  };
  let root = !curr;
  to_nat_seq_index sparent (SZ.v n) (SZ.v root);
  Spec.pure_find_root (to_uf sparent srank (SZ.v n)) (SZ.v root);
  root
}

// FIND-SET: two-pass (find root, then compress)
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
fn find_set
  (parent: A.array SZ.t) (x: SZ.t) (n: SZ.t)
  (#sparent: erased (Seq.seq SZ.t))
  (#srank: erased (Seq.seq SZ.t))
  requires
    A.pts_to parent sparent **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v n <= Seq.length sparent /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n))
    )
  returns root: SZ.t
  ensures exists* sp.
    A.pts_to parent sp **
    pure (
      SZ.v root < SZ.v n /\
      SZ.v x < SZ.v n /\
      Seq.length sp == Seq.length sparent /\
      SZ.v n <= Seq.length sp /\
      is_forest sp (SZ.v n) /\
      SZ.v (Seq.index sp (SZ.v x)) == SZ.v root /\
      SZ.v (Seq.index sp (SZ.v root)) == SZ.v root /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      Spec.uf_inv (to_uf sp srank (SZ.v n)) /\
      SZ.v root == Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v x) /\
      (forall (z: nat). z < SZ.v n ==>
        Spec.pure_find (to_uf sp srank (SZ.v n)) z ==
        Spec.pure_find (to_uf sparent srank (SZ.v n)) z)
    )
{
  // Pass 1: find root (read-only)
  let root = find_root_imp parent x n #srank;
  // Pass 2: compress path from x to root
  compress_path parent x root n #sparent #srank;
  root
}
#pop-options

// ========== UNION: by rank, returns unit ==========

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
fn union
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (x: SZ.t)
  (y: SZ.t)
  (n: SZ.t)
  requires
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v y < SZ.v n /\
      Seq.length srank == Seq.length sparent /\
      SZ.v n <= Seq.length sparent /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      (forall (i: nat). i < SZ.v n ==> SZ.v (Seq.index srank i) < SZ.v n)
    )
  ensures exists* sp sr.
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      is_forest sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      Spec.uf_inv (to_uf sp sr (SZ.v n)) /\
      SZ.v x < SZ.v n /\ SZ.v y < SZ.v n /\
      Spec.pure_find (to_uf sp sr (SZ.v n)) (SZ.v x) ==
        Spec.pure_find (to_uf sp sr (SZ.v n)) (SZ.v y) /\
      (forall (z: nat). z < SZ.v n ==>
        Spec.pure_find (to_uf sparent srank (SZ.v n)) z <>
          Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v x) ==>
        Spec.pure_find (to_uf sparent srank (SZ.v n)) z <>
          Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v y) ==>
        Spec.pure_find (to_uf sp sr (SZ.v n)) z ==
          Spec.pure_find (to_uf sparent srank (SZ.v n)) z) /\
      (forall (z: nat). z < SZ.v n ==>
        (Spec.pure_find (to_uf sparent srank (SZ.v n)) z ==
          Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v x) \/
         Spec.pure_find (to_uf sparent srank (SZ.v n)) z ==
          Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v y)) ==>
        Spec.pure_find (to_uf sp sr (SZ.v n)) z ==
          Spec.pure_find (to_uf sp sr (SZ.v n)) (SZ.v x)) /\
      // Rank monotonicity: output ranks >= input ranks
      (forall (i: nat). i < SZ.v n /\ i < Seq.length sr /\ i < Seq.length srank ==>
        SZ.v (Seq.index sr i) >= SZ.v (Seq.index srank i)) /\
      // Rank bound: output ranks increase by at most 1
      (forall (i: nat). i < SZ.v n /\ i < Seq.length sr /\ i < Seq.length srank ==>
        SZ.v (Seq.index sr i) <= SZ.v (Seq.index srank i) + 1)
    )
{
  // Find roots with path compression (CLRS §21.3)
  let root_x = find_set parent x n #_ #srank;
  with sp1. assert (A.pts_to parent sp1);

  let root_y = find_set parent y n #_ #srank;
  with sp2. assert (A.pts_to parent sp2);

  // Connect imperative rank reads to spec rank values
  to_nat_seq_index srank (SZ.v n) (SZ.v root_x);
  to_nat_seq_index srank (SZ.v n) (SZ.v root_y);

  if (root_x = root_y) {
    // Same root: path compression already done by find_set.
    // pure_find(sp2)(x) == root_x == root_y == pure_find(sp2)(y)
    ()
  } else {
    let rank_x = rank.(root_x);
    let rank_y = rank.(root_y);

    // Establish root_x is still a root in sp2 (for cases linking root_y -> root_x)
    Spec.pure_find_idempotent (to_uf sparent srank (SZ.v n)) (SZ.v x);
    pure_find_self_implies_root_at sp2 srank (SZ.v n) (SZ.v root_x);

    if (rank_x <^ rank_y) {
      // Link root_x -> root_y (lower rank under higher)
      parent.(root_x) <- root_y;
      upd_preserves_is_forest sp2 (SZ.v n) (SZ.v root_x) root_y;
      to_uf_upd_parent sp2 srank (SZ.v n) (SZ.v root_x) root_y;
      Spec.pure_union_preserves_inv (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
      Spec.pure_union_same_set (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
      Spec.pure_union_stability (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
      Spec.pure_union_membership_all (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
      ()
    } else {
      if (rank_x >^ rank_y) {
        // Link root_y -> root_x (lower rank under higher)
        parent.(root_y) <- root_x;
        upd_preserves_is_forest sp2 (SZ.v n) (SZ.v root_y) root_x;
        to_uf_upd_parent sp2 srank (SZ.v n) (SZ.v root_y) root_x;
        Spec.pure_union_preserves_inv (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
        Spec.pure_union_same_set (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
        Spec.pure_union_stability (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
        Spec.pure_union_membership_all (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
        ()
      } else {
        // Equal rank: link root_y -> root_x and increment rank[root_x]
        parent.(root_y) <- root_x;
        upd_preserves_is_forest sp2 (SZ.v n) (SZ.v root_y) root_x;
        let new_rank = SZ.add rank_x 1sz;
        rank.(root_x) <- new_rank;
        to_uf_upd_both sp2 srank (SZ.v n) (SZ.v root_y) root_x (SZ.v root_x) new_rank;
        Spec.pure_union_preserves_inv (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
        Spec.pure_union_same_set (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
        Spec.pure_union_stability (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
        Spec.pure_union_membership_all (to_uf sp2 srank (SZ.v n)) (SZ.v x) (SZ.v y);
        ()
      }
    }
  }
}
#pop-options
