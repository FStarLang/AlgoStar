(*
   CLRS Chapter 23: Prim Key Invariant
   
   Safe weight accessor (swt) and key invariant predicates.
   Factored out of Prim.Impl for modular verification.
*)
module CLRS.Ch23.Prim.KeyInv

open FStar.Mul
open FStar.SizeT
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// Safe weight accessor: total function, no FStar.Mul overflow in Seq.index
let swt (ws: Seq.seq SZ.t) (n: nat{n > 0}) (u: nat{u < n}) (v: nat{v < n /\ Seq.length ws == n * n}) : nat
  = SZ.v (Seq.index ws (u * n + v))

/// Key invariant: for each non-MST vertex v, key[v] <= weight(w,v) for all MST vertices w
[@@"opaque_to_smt"]
let key_inv (ks ims ws: Seq.seq SZ.t) (n: nat) : prop =
  n > 0 /\ Seq.length ks == n /\ Seq.length ims == n /\ Seq.length ws == n * n /\
  (forall (v w: nat). v < n /\ w < n /\
    SZ.v (Seq.index ims v) <> 1 /\
    SZ.v (Seq.index ims w) = 1 /\
    swt ws n w v > 0 /\
    swt ws n w v < SZ.v (65535sz) ==>
    SZ.v (Seq.index ks v) <= swt ws n w v)

/// In-MST vertices have finite keys
[@@"opaque_to_smt"]
let ims_finite_key (ks ims: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length ks == n /\ Seq.length ims == n /\
  (forall (v: nat). v < n /\ SZ.v (Seq.index ims v) = 1 ==>
    SZ.v (Seq.index ks v) < SZ.v (65535sz))

/// Parent-in-MST predicate.
/// Avoids nested Seq.index by having parent_valid as a SEPARATE predicate
/// and using a single quantifier that relies on parent_valid being proven separately.
[@@"opaque_to_smt"]
let parent_in_mst (ks ps ims: Seq.seq SZ.t) (n source: nat) : prop =
  source < n /\ Seq.length ks == n /\ Seq.length ps == n /\ Seq.length ims == n /\
  (forall (j:nat). j < n ==> SZ.v (Seq.index ps j) < n) /\
  // For v with finite key and v <> source:
  // parent[v] < n (from parent_valid) AND ims[parent[v]] = 1
  // We encode the second part without nested Seq.index:
  // "for all v w, if v has finite key and w = parent[v], then ims[w] = 1"
  (forall (v w: nat). v < n /\ w < n /\ 
    SZ.v (Seq.index ks v) < SZ.v (65535sz) /\ v <> source /\
    w == SZ.v (Seq.index ps v) ==>
    SZ.v (Seq.index ims w) = 1)

/// Init: key_inv holds vacuously (no in-MST vertices for key_inv, 
/// only source in MST for ims_finite_key, parent_in_mst trivial)
let key_inv_init (ks ims ws: Seq.seq SZ.t) (n: nat)
  : Lemma (requires n > 0 /\ Seq.length ks == n /\ Seq.length ims == n /\ Seq.length ws == n * n /\
                    (forall (v:nat). v < n ==> SZ.v (Seq.index ims v) <> 1))
          (ensures key_inv ks ims ws n)
  = reveal_opaque (`%key_inv) (key_inv ks ims ws n)

let ims_finite_key_init (ks ims: Seq.seq SZ.t) (n source: nat)
  : Lemma (requires n > 0 /\ source < n /\ Seq.length ks == n /\ Seq.length ims == n /\
                    SZ.v (Seq.index ks source) == 0 /\
                    (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index ims v) <> 1))
          (ensures ims_finite_key ks ims n)
  = reveal_opaque (`%ims_finite_key) (ims_finite_key ks ims n)

let parent_in_mst_init (ks ps ims: Seq.seq SZ.t) (n source: nat)
  : Lemma (requires n > 0 /\ source < n /\ Seq.length ks == n /\ Seq.length ps == n /\ Seq.length ims == n /\
                    (forall (j:nat). j < n ==> SZ.v (Seq.index ps j) < n) /\
                    (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index ks v) >= SZ.v (65535sz)))
          (ensures parent_in_mst ks ps ims n source)
  = reveal_opaque (`%parent_in_mst) (parent_in_mst ks ps ims n source)

/// After update_keys: key_inv preserved because keys only decrease
let key_inv_after_update (ks_old ks_new ims ws: Seq.seq SZ.t) (n: nat)
  : Lemma (requires key_inv ks_old ims ws n /\
                    Seq.length ks_old == n /\
                    Seq.length ks_new == n /\
                    (forall (v:nat). v < n ==> SZ.v (Seq.index ks_new v) <= SZ.v (Seq.index ks_old v)))
          (ensures key_inv ks_new ims ws n)
  = reveal_opaque (`%key_inv) (key_inv ks_old ims ws n);
    reveal_opaque (`%key_inv) (key_inv ks_new ims ws n)

/// After update_keys: ims_finite_key preserved (in-MST keys unchanged)
let ims_finite_key_after_update (ks_old ks_new ims: Seq.seq SZ.t) (n: nat)
  : Lemma (requires ims_finite_key ks_old ims n /\
                    Seq.length ks_old == n /\ Seq.length ims == n /\
                    Seq.length ks_new == n /\
                    (forall (v:nat). v < n /\ SZ.v (Seq.index ims v) = 1 ==>
                      Seq.index ks_old v == Seq.index ks_new v))
          (ensures ims_finite_key ks_new ims n)
  = reveal_opaque (`%ims_finite_key) (ims_finite_key ks_old ims n);
    reveal_opaque (`%ims_finite_key) (ims_finite_key ks_new ims n)

/// Opaque predicates for update_keys output facts
[@@"opaque_to_smt"]
let ims_unchanged (ks_old ps_old ks_new ps_new ims: Seq.seq SZ.t) (n source: nat) : prop =
  Seq.length ks_old == n /\ Seq.length ps_old == n /\
  Seq.length ks_new == n /\ Seq.length ps_new == n /\ Seq.length ims == n /\
  (forall (v:nat). v < n /\ SZ.v (Seq.index ims v) = 1 /\ v <> source ==>
    Seq.index ps_old v == Seq.index ps_new v /\ Seq.index ks_old v == Seq.index ks_new v)

let ims_unchanged_at (ks_old ps_old ks_new ps_new ims: Seq.seq SZ.t) (n source v: nat)
  : Lemma (requires ims_unchanged ks_old ps_old ks_new ps_new ims n source /\
                    Seq.length ims == n /\ Seq.length ks_old == n /\ Seq.length ps_old == n /\
                    Seq.length ks_new == n /\ Seq.length ps_new == n /\
                    v < n /\ SZ.v (Seq.index ims v) = 1 /\ v <> source)
          (ensures Seq.index ps_old v == Seq.index ps_new v /\ Seq.index ks_old v == Seq.index ks_new v)
  = reveal_opaque (`%ims_unchanged) (ims_unchanged ks_old ps_old ks_new ps_new ims n source)

[@@"opaque_to_smt"]
let key_unchanged_parent_unchanged (ks_old ps_old ks_new ps_new: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length ks_old == n /\ Seq.length ps_old == n /\
  Seq.length ks_new == n /\ Seq.length ps_new == n /\
  (forall (v:nat). v < n /\ Seq.index ks_new v == Seq.index ks_old v ==>
    Seq.index ps_new v == Seq.index ps_old v)

let key_unchanged_parent_unchanged_at (ks_old ps_old ks_new ps_new: Seq.seq SZ.t) (n v: nat)
  : Lemma (requires key_unchanged_parent_unchanged ks_old ps_old ks_new ps_new n /\
                    Seq.length ks_old == n /\ Seq.length ks_new == n /\
                    Seq.length ps_old == n /\ Seq.length ps_new == n /\
                    v < n /\ Seq.index ks_new v == Seq.index ks_old v)
          (ensures Seq.index ps_new v == Seq.index ps_old v)
  = reveal_opaque (`%key_unchanged_parent_unchanged) (key_unchanged_parent_unchanged ks_old ps_old ks_new ps_new n)

[@@"opaque_to_smt"]
let key_decreased_parent_is_u (ks_old ks_new ps_new ims: Seq.seq SZ.t) (n u: nat) : prop =
  Seq.length ks_old == n /\ Seq.length ks_new == n /\ Seq.length ps_new == n /\ Seq.length ims == n /\
  (forall (v:nat). v < n /\ SZ.v (Seq.index ims v) <> 1 /\
    SZ.v (Seq.index ks_new v) < SZ.v (Seq.index ks_old v) ==>
    SZ.v (Seq.index ps_new v) == u)

let key_decreased_parent_is_u_at (ks_old ks_new ps_new ims: Seq.seq SZ.t) (n u v: nat)
  : Lemma (requires key_decreased_parent_is_u ks_old ks_new ps_new ims n u /\
                    Seq.length ks_old == n /\ Seq.length ks_new == n /\
                    Seq.length ps_new == n /\ Seq.length ims == n /\
                    v < n /\ SZ.v (Seq.index ims v) <> 1 /\
                    SZ.v (Seq.index ks_new v) < SZ.v (Seq.index ks_old v))
          (ensures SZ.v (Seq.index ps_new v) == u)
  = reveal_opaque (`%key_decreased_parent_is_u) (key_decreased_parent_is_u ks_old ks_new ps_new ims n u)

[@@"opaque_to_smt"]
let keys_only_decrease (ks_old ks_new: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length ks_old == n /\ Seq.length ks_new == n /\
  (forall (v:nat). v < n ==> SZ.v (Seq.index ks_new v) <= SZ.v (Seq.index ks_old v))

let keys_only_decrease_at (ks_old ks_new: Seq.seq SZ.t) (n v: nat)
  : Lemma (requires keys_only_decrease ks_old ks_new n /\
                    Seq.length ks_old == n /\ Seq.length ks_new == n /\ v < n)
          (ensures SZ.v (Seq.index ks_new v) <= SZ.v (Seq.index ks_old v))
  = reveal_opaque (`%keys_only_decrease) (keys_only_decrease ks_old ks_new n)

/// parent_in_mst elim: instantiate the quantifier at specific v, w
let parent_in_mst_at (ks ps ims: Seq.seq SZ.t) (n source v w: nat)
  : Lemma (requires parent_in_mst ks ps ims n source /\
                    Seq.length ks == n /\ Seq.length ps == n /\ Seq.length ims == n /\
                    v < n /\ w < n /\
                    SZ.v (Seq.index ks v) < SZ.v (65535sz) /\ v <> source /\
                    w == SZ.v (Seq.index ps v))
          (ensures SZ.v (Seq.index ims w) = 1)
  = reveal_opaque (`%parent_in_mst) (parent_in_mst ks ps ims n source)

/// After update_keys: parent_in_mst preserved
/// Uses explicit quantifier instantiation — no Z3 quantifier matching needed
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let parent_in_mst_after_update 
    (ks_old ps_old ks_new ps_new ims: Seq.seq SZ.t) (n source u: nat)
  : Lemma 
    (requires 
      parent_in_mst ks_old ps_old ims n source /\
      n > 0 /\ source < n /\ u < n /\
      Seq.length ks_old == n /\ Seq.length ps_old == n /\
      Seq.length ks_new == n /\ Seq.length ps_new == n /\ Seq.length ims == n /\
      SZ.v (Seq.index ims u) = 1 /\
      ims_unchanged ks_old ps_old ks_new ps_new ims n source /\
      key_unchanged_parent_unchanged ks_old ps_old ks_new ps_new n /\
      key_decreased_parent_is_u ks_old ks_new ps_new ims n u /\
      keys_only_decrease ks_old ks_new n /\
      (forall (v:nat). v < n ==> SZ.v (Seq.index ps_new v) < n))
    (ensures parent_in_mst ks_new ps_new ims n source)
  = reveal_opaque (`%parent_in_mst) (parent_in_mst ks_new ps_new ims n source);
    introduce forall (v w: nat). v < n /\ w < n /\
      SZ.v (Seq.index ks_new v) < SZ.v (65535sz) /\ v <> source /\
      w == SZ.v (Seq.index ps_new v) ==> SZ.v (Seq.index ims w) = 1
    with introduce _ ==> _ with _.
      if SZ.v (Seq.index ims v) = 1 then begin
        ims_unchanged_at ks_old ps_old ks_new ps_new ims n source v;
        // Now: ps_old[v] == ps_new[v] AND ks_old[v] == ks_new[v]
        // So key_old[v] = key_new[v] < infinity, and w = SZ.v (ps_new[v]) = SZ.v (ps_old[v])
        let w_old = SZ.v (Seq.index ps_old v) in
        parent_in_mst_at ks_old ps_old ims n source v w_old
      end
      else if Seq.index ks_new v = Seq.index ks_old v then begin
        key_unchanged_parent_unchanged_at ks_old ps_old ks_new ps_new n v;
        let w_old = SZ.v (Seq.index ps_old v) in
        parent_in_mst_at ks_old ps_old ims n source v w_old
      end
      else begin
        // key strictly decreased: parent = u
        keys_only_decrease_at ks_old ks_new n v;
        assert (SZ.v (Seq.index ks_new v) < SZ.v (Seq.index ks_old v));
        key_decreased_parent_is_u_at ks_old ks_new ps_new ims n u v;
        assert (w == u)
      end
#pop-options

/// After add-vertex (in_mst[u] := 1): key_inv needs new MST vertex u
/// key[v] <= weight(u,v) for non-MST v — this is what update_keys establishes
/// For OLD MST vertices w: key_inv already had key[v] <= weight(w,v)
/// So key_inv is preserved on add IF key[v] <= weight(u,v) for all non-MST v
/// (which update_keys ensures by setting key[v] = min(key[v], weight(u,v)))
let key_inv_after_add_vertex (ks ims_old ims_new ws: Seq.seq SZ.t) (n u: nat)
  : Lemma (requires key_inv ks ims_old ws n /\
                    Seq.length ks == n /\ Seq.length ims_old == n /\ Seq.length ws == n * n /\
                    n > 0 /\
                    u < n /\ Seq.length ims_new == n /\
                    SZ.v (Seq.index ims_new u) = 1 /\
                    (forall (v:nat). v < n /\ v <> u ==> Seq.index ims_old v == Seq.index ims_new v) /\
                    // key[v] <= weight(u,v) for all non-MST v with valid edges
                    (forall (v:nat). v < n /\ SZ.v (Seq.index ims_new v) <> 1 /\
                      swt ws n u v > 0 /\ swt ws n u v < SZ.v (65535sz) ==>
                      SZ.v (Seq.index ks v) <= swt ws n u v))
          (ensures key_inv ks ims_new ws n)
  = reveal_opaque (`%key_inv) (key_inv ks ims_old ws n);
    reveal_opaque (`%key_inv) (key_inv ks ims_new ws n)
