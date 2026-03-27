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

/// Safe weight accessor: total function, returns 0 for out-of-bounds
let swt (ws: Seq.seq SZ.t) (n: nat) (u v: nat) : nat
  = if n > 0 && u < n && v < n && Seq.length ws = n * n && u * n + v < Seq.length ws
    then SZ.v (Seq.index ws (u * n + v))
    else 0

/// Key invariant: for each non-MST vertex v, key[v] <= weight(w,v) for all MST vertices w
[@@"opaque_to_smt"]
let key_inv (ks ims ws: Seq.seq SZ.t) (n: nat) : prop =
  n > 0 /\ Seq.length ks == n /\ Seq.length ims == n /\ Seq.length ws == n * n /\
  (forall (v w: nat). v < n /\ w < n /\
    SZ.v (Seq.index ims v) <> 1 /\
    SZ.v (Seq.index ims w) = 1 /\
    w * n + v < n * n /\
    SZ.v (Seq.index ws (w * n + v)) > 0 /\
    SZ.v (Seq.index ws (w * n + v)) < SZ.v (65535sz) ==>
    SZ.v (Seq.index ks v) <= SZ.v (Seq.index ws (w * n + v)))

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

/// Bundle all 4 update_keys progress predicates into one opaque atom.
/// Used in the Pulse update_keys loop invariant to keep VC small.
[@@"opaque_to_smt"]
let update_progress (ks_old ps_old ks_cur ps_cur ims: Seq.seq SZ.t) (n source u: nat) : prop =
  ims_unchanged ks_old ps_old ks_cur ps_cur ims n source /\
  key_unchanged_parent_unchanged ks_old ps_old ks_cur ps_cur n /\
  key_decreased_parent_is_u ks_old ks_cur ps_cur ims n u /\
  keys_only_decrease ks_old ks_cur n

let update_progress_init (ks ps ims: Seq.seq SZ.t) (n source u: nat)
  : Lemma (requires Seq.length ks == n /\ Seq.length ps == n /\ Seq.length ims == n /\
                    n > 0 /\ source < n /\ u < n)
          (ensures update_progress ks ps ks ps ims n source u)
  = reveal_opaque (`%update_progress) (update_progress ks ps ks ps ims n source u);
    reveal_opaque (`%ims_unchanged) (ims_unchanged ks ps ks ps ims n source);
    reveal_opaque (`%key_unchanged_parent_unchanged) (key_unchanged_parent_unchanged ks ps ks ps n);
    reveal_opaque (`%key_decreased_parent_is_u) (key_decreased_parent_is_u ks ks ps ims n u);
    reveal_opaque (`%keys_only_decrease) (keys_only_decrease ks ks n)

#push-options "--z3rlimit 50"
let update_progress_step
    (ks_old ps_old ks_cur ps_cur ims: Seq.seq SZ.t) (n source u i: nat)
    (new_k new_p: SZ.t) (should_update: bool)
  : Lemma
    (requires
      update_progress ks_old ps_old ks_cur ps_cur ims n source u /\
      Seq.length ks_cur == n /\ Seq.length ps_cur == n /\
      Seq.length ks_old == n /\ Seq.length ps_old == n /\
      Seq.length ims == n /\ n > 0 /\ source < n /\ u < n /\ i < n /\
      (should_update ==> SZ.v (Seq.index ims i) <> 1 /\
        SZ.v new_k < SZ.v (Seq.index ks_cur i) /\ SZ.v new_p == u) /\
      (~should_update ==> new_k == Seq.index ks_cur i /\ new_p == Seq.index ps_cur i))
    (ensures update_progress ks_old ps_old (Seq.upd ks_cur i new_k) (Seq.upd ps_cur i new_p) ims n source u)
  = reveal_opaque (`%update_progress) (update_progress ks_old ps_old ks_cur ps_cur ims n source u);
    reveal_opaque (`%update_progress) (update_progress ks_old ps_old (Seq.upd ks_cur i new_k) (Seq.upd ps_cur i new_p) ims n source u);
    reveal_opaque (`%ims_unchanged) (ims_unchanged ks_old ps_old ks_cur ps_cur ims n source);
    reveal_opaque (`%ims_unchanged) (ims_unchanged ks_old ps_old (Seq.upd ks_cur i new_k) (Seq.upd ps_cur i new_p) ims n source);
    reveal_opaque (`%key_unchanged_parent_unchanged) (key_unchanged_parent_unchanged ks_old ps_old ks_cur ps_cur n);
    reveal_opaque (`%key_unchanged_parent_unchanged) (key_unchanged_parent_unchanged ks_old ps_old (Seq.upd ks_cur i new_k) (Seq.upd ps_cur i new_p) n);
    reveal_opaque (`%key_decreased_parent_is_u) (key_decreased_parent_is_u ks_old ks_cur ps_cur ims n u);
    reveal_opaque (`%key_decreased_parent_is_u) (key_decreased_parent_is_u ks_old (Seq.upd ks_cur i new_k) (Seq.upd ps_cur i new_p) ims n u);
    reveal_opaque (`%keys_only_decrease) (keys_only_decrease ks_old ks_cur n);
    reveal_opaque (`%keys_only_decrease) (keys_only_decrease ks_old (Seq.upd ks_cur i new_k) n)
#pop-options

let update_progress_elim (ks_old ps_old ks_new ps_new ims: Seq.seq SZ.t) (n source u: nat)
  : Lemma (requires update_progress ks_old ps_old ks_new ps_new ims n source u)
          (ensures ims_unchanged ks_old ps_old ks_new ps_new ims n source /\
                   key_unchanged_parent_unchanged ks_old ps_old ks_new ps_new n /\
                   key_decreased_parent_is_u ks_old ks_new ps_new ims n u /\
                   keys_only_decrease ks_old ks_new n)
  = reveal_opaque (`%update_progress) (update_progress ks_old ps_old ks_new ps_new ims n source u)

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
                      u * n + v < n * n /\
                      SZ.v (Seq.index ws (u * n + v)) > 0 /\ SZ.v (Seq.index ws (u * n + v)) < SZ.v (65535sz) ==>
                      SZ.v (Seq.index ks v) <= SZ.v (Seq.index ws (u * n + v))))
          (ensures key_inv ks ims_new ws n)
  = reveal_opaque (`%key_inv) (key_inv ks ims_old ws n);
    reveal_opaque (`%key_inv) (key_inv ks ims_new ws n)

/// Derive bare "in-MST → parent in MST" forall from parent_in_mst + ims_finite_key.
/// Needed by prim_safe_add_vertex which expects this as a precondition.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let parent_in_mst_for_ims
    (ks ps ims: Seq.seq SZ.t) (n source: nat)
  : Lemma 
    (requires parent_in_mst ks ps ims n source /\ ims_finite_key ks ims n /\
             Seq.length ks == n /\ Seq.length ps == n /\ Seq.length ims == n /\
             n > 0 /\ source < n)
    (ensures forall (v:nat). v < n /\ v <> source /\ SZ.v (Seq.index ims v) = 1 ==>
               SZ.v (Seq.index ps v) < n /\
               SZ.v (Seq.index ims (SZ.v (Seq.index ps v))) = 1)
  = reveal_opaque (`%parent_in_mst) (parent_in_mst ks ps ims n source);
    reveal_opaque (`%ims_finite_key) (ims_finite_key ks ims n)
#pop-options

/// Extract bare key_inv forall from opaque key_inv.
/// Needed by prim_safe_add_vertex.
let key_inv_bare (ks ims ws: Seq.seq SZ.t) (n: nat)
  : Lemma
    (requires key_inv ks ims ws n /\
              Seq.length ks == n /\ Seq.length ims == n /\ Seq.length ws == n * n /\ n > 0)
    (ensures forall (v w: nat). v < n /\ w < n /\
      SZ.v (Seq.index ims v) <> 1 /\ SZ.v (Seq.index ims w) = 1 /\
      w * n + v < n * n /\
      SZ.v (Seq.index ws (w * n + v)) > 0 /\ SZ.v (Seq.index ws (w * n + v)) < SZ.v (65535sz) ==>
      SZ.v (Seq.index ks v) <= SZ.v (Seq.index ws (w * n + v)))
  = reveal_opaque (`%key_inv) (key_inv ks ims ws n)

/// Same as key_inv_bare but with raw Seq.index (for prim_safe_add_vertex compatibility)
#push-options "--z3rlimit 50"
let key_inv_bare_raw (ks ims ws: Seq.seq SZ.t) (n: nat)
  : Lemma
    (requires key_inv ks ims ws n /\
              Seq.length ks == n /\ Seq.length ims == n /\ Seq.length ws == n * n /\ n > 0)
    (ensures forall (v w: nat). v < n /\ w < n /\
      SZ.v (Seq.index ims v) <> 1 /\ SZ.v (Seq.index ims w) = 1 /\
      w * n + v < n * n /\
      SZ.v (Seq.index ws (w * n + v)) > 0 /\ SZ.v (Seq.index ws (w * n + v)) < SZ.v (65535sz) ==>
      SZ.v (Seq.index ks v) <= SZ.v (Seq.index ws (w * n + v)))
  = reveal_opaque (`%key_inv) (key_inv ks ims ws n)
#pop-options

/// Extract bare ims_unchanged forall (for prim_safe_update_non_mst)
let ims_unchanged_bare (ks_old ps_old ks_new ps_new ims: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires ims_unchanged ks_old ps_old ks_new ps_new ims n source /\
              Seq.length ks_old == n /\ Seq.length ps_old == n /\
              Seq.length ks_new == n /\ Seq.length ps_new == n /\ Seq.length ims == n)
    (ensures forall (v:nat). v < n /\ SZ.v (Seq.index ims v) = 1 /\ v <> source ==>
      Seq.index ps_old v == Seq.index ps_new v /\ Seq.index ks_old v == Seq.index ks_new v)
  = reveal_opaque (`%ims_unchanged) (ims_unchanged ks_old ps_old ks_new ps_new ims n source)

/// Extract parent-in-MST for finite-key vertices (used by mst_edges_noRepeats_add)
#push-options "--z3rlimit 50"
let parent_in_mst_finite_key (ks ps ims: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires parent_in_mst ks ps ims n source /\
             Seq.length ks == n /\ Seq.length ps == n /\ Seq.length ims == n /\
             n > 0 /\ source < n)
    (ensures forall (v:nat). v < n /\ SZ.v (Seq.index ks v) < SZ.v (65535sz) /\ v <> source ==>
               SZ.v (Seq.index ps v) < n /\
               SZ.v (Seq.index ims (SZ.v (Seq.index ps v))) = 1)
  = reveal_opaque (`%parent_in_mst) (parent_in_mst ks ps ims n source)
#pop-options

(*** Combined prim_inv_bundle — used by Prim.Impl to define prim_inv ***)

[@@"opaque_to_smt"]
let prim_inv_bundle (safe kpc: prop) (ks ps ims ws: Seq.seq SZ.t) (n source: nat) : prop =
  safe /\ kpc /\
  n > 0 /\ source < n /\
  Seq.length ks == n /\ Seq.length ps == n /\
  Seq.length ims == n /\ Seq.length ws == n * n /\
  Defs.valid_weights ws n /\ Defs.symmetric_weights ws n /\
  Defs.parent_valid ps n /\ Defs.all_keys_bounded ks /\
  SZ.v (Seq.index ks source) == 0 /\
  Defs.no_zero_edges ws n /\
  key_inv ks ims ws n /\
  ims_finite_key ks ims n /\
  parent_in_mst ks ps ims n source

#push-options "--z3rlimit 50"
let prim_inv_bundle_intro (safe kpc: prop) (ks ps ims ws: Seq.seq SZ.t) (n source: nat)
  : Lemma (requires safe /\ kpc /\ n > 0 /\ source < n /\
      Seq.length ks == n /\ Seq.length ps == n /\
      Seq.length ims == n /\ Seq.length ws == n * n /\
      Defs.valid_weights ws n /\ Defs.symmetric_weights ws n /\
      Defs.parent_valid ps n /\ Defs.all_keys_bounded ks /\
      SZ.v (Seq.index ks source) == 0 /\ Defs.no_zero_edges ws n /\
      key_inv ks ims ws n /\ ims_finite_key ks ims n /\
      parent_in_mst ks ps ims n source)
    (ensures prim_inv_bundle safe kpc ks ps ims ws n source)
  = reveal_opaque (`%prim_inv_bundle) (prim_inv_bundle safe kpc ks ps ims ws n source)

let prim_inv_bundle_elim (safe kpc: prop) (ks ps ims ws: Seq.seq SZ.t) (n source: nat)
  : Lemma (requires prim_inv_bundle safe kpc ks ps ims ws n source)
    (ensures safe /\ kpc /\ n > 0 /\ source < n /\
      Seq.length ks == n /\ Seq.length ps == n /\
      Seq.length ims == n /\ Seq.length ws == n * n /\
      Defs.valid_weights ws n /\ Defs.symmetric_weights ws n /\
      Defs.parent_valid ps n /\ Defs.all_keys_bounded ks /\
      SZ.v (Seq.index ks source) == 0 /\ Defs.no_zero_edges ws n /\
      key_inv ks ims ws n /\ ims_finite_key ks ims n /\
      parent_in_mst ks ps ims n source)
  = reveal_opaque (`%prim_inv_bundle) (prim_inv_bundle safe kpc ks ps ims ws n source)
#pop-options

/// Rebuild prim_inv_bundle after update_keys.
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let prim_inv_bundle_after_update
    (safe_old kpc_old safe_new kpc_new: prop)
    (ks_old ps_old ks_new ps_new ims ws: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires
      prim_inv_bundle safe_old kpc_old ks_old ps_old ims ws n source /\
      safe_new /\ kpc_new /\
      n > 0 /\ source < n /\ u < n /\ Seq.length ims == n /\
      SZ.v (Seq.index ims u) = 1 /\
      Seq.length ks_new == n /\ Seq.length ps_new == n /\
      Defs.all_keys_bounded ks_new /\ Defs.parent_valid ps_new n /\
      SZ.v (Seq.index ks_new source) == 0 /\
      update_progress ks_old ps_old ks_new ps_new ims n source u)
    (ensures prim_inv_bundle safe_new kpc_new ks_new ps_new ims ws n source)
  = prim_inv_bundle_elim safe_old kpc_old ks_old ps_old ims ws n source;
    update_progress_elim ks_old ps_old ks_new ps_new ims n source u;
    // Extract bare foralls for the _after_update lemmas that need them
    ims_unchanged_bare ks_old ps_old ks_new ps_new ims n source;
    reveal_opaque (`%keys_only_decrease) (keys_only_decrease ks_old ks_new n);
    key_inv_after_update ks_old ks_new ims ws n;
    ims_finite_key_after_update ks_old ks_new ims n;
    parent_in_mst_after_update ks_old ps_old ks_new ps_new ims n source u;
    prim_inv_bundle_intro safe_new kpc_new ks_new ps_new ims ws n source
#pop-options

(*** Full prim_loop_state rebuild — all reasoning in KeyInv ***)

/// Opaque loop state: prim_inv_bundle + noRepeats + basics.
/// Matches prim_loop_state from Prim.Impl.
[@@"opaque_to_smt"]
let loop_state
    (inv noRepeats: prop)
    (ks ps ims ws: Seq.seq SZ.t) (n source: nat) : prop =
  n > 0 /\ source < n /\
  Seq.length ks == n /\ Seq.length ps == n /\
  Seq.length ims == n /\ Seq.length ws == n * n /\
  n * n < pow2 64 /\ SZ.fits_u64 /\
  inv /\ noRepeats /\
  SZ.v (Seq.index ks source) == 0 /\
  Defs.all_keys_bounded ks /\
  Defs.parent_valid ps n /\
  (forall (j:nat). j < n ==> SZ.v (Seq.index ims j) = 0 \/ SZ.v (Seq.index ims j) = 1)

#push-options "--z3rlimit 50"
let loop_state_intro (inv noRepeats: prop)
    (ks ps ims ws: Seq.seq SZ.t) (n source: nat)
  : Lemma (requires n > 0 /\ source < n /\
      Seq.length ks == n /\ Seq.length ps == n /\
      Seq.length ims == n /\ Seq.length ws == n * n /\
      n * n < pow2 64 /\ SZ.fits_u64 /\
      inv /\ noRepeats /\
      SZ.v (Seq.index ks source) == 0 /\
      Defs.all_keys_bounded ks /\ Defs.parent_valid ps n /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index ims j) = 0 \/ SZ.v (Seq.index ims j) = 1))
    (ensures loop_state inv noRepeats ks ps ims ws n source)
  = reveal_opaque (`%loop_state) (loop_state inv noRepeats ks ps ims ws n source)

let loop_state_elim (inv noRepeats: prop)
    (ks ps ims ws: Seq.seq SZ.t) (n source: nat)
  : Lemma (requires loop_state inv noRepeats ks ps ims ws n source)
    (ensures n > 0 /\ source < n /\
      Seq.length ks == n /\ Seq.length ps == n /\
      Seq.length ims == n /\ Seq.length ws == n * n /\
      n * n < pow2 64 /\ SZ.fits_u64 /\
      inv /\ noRepeats /\
      SZ.v (Seq.index ks source) == 0 /\
      Defs.all_keys_bounded ks /\ Defs.parent_valid ps n /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index ims j) = 0 \/ SZ.v (Seq.index ims j) = 1))
  = reveal_opaque (`%loop_state) (loop_state inv noRepeats ks ps ims ws n source)
#pop-options

/// Full loop_state rebuild after update_keys.
/// Takes: old loop_state + update_progress + new safe + new kpc + new noRepeats.
/// All reasoning (key_inv, ims_finite_key, parent_in_mst) done here in KeyInv context.
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let loop_state_after_update
    (inv_old noRepeats_old safe_old kpc_old: prop)
    (safe_new kpc_new noRepeats_new: prop)
    (ks_old ps_old ks_new ps_new ims ws: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires
      loop_state inv_old noRepeats_old ks_old ps_old ims ws n source /\
      // inv_old = prim_inv_bundle safe_old kpc_old ... (caller instantiates)
      inv_old == prim_inv_bundle safe_old kpc_old ks_old ps_old ims ws n source /\
      // New state
      safe_new /\ kpc_new /\ noRepeats_new /\
      n > 0 /\ source < n /\
      Seq.length ks_new == n /\ Seq.length ps_new == n /\
      Seq.length ims == n /\
      Defs.all_keys_bounded ks_new /\ Defs.parent_valid ps_new n /\
      SZ.v (Seq.index ks_new source) == 0 /\
      u < n /\ SZ.v (Seq.index ims u) = 1 /\
      update_progress ks_old ps_old ks_new ps_new ims n source u)
    (ensures loop_state
      (prim_inv_bundle safe_new kpc_new ks_new ps_new ims ws n source)
      noRepeats_new ks_new ps_new ims ws n source)
  = loop_state_elim inv_old noRepeats_old ks_old ps_old ims ws n source;
    prim_inv_bundle_after_update safe_old kpc_old safe_new kpc_new
      ks_old ps_old ks_new ps_new ims ws n source u;
    loop_state_intro
      (prim_inv_bundle safe_new kpc_new ks_new ps_new ims ws n source)
      noRepeats_new ks_new ps_new ims ws n source
#pop-options

(*** keys_bounded_by_u — tracks key[v] <= weight(u,v) for non-MST v ***)

/// After update_keys: key[v] <= weight(u,v) for all non-MST v with valid weight(u,v).
/// This is needed by key_inv_after_add_vertex to extend key_inv to new ims.
[@@"opaque_to_smt"]
let keys_bounded_by_u (ks ws ims: Seq.seq SZ.t) (n u: nat) : prop =
  Seq.length ks == n /\ Seq.length ws == n * n /\ Seq.length ims == n /\ u < n /\
  (forall (v:nat). v < n /\ SZ.v (Seq.index ims v) <> 1 /\
    u * n + v < n * n /\
    SZ.v (Seq.index ws (u * n + v)) > 0 /\
    SZ.v (Seq.index ws (u * n + v)) < SZ.v (65535sz) ==>
    SZ.v (Seq.index ks v) <= SZ.v (Seq.index ws (u * n + v)))

let keys_bounded_by_u_elim (ks ws ims: Seq.seq SZ.t) (n u: nat)
  : Lemma (requires keys_bounded_by_u ks ws ims n u /\
                    Seq.length ks == n /\ Seq.length ws == n * n /\ Seq.length ims == n /\ u < n)
          (ensures forall (v:nat). v < n /\ SZ.v (Seq.index ims v) <> 1 /\
            u * n + v < n * n /\
            SZ.v (Seq.index ws (u * n + v)) > 0 /\
            SZ.v (Seq.index ws (u * n + v)) < SZ.v (65535sz) ==>
            SZ.v (Seq.index ks v) <= SZ.v (Seq.index ws (u * n + v)))
  = reveal_opaque (`%keys_bounded_by_u) (keys_bounded_by_u ks ws ims n u)

/// Step: after processing vertex i in update_keys loop.
#push-options "--z3rlimit 50"
let keys_bounded_by_u_step
    (ks ws ims: Seq.seq SZ.t) (n u i: nat)
    (new_k: SZ.t) (should_update: bool)
  : Lemma
    (requires
      keys_bounded_by_u ks ws ims n u /\
      Seq.length ks == n /\ Seq.length ws == n * n /\ Seq.length ims == n /\
      u < n /\ i < n /\
      (should_update ==>
        u * n + i < n * n /\
        SZ.v new_k == SZ.v (Seq.index ws (u * n + i))) /\
      (~should_update ==> new_k == Seq.index ks i /\
        (SZ.v (Seq.index ims i) <> 1 /\ u * n + i < n * n /\
         SZ.v (Seq.index ws (u * n + i)) > 0 /\
         SZ.v (Seq.index ws (u * n + i)) < SZ.v (65535sz) ==>
         SZ.v (Seq.index ks i) <= SZ.v (Seq.index ws (u * n + i)))))
    (ensures keys_bounded_by_u (Seq.upd ks i new_k) ws ims n u)
  = reveal_opaque (`%keys_bounded_by_u) (keys_bounded_by_u ks ws ims n u);
    reveal_opaque (`%keys_bounded_by_u) (keys_bounded_by_u (Seq.upd ks i new_k) ws ims n u)
#pop-options

/// Init: vacuously true (no v satisfies the antecedent if all non-MST keys are infinity)
/// But more practically, we initialize from the fact that the initial keys satisfy this
/// if they're all >= weight(u,v) (which is NOT guaranteed at init).
/// So we use a dummy init that requires the condition explicitly.
let keys_bounded_by_u_intro (ks ws ims: Seq.seq SZ.t) (n u: nat)
  : Lemma (requires Seq.length ks == n /\ Seq.length ws == n * n /\ Seq.length ims == n /\ u < n /\
                    (forall (v:nat). v < n /\ SZ.v (Seq.index ims v) <> 1 /\
                      u * n + v < n * n /\
                      SZ.v (Seq.index ws (u * n + v)) > 0 /\
                      SZ.v (Seq.index ws (u * n + v)) < SZ.v (65535sz) ==>
                      SZ.v (Seq.index ks v) <= SZ.v (Seq.index ws (u * n + v))))
          (ensures keys_bounded_by_u ks ws ims n u)
  = reveal_opaque (`%keys_bounded_by_u) (keys_bounded_by_u ks ws ims n u)
