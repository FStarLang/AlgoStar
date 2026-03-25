module CLRS.Ch23.Prim.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open Pulse.Lib.Reference
open FStar.Mul
open FStar.Math.Lib
open FStar.UInt
open CLRS.Ch23.MST.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U64 = FStar.UInt64

module PrimSpec = CLRS.Ch23.Prim.Spec
module Bridge = CLRS.Ch23.Kruskal.Bridge

// Convert SizeT weights to int for specification
let sizet_to_int (x: SZ.t) : int = SZ.v x

let sizet_seq_to_int_seq (s: Seq.seq SZ.t) : Seq.seq int =
  Seq.init (Seq.length s) (fun (i:nat{i < Seq.length s}) -> sizet_to_int (Seq.index s i))

// Convert weight matrix from SizeT array to adjacency matrix spec
let weights_to_adj_matrix (weights_seq: Seq.seq SZ.t) (n: nat) 
  : Pure adj_matrix
    (requires Seq.length weights_seq == n * n)
    (ensures fun adj -> 
      Seq.length adj == n /\
      (forall (u:nat). u < n ==> Seq.length (Seq.index adj u) == n))
  = Seq.init n (fun (u:nat{u < n}) ->
      Seq.init n (fun (v:nat{v < n}) ->
        let idx = u * n + v in
        let w_sizet = Seq.index weights_seq idx in
        let w : int = sizet_to_int w_sizet in
        // Use spec's infinity value for comparison
        if w >= sizet_to_int infinity then PrimSpec.infinity else w
      )
    )

// Bridging lemma: under valid_weights, the conversion preserves edge weights faithfully.
// If a weight is positive and < infinity (65535), it appears unchanged in the adj matrix.
// If a weight is 0 or >= infinity, it maps to the spec's infinity (10^9) or 0 respectively.
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let weights_to_adj_preserves (weights_seq: Seq.seq SZ.t) (n: nat) (u v: nat)
  : Lemma (requires valid_weights weights_seq n /\ n > 0 /\ u < n /\ v < n /\
                    u * n + v < n * n)
          (ensures (let adj = weights_to_adj_matrix weights_seq n in
                    let w_imp = SZ.v (Seq.index weights_seq (u * n + v)) in
                    let w_spec = Seq.index (Seq.index adj u) v in
                    (w_imp > 0 /\ w_imp < SZ.v infinity ==> w_spec = w_imp) /\
                    (w_imp = 0 ==> w_spec = 0) /\
                    (w_imp >= SZ.v infinity ==> w_spec = PrimSpec.infinity)))
  = ()
#pop-options

// Lemma: Seq.create produces bounded keys
let lemma_create_bounded (n: nat) (v: SZ.t)
  : Lemma (requires SZ.v v <= SZ.v infinity)
          (ensures all_keys_bounded (Seq.create n v))
  = ()

// Lemma: Seq.upd preserves boundedness if new value is bounded
let lemma_upd_preserves_bounded (s: Seq.seq SZ.t) (i: nat) (v: SZ.t)
  : Lemma (requires i < Seq.length s /\ all_keys_bounded s /\ SZ.v v <= SZ.v infinity)
          (ensures all_keys_bounded (Seq.upd s i v))
  = ()

// Lemma: Seq.create with valid value produces parent_valid
let lemma_create_parent_valid (n: nat) (v: SZ.t)
  : Lemma (requires SZ.v v < n)
          (ensures parent_valid (Seq.create n v) n)
  = ()

// Lemma: Seq.upd preserves parent_valid if new value is valid
let lemma_upd_preserves_parent_valid (s: Seq.seq SZ.t) (i: nat) (v: SZ.t) (n: nat)
  : Lemma (requires i < n /\ Seq.length s == n /\ parent_valid s n /\ SZ.v v < n)
          (ensures parent_valid (Seq.upd s i v) n)
  = ()

// Lemma: key_parent_consistent holds vacuously when all non-source keys are infinity
let lemma_key_parent_consistent_init
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      Seq.length key_seq == n /\
      Seq.length parent_seq == n /\
      Seq.length weights_seq == n * n /\
      source < n /\
      (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index key_seq v) >= SZ.v infinity))
    (ensures key_parent_consistent key_seq parent_seq weights_seq n source)
  = ()

// Lemma: Seq.upd preserves key_parent_consistent when key and parent are updated consistently
let lemma_upd_preserves_key_parent_consistent
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source i: nat) (new_key new_parent: SZ.t)
    (should_update: bool)
  : Lemma
    (requires
      Seq.length key_seq == n /\
      Seq.length parent_seq == n /\
      Seq.length weights_seq == n * n /\
      source < n /\ i < n /\ n > 0 /\
      parent_valid parent_seq n /\
      key_parent_consistent key_seq parent_seq weights_seq n source /\
      SZ.v new_parent < n /\
      (should_update ==>
        SZ.v new_parent * n + i < n * n /\
        SZ.v new_key == SZ.v (Seq.index weights_seq (SZ.v new_parent * n + i))) /\
      (~should_update ==>
        new_key == Seq.index key_seq i /\
        new_parent == Seq.index parent_seq i))
    (ensures
      key_parent_consistent (Seq.upd key_seq i new_key) (Seq.upd parent_seq i new_parent)
                            weights_seq n source)
  = ()

// Lemma: writing parent[source] preserves key_parent_consistent (source excluded by v <> source)
let lemma_parent_source_preserves_key_parent_consistent
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat) (new_parent: SZ.t)
  : Lemma
    (requires
      Seq.length key_seq == n /\
      Seq.length parent_seq == n /\
      Seq.length weights_seq == n * n /\
      source < n /\
      key_parent_consistent key_seq parent_seq weights_seq n source /\
      SZ.v new_parent < n)
    (ensures
      key_parent_consistent key_seq (Seq.upd parent_seq source new_parent) weights_seq n source)
  = ()

// Opaque wrapper for key_parent_consistent to control SMT exposure
[@@"opaque_to_smt"]
let prim_kpc (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat) : prop =
  key_parent_consistent key_seq parent_seq weights_seq n source

let prim_kpc_init (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      Seq.length key_seq == n /\
      Seq.length parent_seq == n /\
      Seq.length weights_seq == n * n /\
      source < n /\
      (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index key_seq v) >= SZ.v infinity))
    (ensures prim_kpc key_seq parent_seq weights_seq n source)
  = reveal_opaque (`%prim_kpc) (prim_kpc key_seq parent_seq weights_seq n source);
    lemma_key_parent_consistent_init key_seq parent_seq weights_seq n source

let prim_kpc_step
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source i: nat)
    (new_key new_parent: SZ.t) (should_update: bool)
  : Lemma
    (requires
      Seq.length key_seq == n /\
      Seq.length parent_seq == n /\
      Seq.length weights_seq == n * n /\
      source < n /\ i < n /\ n > 0 /\
      parent_valid parent_seq n /\
      prim_kpc key_seq parent_seq weights_seq n source /\
      SZ.v new_parent < n /\
      (should_update ==>
        SZ.v new_parent * n + i < n * n /\
        SZ.v new_key == SZ.v (Seq.index weights_seq (SZ.v new_parent * n + i))) /\
      (~should_update ==>
        new_key == Seq.index key_seq i /\
        new_parent == Seq.index parent_seq i))
    (ensures prim_kpc (Seq.upd key_seq i new_key) (Seq.upd parent_seq i new_parent)
                      weights_seq n source)
  = reveal_opaque (`%prim_kpc) (prim_kpc key_seq parent_seq weights_seq n source);
    reveal_opaque (`%prim_kpc) (prim_kpc (Seq.upd key_seq i new_key)
                                         (Seq.upd parent_seq i new_parent) weights_seq n source);
    lemma_upd_preserves_key_parent_consistent key_seq parent_seq weights_seq n source i
                                               new_key new_parent should_update

let prim_kpc_parent_source
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat) (new_parent: SZ.t)
  : Lemma
    (requires
      Seq.length key_seq == n /\
      Seq.length parent_seq == n /\
      Seq.length weights_seq == n * n /\
      source < n /\
      prim_kpc key_seq parent_seq weights_seq n source /\
      SZ.v new_parent < n)
    (ensures prim_kpc key_seq (Seq.upd parent_seq source new_parent) weights_seq n source)
  = reveal_opaque (`%prim_kpc) (prim_kpc key_seq parent_seq weights_seq n source);
    reveal_opaque (`%prim_kpc) (prim_kpc key_seq (Seq.upd parent_seq source new_parent)
                                         weights_seq n source);
    lemma_parent_source_preserves_key_parent_consistent key_seq parent_seq weights_seq
                                                         n source new_parent

let prim_kpc_elim (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires prim_kpc key_seq parent_seq weights_seq n source)
    (ensures key_parent_consistent key_seq parent_seq weights_seq n source)
  = reveal_opaque (`%prim_kpc) (prim_kpc key_seq parent_seq weights_seq n source)

// Lemma: if u < n and n*n < bound, then u*n+v fits in 64 bits
// Proved manually via recursive descent
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec lemma_prod_fits (u n: nat) : Lemma
  (requires u < n /\ n > 0)
  (ensures u * n < n * n)
  (decreases n - u)
  = if u >= n - 1 then ()
    else begin
      lemma_prod_fits (u + 1) n;
      assert ((u + 1) * n < n * n);
      assert (u * n + n < n * n);
      assert (u * n < n * n)
    end

let lemma_mul_bound (u n v: nat) (bound: nat)
  : Lemma (requires (u < n /\ v < n /\ n * n < bound /\ n > 0 /\ bound == pow2 64))
          (ensures (u * n < bound /\ u * n + v < bound))
  = lemma_prod_fits u n;
    ()

// Helper: u*n+v < n*n when u < n and v < n
let lemma_index_bound (u v n: nat)
  : Lemma (requires u < n /\ v < n /\ n > 0)
          (ensures u * n + v < n * n)
  = if u + 1 < n then lemma_prod_fits (u + 1) n
    else ()

// Direct U64-based index computation that bypasses SizeT overflow checks  
// Requires: SizeT is 64-bit (fits_u64 holds)
inline_for_extraction  
let compute_weight_idx_u64 (u n v: SZ.t{SZ.v u < SZ.v n /\ SZ.v v < SZ.v n /\ SZ.v n > 0 /\ SZ.v n * SZ.v n < pow2 64 /\ SZ.fits_u64})
  : Tot (idx:SZ.t{SZ.v idx == SZ.v u * SZ.v n + SZ.v v})
  = lemma_mul_bound (SZ.v u) (SZ.v n) (SZ.v v) (pow2 64);
    let u64_u = SZ.sizet_to_uint64 u in
    let u64_n = SZ.sizet_to_uint64 n in
    let u64_v = SZ.sizet_to_uint64 v in
    // Use U64.mul_mod which doesn't require overflow check
    let prod_mod = U64.mul_mod u64_u u64_n in
    // Since we proved u*n < 2^64, the mod operation is identity
    assert (U64.v prod_mod == (U64.v u64_u * U64.v u64_n) % pow2 64);
    assert (U64.v u64_u * U64.v u64_n < pow2 64);
    assert (U64.v prod_mod == U64.v u64_u * U64.v u64_n);
    // Similarly for addition
    let idx_mod = U64.add_mod prod_mod u64_v in
    assert (U64.v idx_mod == (U64.v prod_mod + U64.v u64_v) % pow2 64);
    assert (U64.v prod_mod + U64.v u64_v < pow2 64);
    assert (U64.v idx_mod == U64.v prod_mod + U64.v u64_v);
    // Wrap back to SizeT - use fits_u64_implies_fits lemma
    assert (U64.v idx_mod < pow2 64);
    SZ.fits_u64_implies_fits (U64.v idx_mod);
    FStar.SizeT.uint64_to_sizet idx_mod
#pop-options

// Helper to compute array index u * n + v
inline_for_extraction
let compute_weight_idx = compute_weight_idx_u64

(*** Impl ↔ Spec Bridging — Pure Helper Functions ***)

(*
   The postcondition (prim_correct) proves:
   - key[source] = 0
   - all keys bounded by infinity
   - parent[source] = source

   The function edges_from_parent_key below extracts edges from the
   parent array. A full MST proof would need to show these edges
   match pure_prim from Prim.Spec, requiring a loop invariant that
   tracks correspondence between the imperative key/parent state
   and the pure spec's recursive prim_step.
*)

// Extract MST edges from the parent array:
// For each vertex v ≠ source, emit edge {parent[v], v, key[v]}
let rec edges_from_parent_key
  (parent_seq key_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Pure (list edge)
    (requires Seq.length parent_seq == n /\ Seq.length key_seq == n /\ i <= n)
    (ensures fun _ -> True)
    (decreases (n - i))
  = if i >= n then []
    else if i = source then edges_from_parent_key parent_seq key_seq n source (i + 1)
    else
      let p = SZ.v (Seq.index parent_seq i) in
      let w = SZ.v (Seq.index key_seq i) in
      { u = p; v = i; w = w } :: edges_from_parent_key parent_seq key_seq n source (i + 1)

(*** Greedy Safety for imperative Prim ***)

/// mst_edges_so_far: edges only for in-MST non-source vertices
let rec mst_edges_so_far
  (parent_seq key_seq in_mst_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Pure (list edge)
    (requires Seq.length parent_seq == n /\ Seq.length key_seq == n /\
              Seq.length in_mst_seq == n /\ i <= n)
    (ensures fun _ -> True)
    (decreases (n - i))
  = if i >= n then []
    else if i = source then mst_edges_so_far parent_seq key_seq in_mst_seq n source (i + 1)
    else if SZ.v (Seq.index in_mst_seq i) = 1 then
      let p = SZ.v (Seq.index parent_seq i) in
      let w = SZ.v (Seq.index key_seq i) in
      { u = p; v = i; w = w } :: mst_edges_so_far parent_seq key_seq in_mst_seq n source (i + 1)
    else mst_edges_so_far parent_seq key_seq in_mst_seq n source (i + 1)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec mst_edges_all_in
  (parent_seq key_seq in_mst_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Lemma
    (requires Seq.length parent_seq == n /\ Seq.length key_seq == n /\
              Seq.length in_mst_seq == n /\ i <= n /\ source < n /\
              (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index in_mst_seq v) = 1))
    (ensures mst_edges_so_far parent_seq key_seq in_mst_seq n source i ==
             edges_from_parent_key parent_seq key_seq n source i)
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then mst_edges_all_in parent_seq key_seq in_mst_seq n source (i + 1)
    else mst_edges_all_in parent_seq key_seq in_mst_seq n source (i + 1)

let rec mst_edges_none_in
  (parent_seq key_seq in_mst_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Lemma
    (requires Seq.length parent_seq == n /\ Seq.length key_seq == n /\
              Seq.length in_mst_seq == n /\ i <= n /\ source < n /\
              (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index in_mst_seq v) <> 1))
    (ensures mst_edges_so_far parent_seq key_seq in_mst_seq n source i == [])
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then mst_edges_none_in parent_seq key_seq in_mst_seq n source (i + 1)
    else mst_edges_none_in parent_seq key_seq in_mst_seq n source (i + 1)

let rec mst_edges_ext
  (ps1 ks1 ps2 ks2 in_mst_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Lemma
    (requires Seq.length ps1 == n /\ Seq.length ks1 == n /\
              Seq.length ps2 == n /\ Seq.length ks2 == n /\
              Seq.length in_mst_seq == n /\ i <= n /\ source < n /\
              (forall (v:nat). v < n /\ v <> source /\ SZ.v (Seq.index in_mst_seq v) = 1 ==>
                Seq.index ps1 v == Seq.index ps2 v /\ Seq.index ks1 v == Seq.index ks2 v))
    (ensures mst_edges_so_far ps1 ks1 in_mst_seq n source i ==
             mst_edges_so_far ps2 ks2 in_mst_seq n source i)
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then mst_edges_ext ps1 ks1 ps2 ks2 in_mst_seq n source (i + 1)
    else if SZ.v (Seq.index in_mst_seq i) = 1 then
      mst_edges_ext ps1 ks1 ps2 ks2 in_mst_seq n source (i + 1)
    else
      mst_edges_ext ps1 ks1 ps2 ks2 in_mst_seq n source (i + 1)
#pop-options

/// weights_to_adj_matrix produces well_formed_adj when weights are symmetric
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let weights_to_adj_well_formed (weights_seq: Seq.seq SZ.t) (n: nat)
  : Lemma
    (requires Seq.length weights_seq == n * n /\ n > 0 /\ symmetric_weights weights_seq n)
    (ensures PrimSpec.well_formed_adj (weights_to_adj_matrix weights_seq n) n)
  = PrimSpec.well_formed_adj_intro (weights_to_adj_matrix weights_seq n) n
#pop-options

/// Opaque greedy safety invariant
[@@"opaque_to_smt"]
let prim_safe (parent_seq key_seq in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat) : prop =
  n > 0 /\ source < n /\
  Seq.length parent_seq == n /\ Seq.length key_seq == n /\
  Seq.length in_mst_seq == n /\ Seq.length weights_seq == n * n /\
  (symmetric_weights weights_seq n /\
   all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq n) n) ==>
   (let adj = weights_to_adj_matrix weights_seq n in
    let g = PrimSpec.adj_to_graph adj n in
    let es = mst_edges_so_far parent_seq key_seq in_mst_seq n source 0 in
    exists (t: list edge). is_mst g t /\ subset_edges es t))

#push-options "--z3rlimit 50"
let prim_safe_init
    (parent_seq key_seq in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires n > 0 /\ source < n /\
              Seq.length parent_seq == n /\ Seq.length key_seq == n /\
              Seq.length in_mst_seq == n /\ Seq.length weights_seq == n * n /\
              (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index in_mst_seq v) <> 1))
    (ensures prim_safe parent_seq key_seq in_mst_seq weights_seq n source)
  = mst_edges_none_in parent_seq key_seq in_mst_seq n source 0;
    reveal_opaque (`%prim_safe) (prim_safe parent_seq key_seq in_mst_seq weights_seq n source);
    FStar.Classical.arrow_to_impl
      #(symmetric_weights weights_seq n /\
        all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq n) n))
      #(let adj = weights_to_adj_matrix weights_seq n in
        let g = PrimSpec.adj_to_graph adj n in
        let es = mst_edges_so_far parent_seq key_seq in_mst_seq n source 0 in
        exists (t: list edge). is_mst g t /\ subset_edges es t)
      (fun _ ->
        weights_to_adj_well_formed weights_seq n;
        let adj = weights_to_adj_matrix weights_seq n in
        PrimSpec.adj_to_graph_edges adj n;
        let g = PrimSpec.adj_to_graph adj n in
        let aux (e: edge) : Lemma
          (requires mem_edge e g.edges) (ensures e.u < n /\ e.v < n /\ e.u <> e.v)
          = PrimSpec.adj_to_graph_edges_valid adj n e in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        assert (all_connected g.n g.edges);
        CLRS.Ch23.MST.Existence.mst_exists g)
#pop-options

let prim_safe_elim
    (parent_seq key_seq in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires prim_safe parent_seq key_seq in_mst_seq weights_seq n source /\
              n > 0 /\ source < n /\
              Seq.length parent_seq == n /\ Seq.length key_seq == n /\
              Seq.length in_mst_seq == n /\ Seq.length weights_seq == n * n /\
              symmetric_weights weights_seq n /\
              all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq n) n))
    (ensures (let adj = weights_to_adj_matrix weights_seq n in
              let g = PrimSpec.adj_to_graph adj n in
              let es = mst_edges_so_far parent_seq key_seq in_mst_seq n source 0 in
              exists (t: list edge). is_mst g t /\ subset_edges es t))
  = reveal_opaque (`%prim_safe) (prim_safe parent_seq key_seq in_mst_seq weights_seq n source)

/// mem_edge in mst_edges_so_far: each edge corresponds to an in-MST non-source vertex
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec mst_edges_mem_implies_in_mst
    (ps ks ims: Seq.seq SZ.t) (n source: nat) (i: nat) (e: edge)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\ Seq.length ims == n /\
              i <= n /\ source < n /\ mem_edge e (mst_edges_so_far ps ks ims n source i))
    (ensures exists (v:nat). v >= i /\ v < n /\ v <> source /\
              SZ.v (Seq.index ims v) = 1 /\ edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)}))
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then mst_edges_mem_implies_in_mst ps ks ims n source (i + 1) e
    else if SZ.v (Seq.index ims i) = 1 then
      (if edge_eq e ({u = SZ.v (Seq.index ps i); v = i; w = SZ.v (Seq.index ks i)}) then ()
       else mst_edges_mem_implies_in_mst ps ks ims n source (i + 1) e)
    else mst_edges_mem_implies_in_mst ps ks ims n source (i + 1) e

/// Converse: if vertex v is in MST, its edge is in mst_edges_so_far
let rec mst_edges_in_mst_implies_mem
    (ps ks ims: Seq.seq SZ.t) (n source: nat) (i: nat) (v: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\ Seq.length ims == n /\
              i <= n /\ source < n /\ v >= i /\ v < n /\ v <> source /\
              SZ.v (Seq.index ims v) = 1)
    (ensures mem_edge ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)})
                      (mst_edges_so_far ps ks ims n source i))
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then mst_edges_in_mst_implies_mem ps ks ims n source (i + 1) v
    else if i = v then
      edge_eq_reflexive ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)})
    else if SZ.v (Seq.index ims i) = 1 then
      mst_edges_in_mst_implies_mem ps ks ims n source (i + 1) v
    else
      mst_edges_in_mst_implies_mem ps ks ims n source (i + 1) v
#pop-options

/// subset_edges when every edge in the left list is mem_edge of the right list
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec subset_from_mem (a b: list edge)
  : Lemma (requires forall (e: edge). mem_edge e a ==> mem_edge e b)
          (ensures subset_edges a b)
          (decreases a)
  = match a with | [] -> () | hd :: tl -> subset_from_mem tl b

/// Old mst_edges ⊆ new mst_edges when vertex u is added to in_mst
let mst_edges_add_subset
    (ps ks ims_old ims_new: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\
              Seq.length ims_old == n /\ Seq.length ims_new == n /\
              source < n /\ u < n /\ u <> source /\
              SZ.v (Seq.index ims_old u) <> 1 /\
              SZ.v (Seq.index ims_new u) = 1 /\
              (forall (v:nat). v < n /\ v <> u ==> Seq.index ims_new v == Seq.index ims_old v))
    (ensures subset_edges (mst_edges_so_far ps ks ims_old n source 0)
                          (mst_edges_so_far ps ks ims_new n source 0))
  = // For any edge e in old_edges: e corresponds to some in-MST vertex v ≠ u
    // (since u was not in old MST). v is still in new MST (ims_new v = ims_old v = 1).
    // So e is also in new_edges.
    let aux (e: edge) : Lemma
      (requires mem_edge e (mst_edges_so_far ps ks ims_old n source 0))
      (ensures mem_edge e (mst_edges_so_far ps ks ims_new n source 0))
      = mst_edges_mem_implies_in_mst ps ks ims_old n source 0 e;
        // exists v: v < n, v <> source, ims_old[v] = 1, edge_eq e {ps[v], v, ks[v]}
        // Since v <> u (because ims_old[u] <> 1 but ims_old[v] = 1):
        // ims_new[v] = ims_old[v] = 1
        // So the edge for v is in new_edges too
        FStar.Classical.exists_elim
          (mem_edge e (mst_edges_so_far ps ks ims_new n source 0))
          #nat #(fun v -> v >= 0 /\ v < n /\ v <> source /\
                   SZ.v (Seq.index ims_old v) = 1 /\
                   edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)}))
          ()
          (fun (v: nat{v >= 0 /\ v < n /\ v <> source /\
                       SZ.v (Seq.index ims_old v) = 1 /\
                       edge_eq e ({u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)})}) ->
            // v <> u since ims_old[u] <> 1 but ims_old[v] = 1
            assert (v <> u);
            assert (SZ.v (Seq.index ims_new v) = 1);
            mst_edges_in_mst_implies_mem ps ks ims_new n source 0 v;
            let ev = {u = SZ.v (Seq.index ps v); v = v; w = SZ.v (Seq.index ks v)} in
            edge_eq_symmetric e ev;
            mem_edge_eq ev e (mst_edges_so_far ps ks ims_new n source 0))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    subset_from_mem (mst_edges_so_far ps ks ims_old n source 0)
                    (mst_edges_so_far ps ks ims_new n source 0)
#pop-options

/// Step 1a: positive weight in weights_seq → edge in adj_to_graph
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let weights_edge_in_graph
    (weights_seq: Seq.seq SZ.t) (n u v: nat)
  : Lemma
    (requires n > 0 /\ u < n /\ v < n /\ u <> v /\
              Seq.length weights_seq == n * n /\
              symmetric_weights weights_seq n /\
              valid_weights weights_seq n /\
              SZ.v (Seq.index weights_seq (u * n + v)) > 0 /\
              SZ.v (Seq.index weights_seq (u * n + v)) < SZ.v infinity)
    (ensures (let adj = weights_to_adj_matrix weights_seq n in
              let g = PrimSpec.adj_to_graph adj n in
              let w = SZ.v (Seq.index weights_seq (u * n + v)) in
              mem_edge ({u = u; v = v; w = w}) g.edges))
  = let adj = weights_to_adj_matrix weights_seq n in
    let w = SZ.v (Seq.index weights_seq (u * n + v)) in
    lemma_index_bound u v n;
    weights_to_adj_preserves weights_seq n u v;
    let eu = if u < v then u else v in
    let ev = if u < v then v else u in
    lemma_index_bound eu ev n;
    weights_to_adj_preserves weights_seq n eu ev;
    // adj[eu][ev] = w (positive, < impl infinity 65535)
    // PrimSpec.infinity = 10^9, so adj[eu][ev] ≠ PrimSpec.infinity
    assert (Seq.index (Seq.index adj eu) ev <> PrimSpec.infinity);
    PrimSpec.has_edge_intro adj n eu ev;
    assert (Seq.length adj == n);
    assert (Seq.length (Seq.index adj eu) == n);
    PrimSpec.well_formed_adj_intro adj n;
    PrimSpec.adj_to_graph_has_edge adj n eu ev;
    if u < v then ()
    else begin
      edge_eq_reflexive ({u = ev; v = eu; w = w});
      edge_eq_symmetric ({u = ev; v = eu; w = w})
                         ({u = eu; v = ev; w = w});
      mem_edge_eq ({u = eu; v = ev; w = w})
                  ({u = ev; v = eu; w = w})
                  (PrimSpec.adj_to_graph adj n).edges
    end
#pop-options

/// Graph edge weight equals weights_seq entry (for valid weights + symmetric)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let graph_edge_weight_eq
    (weights_seq: Seq.seq SZ.t) (n: nat) (e: edge)
  : Lemma
    (requires n > 0 /\ Seq.length weights_seq == n * n /\
              valid_weights weights_seq n /\ symmetric_weights weights_seq n /\
              mem_edge e (PrimSpec.adj_to_graph (weights_to_adj_matrix weights_seq n) n).edges /\
              e.u < n /\ e.v < n)
    (ensures e.w = SZ.v (Seq.index weights_seq (e.u * n + e.v)))
  = let adj = weights_to_adj_matrix weights_seq n in
    PrimSpec.adj_to_graph_edges_valid adj n e;
    PrimSpec.well_formed_adj_intro adj n;
    PrimSpec.adj_to_graph_edge_weight adj n e;
    lemma_index_bound e.u e.v n;
    weights_to_adj_preserves weights_seq n e.u e.v
#pop-options

/// Standalone cut_property application for Prim greedy step.
/// Separated from prim_safe_add_vertex for solver efficiency.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let prim_cut_step
    (parent_seq key_seq in_mst_old weights_seq: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ u < n /\ u <> source /\
      Seq.length parent_seq == n /\ Seq.length key_seq == n /\
      Seq.length in_mst_old == n /\ Seq.length weights_seq == n * n /\
      valid_weights weights_seq n /\
      symmetric_weights weights_seq n /\
      parent_valid parent_seq n /\
      key_parent_consistent key_seq parent_seq weights_seq n source /\
      SZ.v (Seq.index in_mst_old u) <> 1 /\
      SZ.v (Seq.index key_seq u) > 0 /\
      SZ.v (Seq.index key_seq u) < SZ.v infinity /\
      SZ.v (Seq.index in_mst_old (SZ.v (Seq.index parent_seq u))) = 1 /\
      // All in-MST non-source vertices have parent in MST
      (forall (v:nat). v < n /\ v <> source /\ SZ.v (Seq.index in_mst_old v) = 1 ==>
        SZ.v (Seq.index in_mst_old (SZ.v (Seq.index parent_seq v))) = 1) /\
      // extract-min: key[u] <= key[v] for all non-MST v
      (forall (v:nat). v < n /\ SZ.v (Seq.index in_mst_old v) <> 1 ==>
        SZ.v (Seq.index key_seq u) <= SZ.v (Seq.index key_seq v)) /\
      // key invariant: key[v] <= weight(w,v) for MST w, non-MST v
      (forall (v w: nat). v < n /\ w < n /\
        SZ.v (Seq.index in_mst_old v) <> 1 /\
        SZ.v (Seq.index in_mst_old w) = 1 /\
        w * n + v < n * n /\
        SZ.v (Seq.index weights_seq (w * n + v)) > 0 /\
        SZ.v (Seq.index weights_seq (w * n + v)) < SZ.v infinity ==>
        SZ.v (Seq.index key_seq v) <= SZ.v (Seq.index weights_seq (w * n + v))) /\
      // No zero-weight edges (standard MST convention: weights > 0)
      (forall (u v: nat). u < n /\ v < n /\ u * n + v < n * n /\
        SZ.v (Seq.index weights_seq (u * n + v)) = 0 ==>
        u = v) /\
      // old edges are safe
      (let adj = weights_to_adj_matrix weights_seq n in
       let g = PrimSpec.adj_to_graph adj n in
       let old_es = mst_edges_so_far parent_seq key_seq in_mst_old n source 0 in
       exists (t: list edge). is_mst g t /\ subset_edges old_es t))
    (ensures
      (let adj = weights_to_adj_matrix weights_seq n in
       let g = PrimSpec.adj_to_graph adj n in
       let pu = SZ.v (Seq.index parent_seq u) in
       let ku = SZ.v (Seq.index key_seq u) in
       let new_edge : edge = {u = pu; v = u; w = ku} in
       let old_es = mst_edges_so_far parent_seq key_seq in_mst_old n source 0 in
       exists (t: list edge). is_mst g t /\ subset_edges (new_edge :: old_es) t))
  = let adj = weights_to_adj_matrix weights_seq n in
    let g = PrimSpec.adj_to_graph adj n in
    let pu = SZ.v (Seq.index parent_seq u) in
    let ku = SZ.v (Seq.index key_seq u) in
    let new_edge : edge = {u = pu; v = u; w = ku} in
    let old_es = mst_edges_so_far parent_seq key_seq in_mst_old n source 0 in
    PrimSpec.adj_to_graph_edges adj n;
    PrimSpec.well_formed_adj_intro adj n;
    // new_edge ∈ g.edges
    assert (pu <> u);
    lemma_index_bound pu u n;
    lemma_prod_fits pu n;
    weights_edge_in_graph weights_seq n pu u;
    // Define cut
    let s : cut = fun v -> v < n && SZ.v (Seq.index in_mst_old v) = 1 in
    // new_edge crosses cut: pu in MST, u not
    assert (crosses_cut new_edge s);
    // respects: no old edge crosses cut
    let rec respects_proof (es: list edge)
      : Lemma (requires 
                (forall (e: edge). mem_edge e es ==>
                  (exists (v:nat). v >= 0 /\ v < n /\ v <> source /\
                    SZ.v (Seq.index in_mst_old v) = 1 /\
                    edge_eq e ({u = SZ.v (Seq.index parent_seq v); v = v; w = SZ.v (Seq.index key_seq v)}))))
              (ensures respects es s)
              (decreases es)
      = match es with
        | [] -> ()
        | e :: tl ->
          // e has both endpoints in MST → same side of cut → doesn't cross
          FStar.Classical.exists_elim
            (not (crosses_cut e s))
            #nat #(fun v -> v >= 0 /\ v < n /\ v <> source /\
                     SZ.v (Seq.index in_mst_old v) = 1 /\
                     edge_eq e ({u = SZ.v (Seq.index parent_seq v); v = v; w = SZ.v (Seq.index key_seq v)}))
            ()
            (fun (v:nat{v >= 0 /\ v < n /\ v <> source /\
                        SZ.v (Seq.index in_mst_old v) = 1 /\
                        edge_eq e ({u = SZ.v (Seq.index parent_seq v); v = v; w = SZ.v (Seq.index key_seq v)})}) ->
              edge_eq_endpoints e ({u = SZ.v (Seq.index parent_seq v); v = v; w = SZ.v (Seq.index key_seq v)});
              let pv = SZ.v (Seq.index parent_seq v) in
              // v in MST, parent[v] in MST (from precondition)
              // s(v) = true, s(pv) = true → crosses_cut e s = false
              assert (s v = true);
              assert (s pv = true));
          respects_proof tl
    in
    // Prove the mem_edge precondition for old_es
    let mem_proof (e: edge) : Lemma
      (requires mem_edge e old_es)
      (ensures exists (v:nat). v >= 0 /\ v < n /\ v <> source /\
                SZ.v (Seq.index in_mst_old v) = 1 /\
                edge_eq e ({u = SZ.v (Seq.index parent_seq v); v = v; w = SZ.v (Seq.index key_seq v)}))
      = mst_edges_mem_implies_in_mst parent_seq key_seq in_mst_old n source 0 e
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires mem_proof);
    respects_proof old_es;
    // is_light_edge: new_edge.w ≤ e'.w for all crossing edges
    let light_proof (e': edge) : Lemma
      (requires mem_edge e' g.edges /\ crosses_cut e' s)
      (ensures new_edge.w <= e'.w)
      = PrimSpec.adj_to_graph_edges_valid adj n e';
        graph_edge_weight_eq weights_seq n e';
        // e'.w = SZ.v (Seq.index weights_seq (e'.u * n + e'.v))
        if s e'.u then begin
          // e'.u in MST, e'.v not. e'.w = weights[e'.u*n+e'.v]
          lemma_index_bound (e'.u) (e'.v) n;
          let w_val = SZ.v (Seq.index weights_seq (e'.u * n + e'.v)) in
          assert (e'.w = w_val);
          // no_zero_edges: w_val = 0 ==> e'.u = e'.v. But e'.u <> e'.v (from edges_valid).
          // So w_val > 0. With valid_weights: w_val < infinity.
          assert (w_val > 0);
          // key invariant: key[e'.v] ≤ w_val = e'.w
          // extract-min: key[u] ≤ key[e'.v]
          // So: new_edge.w = ku = key[u] ≤ e'.w
          ()
        end else begin
          // e'.v in MST, e'.u not
          lemma_index_bound (e'.u) (e'.v) n;
          lemma_index_bound (e'.v) (e'.u) n;
          let w_val = SZ.v (Seq.index weights_seq (e'.u * n + e'.v)) in
          assert (e'.w = w_val);
          assert (e'.u <> e'.v);
          assert (w_val > 0);
          // symmetric: weights[e'.v*n+e'.u] = w_val
          // key invariant: key[e'.u] <= weights[e'.v*n+e'.u] = w_val = e'.w
          // extract-min: key[u] <= key[e'.u]
          ()
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires light_proof);
    // valid edges
    let ve (e': edge) : Lemma
      (requires mem_edge e' g.edges) (ensures e'.u < g.n /\ e'.v < g.n)
      = PrimSpec.adj_to_graph_edges_valid adj n e'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ve);
    // Apply cut_property
    cut_property g old_es new_edge s
#pop-options

/// Greedy step: adding vertex u to MST preserves safety.
#push-options "--z3rlimit 200"
let prim_safe_add_vertex
    (parent_seq key_seq in_mst_old in_mst_new weights_seq: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires prim_safe parent_seq key_seq in_mst_old weights_seq n source /\
              n > 0 /\ source < n /\ u < n /\
              Seq.length parent_seq == n /\ Seq.length key_seq == n /\
              Seq.length in_mst_old == n /\ Seq.length in_mst_new == n /\
              Seq.length weights_seq == n * n /\
              parent_valid parent_seq n /\
              prim_kpc key_seq parent_seq weights_seq n source /\
              // in_mst_new = upd in_mst_old u 1
              SZ.v (Seq.index in_mst_new u) = 1 /\
              (forall (v:nat). v < n /\ v <> u ==> Seq.index in_mst_new v == Seq.index in_mst_old v) /\
              // u was the minimum-key non-MST vertex
              SZ.v (Seq.index in_mst_old u) <> 1 /\
              SZ.v (Seq.index key_seq u) < SZ.v infinity /\
              // parent[u] is in MST (was added before u)
              SZ.v (Seq.index in_mst_old (SZ.v (Seq.index parent_seq u))) = 1 /\
              // key[u] <= key[v] for all non-MST v (extract-min result)
              (forall (v:nat). v < n /\ SZ.v (Seq.index in_mst_old v) <> 1 ==>
                SZ.v (Seq.index key_seq u) <= SZ.v (Seq.index key_seq v)) /\
              // key invariant: key[v] <= weight(w,v) for MST w, non-MST v
              (forall (v w: nat). v < n /\ w < n /\
                SZ.v (Seq.index in_mst_old v) <> 1 /\
                SZ.v (Seq.index in_mst_old w) = 1 /\
                SZ.v (Seq.index weights_seq (w * n + v)) > 0 /\
                SZ.v (Seq.index weights_seq (w * n + v)) < SZ.v infinity ==>
                SZ.v (Seq.index key_seq v) <= SZ.v (Seq.index weights_seq (w * n + v))) /\
              // Additional for proof: valid weights + key > 0
              valid_weights weights_seq n /\
              SZ.v (Seq.index key_seq u) > 0 /\
              // No zero-weight edges (weight 0 = no edge)
              (forall (u v: nat). u < n /\ v < n /\ u * n + v < n * n /\
                SZ.v (Seq.index weights_seq (u * n + v)) = 0 ==> u = v) /\
              // All in-MST non-source vertices have parent in MST
              (forall (v:nat). v < n /\ v <> source /\ SZ.v (Seq.index in_mst_old v) = 1 ==>
                SZ.v (Seq.index in_mst_old (SZ.v (Seq.index parent_seq v))) = 1))
    (ensures prim_safe parent_seq key_seq in_mst_new weights_seq n source)
  = // Proof structure:
    // 1. Old edges are safe: ∃T. is_mst T ∧ old_edges ⊆ T
    // 2. New edge (parent[u], u, key[u]) + old_edges is safe by greedy_step_safe
    //    → ∃T'. is_mst T' ∧ (new_edge :: old_edges) ⊆ T'
    // 3. New mst_edges ⊆ (new_edge :: old_edges) by construction
    // 4. Therefore new mst_edges ⊆ T'
    reveal_opaque (`%prim_safe) (prim_safe parent_seq key_seq in_mst_old weights_seq n source);
    reveal_opaque (`%prim_safe) (prim_safe parent_seq key_seq in_mst_new weights_seq n source);
    // New edges ⊆ new_edge :: old_edges
    let old_es = mst_edges_so_far parent_seq key_seq in_mst_old n source 0 in
    let new_es = mst_edges_so_far parent_seq key_seq in_mst_new n source 0 in
    let pu = SZ.v (Seq.index parent_seq u) in
    let ku = SZ.v (Seq.index key_seq u) in
    let new_edge : edge = {u = pu; v = u; w = ku} in
    // Every edge in new_es is either new_edge or in old_es
    let aux (e: edge) : Lemma
      (requires mem_edge e new_es)
      (ensures mem_edge e (new_edge :: old_es))
      = mst_edges_mem_implies_in_mst parent_seq key_seq in_mst_new n source 0 e;
        FStar.Classical.exists_elim
          (mem_edge e (new_edge :: old_es))
          #nat #(fun v -> v >= 0 /\ v < n /\ v <> source /\
                   SZ.v (Seq.index in_mst_new v) = 1 /\
                   edge_eq e ({u = SZ.v (Seq.index parent_seq v); v = v; w = SZ.v (Seq.index key_seq v)}))
          ()
          (fun (v: nat{v >= 0 /\ v < n /\ v <> source /\
                       SZ.v (Seq.index in_mst_new v) = 1 /\
                       edge_eq e ({u = SZ.v (Seq.index parent_seq v); v = v; w = SZ.v (Seq.index key_seq v)})}) ->
            if v = u then ()  // e is the new edge
            else begin
              // v was already in old MST
              assert (SZ.v (Seq.index in_mst_old v) = 1);
              mst_edges_in_mst_implies_mem parent_seq key_seq in_mst_old n source 0 v;
              let ev = {u = SZ.v (Seq.index parent_seq v); v = v; w = SZ.v (Seq.index key_seq v)} in
              edge_eq_symmetric e ev;
              mem_edge_eq ev e old_es
              // e ∈ old_es, so e ∈ new_edge :: old_es
            end)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    subset_from_mem new_es (new_edge :: old_es);
    // Now derive prim_safe using arrow_to_impl
    FStar.Classical.arrow_to_impl
      #(symmetric_weights weights_seq n /\
        all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq n) n))
      #(let adj = weights_to_adj_matrix weights_seq n in
        let g = PrimSpec.adj_to_graph adj n in
        exists (t: list edge). is_mst g t /\ subset_edges new_es t)
      (fun _ ->
        // From old prim_safe: ∃T. is_mst T ∧ old_es ⊆ T
        let adj = weights_to_adj_matrix weights_seq n in
        let g = PrimSpec.adj_to_graph adj n in
        // old safety is available
        assert (exists (t: list edge). is_mst g t /\ subset_edges old_es t);
        if u = source then begin
          // source is skipped by mst_edges_so_far. For all v ≠ source (= u):
          // ims_new[v] = ims_old[v]. So new_es = old_es by ext.
          mst_edges_ext parent_seq key_seq parent_seq key_seq in_mst_old n source 0;
          // Wait — mst_edges_ext compares different ps/ks with same ims.
          // I need: same ps/ks, different ims but equal for in-MST vertices.
          // Since u = source is skipped, and all v ≠ source have ims_new = ims_old,
          // the two mst_edges_so_far calls produce identical results.
          // But mst_edges_ext requires same ims. I need a new ext lemma for different ims.
          // Actually, mst_edges_add_subset already gives old ⊆ new.
          // And the reverse: for any e in new_es, the vertex v has ims_new[v] = 1.
          // Since v ≠ source (skipped) and v ≠ u = source (same), ims_old[v] = ims_new[v] = 1.
          // So e is also in old_es. Hence new_es ⊆ old_es.
          // With both directions: new_es and old_es have same edges.
          // old_es ⊆ T, so new_es ⊆ T. QED.
          // Use subset_from_mem new_es old_es (then transitivity with T)
          let aux2 (e: edge) : Lemma
            (requires mem_edge e new_es)
            (ensures mem_edge e old_es)
            = mst_edges_mem_implies_in_mst parent_seq key_seq in_mst_new n source 0 e;
              FStar.Classical.exists_elim
                (mem_edge e old_es) #nat
                #(fun v -> v >= 0 /\ v < n /\ v <> source /\
                   SZ.v (Seq.index in_mst_new v) = 1 /\
                   edge_eq e ({u = SZ.v (Seq.index parent_seq v); v = v; w = SZ.v (Seq.index key_seq v)}))
                ()
                (fun (v:nat{v >= 0 /\ v < n /\ v <> source /\
                   SZ.v (Seq.index in_mst_new v) = 1 /\
                   edge_eq e ({u = SZ.v (Seq.index parent_seq v); v = v; w = SZ.v (Seq.index key_seq v)})}) ->
                  assert (v <> u); // v <> source = u
                  assert (SZ.v (Seq.index in_mst_old v) = 1);
                  mst_edges_in_mst_implies_mem parent_seq key_seq in_mst_old n source 0 v;
                  let ev = {u = SZ.v (Seq.index parent_seq v); v = v; w = SZ.v (Seq.index key_seq v)} in
                  edge_eq_symmetric e ev;
                  mem_edge_eq ev e old_es)
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires aux2);
          subset_from_mem new_es old_es;
          // new_es ⊆ old_es ⊆ T
          FStar.Classical.exists_elim
            (exists (t: list edge). is_mst g t /\ subset_edges new_es t)
            #(list edge) #(fun t -> is_mst g t /\ subset_edges old_es t) ()
            (fun (t: list edge{is_mst g t /\ subset_edges old_es t}) ->
              subset_edges_transitive new_es old_es t)
        end
        else begin
          // u ≠ source: use prim_cut_step (cut_property based)
          prim_kpc_elim key_seq parent_seq weights_seq n source;
          prim_cut_step parent_seq key_seq in_mst_old weights_seq n source u;
          // Chain: new_es ⊆ (new_edge :: old_es) ⊆ T'
          FStar.Classical.exists_elim
            (exists (t: list edge). is_mst g t /\ subset_edges new_es t)
            #(list edge) #(fun t -> is_mst g t /\ subset_edges (new_edge :: old_es) t) ()
            (fun (t: list edge{is_mst g t /\ subset_edges (new_edge :: old_es) t}) ->
              subset_edges_transitive new_es (new_edge :: old_es) t)
        end)
#pop-options

let prim_safe_update_non_mst
    (ps1 ks1 ps2 ks2 in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires prim_safe ps1 ks1 in_mst_seq weights_seq n source /\
              n > 0 /\ source < n /\
              Seq.length ps1 == n /\ Seq.length ks1 == n /\
              Seq.length in_mst_seq == n /\
              Seq.length ps2 == n /\ Seq.length ks2 == n /\
              (forall (v:nat). v < n /\ v <> source /\ SZ.v (Seq.index in_mst_seq v) = 1 ==>
                Seq.index ps1 v == Seq.index ps2 v /\ Seq.index ks1 v == Seq.index ks2 v))
    (ensures prim_safe ps2 ks2 in_mst_seq weights_seq n source)
  = mst_edges_ext ps1 ks1 ps2 ks2 in_mst_seq n source 0;
    reveal_opaque (`%prim_safe) (prim_safe ps1 ks1 in_mst_seq weights_seq n source);
    reveal_opaque (`%prim_safe) (prim_safe ps2 ks2 in_mst_seq weights_seq n source)

(*** Opaque combined invariant for outer loop ***)

/// Bundle all loop invariants into one opaque predicate.
/// This keeps the Pulse VC small while containing all needed properties.
[@@"opaque_to_smt"]
let prim_inv
    (key_seq parent_seq in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat) : prop =
  prim_safe parent_seq key_seq in_mst_seq weights_seq n source /\
  prim_kpc key_seq parent_seq weights_seq n source /\
  n > 0 /\ source < n /\
  Seq.length key_seq == n /\ Seq.length parent_seq == n /\
  Seq.length in_mst_seq == n /\ Seq.length weights_seq == n * n /\
  valid_weights weights_seq n /\
  symmetric_weights weights_seq n /\
  parent_valid parent_seq n /\
  all_keys_bounded key_seq /\
  SZ.v (Seq.index key_seq source) == 0 /\
  // No zero-weight edges
  (forall (u v: nat). u < n /\ v < n /\ u * n + v < n * n /\
    SZ.v (Seq.index weights_seq (u * n + v)) = 0 ==> u = v) /\
  // Key invariant: key[v] <= weight(w,v) for in-MST w, non-MST v
  (forall (v w: nat). v < n /\ w < n /\
    SZ.v (Seq.index in_mst_seq v) <> 1 /\
    SZ.v (Seq.index in_mst_seq w) = 1 /\
    w * n + v < n * n /\
    SZ.v (Seq.index weights_seq (w * n + v)) > 0 /\
    SZ.v (Seq.index weights_seq (w * n + v)) < SZ.v infinity ==>
    SZ.v (Seq.index key_seq v) <= SZ.v (Seq.index weights_seq (w * n + v))) /\
  // In-MST vertices have finite keys (maintained: extract-min selects finite-key, keys don't increase for MST vertices)
  (forall (v: nat). v < n /\ SZ.v (Seq.index in_mst_seq v) = 1 ==>
    SZ.v (Seq.index key_seq v) < SZ.v infinity) /\
  // Parent-in-MST for finite-key non-source vertices
  (forall (v: nat). v < n /\ SZ.v (Seq.index key_seq v) < SZ.v infinity /\ v <> source ==>
    SZ.v (Seq.index in_mst_seq (SZ.v (Seq.index parent_seq v))) = 1)

/// Init: all vacuously true at start
#push-options "--z3rlimit 200 --split_queries always"
let prim_inv_init
    (key_seq parent_seq in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\
      Seq.length key_seq == n /\ Seq.length parent_seq == n /\
      Seq.length in_mst_seq == n /\ Seq.length weights_seq == n * n /\
      valid_weights weights_seq n /\
      symmetric_weights weights_seq n /\
      parent_valid parent_seq n /\
      all_keys_bounded key_seq /\
      SZ.v (Seq.index key_seq source) == 0 /\
      prim_safe parent_seq key_seq in_mst_seq weights_seq n source /\
      prim_kpc key_seq parent_seq weights_seq n source /\
      // No zero edges
      (forall (u v: nat). u < n /\ v < n /\ u * n + v < n * n /\
        SZ.v (Seq.index weights_seq (u * n + v)) = 0 ==> u = v) /\
      // Initially: no vertex in MST, so key inv and parent-in-MST are vacuous
      (forall (v:nat). v < n ==> SZ.v (Seq.index in_mst_seq v) <> 1) /\
      // All non-source keys >= infinity
      (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index key_seq v) >= SZ.v infinity))
    (ensures prim_inv key_seq parent_seq in_mst_seq weights_seq n source)
  = reveal_opaque (`%prim_inv) (prim_inv key_seq parent_seq in_mst_seq weights_seq n source)
#pop-options

/// Elim: extract all components from prim_inv
let prim_inv_elim
    (key_seq parent_seq in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires prim_inv key_seq parent_seq in_mst_seq weights_seq n source)
    (ensures
      prim_safe parent_seq key_seq in_mst_seq weights_seq n source /\
      prim_kpc key_seq parent_seq weights_seq n source /\
      n > 0 /\ source < n /\
      Seq.length key_seq == n /\ Seq.length parent_seq == n /\
      Seq.length in_mst_seq == n /\ Seq.length weights_seq == n * n /\
      valid_weights weights_seq n /\
      symmetric_weights weights_seq n /\
      parent_valid parent_seq n /\
      all_keys_bounded key_seq /\
      SZ.v (Seq.index key_seq source) == 0 /\
      (forall (u v: nat). u < n /\ v < n /\ u * n + v < n * n /\
        SZ.v (Seq.index weights_seq (u * n + v)) = 0 ==> u = v) /\
      (forall (v w: nat). v < n /\ w < n /\
        SZ.v (Seq.index in_mst_seq v) <> 1 /\
        SZ.v (Seq.index in_mst_seq w) = 1 /\
        w * n + v < n * n /\
        SZ.v (Seq.index weights_seq (w * n + v)) > 0 /\
        SZ.v (Seq.index weights_seq (w * n + v)) < SZ.v infinity ==>
        SZ.v (Seq.index key_seq v) <= SZ.v (Seq.index weights_seq (w * n + v))) /\
      (forall (v: nat). v < n /\ SZ.v (Seq.index in_mst_seq v) = 1 ==>
        SZ.v (Seq.index key_seq v) < SZ.v infinity) /\
      (forall (v: nat). v < n /\ SZ.v (Seq.index key_seq v) < SZ.v infinity /\ v <> source ==>
        SZ.v (Seq.index in_mst_seq (SZ.v (Seq.index parent_seq v))) = 1))
  = reveal_opaque (`%prim_inv) (prim_inv key_seq parent_seq in_mst_seq weights_seq n source)

/// After extract-min + in_mst[u]:=1: advance greedy safety.
#push-options "--z3rlimit 600 --split_queries always --fuel 2 --ifuel 1"
let prim_inv_add_vertex
    (key_seq parent_seq in_mst_old in_mst_new weights_seq: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires
      prim_inv key_seq parent_seq in_mst_old weights_seq n source /\
      n > 0 /\ source < n /\ u < n /\ u <> source /\
      Seq.length key_seq == n /\ Seq.length parent_seq == n /\
      Seq.length in_mst_old == n /\ Seq.length in_mst_new == n /\
      Seq.length weights_seq == n * n /\
      // Binary ims values (from algorithm: only writes 0 or 1)
      (forall (j:nat). j < n ==> SZ.v (Seq.index in_mst_old j) = 0 \/ SZ.v (Seq.index in_mst_old j) = 1) /\
      SZ.v (Seq.index in_mst_old u) = 0 /\
      SZ.v (Seq.index in_mst_new u) = 1 /\
      (forall (v:nat). v < n /\ v <> u ==> Seq.index in_mst_new v == Seq.index in_mst_old v) /\
      // Extract-min result using = 0 (matches code comparison)
      (forall (v:nat). v < n /\ SZ.v (Seq.index in_mst_old v) = 0 ==>
        SZ.v (Seq.index key_seq u) <= SZ.v (Seq.index key_seq v)) /\
      SZ.v (Seq.index key_seq u) < SZ.v infinity)
    (ensures
      prim_safe parent_seq key_seq in_mst_new weights_seq n source /\
      prim_kpc key_seq parent_seq weights_seq n source)
  = prim_inv_elim key_seq parent_seq in_mst_old weights_seq n source;
    prim_kpc_elim key_seq parent_seq weights_seq n source;
    // key[u] > 0: parent-in-MST gives ims_old[parent[u]] = 1 (since key[u] < infinity, u <> source).
    // So parent[u] <> u (ims_old[parent[u]] = 1 but ims_old[u] <> 1).
    // kpc: key[u] = weights[parent[u]*n+u]. no_zero_edges + parent[u] <> u: weights > 0.
    let pu = SZ.v (Seq.index parent_seq u) in
    assert (SZ.v (Seq.index in_mst_old pu) = 1); // from parent-in-MST
    assert (pu <> u); // ims_old[pu] = 1, ims_old[u] <> 1
    lemma_index_bound pu u n;
    // kpc gives key[u] = weights[pu*n+u]
    assert (SZ.v (Seq.index key_seq u) == SZ.v (Seq.index weights_seq (pu * n + u)));
    // no_zero_edges: weights[pu*n+u] = 0 → pu = u, contradiction
    assert (SZ.v (Seq.index key_seq u) > 0);
    // Parent-in-MST for old in-MST non-source vertices:
    // From in-MST → finite-key, plus parent-in-MST for finite-key
    assert (forall (v:nat). v < n /\ v <> source /\ SZ.v (Seq.index in_mst_old v) = 1 ==>
      SZ.v (Seq.index in_mst_old (SZ.v (Seq.index parent_seq v))) = 1);
    // Call prim_safe_add_vertex
    prim_safe_add_vertex parent_seq key_seq in_mst_old in_mst_new weights_seq n source u
#pop-options

/// Opaque context bundle for extract-min loop pass-through.
/// Keeps the extract-min loop VC small by hiding all outer invariants behind one atom.
[@@"opaque_to_smt"]
let extract_min_ctx
    (key_seq parent_seq in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat) : prop =
  n > 0 /\ source < n /\
  Seq.length key_seq == n /\ Seq.length parent_seq == n /\
  Seq.length in_mst_seq == n /\ Seq.length weights_seq == n * n /\
  prim_inv key_seq parent_seq in_mst_seq weights_seq n source /\
  Bridge.noRepeats_edge (mst_edges_so_far parent_seq key_seq in_mst_seq n source 0) /\
  SZ.v (Seq.index key_seq source) == 0 /\
  all_keys_bounded key_seq /\
  (forall (j:nat). j < Seq.length parent_seq ==> SZ.v (Seq.index parent_seq j) < n) /\
  (forall (j:nat). j < n ==> SZ.v (Seq.index in_mst_seq j) = 0 \/ SZ.v (Seq.index in_mst_seq j) = 1)

let extract_min_ctx_intro
    (key_seq parent_seq in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\
      Seq.length key_seq == n /\ Seq.length parent_seq == n /\
      Seq.length in_mst_seq == n /\ Seq.length weights_seq == n * n /\
      prim_inv key_seq parent_seq in_mst_seq weights_seq n source /\
      Bridge.noRepeats_edge (mst_edges_so_far parent_seq key_seq in_mst_seq n source 0) /\
      SZ.v (Seq.index key_seq source) == 0 /\
      all_keys_bounded key_seq /\
      (forall (j:nat). j < Seq.length parent_seq ==> SZ.v (Seq.index parent_seq j) < n) /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index in_mst_seq j) = 0 \/ SZ.v (Seq.index in_mst_seq j) = 1))
    (ensures extract_min_ctx key_seq parent_seq in_mst_seq weights_seq n source)
  = reveal_opaque (`%extract_min_ctx) (extract_min_ctx key_seq parent_seq in_mst_seq weights_seq n source)

let extract_min_ctx_elim
    (key_seq parent_seq in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires extract_min_ctx key_seq parent_seq in_mst_seq weights_seq n source /\
              Seq.length key_seq == n /\ Seq.length parent_seq == n /\
              Seq.length in_mst_seq == n /\ source < n)
    (ensures
      prim_inv key_seq parent_seq in_mst_seq weights_seq n source /\
      Bridge.noRepeats_edge (mst_edges_so_far parent_seq key_seq in_mst_seq n source 0) /\
      SZ.v (Seq.index key_seq source) == 0 /\
      all_keys_bounded key_seq /\
      (forall (j:nat). j < Seq.length parent_seq ==> SZ.v (Seq.index parent_seq j) < n) /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index in_mst_seq j) = 0 \/ SZ.v (Seq.index in_mst_seq j) = 1))
  = reveal_opaque (`%extract_min_ctx) (extract_min_ctx key_seq parent_seq in_mst_seq weights_seq n source)

/// Adding source to MST: prim_safe unchanged (source skipped in mst_edges_so_far).
/// Also: prim_inv is maintained (all dynamic invariants are vacuous or unchanged).
#push-options "--z3rlimit 600 --fuel 2 --ifuel 1"
let prim_inv_add_source
    (key_seq parent_seq in_mst_old in_mst_new weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      prim_inv key_seq parent_seq in_mst_old weights_seq n source /\
      n > 0 /\ source < n /\
      Seq.length key_seq == n /\ Seq.length parent_seq == n /\
      Seq.length in_mst_old == n /\ Seq.length in_mst_new == n /\
      Seq.length weights_seq == n * n /\
      SZ.v (Seq.index in_mst_new source) = 1 /\
      (forall (v:nat). v < n /\ v <> source ==> Seq.index in_mst_new v == Seq.index in_mst_old v))
    (ensures
      prim_safe parent_seq key_seq in_mst_new weights_seq n source /\
      prim_kpc key_seq parent_seq weights_seq n source)
  = prim_inv_elim key_seq parent_seq in_mst_old weights_seq n source;
    // Prove mst_edges_so_far is identical for old and new ims (source is skipped)
    let rec ext_ims (ps ks: Seq.seq SZ.t) (ims1 ims2: Seq.seq SZ.t) (nn src: nat) (i: nat)
      : Lemma
        (requires Seq.length ps == nn /\ Seq.length ks == nn /\ Seq.length ims1 == nn /\ Seq.length ims2 == nn /\
                  i <= nn /\ src < nn /\
                  (forall (v:nat). v < nn /\ v <> src ==> Seq.index ims1 v == Seq.index ims2 v))
        (ensures mst_edges_so_far ps ks ims1 nn src i == mst_edges_so_far ps ks ims2 nn src i)
        (decreases (nn - i))
      = if i >= nn then ()
        else if i = src then ext_ims ps ks ims1 ims2 nn src (i + 1)
        else begin
          ext_ims ps ks ims1 ims2 nn src (i + 1);
          assert (Seq.index ims1 i == Seq.index ims2 i)
        end
    in
    ext_ims parent_seq key_seq in_mst_old in_mst_new n source 0;
    // prim_safe: mst_edges_so_far equal → prim_safe transfers
    reveal_opaque (`%prim_safe) (prim_safe parent_seq key_seq in_mst_old weights_seq n source);
    reveal_opaque (`%prim_safe) (prim_safe parent_seq key_seq in_mst_new weights_seq n source)
#pop-options

/// After update-keys loop: update prim_inv with new key/parent sequences.
/// Update-keys only modifies non-MST vertices, so prim_safe is preserved
/// (it only depends on in-MST vertices' parent/key).
#push-options "--z3rlimit 200 --split_queries always"
let prim_inv_after_update_keys
    (ks_old ps_old ks_new ps_new in_mst_seq weights_seq: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires
      // prim_safe on old key/parent is given
      prim_safe ps_old ks_old in_mst_seq weights_seq n source /\
      prim_kpc ks_new ps_new weights_seq n source /\
      n > 0 /\ source < n /\ u < n /\
      Seq.length ks_old == n /\ Seq.length ps_old == n /\
      Seq.length ks_new == n /\ Seq.length ps_new == n /\
      Seq.length in_mst_seq == n /\ Seq.length weights_seq == n * n /\
      valid_weights weights_seq n /\
      symmetric_weights weights_seq n /\
      parent_valid ps_new n /\
      all_keys_bounded ks_new /\
      SZ.v (Seq.index ks_new source) == 0 /\
      SZ.v (Seq.index in_mst_seq u) = 1 /\
      // In-MST vertices' key/parent unchanged
      (forall (v:nat). v < n /\ v <> source /\ SZ.v (Seq.index in_mst_seq v) = 1 ==>
        Seq.index ps_old v == Seq.index ps_new v /\ Seq.index ks_old v == Seq.index ks_new v) /\
      // No zero edges
      (forall (uv vv: nat). uv < n /\ vv < n /\ uv * n + vv < n * n /\
        SZ.v (Seq.index weights_seq (uv * n + vv)) = 0 ==> uv = vv) /\
      // Key invariant fully restored (for all MST w including u)
      (forall (v w: nat). v < n /\ w < n /\
        SZ.v (Seq.index in_mst_seq v) <> 1 /\
        SZ.v (Seq.index in_mst_seq w) = 1 /\
        w * n + v < n * n /\
        SZ.v (Seq.index weights_seq (w * n + v)) > 0 /\
        SZ.v (Seq.index weights_seq (w * n + v)) < SZ.v infinity ==>
        SZ.v (Seq.index ks_new v) <= SZ.v (Seq.index weights_seq (w * n + v))) /\
      // Parent-in-MST maintained: for non-source v with finite key, parent in MST
      (forall (v: nat). v < n /\ SZ.v (Seq.index ks_new v) < SZ.v infinity /\ v <> source ==>
        SZ.v (Seq.index in_mst_seq (SZ.v (Seq.index ps_new v))) = 1) /\
      // In-MST vertices have finite keys (unchanged from old; keys only change for non-MST)
      (forall (v: nat). v < n /\ SZ.v (Seq.index in_mst_seq v) = 1 ==>
        SZ.v (Seq.index ks_new v) < SZ.v infinity))
    (ensures prim_inv ks_new ps_new in_mst_seq weights_seq n source)
  = // prim_safe transfers from old to new key/parent
    prim_safe_update_non_mst ps_old ks_old ps_new ks_new in_mst_seq weights_seq n source;
    reveal_opaque (`%prim_inv) (prim_inv ks_new ps_new in_mst_seq weights_seq n source)
#pop-options

(*** Post-loop MST derivation helpers ***)

/// Length of edges_from_parent_key is n - 1
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec efpk_length
    (ps ks: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\ i <= n /\ source < n)
    (ensures FStar.List.Tot.length (edges_from_parent_key ps ks n source i) =
             n - i - (if i <= source then 1 else 0))
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then efpk_length ps ks n source (i + 1)
    else efpk_length ps ks n source (i + 1)
#pop-options

/// Each edge in efpk has valid endpoints (from parent_valid)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec efpk_valid_endpoints
    (ps ks: Seq.seq SZ.t) (n source: nat) (i: nat) (e: edge)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\ i <= n /\ source < n /\
              parent_valid ps n /\
              mem_edge e (edges_from_parent_key ps ks n source i))
    (ensures e.u < n /\ e.v < n)
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then efpk_valid_endpoints ps ks n source (i + 1) e
    else
      let ei = {u = SZ.v (Seq.index ps i); v = i; w = SZ.v (Seq.index ks i)} in
      if edge_eq e ei then begin
        edge_eq_endpoints e ei;
        // ei.u = parent[i], ei.v = i. edges_from_parent_key skips source (i <> source).
        // We need parent[i] <> i. parent_valid gives parent[i] < n, but not <> i.
        // Actually, for edges_from_parent_key, we don't know parent[i] <> i in general.
        // But the caller provides parent_valid which only says < n.
        // However, the edge IS in the graph, so u <> v should follow from the fact that
        // it's a valid graph edge. For now, let me just prove the endpoints from edge_eq.
        // edge_eq e ei → (e.u=ei.u ∧ e.v=ei.v) ∨ (e.u=ei.v ∧ e.v=ei.u)
        // In either case, {e.u, e.v} = {parent[i], i}. Need parent[i] <> i.
        // But we don't have this! Let me weaken the ensures to just e.u < n /\ e.v < n.
        assert (e.u < n /\ e.v < n)
      end
      else efpk_valid_endpoints ps ks n source (i + 1) e

/// Each edge in efpk has one endpoint = some j >= i where j <> source and j is the loop index
/// More precisely: there exists j >= i, j < n, j <> source such that
/// edge_eq e {parent[j], j, key[j]}
let rec efpk_v_ge_i
    (ps ks: Seq.seq SZ.t) (n source: nat) (i: nat) (e: edge)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\ i <= n /\ source < n /\
              mem_edge e (edges_from_parent_key ps ks n source i))
    (ensures exists (j:nat). j >= i /\ j < n /\ j <> source /\
              edge_eq e ({u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)}))
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then efpk_v_ge_i ps ks n source (i + 1) e
    else
      let ei = {u = SZ.v (Seq.index ps i); v = i; w = SZ.v (Seq.index ks i)} in
      if edge_eq e ei then ()
      else efpk_v_ge_i ps ks n source (i + 1) e

/// Track noRepeats through add-vertex step using parent-in-MST.
/// When adding u to MST, parent[v] ≠ u for all in-MST v (because ims[u] <> 1 but ims[parent[v]] = 1).
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec mst_edges_noRepeats_add
    (ps ks ims_old ims_new: Seq.seq SZ.t) (n source u: nat) (i: nat)
  : Lemma
    (requires
      Seq.length ps == n /\ Seq.length ks == n /\
      Seq.length ims_old == n /\ Seq.length ims_new == n /\
      i <= n /\ source < n /\ u < n /\ u <> source /\
      parent_valid ps n /\
      all_keys_bounded ks /\
      SZ.v (Seq.index ks u) < SZ.v infinity /\
      SZ.v (Seq.index ims_old u) <> 1 /\
      SZ.v (Seq.index ims_new u) = 1 /\
      (forall (v:nat). v < n /\ v <> u ==> Seq.index ims_new v == Seq.index ims_old v) /\
      // Parent-in-MST (pre-add): parent[v] is in old MST for finite-key non-source v
      (forall (v:nat). v < n /\ SZ.v (Seq.index ks v) < SZ.v infinity /\ v <> source ==>
        SZ.v (Seq.index ims_old (SZ.v (Seq.index ps v))) = 1) /\
      // Old edges have noRepeats
      Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_old n source i))
    (ensures Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_new n source i))
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then
      mst_edges_noRepeats_add ps ks ims_old ims_new n source u (i + 1)
    else begin
      let ei = {u = SZ.v (Seq.index ps i); v = i; w = SZ.v (Seq.index ks i)} in
      let old_here = SZ.v (Seq.index ims_old i) = 1 in
      let new_here = SZ.v (Seq.index ims_new i) = 1 in
      if i = u then begin
        // Newly added vertex. ei is the new edge. Need: ei ∉ tail AND tail is noRepeats.
        assert (new_here);
        assert (not old_here);
        mst_edges_noRepeats_add ps ks ims_old ims_new n source u (i + 1);
        // ei = {parent[u], u, key[u]}. For any e in tail (mst_edges_so_far ... (i+1)):
        // e corresponds to some j > u with ims_new[j] = 1. Since j <> u, ims_old[j] = 1.
        // edge_eq ei e case 2: parent[u] = j and u = parent[j].
        // parent[j] = u means ims_old[parent[j]] = ims_old[u] <> 1. But parent-in-MST says
        // ims_old[parent[j]] = 1 (if key[j] < infinity and j <> source).
        // If key[j] >= infinity: j is in MST (ims_old[j] = 1) but key[j] >= infinity.
        //   edges_from_parent_key still includes j... yes, unconditionally if ims[j] = 1 in mst_edges_so_far.
        //   But actually, mst_edges_so_far includes j if ims[j] = 1 regardless of key value.
        //   Hmm. For edge_eq ei e where e = {parent[j], j, key[j]}:
        //   Case 2: parent[u] = j and u = parent[j] and key[u] = key[j].
        //   If key[j] < infinity: parent-in-MST gives ims_old[parent[j]] = ims_old[u] = 1. 
        //   But ims_old[u] <> 1. Contradiction. So case 2 impossible when key[j] < infinity.
        //   If key[j] >= infinity (= infinity since bounded): key[u] < infinity (from extract-min).
        //   So key[u] <> key[j]. Edge_eq requires same weight. Case 2 impossible.
        // edge_eq ei e case 1: parent[u] = parent[j] and u = j. But j > u (from i+1). Contradiction.
        // So not (mem_edge ei tail).
        let tl_new = mst_edges_so_far ps ks ims_new n source (i + 1) in
        let aux (e: edge) : Lemma
          (requires mem_edge e tl_new)
          (ensures ~(edge_eq ei e))
          = // e corresponds to some j >= i+1 with ims_new[j] = 1
            mst_edges_mem_implies_in_mst ps ks ims_new n source (i + 1) e;
            FStar.Classical.exists_elim
              (~(edge_eq ei e))
              #nat #(fun j -> j >= i + 1 /\ j < n /\ j <> source /\
                       SZ.v (Seq.index ims_new j) = 1 /\
                       edge_eq e ({u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)}))
              ()
              (fun (j: nat{j >= i + 1 /\ j < n /\ j <> source /\
                           SZ.v (Seq.index ims_new j) = 1 /\
                           edge_eq e ({u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)})}) ->
                assert (j <> u); // j >= i+1 = u+1
                assert (SZ.v (Seq.index ims_old j) = 1);
                let ej = {u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)} in
                // ei = {parent[u], u, key[u]}. If edge_eq ei e and edge_eq e ej, then edge_eq ei ej.
                // (by transitivity)
                // Case 1 for edge_eq ei ej: parent[u] = parent[j] and u = j → j = u, contradiction.
                // Case 2 for edge_eq ei ej: parent[u] = j and u = parent[j] and key[u] = key[j].
                //   If key[j] < infinity: parent-in-MST → ims_old[parent[j]] = ims_old[u] = 1. But ims_old[u] <> 1.
                //   If key[j] >= infinity: key[u] < infinity <> key[j]. Weight mismatch.
                if edge_eq ei e then begin
                  edge_eq_transitive ei e ej;
                  // Now edge_eq ei ej. ei.v = u = i, ej.v = j > i.
                  edge_eq_endpoints ei ej;
                  // endpoints: {parent[u], u} = {parent[j], j}
                  // Since u < j (u = i, j >= i+1), u <> j.
                  // So parent[u] = j and u = parent[j].
                  // parent[j] = u means ims_old[parent[j]] = ims_old[u] <> 1.
                  // But if key[j] < SZ.v infinity:
                  //   parent-in-MST: ims_old[parent[j]] = 1. Contradiction.
                  // If key[j] >= SZ.v infinity:
                  //   key[u] < SZ.v infinity <> key[j] >= SZ.v infinity.
                  //   edge_eq requires same w. ei.w = key[u] < infinity, ej.w = key[j] >= infinity.
                  //   So ei.w <> ej.w. edge_eq ei ej is false. Contradiction.
                  ()
                end)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end
      else if new_here then begin
        // Was already in old MST (since i <> u and ims_new = ims_old for i <> u)
        assert (old_here);
        mst_edges_noRepeats_add ps ks ims_old ims_new n source u (i + 1);
        // Old noRepeats: ei not in old tail AND old tail is noRepeats.
        // New tail adds u's edge. Need: ei not in new tail.
        // Old: not (mem_edge ei (mst_edges_so_far ps ks ims_old n source (i+1))).
        // New tail = old tail + possibly u's edge (at position u if u > i).
        // If u > i: new tail has all of old tail's edges plus {parent[u], u, key[u]}.
        // Need: ei ≠ {parent[u], u, key[u]}.
        // ei = {parent[i], i, key[i]}. u's edge = {parent[u], u, key[u]}.
        // Case 1: parent[i] = parent[u] and i = u → i <> u, contradiction.
        // Case 2: parent[i] = u and i = parent[u] and key[i] = key[u].
        //   parent[i] = u means ims_old[parent[i]] = ims_old[u] <> 1.
        //   But parent-in-MST (old): if key[i] < infinity, ims_old[parent[i]] = 1. Contradiction.
        //   If key[i] >= infinity: key[i] <> key[u] (key[u] < infinity). Weight mismatch.
        // So not (edge_eq ei u_edge). Combined with old: not (mem_edge ei new_tail).
        // Actually, I need a more careful argument using mst_edges_so_far structure.
        // Let me just use: old tail was noRepeats and ei wasn't in old tail.
        // new tail: for any e in new tail, either e was in old tail or e corresponds to vertex u.
        let tl_new = mst_edges_so_far ps ks ims_new n source (i + 1) in
        let aux (e: edge) : Lemma
          (requires mem_edge e tl_new)
          (ensures ~(edge_eq ei e))
          = mst_edges_mem_implies_in_mst ps ks ims_new n source (i + 1) e;
            FStar.Classical.exists_elim
              (~(edge_eq ei e))
              #nat #(fun j -> j >= i + 1 /\ j < n /\ j <> source /\
                       SZ.v (Seq.index ims_new j) = 1 /\
                       edge_eq e ({u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)}))
              ()
              (fun (j: nat{j >= i + 1 /\ j < n /\ j <> source /\
                           SZ.v (Seq.index ims_new j) = 1 /\
                           edge_eq e ({u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)})}) ->
                let ej = {u = SZ.v (Seq.index ps j); v = j; w = SZ.v (Seq.index ks j)} in
                if j = u then begin
                  // e corresponds to the newly added vertex u.
                  // ei = {parent[i], i, key[i]}, ej = {parent[u], u, key[u]}.
                  // If edge_eq ei e and edge_eq e ej → edge_eq ei ej.
                  // edge_eq ei ej: endpoints {parent[i], i} = {parent[u], u}. i <> u.
                  // So parent[i] = u and i = parent[u].
                  // parent[i] = u: ims_old[u] <> 1. But parent-in-MST (old ims, before add):
                  //   if key[i] < infinity: ims_old[parent[i]] = ims_old[u] = 1. Contradiction.
                  //   if key[i] >= infinity: key[i] >= infinity <> key[u] < infinity. Weight mismatch.
                  if edge_eq ei e then begin
                    edge_eq_transitive ei e ej;
                    edge_eq_endpoints ei ej;
                    ()
                  end
                end else begin
                  // j was in old MST (j <> u → ims_old[j] = ims_new[j] = 1)
                  assert (SZ.v (Seq.index ims_old j) = 1);
                  mst_edges_in_mst_implies_mem ps ks ims_old n source (i + 1) j;
                  // ej ∈ old tail. And ei ∉ old tail (from old noRepeats). 
                  // If edge_eq ei e and edge_eq e ej → edge_eq ei ej.
                  // But mem_edge ej old_tail and not (mem_edge ei old_tail).
                  // If edge_eq ei ej, then mem_edge_eq ei ej old_tail → mem_edge ei old_tail. Contradiction.
                  if edge_eq ei e then begin
                    edge_eq_transitive ei e ej;
                    edge_eq_symmetric ei ej;
                    mem_edge_eq ej ei (mst_edges_so_far ps ks ims_old n source (i + 1))
                  end
                end)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end
      else begin
        // Not in MST (neither old nor new, since i <> u → ims_new = ims_old)
        assert (not old_here);
        mst_edges_noRepeats_add ps ks ims_old ims_new n source u (i + 1)
      end
    end
#pop-options

/// noRepeats for mst_edges_so_far is initially trivially true (no edges)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let mst_edges_noRepeats_init
    (ps ks ims: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\
              Seq.length ims == n /\ source < n /\
              (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index ims v) <> 1))
    (ensures Bridge.noRepeats_edge (mst_edges_so_far ps ks ims n source 0))
  = mst_edges_none_in ps ks ims n source 0
#pop-options

/// Helpers for post-loop: remove_edge_first, pigeonhole, all_connected_from_superset
/// (Copied from Kruskal.Impl since they're local to that module)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec remove_edge_first (e: edge) (l: list edge) : list edge =
  match l with
  | [] -> []
  | hd :: tl -> if edge_eq e hd then tl else hd :: remove_edge_first e tl

let rec remove_edge_first_length (e: edge) (l: list edge)
  : Lemma (requires mem_edge e l)
          (ensures FStar.List.Tot.length (remove_edge_first e l) = FStar.List.Tot.length l - 1)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl -> if edge_eq e hd then () else remove_edge_first_length e tl

let rec remove_edge_first_mem (x e: edge) (l: list edge)
  : Lemma (requires mem_edge x l /\ ~(edge_eq x e))
          (ensures mem_edge x (remove_edge_first e l))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      if edge_eq e hd then begin
        if edge_eq x hd then begin
          edge_eq_symmetric e hd;
          edge_eq_transitive x hd e
        end
      end
      else if edge_eq x hd then ()
      else remove_edge_first_mem x e tl

let rec pigeonhole_edges (a b: list edge)
  : Lemma
    (requires Bridge.noRepeats_edge a /\ subset_edges a b /\
              FStar.List.Tot.length a = FStar.List.Tot.length b)
    (ensures forall (e: edge). mem_edge e b ==> mem_edge e a)
    (decreases a)
  = match a with
    | [] -> ()
    | hd :: tl ->
      assert (mem_edge hd b);
      let b' = remove_edge_first hd b in
      remove_edge_first_length hd b;
      let rec prove_tl_subset (p: list edge)
        : Lemma (requires (forall (e: edge). mem_edge e p ==> mem_edge e tl) /\
                          Bridge.noRepeats_edge (hd :: tl) /\
                          subset_edges (hd :: tl) b)
                (ensures subset_edges p b')
                (decreases p)
        = match p with
          | [] -> ()
          | e :: rest ->
            assert (mem_edge e tl);
            assert (not (mem_edge hd tl));
            (if edge_eq e hd then begin
              edge_eq_symmetric e hd;
              mem_edge_eq hd e tl
            end);
            mem_edge_subset e (hd :: tl) b;
            remove_edge_first_mem e hd b;
            prove_tl_subset rest
      in
      prove_tl_subset tl;
      pigeonhole_edges tl b';
      let aux (e: edge) : Lemma
        (requires mem_edge e b)
        (ensures mem_edge e a)
        = if edge_eq e hd then ()
          else begin
            remove_edge_first_mem e hd b;
            assert (mem_edge e b');
            assert (mem_edge e tl)
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let all_connected_from_superset (nn: nat) (sub sup: list edge)
  : Lemma
    (requires
      nn > 0 /\
      all_connected nn sub /\
      (forall (e: edge). mem_edge e sub ==> mem_edge e sup))
    (ensures all_connected nn sup)
  = let aux (v: nat) : Lemma
      (requires v < nn) (ensures reachable sup 0 v)
      = assert (reachable sub 0 v);
        let path_transfer (path: list edge) : Lemma
          (requires subset_edges path sub /\ is_path_from_to path 0 v)
          (ensures reachable sup 0 v)
          = let rec transfer_subset (p: list edge)
              : Lemma (requires subset_edges p sub)
                      (ensures subset_edges p sup)
                      (decreases p)
              = match p with
                | [] -> ()
                | hd :: tl -> transfer_subset tl
            in
            transfer_subset path
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires path_transfer)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options


(*** Greedy step helpers ***)

/// mst_edges_so_far is unchanged when only ims[source] changes
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec mst_edges_source_unchanged
    (ps ks ims_old ims_new: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\
              Seq.length ims_old == n /\ Seq.length ims_new == n /\
              i <= n /\ source < n /\
              (forall (v:nat). v < n /\ v <> source ==> Seq.index ims_old v == Seq.index ims_new v))
    (ensures mst_edges_so_far ps ks ims_old n source i == mst_edges_so_far ps ks ims_new n source i)
    (decreases (n - i))
  = if i >= n then ()
    else if i = source then mst_edges_source_unchanged ps ks ims_old ims_new n source (i + 1)
    else begin
      mst_edges_source_unchanged ps ks ims_old ims_new n source (i + 1);
      assert (Seq.index ims_old i == Seq.index ims_new i)
    end
#pop-options


(*** Helpers for closing admits ***)

let rec count_ones (s: Seq.seq SZ.t) (n: nat) (i: nat)
  : Pure nat (requires Seq.length s >= n /\ i <= n) (ensures fun r -> r <= n - i) (decreases (n - i))
  = if i >= n then 0
    else (if SZ.v (Seq.index s i) = 1 then 1 else 0) + count_ones s n (i + 1)

#push-options "--fuel 2 --ifuel 0 --z3rlimit 50"
let rec count_ones_upd (s: Seq.seq SZ.t) (n u: nat) (i: nat)
  : Lemma
    (requires Seq.length s >= n /\ i <= n /\ u < n /\ SZ.v (Seq.index s u) <> 1 /\
              (forall (j:nat). j < n ==> SZ.v (Seq.index s j) = 0 \/ SZ.v (Seq.index s j) = 1))
    (ensures count_ones (Seq.upd s u 1sz) n i == count_ones s n i + (if i <= u then 1 else 0))
    (decreases (n - i))
  = if i >= n then ()
    else begin count_ones_upd s n u (i + 1);
      if i = u then assert (SZ.v (Seq.index (Seq.upd s u 1sz) i) = 1)
      else assert (Seq.index (Seq.upd s u 1sz) i == Seq.index s i) end
#pop-options

#push-options "--fuel 2 --ifuel 0 --z3rlimit 50"
let rec count_ones_all (s: Seq.seq SZ.t) (n: nat) (i: nat)
  : Lemma
    (requires Seq.length s >= n /\ i <= n /\ count_ones s n i = n - i /\
              (forall (j:nat). j < n ==> SZ.v (Seq.index s j) = 0 \/ SZ.v (Seq.index s j) = 1))
    (ensures forall (v:nat). v >= i /\ v < n ==> SZ.v (Seq.index s v) = 1)
    (decreases (n - i))
  = if i >= n then ()
    else begin
      if SZ.v (Seq.index s i) <> 1 then assert (count_ones s n (i + 1) <= n - i - 1);
      count_ones_all s n (i + 1) end
#pop-options

#push-options "--fuel 2 --ifuel 0 --z3rlimit 50"
let rec count_ones_has_zero (s: Seq.seq SZ.t) (n: nat) (i: nat)
  : Lemma
    (requires Seq.length s >= n /\ i <= n /\ count_ones s n i < n - i)
    (ensures exists (v:nat). v >= i /\ v < n /\ SZ.v (Seq.index s v) <> 1)
    (decreases (n - i))
  = if i >= n then () else if SZ.v (Seq.index s i) <> 1 then () else count_ones_has_zero s n (i + 1)
#pop-options

#push-options "--fuel 2 --ifuel 0 --z3rlimit 50"
let rec count_ones_pos (s: Seq.seq SZ.t) (n: nat) (i: nat) (v: nat)
  : Lemma
    (requires Seq.length s >= n /\ i <= n /\ v >= i /\ v < n /\ SZ.v (Seq.index s v) = 1)
    (ensures count_ones s n i >= 1) (decreases (n - i))
  = if i >= n then () else if i = v then () else count_ones_pos s n (i + 1) v
#pop-options

#push-options "--fuel 2 --ifuel 0 --z3rlimit 30"
let rec count_ones_zero (s: Seq.seq SZ.t) (n: nat) (i: nat)
  : Lemma
    (requires Seq.length s >= n /\ i <= n /\ (forall (j:nat). j < n ==> SZ.v (Seq.index s j) <> 1))
    (ensures count_ones s n i = 0) (decreases (n - i))
  = if i >= n then () else count_ones_zero s n (i + 1)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec mst_edges_source_ims_unchanged
    (ps ks ims1 ims2: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\ Seq.length ims1 == n /\ Seq.length ims2 == n /\
              i <= n /\ source < n /\ (forall (v:nat). v < n /\ v <> source ==> Seq.index ims1 v == Seq.index ims2 v))
    (ensures mst_edges_so_far ps ks ims1 n source i == mst_edges_so_far ps ks ims2 n source i)
    (decreases (n - i))
  = if i >= n then () else if i = source then mst_edges_source_ims_unchanged ps ks ims1 ims2 n source (i + 1)
    else begin mst_edges_source_ims_unchanged ps ks ims1 ims2 n source (i + 1); assert (Seq.index ims1 i == Seq.index ims2 i) end
#pop-options

let mst_edges_noRepeats_source_unchanged (ps ks ims_old ims_new: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires Seq.length ps == n /\ Seq.length ks == n /\ Seq.length ims_old == n /\ Seq.length ims_new == n /\
              source < n /\ (forall (v:nat). v < n /\ v <> source ==> Seq.index ims_old v == Seq.index ims_new v) /\
              Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_old n source 0))
    (ensures Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_new n source 0))
  = mst_edges_source_ims_unchanged ps ks ims_old ims_new n source 0

#push-options "--z3rlimit 600 --fuel 2 --ifuel 1 --split_queries always"
let min_key_finite (ks ps ims ws: Seq.seq SZ.t) (n source u: nat) (min_key: nat)
  : Lemma
    (requires
      prim_inv ks ps ims ws n source /\ n > 0 /\ source < n /\ u < n /\
      Seq.length ks == n /\ Seq.length ps == n /\ Seq.length ims == n /\ Seq.length ws == n * n /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index ims j) = 0 \/ SZ.v (Seq.index ims j) = 1) /\
      min_key <= SZ.v infinity /\
      (min_key < SZ.v infinity ==> min_key == SZ.v (Seq.index ks u) /\ SZ.v (Seq.index ims u) = 0) /\
      (forall (j:nat). j < n /\ SZ.v (Seq.index ims j) = 0 ==> min_key <= SZ.v (Seq.index ks j)) /\
      (exists (v:nat). v < n /\ SZ.v (Seq.index ims v) <> 1) /\
      all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n))
    (ensures min_key < SZ.v infinity /\ SZ.v (Seq.index ks u) < SZ.v infinity /\ SZ.v (Seq.index ims u) = 0)
  = prim_inv_elim ks ps ims ws n source;
    prim_kpc_elim ks ps ws n source;
    if SZ.v (Seq.index ims source) = 0 then begin
      assert (min_key <= SZ.v (Seq.index ks source));
      assert (SZ.v (Seq.index ks source) == 0);
      assert (min_key < SZ.v infinity)
    end else begin
      assert (SZ.v (Seq.index ims source) = 1);
      let adj = weights_to_adj_matrix ws n in
      let g_edges = PrimSpec.adj_to_edges adj n in
      PrimSpec.adj_to_graph_edges adj n;
      FStar.Classical.exists_elim
        (min_key < SZ.v infinity /\ SZ.v (Seq.index ks u) < SZ.v infinity /\ SZ.v (Seq.index ims u) = 0)
        #nat #(fun v -> v < n /\ SZ.v (Seq.index ims v) <> 1) ()
        (fun (v0: nat{v0 < n /\ SZ.v (Seq.index ims v0) <> 1}) ->
          assert (reachable g_edges 0 source); assert (reachable g_edges 0 v0);
          reachable_symmetric g_edges 0 source; reachable_transitive g_edges source 0 v0;
          let s : cut = fun (v: nat) -> v < Seq.length ims && SZ.v (Seq.index ims v) = 1 in
          FStar.Classical.exists_elim
            (min_key < SZ.v infinity /\ SZ.v (Seq.index ks u) < SZ.v infinity /\ SZ.v (Seq.index ims u) = 0)
            #(list edge) #(fun path -> subset_edges path g_edges /\ is_path_from_to path source v0) ()
            (fun (path: list edge{subset_edges path g_edges /\ is_path_from_to path source v0}) ->
              path_crosses_when_sides_differ path g_edges s source v0;
              FStar.Classical.exists_elim
                (min_key < SZ.v infinity /\ SZ.v (Seq.index ks u) < SZ.v infinity /\ SZ.v (Seq.index ims u) = 0)
                #edge #(fun e' -> mem_edge e' path /\ mem_edge e' g_edges /\ crosses_cut e' s) ()
                (fun (e': edge{mem_edge e' path /\ mem_edge e' g_edges /\ crosses_cut e' s}) ->
                  PrimSpec.adj_to_graph_edges_valid adj n e';
                  weights_to_adj_well_formed ws n;
                  graph_edge_weight_eq ws n e';
                  lemma_index_bound e'.u e'.v n; lemma_index_bound e'.v e'.u n;
                  if SZ.v (Seq.index ims e'.u) = 1 && SZ.v (Seq.index ims e'.v) <> 1 then begin
                    assert (SZ.v (Seq.index ims e'.v) = 0);
                    assert (min_key <= SZ.v (Seq.index ks e'.v))
                  end else assert (SZ.v (Seq.index ims e'.u) = 0))))
    end
#pop-options

/// Source case greedy step.
#push-options "--z3rlimit 4000 --fuel 2 --ifuel 1"
let prim_greedy_step_source
    (ks ps ims_old ims_new ws: Seq.seq SZ.t) (n source: nat) (min_key: nat) (iter_count: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\
      Seq.length ks == n /\ Seq.length ps == n /\
      Seq.length ims_old == n /\ Seq.length ims_new == n /\
      Seq.length ws == n * n /\
      prim_inv ks ps ims_old ws n source /\
      Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_old n source 0) /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index ims_old j) = 0 \/ SZ.v (Seq.index ims_old j) = 1) /\
      SZ.v (Seq.index ims_new source) = 1 /\
      (forall (v:nat). v < n /\ v <> source ==> Seq.index ims_new v == Seq.index ims_old v) /\
      min_key <= SZ.v infinity /\
      (min_key < SZ.v infinity ==>
        min_key == SZ.v (Seq.index ks source) /\ SZ.v (Seq.index ims_old source) = 0) /\
      (forall (j:nat). j < n /\ SZ.v (Seq.index ims_old j) = 0 ==>
        min_key <= SZ.v (Seq.index ks j)) /\
      count_ones ims_old n 0 = iter_count /\ iter_count < n /\
      all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n))
    (ensures
      prim_safe ps ks ims_new ws n source /\
      prim_kpc ks ps ws n source /\
      Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_new n source 0) /\
      count_ones ims_new n 0 = iter_count + 1 /\
      SZ.v (Seq.index ims_new source) = 1 /\
      SZ.v (Seq.index ims_old source) = 0 /\
      SZ.v (Seq.index ks source) < SZ.v infinity)
  = prim_inv_elim ks ps ims_old ws n source;
    count_ones_has_zero ims_old n 0;
    min_key_finite ks ps ims_old ws n source source min_key;
    assert (Seq.equal ims_new (Seq.upd ims_old source 1sz));
    Seq.lemma_eq_elim ims_new (Seq.upd ims_old source 1sz);
    count_ones_upd ims_old n source 0;
    prim_inv_add_source ks ps ims_old ims_new ws n source;
    mst_edges_noRepeats_source_unchanged ps ks ims_old ims_new n source
#pop-options

/// Non-source case greedy step.
#push-options "--z3rlimit 2000 --fuel 2 --ifuel 1"
let prim_greedy_step_nonsource
    (ks ps ims_old ims_new ws: Seq.seq SZ.t) (n source u: nat) (min_key: nat) (iter_count: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ u < n /\ u <> source /\
      Seq.length ks == n /\ Seq.length ps == n /\
      Seq.length ims_old == n /\ Seq.length ims_new == n /\
      Seq.length ws == n * n /\
      prim_inv ks ps ims_old ws n source /\
      Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_old n source 0) /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index ims_old j) = 0 \/ SZ.v (Seq.index ims_old j) = 1) /\
      SZ.v (Seq.index ims_new u) = 1 /\
      (forall (v:nat). v < n /\ v <> u ==> Seq.index ims_new v == Seq.index ims_old v) /\
      min_key <= SZ.v infinity /\
      (min_key < SZ.v infinity ==>
        min_key == SZ.v (Seq.index ks u) /\ SZ.v (Seq.index ims_old u) = 0) /\
      (forall (j:nat). j < n /\ SZ.v (Seq.index ims_old j) = 0 ==>
        min_key <= SZ.v (Seq.index ks j)) /\
      count_ones ims_old n 0 = iter_count /\ iter_count < n /\
      (iter_count > 0 ==> SZ.v (Seq.index ims_old source) = 1) /\
      all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n))
    (ensures
      prim_safe ps ks ims_new ws n source /\
      prim_kpc ks ps ws n source /\
      Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_new n source 0) /\
      count_ones ims_new n 0 = iter_count + 1 /\
      SZ.v (Seq.index ims_new source) = 1 /\
      SZ.v (Seq.index ims_old u) = 0 /\
      SZ.v (Seq.index ks u) < SZ.v infinity)
  = count_ones_has_zero ims_old n 0;
    min_key_finite ks ps ims_old ws n source u min_key;
    assert (Seq.equal ims_new (Seq.upd ims_old u 1sz));
    Seq.lemma_eq_elim ims_new (Seq.upd ims_old u 1sz);
    count_ones_upd ims_old n u 0;
    prim_inv_add_vertex ks ps ims_old ims_new ws n source u;
    prim_inv_elim ks ps ims_old ws n source;
    mst_edges_noRepeats_add ps ks ims_old ims_new n source u 0;
    assert (SZ.v (Seq.index ims_old (SZ.v (Seq.index ps u))) = 1);
    let pu = SZ.v (Seq.index ps u) in
    count_ones_pos ims_old n 0 pu
#pop-options

/// Combined greedy step for Pulse.
#push-options "--z3rlimit 4000 --fuel 2 --ifuel 1"
let prim_greedy_step
    (ks ps ims_old ims_new ws: Seq.seq SZ.t) (n source u: nat) (min_key: nat) (iter_count: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ u < n /\
      Seq.length ks == n /\ Seq.length ps == n /\
      Seq.length ims_old == n /\ Seq.length ims_new == n /\
      Seq.length ws == n * n /\
      prim_inv ks ps ims_old ws n source /\
      Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_old n source 0) /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index ims_old j) = 0 \/ SZ.v (Seq.index ims_old j) = 1) /\
      SZ.v (Seq.index ims_new u) = 1 /\
      (forall (v:nat). v < n /\ v <> u ==> Seq.index ims_new v == Seq.index ims_old v) /\
      min_key <= SZ.v infinity /\
      (min_key < SZ.v infinity ==>
        min_key == SZ.v (Seq.index ks u) /\ SZ.v (Seq.index ims_old u) = 0) /\
      (forall (j:nat). j < n /\ SZ.v (Seq.index ims_old j) = 0 ==>
        min_key <= SZ.v (Seq.index ks j)) /\
      count_ones ims_old n 0 = iter_count /\ iter_count < n /\
      (iter_count > 0 ==> SZ.v (Seq.index ims_old source) = 1) /\
      all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix ws n) n))
    (ensures
      prim_safe ps ks ims_new ws n source /\
      prim_kpc ks ps ws n source /\
      Bridge.noRepeats_edge (mst_edges_so_far ps ks ims_new n source 0) /\
      count_ones ims_new n 0 = iter_count + 1 /\
      SZ.v (Seq.index ims_new source) = 1 /\
      SZ.v (Seq.index ims_old u) = 0 /\
      SZ.v (Seq.index ks u) < SZ.v infinity /\
      (forall (j:nat). j < n ==> SZ.v (Seq.index ims_new j) = 0 \/ SZ.v (Seq.index ims_new j) = 1))
  = if u = source then
      prim_greedy_step_source ks ps ims_old ims_new ws n source min_key iter_count
    else begin
      prim_greedy_step_nonsource ks ps ims_old ims_new ws n source u min_key iter_count;
      prim_inv_elim ks ps ims_old ws n source
    end
#pop-options


/// Opaque MST result: imperative edges form MST for connected symmetric graphs
[@@"opaque_to_smt"]
let prim_mst_result
    (parent_seq key_seq weights_seq: Seq.seq SZ.t) (n source: nat) : prop =
  n > 0 /\ source < n /\
  Seq.length parent_seq == n /\ Seq.length key_seq == n /\
  Seq.length weights_seq == n * n /\
  (symmetric_weights weights_seq n /\
   all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq n) n) ==>
   is_mst (PrimSpec.adj_to_graph (weights_to_adj_matrix weights_seq n) n)
          (edges_from_parent_key parent_seq key_seq n source 0))

let prim_mst_result_elim
    (parent_seq key_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires prim_mst_result parent_seq key_seq weights_seq n source /\
              Seq.length parent_seq == n /\ Seq.length key_seq == n /\
              symmetric_weights weights_seq n /\
              all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq n) n))
    (ensures is_mst (PrimSpec.adj_to_graph (weights_to_adj_matrix weights_seq n) n)
                    (edges_from_parent_key parent_seq key_seq n source 0))
  = reveal_opaque (`%prim_mst_result) (prim_mst_result parent_seq key_seq weights_seq n source)

/// Post-loop MST derivation: from prim_inv + all vertices in MST + symmetric + connected → is_mst
/// Split into two parts: this helper proves is_mst directly (given symmetric + connected),
/// then the main function wraps it into prim_mst_result.
#restart-solver
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries always"
let derive_prim_is_mst
    (key_seq parent_seq in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      prim_inv key_seq parent_seq in_mst_seq weights_seq n source /\
      n > 0 /\ source < n /\
      Seq.length parent_seq == n /\ Seq.length key_seq == n /\
      Seq.length in_mst_seq == n /\ Seq.length weights_seq == n * n /\
      Bridge.noRepeats_edge (mst_edges_so_far parent_seq key_seq in_mst_seq n source 0) /\
      (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index in_mst_seq v) = 1) /\
      symmetric_weights weights_seq n /\
      all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq n) n))
    (ensures is_mst (PrimSpec.adj_to_graph (weights_to_adj_matrix weights_seq n) n)
                    (edges_from_parent_key parent_seq key_seq n source 0))
  = prim_inv_elim key_seq parent_seq in_mst_seq weights_seq n source;
    mst_edges_all_in parent_seq key_seq in_mst_seq n source 0;
    efpk_length parent_seq key_seq n source 0;
    let adj = weights_to_adj_matrix weights_seq n in
    let g = PrimSpec.adj_to_graph adj n in
    let efpk = edges_from_parent_key parent_seq key_seq n source 0 in
    PrimSpec.adj_to_graph_edges adj n;
    prim_safe_elim parent_seq key_seq in_mst_seq weights_seq n source;
    let ve (e: edge) : Lemma
      (requires mem_edge e g.edges) (ensures e.u < g.n /\ e.v < g.n /\ e.u <> e.v)
      = PrimSpec.adj_to_graph_edges_valid adj n e
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ve);
    FStar.Classical.exists_elim
      (is_mst g efpk)
      #(list edge) #(fun t -> is_mst g t /\ subset_edges efpk t) ()
      (fun (t: list edge{is_mst g t /\ subset_edges efpk t}) ->
        assert (is_spanning_tree g t);
        assert (acyclic g.n t);
        pigeonhole_edges efpk t;
        all_connected_from_superset n t efpk;
        subset_edges_transitive efpk t g.edges;
        // efpk ⊆ t and t is acyclic → efpk is acyclic
        let aux_acyclic (e: edge) : Lemma
          (requires mem_edge e efpk)
          (ensures mem_edge e t)
          = mem_edge_subset e efpk t
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_acyclic);
        acyclic_subset g.n t efpk;
        Bridge.safe_spanning_tree_is_mst g efpk)

let derive_prim_mst_post_loop
    (key_seq parent_seq in_mst_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      prim_inv key_seq parent_seq in_mst_seq weights_seq n source /\
      n > 0 /\ source < n /\
      Seq.length parent_seq == n /\ Seq.length key_seq == n /\
      Seq.length in_mst_seq == n /\ Seq.length weights_seq == n * n /\
      Bridge.noRepeats_edge (mst_edges_so_far parent_seq key_seq in_mst_seq n source 0) /\
      (forall (v:nat). v < n /\ v <> source ==> SZ.v (Seq.index in_mst_seq v) = 1))
    (ensures prim_mst_result parent_seq key_seq weights_seq n source)
  = prim_inv_elim key_seq parent_seq in_mst_seq weights_seq n source;
    reveal_opaque (`%prim_mst_result) (prim_mst_result parent_seq key_seq weights_seq n source);
    FStar.Classical.arrow_to_impl
      #(symmetric_weights weights_seq n /\
        all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq n) n))
      #(is_mst (PrimSpec.adj_to_graph (weights_to_adj_matrix weights_seq n) n)
               (edges_from_parent_key parent_seq key_seq n source 0))
      (fun _ -> derive_prim_is_mst key_seq parent_seq in_mst_seq weights_seq n source)
#pop-options

// Prim's MST algorithm
// Given:
//   - weights: n×n weight matrix (flattened as array[n*n])
//   - n: number of vertices
//   - source: starting vertex
// Output:
//   - key: array of minimum edge weights to add each vertex to MST
//   - in_mst: array indicating which vertices are in MST

/// Hoisted extract-min loop: find the minimum-key non-MST vertex.
/// Returns (min_idx, min_key) pair.
#push-options "--z3rlimit 400"
fn find_min_vertex
  (key_a: array SZ.t) (#key_seq: Ghost.erased (Seq.seq SZ.t))
  (in_mst: array SZ.t) (#in_mst_seq: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  requires A.pts_to key_a key_seq ** A.pts_to in_mst in_mst_seq ** pure (
    SZ.v n > 0 /\
    Seq.length key_seq == SZ.v n /\
    Seq.length in_mst_seq == SZ.v n /\
    all_keys_bounded key_seq /\
    SZ.fits_u64
  )
  returns res: (SZ.t & SZ.t)
  ensures A.pts_to key_a key_seq ** A.pts_to in_mst in_mst_seq ** pure (
    Seq.length key_seq == SZ.v n /\
    Seq.length in_mst_seq == SZ.v n /\
    SZ.v (fst res) < SZ.v n /\
    SZ.v (snd res) <= SZ.v infinity /\
    (SZ.v (snd res) < SZ.v infinity ==>
      SZ.v (snd res) == SZ.v (Seq.index key_seq (SZ.v (fst res))) /\
      SZ.v (Seq.index in_mst_seq (SZ.v (fst res))) = 0) /\
    (forall (j:nat). j < SZ.v n /\ SZ.v (Seq.index in_mst_seq j) = 0 ==>
      SZ.v (snd res) <= SZ.v (Seq.index key_seq j))
  )
{
  let mut min_idx: SZ.t = 0sz;
  let mut min_key: SZ.t = infinity;
  let mut find_i: SZ.t = 0sz;
  
  while (
    let v_find_i = !find_i;
    v_find_i <^ n
  )
  invariant exists* v_find_i v_min_idx v_min_key key_seq0 in_mst_seq0.
    R.pts_to find_i v_find_i **
    R.pts_to min_idx v_min_idx **
    R.pts_to min_key v_min_key **
    A.pts_to key_a key_seq0 **
    A.pts_to in_mst in_mst_seq0 **
    pure (
      SZ.v v_find_i <= SZ.v n /\
      SZ.v v_min_idx < SZ.v n /\
      Seq.length key_seq0 == SZ.v n /\
      Seq.length in_mst_seq0 == SZ.v n /\
      SZ.v n > 0 /\ SZ.fits_u64 /\
      all_keys_bounded key_seq0 /\
      // Ghost frame: arrays unchanged
      key_seq0 == Ghost.reveal key_seq /\
      in_mst_seq0 == Ghost.reveal in_mst_seq /\
      // Extract-min tracking:
      SZ.v v_min_key <= SZ.v infinity /\
      (SZ.v v_min_key < SZ.v infinity ==>
        SZ.v v_min_key == SZ.v (Seq.index key_seq0 (SZ.v v_min_idx)) /\
        SZ.v (Seq.index in_mst_seq0 (SZ.v v_min_idx)) = 0) /\
      (forall (j:nat). j < SZ.v v_find_i /\ SZ.v (Seq.index in_mst_seq0 j) = 0 ==>
        SZ.v v_min_key <= SZ.v (Seq.index key_seq0 j))
    )
  decreases (SZ.v n - SZ.v !find_i)
  {
    let v_find_i = !find_i;
    let ki = A.op_Array_Access key_a v_find_i;
    let in_mst_i = A.op_Array_Access in_mst v_find_i;
    let v_min_key = !min_key;
    let v_min_idx = !min_idx;
    
    assert (pure (SZ.v ki <= SZ.v infinity));
    
    let cond1 = (in_mst_i = 0sz);
    let cond2 = (ki <^ v_min_key);
    let should_update = (cond1 && cond2);
    let new_min_key : SZ.t = (if should_update then ki else v_min_key);
    let new_min_idx : SZ.t = (if should_update then v_find_i else v_min_idx);
    
    min_key := new_min_key;
    min_idx := new_min_idx;
    
    find_i := v_find_i +^ 1sz;
  };
  
  let result = !min_idx;
  let final_key = !min_key;
  (result, final_key)
}
#pop-options

#push-options "--z3rlimit 400"
//SNIPPET_START: prim_sig
fn prim
  (#p: perm)
  (weights: array SZ.t)
  (#weights_seq: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (source: SZ.t)
  requires A.pts_to weights #p weights_seq ** pure (
    SZ.v n > 0 /\
    SZ.v n * SZ.v n < pow2 64 /\
    SZ.v source < SZ.v n /\
    Seq.length weights_seq == SZ.v n * SZ.v n /\
    SZ.fits_u64 /\
    valid_weights weights_seq (SZ.v n) /\
    symmetric_weights weights_seq (SZ.v n) /\
    all_connected (SZ.v n) (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq (SZ.v n)) (SZ.v n)) /\
    // No zero-weight off-diagonal entries (standard MST convention)
    (forall (u v: nat). u < SZ.v n /\ v < SZ.v n /\ u * SZ.v n + v < SZ.v n * SZ.v n /\
      SZ.v (Seq.index weights_seq (u * SZ.v n + v)) = 0 ==> u = v)
  )
  returns res: (V.vec SZ.t & V.vec SZ.t)
  ensures exists* (key_seq parent_seq: Ghost.erased (Seq.seq SZ.t)).
    A.pts_to weights #p weights_seq **
    V.pts_to (fst res) key_seq **
    V.pts_to (snd res) parent_seq **
    pure (prim_correct key_seq parent_seq weights_seq (SZ.v n) (SZ.v source) /\
          prim_mst_result parent_seq key_seq weights_seq (SZ.v n) (SZ.v source))
//SNIPPET_END: prim_sig
{
  // Allocate key array, initialized to infinity
  let key = V.alloc infinity n;
  V.to_array_pts_to key;
  let key_a = V.vec_to_array key;
  rewrite (A.pts_to (V.vec_to_array key) (Seq.create (SZ.v n) infinity))
       as (A.pts_to key_a (Seq.create (SZ.v n) infinity));
  
  // Allocate parent array, initialized to source
  let parent_v = V.alloc source n;
  V.to_array_pts_to parent_v;
  let parent_a = V.vec_to_array parent_v;
  rewrite (A.pts_to (V.vec_to_array parent_v) (Seq.create (SZ.v n) source))
       as (A.pts_to parent_a (Seq.create (SZ.v n) source));
  
  // Set key[source] = 0
  A.op_Array_Assignment key_a source 0sz;
  
  // Establish initial correctness properties
  with key_seq_init. assert (A.pts_to key_a key_seq_init);
  lemma_create_bounded (SZ.v n) infinity;
  lemma_upd_preserves_bounded (Seq.create (SZ.v n) infinity) (SZ.v source) 0sz;
  assert (pure (Seq.equal key_seq_init (Seq.upd (Seq.create (SZ.v n) infinity) (SZ.v source) 0sz)));
  assert (pure (SZ.v (Seq.index key_seq_init (SZ.v source)) == 0));
  assert (pure (all_keys_bounded key_seq_init));
  
  // Allocate in_mst array, initialized to 0
  let in_mst_v = V.alloc 0sz n;
  V.to_array_pts_to in_mst_v;
  let in_mst = V.vec_to_array in_mst_v;
  rewrite (A.pts_to (V.vec_to_array in_mst_v) (Seq.create (SZ.v n) 0sz))
       as (A.pts_to in_mst (Seq.create (SZ.v n) 0sz));
  
  // Establish initial parent array and new properties
  with parent_init. assert (A.pts_to parent_a parent_init);
  lemma_create_parent_valid (SZ.v n) source;
  assert (pure (parent_valid parent_init (SZ.v n)));
  prim_kpc_init key_seq_init parent_init weights_seq (SZ.v n) (SZ.v source);
  
  // Establish greedy safety and prim_inv
  with in_mst_init. assert (A.pts_to in_mst in_mst_init);
  assert (pure (Seq.equal in_mst_init (Seq.create (SZ.v n) 0sz)));
  prim_safe_init parent_init key_seq_init in_mst_init weights_seq (SZ.v n) (SZ.v source);
  prim_inv_init key_seq_init parent_init in_mst_init weights_seq (SZ.v n) (SZ.v source);
  mst_edges_noRepeats_init parent_init key_seq_init in_mst_init (SZ.v n) (SZ.v source);
  
  // Main loop: n iterations
  let mut iter: SZ.t = 0sz;
  
  while (
    let v_iter = !iter;
    v_iter <^ n
  )
  invariant exists* v_iter key_seq in_mst_seq parent_seq.
    R.pts_to iter v_iter **
    A.pts_to key_a key_seq **
    A.pts_to in_mst in_mst_seq **
    A.pts_to parent_a parent_seq **
    A.pts_to weights #p weights_seq **
    pure (
      SZ.v v_iter <= SZ.v n + 1 /\
      Seq.length key_seq == SZ.v n /\
      Seq.length in_mst_seq == SZ.v n /\
      Seq.length parent_seq == SZ.v n /\
      SZ.v n * SZ.v n < pow2 64 /\ SZ.fits_u64 /\
      Seq.length weights_seq == SZ.v n * SZ.v n /\
      SZ.v n > 0 /\ SZ.v source < SZ.v n /\
      prim_inv key_seq parent_seq in_mst_seq weights_seq (SZ.v n) (SZ.v source) /\
      Bridge.noRepeats_edge (mst_edges_so_far parent_seq key_seq in_mst_seq (SZ.v n) (SZ.v source) 0) /\
      // Maintain functional correctness (needed for Pulse array operations):
      SZ.v (Seq.index key_seq (SZ.v source)) == 0 /\
      all_keys_bounded key_seq /\
      (forall (j:nat). j < Seq.length parent_seq ==> SZ.v (Seq.index parent_seq j) < SZ.v n) /\
      (forall (j:nat). j < SZ.v n ==> SZ.v (Seq.index in_mst_seq j) = 0 \/ SZ.v (Seq.index in_mst_seq j) = 1) /\
      count_ones in_mst_seq (SZ.v n) 0 = SZ.v v_iter /\
      (SZ.v v_iter > 0 ==> SZ.v (Seq.index in_mst_seq (SZ.v source)) = 1) /\
      all_connected (SZ.v n) (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq (SZ.v n)) (SZ.v n))
    )
  // TODO: decreases — proof interference
  {
    // Find minimum key vertex not in MST (hoisted function)
    let min_result = find_min_vertex key_a in_mst n;
    let u = fst min_result;
    
    // Save old state for the greedy step proof
    with ks_pre_add ps_pre_add ims_pre_add. 
      assert (A.pts_to key_a ks_pre_add ** A.pts_to parent_a ps_pre_add ** A.pts_to in_mst ims_pre_add);
    
    // Add u to MST
    A.op_Array_Assignment in_mst u 1sz;
    
    // Greedy step: branch on u = source vs u <> source
    with ims_post_add. assert (A.pts_to in_mst ims_post_add);
    
    // Greedy step
    with v_iter_pre. assert (R.pts_to iter v_iter_pre);
    prim_greedy_step ks_pre_add ps_pre_add ims_pre_add ims_post_add weights_seq
      (SZ.v n) (SZ.v source) (SZ.v u) (SZ.v (snd min_result)) (SZ.v v_iter_pre);
    
    // After add-vertex: prim_safe and prim_kpc on new in_mst
    
    // Update keys of neighbors
    let mut update_i: SZ.t = 0sz;
    
    while (
      let v_update_i = !update_i;
      v_update_i <^ n
    )
    invariant exists* v_update_i v_iter key_seq in_mst_seq parent_seq.
      R.pts_to update_i v_update_i **
      R.pts_to iter v_iter **
      A.pts_to key_a key_seq **
      A.pts_to in_mst in_mst_seq **
      A.pts_to parent_a parent_seq **
      A.pts_to weights #p weights_seq **
      pure (
        SZ.v v_update_i <= SZ.v n /\
        SZ.v u < SZ.v n /\
        SZ.v v_iter <= SZ.v n /\
        Seq.length key_seq == SZ.v n /\
        Seq.length in_mst_seq == SZ.v n /\
        Seq.length parent_seq == SZ.v n /\
        SZ.v u * SZ.v n < pow2 64 /\
        (forall (i:nat). i < SZ.v n ==> SZ.v u * SZ.v n + i < pow2 64) /\
        // Maintain functional correctness:
        SZ.v (Seq.index key_seq (SZ.v source)) == 0 /\
        all_keys_bounded key_seq /\
        (forall (j:nat). j < Seq.length parent_seq ==> SZ.v (Seq.index parent_seq j) < SZ.v n) /\
        Seq.length weights_seq == SZ.v n * SZ.v n /\
        SZ.v n > 0 /\ SZ.v source < SZ.v n /\
        SZ.v n * SZ.v n < pow2 64 /\ SZ.fits_u64 /\
        prim_kpc key_seq parent_seq weights_seq (SZ.v n) (SZ.v source) /\
        prim_safe parent_seq key_seq in_mst_seq weights_seq (SZ.v n) (SZ.v source)
      )
    decreases (SZ.v n - SZ.v !update_i)
    {
      let v = !update_i;
      
      // Read current values
      let key_v = A.op_Array_Access key_a v;
      let in_mst_v = A.op_Array_Access in_mst v;
      
      // Compute weight index: u * n + v
      let weight_idx = compute_weight_idx u n v;
      // Explicit bounds hint for Z3 stability
      lemma_index_bound (SZ.v u) (SZ.v v) (SZ.v n);
      let weight_uv = A.op_Array_Access weights weight_idx;
      
      // Read old parent BEFORE key write (needed for prim_kpc_step)
      let old_parent_v = A.op_Array_Access parent_a v;
      
      // Compute new key and parent values unconditionally
      let cond_not_in_mst = (in_mst_v = 0sz);
      let cond_weight_better = (weight_uv <^ key_v);
      let cond_weight_valid = (weight_uv <^ infinity);
      let should_update_key = (cond_not_in_mst && cond_weight_better && cond_weight_valid);
      let new_key_v : SZ.t = (if should_update_key then weight_uv else key_v);
      let new_parent_v : SZ.t = (if should_update_key then u else old_parent_v);
      
      // Prove that new_key_v is bounded
      assert (pure (SZ.v new_key_v <= SZ.v infinity));
      
      // Maintain key_parent_consistent via opaque wrapper
      with ks ps. assert (A.pts_to key_a ks ** A.pts_to parent_a ps);
      prim_kpc_step ks ps weights_seq (SZ.v n) (SZ.v source) (SZ.v v) new_key_v new_parent_v should_update_key;
      
      // Write key
      A.op_Array_Assignment key_a v new_key_v;
      
      // Assert key invariant is maintained after key write
      with key_seq'. assert (A.pts_to key_a key_seq');
      assert (pure (SZ.v (Seq.index key_seq' (SZ.v source)) == 0));
      assert (pure (all_keys_bounded key_seq'));
      assert (pure (Seq.length key_seq' == SZ.v n));
      
      // Write parent
      A.op_Array_Assignment parent_a v new_parent_v;
      
      // Maintain prim_safe: only non-MST vertices modified
      with ks_after ps_after ims_after. assert (A.pts_to key_a ks_after ** A.pts_to parent_a ps_after ** A.pts_to in_mst ims_after);
      prim_safe_update_non_mst ps ks ps_after ks_after ims_after weights_seq (SZ.v n) (SZ.v source);
      
      update_i := v +^ 1sz;
    };
    
    // Increment iteration counter
    let v_iter = !iter;
    assert (pure (SZ.v n * SZ.v n < pow2 64));
    assert (pure (SZ.v v_iter + 1 < pow2 64));
    SZ.fits_u64_implies_fits (SZ.v v_iter + 1);
    let new_iter = v_iter +^ 1sz;
    assert (pure (SZ.v new_iter == SZ.v v_iter + 1));
    iter := new_iter;
  };
  
  // Set parent[source] = source (source is MST root)
  with old_parent_seq. assert (A.pts_to parent_a old_parent_seq);
  A.op_Array_Assignment parent_a source source;
  
  // Extract prim_kpc from prim_inv
  with old_key_seq old_ims_final. assert (A.pts_to key_a old_key_seq ** A.pts_to in_mst old_ims_final);
  prim_inv_elim old_key_seq old_parent_seq old_ims_final weights_seq (SZ.v n) (SZ.v source);
  
  // Prove parent_valid is maintained after parent[source] = source
  with final_parent_seq. assert (A.pts_to parent_a final_parent_seq);
  lemma_upd_preserves_parent_valid old_parent_seq (SZ.v source) source (SZ.v n);
  // Maintain key_parent_consistent after parent[source] = source
  prim_kpc_parent_source old_key_seq old_parent_seq weights_seq (SZ.v n) (SZ.v source) source;
  prim_kpc_elim old_key_seq final_parent_seq weights_seq (SZ.v n) (SZ.v source);
  
  // Derive prim_mst_result using derive_prim_mst_post_loop
  // Derive prim_mst_result
  count_ones_all old_ims_final (SZ.v n) 0;
  derive_prim_mst_post_loop old_key_seq old_parent_seq old_ims_final weights_seq (SZ.v n) (SZ.v source);
  
  // Free the in_mst array
  with s_in_mst. assert (A.pts_to in_mst s_in_mst);
  rewrite (A.pts_to in_mst s_in_mst) as (A.pts_to (V.vec_to_array in_mst_v) s_in_mst);
  V.to_vec_pts_to in_mst_v;
  V.free in_mst_v;
  
  // Convert key array back to vec for return
  with s_key. assert (A.pts_to key_a s_key);
  rewrite (A.pts_to key_a s_key) as (A.pts_to (V.vec_to_array key) s_key);
  V.to_vec_pts_to key;
  
  // Convert parent array back to vec for return
  with s_parent. assert (A.pts_to parent_a s_parent);
  rewrite (A.pts_to parent_a s_parent) as (A.pts_to (V.vec_to_array parent_v) s_parent);
  V.to_vec_pts_to parent_v;
  
  (key, parent_v)
}
#pop-options

(*** MST Bridging Theorem ***)

/// Main MST theorem: if the extracted edges form a safe spanning tree, the result is MST.
///
/// Preconditions from the Pulse function: prim_correct
/// Additional preconditions (true for Prim's greedy selection, but
/// not yet tracked by the Pulse loop invariant):
///   - Extracted edges form a spanning tree of the graph
///   - Extracted edges are safe (⊆ some MST), from greedy_step_safe induction
///   - No duplicate edges
///
/// See Kruskal.Bridge for safe_spanning_tree_is_mst.
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let prim_result_is_mst
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      n > 0 /\
      prim_correct key_seq parent_seq weights_seq n source /\
      Seq.length weights_seq == n * n /\
      (let adj = weights_to_adj_matrix weights_seq n in
       let g = PrimSpec.adj_to_graph adj n in
       let wes = edges_from_parent_key parent_seq key_seq n source 0 in
       is_spanning_tree g wes /\
       (exists (t: list edge). is_mst g t /\ subset_edges wes t) /\
       Bridge.noRepeats_edge wes /\
       (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v)))
    (ensures
      (let adj = weights_to_adj_matrix weights_seq n in
       let g = PrimSpec.adj_to_graph adj n in
       let wes = edges_from_parent_key parent_seq key_seq n source 0 in
       is_mst g wes))
  = let adj = weights_to_adj_matrix weights_seq n in
    let g = PrimSpec.adj_to_graph adj n in
    let wes = edges_from_parent_key parent_seq key_seq n source 0 in
    Bridge.safe_spanning_tree_is_mst g wes
#pop-options
