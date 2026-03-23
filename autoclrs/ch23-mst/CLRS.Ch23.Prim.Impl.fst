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

/// Greedy step: adding vertex u to MST preserves safety.
let prim_safe_add_vertex
    (parent_seq key_seq in_mst_old in_mst_new weights_seq: Seq.seq SZ.t) (n source u: nat)
  : Lemma
    (requires prim_safe parent_seq key_seq in_mst_old weights_seq n source /\
              n > 0 /\ source < n /\ u < n /\
              Seq.length parent_seq == n /\ Seq.length key_seq == n /\
              Seq.length in_mst_old == n /\ Seq.length in_mst_new == n /\
              Seq.length weights_seq == n * n /\
              parent_valid parent_seq n /\
              prim_kpc parent_seq key_seq weights_seq n source /\
              // in_mst_new = upd in_mst_old u 1
              SZ.v (Seq.index in_mst_new u) = 1 /\
              (forall (v:nat). v < n /\ v <> u ==> Seq.index in_mst_new v == Seq.index in_mst_old v) /\
              // u was the minimum-key non-MST vertex
              SZ.v (Seq.index in_mst_old u) <> 1 /\
              SZ.v (Seq.index key_seq u) < SZ.v infinity /\
              (forall (v:nat). v < n /\ SZ.v (Seq.index in_mst_old v) <> 1 ==>
                SZ.v (Seq.index key_seq u) <= SZ.v (Seq.index key_seq v)))
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
    // subset_edges new_es (new_edge :: old_es) established
    // Now derive prim_safe from this + old safety
    // Case: u = source → new_es = old_es (source is skipped), trivially safe
    // Case: u ≠ source → need greedy_step_safe (TODO: add key invariant precondition)
    admit () // Remaining: greedy_step_safe application + key invariant
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

// Prim's MST algorithm
// Given:
//   - weights: n×n weight matrix (flattened as array[n*n])
//   - n: number of vertices
//   - source: starting vertex
// Output:
//   - key: array of minimum edge weights to add each vertex to MST
//   - in_mst: array indicating which vertices are in MST

#push-options "--z3rlimit 200"
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
    SZ.fits_u64  // Require 64-bit SizeT for index computation
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
  
  // Establish greedy safety: initially no non-source vertices in MST
  with in_mst_init. assert (A.pts_to in_mst in_mst_init);
  assert (pure (Seq.equal in_mst_init (Seq.create (SZ.v n) 0sz)));
  prim_safe_init parent_init key_seq_init in_mst_init weights_seq (SZ.v n) (SZ.v source);
  
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
      // Maintain functional correctness:
      SZ.v (Seq.index key_seq (SZ.v source)) == 0 /\
      all_keys_bounded key_seq /\
      (forall (j:nat). j < Seq.length parent_seq ==> SZ.v (Seq.index parent_seq j) < SZ.v n) /\
      prim_kpc key_seq parent_seq weights_seq (SZ.v n) (SZ.v source) /\
      prim_safe parent_seq key_seq in_mst_seq weights_seq (SZ.v n) (SZ.v source)
    )
  // TODO: decreases — proof interference
  {
    // Find minimum key vertex not in MST
    let mut min_idx: SZ.t = 0sz;
    let mut min_key: SZ.t = infinity;
    let mut find_i: SZ.t = 0sz;
    
    while (
      let v_find_i = !find_i;
      v_find_i <^ n
    )
    invariant exists* v_find_i v_min_idx v_min_key v_iter key_seq in_mst_seq parent_seq.
      R.pts_to find_i v_find_i **
      R.pts_to min_idx v_min_idx **
      R.pts_to min_key v_min_key **
      R.pts_to iter v_iter **
      A.pts_to key_a key_seq **
      A.pts_to in_mst in_mst_seq **
      A.pts_to parent_a parent_seq **
      A.pts_to weights #p weights_seq **
      pure (
        SZ.v v_find_i <= SZ.v n /\
        SZ.v v_min_idx < SZ.v n /\
        SZ.v v_iter <= SZ.v n /\
        Seq.length key_seq == SZ.v n /\
        Seq.length in_mst_seq == SZ.v n /\
        Seq.length parent_seq == SZ.v n /\
        // Maintain functional correctness:
        SZ.v (Seq.index key_seq (SZ.v source)) == 0 /\
        all_keys_bounded key_seq /\
        (forall (j:nat). j < Seq.length parent_seq ==> SZ.v (Seq.index parent_seq j) < SZ.v n) /\
        prim_kpc key_seq parent_seq weights_seq (SZ.v n) (SZ.v source) /\
        prim_safe parent_seq key_seq in_mst_seq weights_seq (SZ.v n) (SZ.v source)
      )
    decreases (SZ.v n - SZ.v !find_i)
    {
      let v_find_i = !find_i;
      let ki = A.op_Array_Access key_a v_find_i;
      let in_mst_i = A.op_Array_Access in_mst v_find_i;
      let v_min_key = !min_key;
      let v_min_idx = !min_idx;
      
      // Update min_key and min_idx unconditionally
      let cond1 = (in_mst_i = 0sz);
      let cond2 = (ki <^ v_min_key);
      let should_update = (cond1 && cond2);
      let new_min_key : SZ.t = (if should_update then ki else v_min_key);
      let new_min_idx : SZ.t = (if should_update then v_find_i else v_min_idx);
      
      min_key := new_min_key;
      min_idx := new_min_idx;
      
      find_i := v_find_i +^ 1sz;
    };
    
    // Add min_idx to MST
    let u = !min_idx;
    A.op_Array_Assignment in_mst u 1sz;
    
    // Greedy step: prim_safe is maintained after adding vertex u to MST
    with ks_step ps_step ims_step. 
      assert (A.pts_to key_a ks_step ** A.pts_to parent_a ps_step ** A.pts_to in_mst ims_step);
    // TODO: need extract-min minimality tracked through the extract-min loop
    // For now, use admitted prim_safe_add_vertex
    admit (); // prim_safe_add_vertex ps_step ks_step ... 
    assert (pure (prim_safe ps_step ks_step ims_step weights_seq (SZ.v n) (SZ.v source)));
    
    // Carry prim_kpc through in_mst write (prim_kpc doesn't depend on in_mst)
    lemma_mul_bound (SZ.v u) (SZ.v n) 0 (pow2 64);
    
    // Update keys of neighbors
    let mut update_i: SZ.t = 0sz;
    
    while (
      let v_update_i = !update_i;
      v_update_i <^ n
    )
    invariant exists* v_update_i v_iter u key_seq in_mst_seq parent_seq.
      R.pts_to update_i v_update_i **
      R.pts_to iter v_iter **
      R.pts_to min_idx u **
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
  
  // Prove parent_valid is maintained after parent[source] = source
  with final_parent_seq. assert (A.pts_to parent_a final_parent_seq);
  lemma_upd_preserves_parent_valid old_parent_seq (SZ.v source) source (SZ.v n);
  // Maintain and reveal key_parent_consistent after parent[source] = source
  with old_key_seq. assert (A.pts_to key_a old_key_seq);
  prim_kpc_parent_source old_key_seq old_parent_seq weights_seq (SZ.v n) (SZ.v source) source;
  prim_kpc_elim old_key_seq final_parent_seq weights_seq (SZ.v n) (SZ.v source);
  
  // Derive prim_mst_result from prim_safe
  // TODO: prove via mst_edges_all_in + safe_spanning_tree_is_mst chain
  with s_in_mst_final. assert (A.pts_to in_mst s_in_mst_final);
  admit (); // prim_mst_result establishment
  
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
