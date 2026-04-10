module CLRS.Ch23.Prim.C.BridgeLemmas

/// Bridge lemmas connecting c2pulse's option SZ.t representation
/// to the Seq SZ.t representation used by CLRS.Ch23.Prim.Impl specs.

open FStar.Mul
module Seq = FStar.Seq
module SZ = FStar.SizeT
open CLRS.Ch23.Prim.Impl

/// Convert option SZ.t to SZ.t (None → 0sz)
let unwrap_sz_val (o: option SZ.t) : SZ.t =
  match o with | Some v -> v | None -> 0sz

/// Bridge: unwrap_sz_val equals Some?.v when Some? holds
val unwrap_eq_somev (o: option SZ.t)
  : Lemma (requires Some? o) (ensures unwrap_sz_val o == Some?.v o)
    [SMTPat (unwrap_sz_val o)]

/// Convert option-SZ.t sequence to SZ.t sequence
let unwrap_sizet_seq (s: Seq.seq (option SZ.t)) (n: nat{n <= Seq.length s})
  : Seq.seq SZ.t =
  Seq.init n (fun (i: nat{i < n}) -> unwrap_sz_val (Seq.index s i))

val unwrap_sizet_seq_length (s: Seq.seq (option SZ.t)) (n: nat{n <= Seq.length s})
  : Lemma (ensures Seq.length (unwrap_sizet_seq s n) = n)
          [SMTPat (Seq.length (unwrap_sizet_seq s n))]

val unwrap_sizet_seq_index (s: Seq.seq (option SZ.t)) (n: nat{n <= Seq.length s}) (i: nat{i < n})
  : Lemma (ensures Seq.index (unwrap_sizet_seq s n) i == unwrap_sz_val (Seq.index s i))
          [SMTPat (Seq.index (unwrap_sizet_seq s n) i)]

/// Seq.upd commutes with unwrap
val unwrap_upd_commutes (s: Seq.seq (option SZ.t)) (n: nat{n <= Seq.length s}) (i: nat{i < n}) (v: SZ.t)
  : Lemma (ensures unwrap_sizet_seq (Seq.upd s i (Some v)) n == Seq.upd (unwrap_sizet_seq s n) i v)

/// key_parent_consistent over option sequences
let kpc_opt (sk sp sw: Seq.seq (option SZ.t)) (n source: nat) : prop =
  n <= Seq.length sk /\ n <= Seq.length sp /\ n * n <= Seq.length sw /\
  key_parent_consistent (unwrap_sizet_seq sk n) (unwrap_sizet_seq sp n) (unwrap_sizet_seq sw (n * n)) n source

/// kpc_opt initialization: all keys == Some infinity → kpc holds vacuously
/// Uses nat quantifier to match _inline_pulse invariant from init loop.
val kpc_opt_init (sk sp sw: Seq.seq (option SZ.t)) (n source: nat)
  : Lemma
    (requires
      n <= Seq.length sk /\ n <= Seq.length sp /\ n * n <= Seq.length sw /\
      source < n /\
      (forall (v:nat). v < n ==> Seq.index sk v == Some infinity))
    (ensures kpc_opt sk sp sw n source)

/// kpc_opt step: updating key[v] and parent[v] preserves kpc.
/// Uses Seq.index == Some w_uv (directly from array_read + array_initialized).
val kpc_opt_step (sk sp sw: Seq.seq (option SZ.t)) (n source: nat) (u v_idx w_uv: SZ.t)
  : Lemma
    (requires
      kpc_opt sk sp sw n source /\
      SZ.v v_idx < n /\ SZ.v u < n /\ source < n /\ n > 0 /\
      SZ.v u * n + SZ.v v_idx < n * n /\
      Seq.index sw (SZ.v u * n + SZ.v v_idx) == Some w_uv)
    (ensures kpc_opt (Seq.upd sk (SZ.v v_idx) (Some w_uv)) (Seq.upd sp (SZ.v v_idx) (Some u)) sw n source)

/// kpc_opt: writing key[source] preserves kpc (source excluded from quantifier)
val kpc_opt_write_source_key (sk sp sw: Seq.seq (option SZ.t)) (n source: nat) (new_key: SZ.t)
  : Lemma
    (requires kpc_opt sk sp sw n source /\ source < n /\ n <= Seq.length sk)
    (ensures kpc_opt (Seq.upd sk source (Some new_key)) sp sw n source)

/// kpc_opt: writing parent[source] preserves kpc (source excluded from quantifier)
val kpc_opt_write_source_parent (sk sp sw: Seq.seq (option SZ.t)) (n source: nat) (new_parent: SZ.t)
  : Lemma
    (requires kpc_opt sk sp sw n source /\ source < n /\ n <= Seq.length sp /\ SZ.v new_parent < n)
    (ensures kpc_opt sk (Seq.upd sp source (Some new_parent)) sw n source)

/// Assemble prim_correct from c2pulse-level properties
val prim_correct_assembly (sk sp sw: Seq.seq (option SZ.t)) (n source: nat)
  : Lemma
    (requires
      n <= Seq.length sk /\ n <= Seq.length sp /\ n * n <= Seq.length sw /\
      source < n /\
      SZ.v (unwrap_sz_val (Seq.index sk source)) == 0 /\
      (forall (v:nat). v < n ==> SZ.v (unwrap_sz_val (Seq.index sk v)) <= SZ.v infinity) /\
      SZ.v (unwrap_sz_val (Seq.index sp source)) == source /\
      (forall (v:nat). v < n ==> SZ.v (unwrap_sz_val (Seq.index sp v)) < n) /\
      kpc_opt sk sp sw n source)
    (ensures prim_correct (unwrap_sizet_seq sk n) (unwrap_sizet_seq sp n) (unwrap_sizet_seq sw (n * n)) n source)

/// Bridge SZ.t quantifier to nat quantifier for key bounds.
/// Converts c2pulse's forall(SZ.t) to the nat forall needed by prim_correct_assembly.
val keys_bounded_nat (sk: Seq.seq (option SZ.t)) (n: SZ.t)
  : Lemma
    (requires
      SZ.v n <= Seq.length sk /\
      (forall (i:nat). i < Seq.length sk ==> Some? (Seq.index sk i)) /\
      (forall (j:SZ.t). SZ.v j < SZ.v n ==> SZ.v (Some?.v (Seq.index sk (SZ.v j))) <= SZ.v infinity))
    (ensures
      forall (v:nat). v < SZ.v n ==> SZ.v (unwrap_sz_val (Seq.index sk v)) <= SZ.v infinity)

/// Bridge SZ.t quantifier to nat quantifier for parent validity.
val parents_valid_nat (sp: Seq.seq (option SZ.t)) (n: SZ.t)
  : Lemma
    (requires
      SZ.v n <= Seq.length sp /\
      (forall (i:nat). i < Seq.length sp ==> Some? (Seq.index sp i)) /\
      (forall (j:SZ.t). SZ.v j < SZ.v n ==> SZ.v (Some?.v (Seq.index sp (SZ.v j))) < SZ.v n))
    (ensures
      forall (v:nat). v < SZ.v n ==> SZ.v (unwrap_sz_val (Seq.index sp v)) < SZ.v n)
