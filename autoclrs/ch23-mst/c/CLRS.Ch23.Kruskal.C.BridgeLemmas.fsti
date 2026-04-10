module CLRS.Ch23.Kruskal.C.BridgeLemmas

/// Bridge lemmas connecting c2pulse's option-typed representations
/// to the Seq int / Seq SZ.t representations used by Kruskal specs.

open FStar.Mul
module Seq = FStar.Seq
module SZ = FStar.SizeT
module I32 = FStar.Int32
open CLRS.Ch23.Kruskal.Impl
open CLRS.Ch23.Kruskal.Defs

/// --- Int32 unwrapping (for adjacency matrix: Seq.seq (option I32.t) → Seq.seq int) ---

let unwrap_int32_val (o: option I32.t) : int =
  match o with | Some v -> I32.v v | None -> 0

val unwrap_int32_eq_somev (o: option I32.t)
  : Lemma (requires Some? o) (ensures unwrap_int32_val o == I32.v (Some?.v o))
    [SMTPat (unwrap_int32_val o)]

let unwrap_int32_seq (s: Seq.seq (option I32.t)) (n: nat{n <= Seq.length s})
  : Seq.seq int =
  Seq.init n (fun (i: nat{i < n}) -> unwrap_int32_val (Seq.index s i))

val unwrap_int32_seq_length (s: Seq.seq (option I32.t)) (n: nat{n <= Seq.length s})
  : Lemma (ensures Seq.length (unwrap_int32_seq s n) = n)
    [SMTPat (Seq.length (unwrap_int32_seq s n))]

val unwrap_int32_seq_index (s: Seq.seq (option I32.t)) (n: nat{n <= Seq.length s}) (i: nat{i < n})
  : Lemma (ensures Seq.index (unwrap_int32_seq s n) i == unwrap_int32_val (Seq.index s i))
    [SMTPat (Seq.index (unwrap_int32_seq s n) i)]

/// --- SZ.t unwrapping (for edge/parent arrays: Seq.seq (option SZ.t) → Seq.seq SZ.t) ---

let unwrap_sz_val (o: option SZ.t) : SZ.t =
  match o with | Some v -> v | None -> 0sz

val unwrap_sz_eq_somev (o: option SZ.t)
  : Lemma (requires Some? o) (ensures unwrap_sz_val o == Some?.v o)
    [SMTPat (unwrap_sz_val o)]

let unwrap_sizet_seq (s: Seq.seq (option SZ.t)) (n: nat{n <= Seq.length s})
  : Seq.seq SZ.t =
  Seq.init n (fun (i: nat{i < n}) -> unwrap_sz_val (Seq.index s i))

val unwrap_sizet_seq_length (s: Seq.seq (option SZ.t)) (n: nat{n <= Seq.length s})
  : Lemma (ensures Seq.length (unwrap_sizet_seq s n) = n)
    [SMTPat (Seq.length (unwrap_sizet_seq s n))]

/// --- Bundled postcondition predicate ---

let kruskal_result_post
  (sadj: Seq.seq (option I32.t))
  (seu sev: Seq.seq (option SZ.t))
  (n: nat{n <= Seq.length seu /\ n <= Seq.length sev})
  (adj_len: nat{adj_len <= Seq.length sadj})
  (ec: nat) : prop =
  result_is_forest_adj
    (unwrap_int32_seq sadj adj_len)
    (sizet_seq_to_int (unwrap_sizet_seq seu n))
    (sizet_seq_to_int (unwrap_sizet_seq sev n))
    n ec /\
  kruskal_mst_result
    (unwrap_int32_seq sadj adj_len)
    (sizet_seq_to_int (unwrap_sizet_seq seu n))
    (sizet_seq_to_int (unwrap_sizet_seq sev n))
    n ec

/// --- Assembly lemma ---
/// NOTE: proof uses admit() — the complex union-find / is_forest / MST proof
/// from CLRS.Ch23.Kruskal.Impl.fst (2373 lines) is not ported to the C bridge.
/// The C code structurally carries the right spec shape; completing the proof
/// requires porting kruskal_inv tracking + UF correspondence.

val kruskal_result_assembly
  (sadj: Seq.seq (option I32.t))
  (seu sev: Seq.seq (option SZ.t))
  (n ec: SZ.t)
  (adj_len: nat)
  : Lemma
    (requires
      SZ.v n > 0 /\ adj_len = SZ.v n * SZ.v n /\ adj_len <= Seq.length sadj /\
      SZ.v n <= Seq.length seu /\ SZ.v n <= Seq.length sev /\
      SZ.v ec < SZ.v n /\
      (forall (k:SZ.t). SZ.lt k ec ==> SZ.lt (unwrap_sz_val (Seq.index seu (SZ.v k))) n) /\
      (forall (k:SZ.t). SZ.lt k ec ==> SZ.lt (unwrap_sz_val (Seq.index sev (SZ.v k))) n))
    (ensures kruskal_result_post sadj seu sev (SZ.v n) adj_len (SZ.v ec))
