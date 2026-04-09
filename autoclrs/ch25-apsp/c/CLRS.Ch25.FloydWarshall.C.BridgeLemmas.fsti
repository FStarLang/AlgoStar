module CLRS.Ch25.FloydWarshall.C.BridgeLemmas

(**
 * Bridge lemmas connecting the c2pulse C implementation specifications
 * to the F* mathematical spec in CLRS.Ch25.FloydWarshall.Spec.
 *
 * The c2pulse implementation (floydWarshall.c) operates on Int32.t arrays
 * with the precondition that all entries are in [0, INF].  The handwritten
 * Pulse implementation (CLRS.Ch25.FloydWarshall.Impl) operates on
 * mathematical int arrays and proves contents == fw_outer.
 *
 * These bridge lemmas establish:
 * 1. weights_bounded (from Spec) implies the [0, INF] bounds when
 *    combined with an upper-bound assumption on infinite values.
 * 2. The fw_outer computation preserves the [0, INF] bound,
 *    matching the C code's postcondition.
 * 3. fw_outer values are monotone-decreasing relative to the input,
 *    matching the C code's dist[p] <= old(dist[p]) postcondition.
 *)

open FStar.Mul
open FStar.Seq
open CLRS.Ch25.FloydWarshall.Spec

(** Bridge 1: weights_bounded + values <= inf implies [0, inf] bound.
    The C code requires all entries in [0, INF].  This lemma shows that
    weights_bounded plus an upper bound on infinite values suffices. *)
val weights_bounded_entries_in_range (d: seq int) (n: nat) (p: nat)
  : Lemma
    (requires
      weights_bounded d n /\ p < n * n /\
      index d p <= inf)
    (ensures index d p >= 0 /\ index d p <= inf)

(** Bridge 2: fw_inner_j preserves non-negativity.
    When all entries are non-negative, the relaxation min(d_ij, d_ik + d_kj)
    remains non-negative.  Also establishes length preservation. *)
val fw_inner_j_preserves_nonneg
  (d: seq int) (n k i j: nat) (d_ik: int)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ k < n /\ i < n /\
      d_ik >= 0 /\
      (forall (p: nat). p < n * n ==> index d p >= 0))
    (ensures
      length (fw_inner_j d n k i j d_ik) == n * n /\
      (forall (p: nat). p < n * n ==>
        index (fw_inner_j d n k i j d_ik) p >= 0))

(** Bridge 3: fw_inner_j preserves [0, inf] bound.
    When all entries are in [0, inf] and d_ik in [0, inf],
    relaxation keeps values in [0, inf]. *)
val fw_inner_j_preserves_bound
  (d: seq int) (n k i j: nat) (d_ik: int)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ k < n /\ i < n /\
      d_ik >= 0 /\ d_ik <= inf /\
      (forall (p: nat). p < n * n ==> index d p >= 0 /\ index d p <= inf))
    (ensures
      length (fw_inner_j d n k i j d_ik) == n * n /\
      (forall (p: nat). p < n * n ==>
        index (fw_inner_j d n k i j d_ik) p >= 0 /\
        index (fw_inner_j d n k i j d_ik) p <= inf))

(** Bridge 4: fw_outer preserves [0, inf] bounds.
    This is the key bridge: if the input is in [0, inf],
    then fw_outer keeps all values in [0, inf]. *)
val fw_outer_preserves_bounds
  (d: seq int) (n k: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\
      (forall (p: nat). p < n * n ==> index d p >= 0 /\ index d p <= inf))
    (ensures
      length (fw_outer d n k) == n * n /\
      (forall (p: nat). p < n * n ==>
        index (fw_outer d n k) p >= 0 /\
        index (fw_outer d n k) p <= inf))

(** Bridge 5: fw_inner_j is monotone-decreasing at each position.
    The relaxation step can only decrease values. *)
val fw_inner_j_monotone
  (d: seq int) (n k i j: nat) (d_ik: int) (p: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ k < n /\ i < n /\ p < n * n /\
      d_ik >= 0)
    (ensures
      length (fw_inner_j d n k i j d_ik) == n * n /\
      index (fw_inner_j d n k i j d_ik) p <= index d p)

(** Bridge 6: fw_outer is monotone-decreasing.
    Each entry in fw_outer d n k is <= the corresponding entry in d.
    This matches the C code's dist[p] <= old(dist[p]) postcondition. *)
val fw_outer_monotone
  (d: seq int) (n k: nat) (p: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ p < n * n /\
      (forall (q: nat). q < n * n ==> index d q >= 0))
    (ensures
      length (fw_outer d n k) == n * n /\
      index (fw_outer d n k) p <= index d p)
