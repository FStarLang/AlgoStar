(**
 * ISMM: Arithmetic helper lemmas for SZ.fits and index bounds.
 *
 * Adapted from CLRS.Ch22.Graph.Common (autoclrs).
 * These lemmas help discharge SZ.fits and array index proof obligations
 * in the Freeze, Dispose, and RefCount implementations.
 *)
module ISMM.Arith.Lemmas

open FStar.Mul
module SZ = FStar.SizeT

(*** Strict product bound: c < a ∧ d < b ⟹ c*b + d < a*b ***)
let product_strict_bound (a b c d: nat)
  : Lemma (requires c < a /\ d < b)
          (ensures c * b + d < a * b)
  = ()

(*** SZ.fits preservation for smaller products ***)
let fits_product_smaller (a b c d: nat)
  : Lemma (requires c < a /\ d <= b /\ SZ.fits (a * b))
          (ensures SZ.fits (c * b) /\ SZ.fits (c * b + d))
  = assert (c * b <= a * b);
    assert (c * b + d <= a * b)

(*** SZ.fits for n*(n+1) when SZ.fits(n*(n+1)) is given ***)
(* Note: SZ.fits(n*n) does NOT imply SZ.fits(n*(n+1)).
   Callers should include SZ.fits(n*(n+1)) as a precondition when using ghost counters. *)


(*** Ghost counter bound: gc < n*(n+1) ⟹ fits(gc+1) ***)
let ghost_ctr_fits (n gc: nat)
  : Lemma (requires gc < n * (n + 1) /\ SZ.fits (n * (n + 1)))
          (ensures SZ.fits (gc + 1))
  = assert (gc + 1 <= n * (n + 1))

(*** Inner counter bound: ic < n*n ⟹ fits(ic+1) ***)
let inner_ctr_fits (n ic: nat)
  : Lemma (requires ic < n * n /\ SZ.fits (n * n))
          (ensures SZ.fits (ic + 1))
  = assert (ic + 1 <= n * n)

(*** RC increment: rc < n*n ⟹ fits(rc+1) ***)
let rc_inc_fits (rc bound: nat)
  : Lemma (requires rc < bound /\ SZ.fits bound)
          (ensures SZ.fits (rc + 1))
  = assert (rc + 1 <= bound)

(*** RC decrement: rc > 0 ⟹ fits(rc-1) ***)
let rc_dec_fits (rc: nat)
  : Lemma (requires rc > 0 /\ SZ.fits rc)
          (ensures SZ.fits (rc - 1))
  = ()

(*** Adjacency index fits: x < n ∧ fi < n ∧ fits(n*n) ⟹ fits(x*n+fi) ∧ x*n+fi < n*n ***)
let adj_index_fits (n x fi: nat)
  : Lemma (requires x < n /\ fi < n /\ SZ.fits (n * n))
          (ensures SZ.fits (x * n + fi) /\ x * n + fi < n * n)
  = product_strict_bound n n x fi

module Seq = FStar.Seq

(*** Stack content invariant after push: upd preserves all-less-than bound ***)
let seq_upd_content_bound (s: Seq.seq SZ.t) (top: nat) (bound: nat) (v: SZ.t)
  : Lemma
    (requires
      top < Seq.length s /\
      SZ.v v < bound /\
      (forall (i:nat). i < top ==> SZ.v (Seq.index s i) < bound))
    (ensures
      (forall (i:nat). {:pattern (Seq.index (Seq.upd s top v) i)}
        i < top + 1 ==> SZ.v (Seq.index (Seq.upd s top v) i) < bound))
  = let aux (i:nat{i < top + 1})
      : Lemma (SZ.v (Seq.index (Seq.upd s top v) i) < bound)
      = if i = top then Seq.lemma_index_upd1 s top v
        else Seq.lemma_index_upd2 s top v i
    in FStar.Classical.forall_intro aux

(*** Stack content after push: ≤ variant (for edge stacks) ***)
let seq_upd_content_le_bound (s: Seq.seq SZ.t) (top: nat) (bound: nat) (v: SZ.t)
  : Lemma
    (requires
      top < Seq.length s /\
      SZ.v v <= bound /\
      (forall (i:nat). i < top ==> SZ.v (Seq.index s i) <= bound))
    (ensures
      (forall (i:nat). {:pattern (Seq.index (Seq.upd s top v) i)}
        i < top + 1 ==> SZ.v (Seq.index (Seq.upd s top v) i) <= bound))
  = let aux (i:nat{i < top + 1})
      : Lemma (SZ.v (Seq.index (Seq.upd s top v) i) <= bound)
      = if i = top then Seq.lemma_index_upd1 s top v
        else Seq.lemma_index_upd2 s top v i
    in FStar.Classical.forall_intro aux

(*** Edge update preserves content invariant: updating an existing entry ≤ bound ***)
let seq_upd_existing_le_bound (s: Seq.seq SZ.t) (top: nat) (bound: nat) (idx: nat) (v: SZ.t)
  : Lemma
    (requires
      idx < top /\ top <= Seq.length s /\
      SZ.v v <= bound /\
      (forall (i:nat). i < top ==> SZ.v (Seq.index s i) <= bound))
    (ensures
      (forall (i:nat). {:pattern (Seq.index (Seq.upd s idx v) i)}
        i < top ==> SZ.v (Seq.index (Seq.upd s idx v) i) <= bound))
  = let aux (i:nat{i < top})
      : Lemma (SZ.v (Seq.index (Seq.upd s idx v) i) <= bound)
      = if i = idx then Seq.lemma_index_upd1 s idx v
        else Seq.lemma_index_upd2 s idx v i
    in FStar.Classical.forall_intro aux
