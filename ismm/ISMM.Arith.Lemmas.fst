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

(*** RC-positive invariant preservation: tag update to non-3 preserves forall i. tag[i]=3 ==> rc[i]>0 ***)
let tag_upd_preserves_rc_positive (stag src: Seq.seq SZ.t) (n idx: nat) (v: SZ.t)
  : Lemma
    (requires idx < n /\ n <= Seq.length stag /\ n <= Seq.length src /\
     SZ.v v <> 3 /\
     (forall (i:nat). {:pattern (Seq.index stag i)} i < n /\ SZ.v (Seq.index stag i) == 3 ==> SZ.v (Seq.index src i) > 0))
    (ensures
     (forall (i:nat). {:pattern (Seq.index (Seq.upd stag idx v) i)}
       i < n /\ SZ.v (Seq.index (Seq.upd stag idx v) i) == 3 ==> SZ.v (Seq.index src i) > 0))
  = let stag' = Seq.upd stag idx v in
    let aux (i:nat{i < n /\ SZ.v (Seq.index stag' i) == 3})
      : Lemma (SZ.v (Seq.index src i) > 0)
      = if i = idx then (Seq.lemma_index_upd1 stag idx v; assert False)
        else Seq.lemma_index_upd2 stag idx v i
    in FStar.Classical.forall_intro aux

(*** RC-positive invariant preservation: refcount update preserves forall i. tag[i]=3 ==> rc[i]>0 ***)
let rc_upd_preserves_rc_positive (stag src: Seq.seq SZ.t) (n idx: nat) (v: SZ.t)
  : Lemma
    (requires idx < n /\ n <= Seq.length stag /\ n <= Seq.length src /\
     (SZ.v (Seq.index stag idx) == 3 ==> SZ.v v > 0) /\
     (forall (i:nat). {:pattern (Seq.index stag i)} i < n /\ SZ.v (Seq.index stag i) == 3 ==> SZ.v (Seq.index src i) > 0))
    (ensures
     (forall (i:nat). {:pattern (Seq.index stag i)}
       i < n /\ SZ.v (Seq.index stag i) == 3 ==> SZ.v (Seq.index (Seq.upd src idx v) i) > 0))
  = let src' = Seq.upd src idx v in
    let aux (i:nat{i < n /\ SZ.v (Seq.index stag i) == 3})
      : Lemma (SZ.v (Seq.index src' i) > 0)
      = if i = idx then Seq.lemma_index_upd1 src idx v
        else Seq.lemma_index_upd2 src idx v i
    in FStar.Classical.forall_intro aux

(*** Combined tag+rc update at same index: new_tag ≠ 3 preserves RC-positive ***)
let tag_rc_upd_preserves_rc_positive (stag src: Seq.seq SZ.t) (n idx: nat) (new_tag new_rc: SZ.t)
  : Lemma
    (requires idx < n /\ n <= Seq.length stag /\ n <= Seq.length src /\
     SZ.v new_tag <> 3 /\
     (forall (i:nat). {:pattern (Seq.index stag i)} i < n /\ SZ.v (Seq.index stag i) == 3 ==> SZ.v (Seq.index src i) > 0))
    (ensures
     (let stag' = Seq.upd stag idx new_tag in
      let src' = Seq.upd src idx new_rc in
      forall (i:nat). {:pattern (Seq.index stag' i)}
        i < n /\ SZ.v (Seq.index stag' i) == 3 ==> SZ.v (Seq.index src' i) > 0))
  = let stag' = Seq.upd stag idx new_tag in
    let src' = Seq.upd src idx new_rc in
    let aux (i:nat{i < n /\ SZ.v (Seq.index stag' i) == 3})
      : Lemma (SZ.v (Seq.index src' i) > 0)
      = if i = idx then (Seq.lemma_index_upd1 stag idx new_tag; assert False)
        else begin
          Seq.lemma_index_upd2 stag idx new_tag i;
          Seq.lemma_index_upd2 src idx new_rc i
        end
    in FStar.Classical.forall_intro aux

(*** RC-positive: tag update at exception index upgrades exception-form to standard-form ***)
let tag_upd_upgrades_rc_positive (stag src: Seq.seq SZ.t) (n idx: nat) (v: SZ.t)
  : Lemma
    (requires idx < n /\ n <= Seq.length stag /\ n <= Seq.length src /\
     SZ.v v <> 3 /\
     (forall (i:nat). {:pattern (Seq.index stag i)} i < n /\ SZ.v (Seq.index stag i) == 3 /\ i <> idx ==> SZ.v (Seq.index src i) > 0))
    (ensures
     (forall (i:nat). {:pattern (Seq.index (Seq.upd stag idx v) i)}
       i < n /\ SZ.v (Seq.index (Seq.upd stag idx v) i) == 3 ==> SZ.v (Seq.index src i) > 0))
  = let stag' = Seq.upd stag idx v in
    let aux (i:nat{i < n /\ SZ.v (Seq.index stag' i) == 3})
      : Lemma (SZ.v (Seq.index src i) > 0)
      = if i = idx then (Seq.lemma_index_upd1 stag idx v; assert False)
        else Seq.lemma_index_upd2 stag idx v i
    in FStar.Classical.forall_intro aux

(*** ========== count_nonzero: counting tagged nodes ========== ***)

/// Count how many entries in s[0..n) are nonzero.
let rec count_nonzero (s: Seq.seq SZ.t) (n: nat{n <= Seq.length s}) : Tot nat (decreases n)
  = if n = 0 then 0
    else (if SZ.v (Seq.index s (n - 1)) <> 0 then 1 else 0) + count_nonzero s (n - 1)

/// count_nonzero is at most n
let rec count_nonzero_le_n (s: Seq.seq SZ.t) (n: nat{n <= Seq.length s})
  : Lemma (ensures count_nonzero s n <= n) (decreases n)
  = if n = 0 then () else count_nonzero_le_n s (n - 1)

/// If s[y] = 0 for some y < n, then count_nonzero < n
let rec count_nonzero_lt_when_zero (s: Seq.seq SZ.t) (n: nat{n <= Seq.length s}) (y: nat)
  : Lemma (requires y < n /\ SZ.v (Seq.index s y) == 0)
          (ensures count_nonzero s n < n)
          (decreases n)
  = if n = 0 then ()
    else if y = n - 1 then
      count_nonzero_le_n s (n - 1)
    else begin
      count_nonzero_lt_when_zero s (n - 1) y
    end

/// Extensionality: sequences agreeing on [0..n) have equal count_nonzero
let rec count_nonzero_ext (s1 s2: Seq.seq SZ.t) (n: nat{n <= Seq.length s1 /\ n <= Seq.length s2})
  : Lemma (requires forall (i:nat). i < n ==> Seq.index s1 i == Seq.index s2 i)
          (ensures count_nonzero s1 n == count_nonzero s2 n)
          (decreases n)
  = if n = 0 then () else count_nonzero_ext s1 s2 (n - 1)

/// Setting a zero entry to nonzero increases count by 1
let rec count_nonzero_set_nz (s: Seq.seq SZ.t) (n: nat{n <= Seq.length s}) (y: nat) (v: SZ.t)
  : Lemma (requires y < n /\ SZ.v (Seq.index s y) == 0 /\ SZ.v v <> 0)
          (ensures count_nonzero (Seq.upd s y v) n == count_nonzero s n + 1)
          (decreases n)
  = let s' = Seq.upd s y v in
    if n = 0 then ()
    else if y = n - 1 then begin
      Seq.lemma_index_upd1 s y v;
      // s' agrees with s on [0..n-1) since y = n-1
      let aux (i:nat{i < n - 1}) : Lemma (Seq.index s' i == Seq.index s i)
        = Seq.lemma_index_upd2 s y v i
      in FStar.Classical.forall_intro aux;
      count_nonzero_ext s' s (n - 1)
    end else begin
      Seq.lemma_index_upd2 s y v (n - 1);
      count_nonzero_set_nz s (n - 1) y v
    end

/// Setting a nonzero entry to nonzero preserves count
let rec count_nonzero_set_nz_nz (s: Seq.seq SZ.t) (n: nat{n <= Seq.length s}) (y: nat) (v: SZ.t)
  : Lemma (requires y < n /\ SZ.v (Seq.index s y) <> 0 /\ SZ.v v <> 0)
          (ensures count_nonzero (Seq.upd s y v) n == count_nonzero s n)
          (decreases n)
  = let s' = Seq.upd s y v in
    if n = 0 then ()
    else if y = n - 1 then begin
      Seq.lemma_index_upd1 s y v;
      let aux (i:nat{i < n - 1}) : Lemma (Seq.index s' i == Seq.index s i)
        = Seq.lemma_index_upd2 s y v i
      in FStar.Classical.forall_intro aux;
      count_nonzero_ext s' s (n - 1)
    end else begin
      Seq.lemma_index_upd2 s y v (n - 1);
      count_nonzero_set_nz_nz s (n - 1) y v
    end

/// Updating any entry with a nonzero value doesn't decrease count_nonzero.
/// Covers: 0→nonzero (increases by 1) and nonzero→nonzero (unchanged).
let count_nonzero_nondec (s: Seq.seq SZ.t) (n y: nat) (v: SZ.t)
  : Lemma (requires y < n /\ n <= Seq.length s /\ SZ.v v <> 0)
          (ensures count_nonzero (Seq.upd s y v) n >= count_nonzero s n)
  = if SZ.v (Seq.index s y) = 0
    then count_nonzero_set_nz s n y v
    else count_nonzero_set_nz_nz s n y v

/// Updating a zero entry with zero is a no-op for count_nonzero.
let rec count_nonzero_set_zero_zero (s: Seq.seq SZ.t) (n y: nat) (v: SZ.t)
  : Lemma (requires y < n /\ n <= Seq.length s /\ SZ.v (Seq.index s y) == 0 /\ SZ.v v == 0)
          (ensures count_nonzero (Seq.upd s y v) n == count_nonzero s n)
          (decreases n)
  = let s' = Seq.upd s y v in
    if n = 0 then ()
    else if y = n - 1 then begin
      Seq.lemma_index_upd1 s y v;
      let aux (i:nat{i < n - 1}) : Lemma (Seq.index s' i == Seq.index s i)
        = Seq.lemma_index_upd2 s y v i
      in FStar.Classical.forall_intro aux;
      count_nonzero_ext s' s (n - 1)
    end else begin
      Seq.lemma_index_upd2 s y v (n - 1);
      count_nonzero_set_zero_zero s (n - 1) y v
    end

/// General: writing any value that doesn't turn nonzero to zero can't decrease count.
/// This covers handle_post_order's tag write (tag[rep_x] <- new_tag where
/// new_tag ∈ {3sz, cur_tag}).
let count_nonzero_write_nondec (s: Seq.seq SZ.t) (n y: nat) (v: SZ.t)
  : Lemma (requires y < n /\ n <= Seq.length s /\
           (SZ.v (Seq.index s y) == 0 \/ SZ.v v <> 0))
          (ensures count_nonzero (Seq.upd s y v) n >= count_nonzero s n)
  = if SZ.v v <> 0
    then count_nonzero_nondec s n y v
    else count_nonzero_set_zero_zero s n y v
