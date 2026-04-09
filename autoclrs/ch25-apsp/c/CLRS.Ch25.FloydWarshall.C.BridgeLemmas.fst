module CLRS.Ch25.FloydWarshall.C.BridgeLemmas

(**
 * Proofs for bridge lemmas connecting the c2pulse C implementation
 * to the F* mathematical spec.
 *)

open FStar.Mul
open FStar.Seq
open CLRS.Ch25.FloydWarshall.Spec

#set-options "--z3rlimit 40 --split_queries always"

(** Bridge 1: trivial from the hypotheses *)
let weights_bounded_entries_in_range (d: seq int) (n: nat) (p: nat)
  : Lemma
    (requires weights_bounded d n /\ p < n * n /\ index d p <= inf)
    (ensures index d p >= 0 /\ index d p <= inf)
  = ()

(** Helper: index bound for row-major layout *)
private let index_bound (a b n: nat)
  : Lemma (requires a < n /\ b < n)
          (ensures a * n + b < n * n)
  = FStar.Math.Lemmas.lemma_mult_le_right n a (n - 1);
    FStar.Math.Lemmas.distributivity_sub_left n 1 n

(** Bridge 2: fw_inner_j preserves non-negativity *)
let rec fw_inner_j_preserves_nonneg
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
    (decreases (n - j))
  = lemma_fw_inner_j_len d n k i j d_ik;
    if j >= n then ()
    else begin
      index_bound i j n;
      index_bound k j n;
      let d_ij = index d (i * n + j) in
      let d_kj = index d (k * n + j) in
      let via_k = d_ik + d_kj in
      let new_val = if via_k < d_ij then via_k else d_ij in
      assert (new_val >= 0);
      let d' = upd d (i * n + j) new_val in
      assert (forall (p: nat). p < n * n ==> index d' p >= 0);
      fw_inner_j_preserves_nonneg d' n k i (j + 1) d_ik
    end

(** Bridge 3: fw_inner_j preserves [0, inf] bound *)
let rec fw_inner_j_preserves_bound
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
    (decreases (n - j))
  = lemma_fw_inner_j_len d n k i j d_ik;
    if j >= n then ()
    else begin
      index_bound i j n;
      index_bound k j n;
      let d_ij = index d (i * n + j) in
      let d_kj = index d (k * n + j) in
      let via_k = d_ik + d_kj in
      let new_val = if via_k < d_ij then via_k else d_ij in
      assert (new_val >= 0);
      assert (new_val <= d_ij);
      assert (d_ij <= inf);
      let d' = upd d (i * n + j) new_val in
      assert (forall (p: nat). p < n * n ==> index d' p >= 0 /\ index d' p <= inf);
      fw_inner_j_preserves_bound d' n k i (j + 1) d_ik
    end

(** Helper: fw_inner_i preserves [0, inf] *)
private let rec fw_inner_i_preserves_bounds_aux
  (d: seq int) (n k i: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ k < n /\
      (forall (p: nat). p < n * n ==> index d p >= 0 /\ index d p <= inf))
    (ensures
      length (fw_inner_i d n k i) == n * n /\
      (forall (p: nat). p < n * n ==>
        index (fw_inner_i d n k i) p >= 0 /\
        index (fw_inner_i d n k i) p <= inf))
    (decreases (n - i))
  = lemma_fw_inner_i_len d n k i;
    if i >= n then ()
    else begin
      index_bound i k n;
      let d_ik = index d (i * n + k) in
      assert (d_ik >= 0 /\ d_ik <= inf);
      fw_inner_j_preserves_bound d n k i 0 d_ik;
      let d' = fw_inner_j d n k i 0 d_ik in
      fw_inner_i_preserves_bounds_aux d' n k (i + 1)
    end

(** Bridge 4: fw_outer preserves [0, inf] bounds *)
let rec fw_outer_preserves_bounds
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
    (decreases (n - k))
  = lemma_fw_outer_len d n k;
    if k >= n then ()
    else begin
      let d' = fw_inner_i d n k 0 in
      fw_inner_i_preserves_bounds_aux d n k 0;
      fw_outer_preserves_bounds d' n (k + 1)
    end

(** Bridge 5: fw_inner_j is monotone-decreasing at each position *)
let rec fw_inner_j_monotone
  (d: seq int) (n k i j: nat) (d_ik: int) (p: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ k < n /\ i < n /\ p < n * n /\
      d_ik >= 0)
    (ensures
      length (fw_inner_j d n k i j d_ik) == n * n /\
      index (fw_inner_j d n k i j d_ik) p <= index d p)
    (decreases (n - j))
  = lemma_fw_inner_j_len d n k i j d_ik;
    if j >= n then ()
    else begin
      index_bound i j n;
      index_bound k j n;
      let d_ij = index d (i * n + j) in
      let d_kj = index d (k * n + j) in
      let via_k = d_ik + d_kj in
      let new_val = if via_k < d_ij then via_k else d_ij in
      let d' = upd d (i * n + j) new_val in
      assert (new_val <= d_ij);
      assert (index d' (i * n + j) <= index d (i * n + j));
      assert (forall (q: nat). q < n * n /\ q <> i * n + j ==>
        index d' q == index d q);
      fw_inner_j_monotone d' n k i (j + 1) d_ik p;
      assert (index (fw_inner_j d' n k i (j + 1) d_ik) p <= index d' p);
      assert (index d' p <= index d p)
    end

(** Helper: fw_inner_i is monotone-decreasing *)
private let rec fw_inner_i_monotone
  (d: seq int) (n k i: nat) (p: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ k < n /\ p < n * n /\
      (forall (q: nat). q < n * n ==> index d q >= 0))
    (ensures
      length (fw_inner_i d n k i) == n * n /\
      index (fw_inner_i d n k i) p <= index d p)
    (decreases (n - i))
  = lemma_fw_inner_i_len d n k i;
    if i >= n then ()
    else begin
      index_bound i k n;
      let d_ik = index d (i * n + k) in
      assert (d_ik >= 0);
      fw_inner_j_monotone d n k i 0 d_ik p;
      let d' = fw_inner_j d n k i 0 d_ik in
      lemma_fw_inner_j_len d n k i 0 d_ik;
      fw_inner_j_preserves_nonneg d n k i 0 d_ik;
      fw_inner_i_monotone d' n k (i + 1) p
    end

(** Helper: fw_inner_i preserves non-negativity *)
private let rec fw_inner_i_preserves_nonneg_aux
  (d: seq int) (n k i: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ k < n /\
      (forall (q: nat). q < n * n ==> index d q >= 0))
    (ensures
      length (fw_inner_i d n k i) == n * n /\
      (forall (q: nat). q < n * n ==> index (fw_inner_i d n k i) q >= 0))
    (decreases (n - i))
  = lemma_fw_inner_i_len d n k i;
    if i >= n then ()
    else begin
      index_bound i k n;
      let d_ik = index d (i * n + k) in
      fw_inner_j_preserves_nonneg d n k i 0 d_ik;
      let d' = fw_inner_j d n k i 0 d_ik in
      fw_inner_i_preserves_nonneg_aux d' n k (i + 1)
    end

(** Bridge 6: fw_outer is monotone-decreasing *)
let rec fw_outer_monotone
  (d: seq int) (n k: nat) (p: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ p < n * n /\
      (forall (q: nat). q < n * n ==> index d q >= 0))
    (ensures
      length (fw_outer d n k) == n * n /\
      index (fw_outer d n k) p <= index d p)
    (decreases (n - k))
  = lemma_fw_outer_len d n k;
    if k >= n then ()
    else begin
      let d' = fw_inner_i d n k 0 in
      lemma_fw_inner_i_len d n k 0;
      fw_inner_i_monotone d n k 0 p;
      fw_inner_i_preserves_nonneg_aux d n k 0;
      fw_outer_monotone d' n (k + 1) p
    end
