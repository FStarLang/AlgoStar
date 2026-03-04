module CLRS.Ch25.FloydWarshall.Spec

(**
 * Pure specification of Floyd-Warshall (CLRS §25.2, Equation 25.5).
 *
 * Defines the FW recurrence d^(k)[i][j], an imperative-mirroring pure spec
 * (fw_inner_j, fw_inner_i, fw_outer), safety predicates, and length
 * preservation lemmas.
 *
 * NO admits. NO assumes.
 *)

open FStar.Mul
open FStar.Seq

//SNIPPET_START: inf
// Sentinel value for "infinity" (no edge)
let inf : int = 1000000
//SNIPPET_END: inf

//SNIPPET_START: safety_predicates
// Safety predicate: all finite edge weights are bounded so that path sums
// (at most n-1 additions) cannot reach the infinity sentinel.
let weights_bounded (d: seq int) (n: nat) : prop =
  length d == n * n /\
  (forall (i: nat). i < n * n ==>
    (index d i >= 0 /\ (index d i < inf ==> index d i <= inf / n)))

// Safety predicate: diagonal entries are non-negative (no negative self-loops).
// Required for the correctness proof (no negative cycles assumption).
let non_negative_diagonal (d: seq int) (n: nat) : prop =
  length d == n * n /\
  (forall (v: nat). v < n ==> index d (v * n + v) >= 0)
//SNIPPET_END: safety_predicates

(*** Pure imperative-mirroring specification ***)

//SNIPPET_START: pure_spec
// fw_inner_j: process columns j..n-1 for row i with intermediate vertex k
// d_ik is cached (read once before the j-loop in the imperative code)
let rec fw_inner_j (d: seq int) (n k i j: nat) (d_ik: int) 
  : Tot (seq int) (decreases (n - j)) =
  if j >= n || i >= n || k >= n || length d <> n * n then d
  else
    let d_ij = index d (i * n + j) in
    let d_kj = index d (k * n + j) in
    let via_k = d_ik + d_kj in
    let new_val = if via_k < d_ij then via_k else d_ij in
    fw_inner_j (upd d (i * n + j) new_val) n k i (j + 1) d_ik

// fw_inner_i: process rows i..n-1 for intermediate vertex k
let rec fw_inner_i (d: seq int) (n k i: nat) 
  : Tot (seq int) (decreases (n - i)) =
  if i >= n || k >= n || length d <> n * n then d
  else
    let d_ik = index d (i * n + k) in
    fw_inner_i (fw_inner_j d n k i 0 d_ik) n k (i + 1)

// fw_outer: process intermediate vertices k..n-1
let rec fw_outer (d: seq int) (n k: nat) 
  : Tot (seq int) (decreases (n - k)) =
  if k >= n || length d <> n * n then d
  else fw_outer (fw_inner_i d n k 0) n (k + 1)
//SNIPPET_END: pure_spec

(*** FW Recurrence — d^(k)[i][j] (CLRS Equation 25.5) ***)

//SNIPPET_START: fw_entry
(* d^(0)[i][j] = adj[i*n+j]  (direct edge weight)
   d^(k)[i][j] = min(d^(k-1)[i][j], d^(k-1)[i][k-1] + d^(k-1)[k-1][j])
   Here k counts how many vertices have been considered as intermediates:
   k=0 means no intermediates, k=n means all vertices considered. *)
let rec fw_entry (adj: seq int) (n: nat) (i j k: nat)
  : Tot int (decreases k)
  = if i >= n || j >= n || length adj <> n * n then inf
    else if k = 0 then index adj (i * n + j)
    else
      let without = fw_entry adj n i j (k - 1) in
      let d_ik = fw_entry adj n i (k - 1) (k - 1) in
      let d_kj = fw_entry adj n (k - 1) j (k - 1) in
      let via_k = d_ik + d_kj in
      if via_k < without then via_k else without
//SNIPPET_END: fw_entry

//SNIPPET_START: length_lemmas
// Length preservation lemmas
let rec lemma_fw_inner_j_len (d: seq int) (n k i j: nat) (d_ik: int)
  : Lemma (ensures length (fw_inner_j d n k i j d_ik) == length d)
          (decreases (n - j))
  = if j >= n || i >= n || k >= n || length d <> n * n then ()
    else
      let d_ij = index d (i * n + j) in
      let d_kj = index d (k * n + j) in
      let via_k = d_ik + d_kj in
      let new_val = if via_k < d_ij then via_k else d_ij in
      lemma_fw_inner_j_len (upd d (i * n + j) new_val) n k i (j + 1) d_ik

let rec lemma_fw_inner_i_len (d: seq int) (n k i: nat)
  : Lemma (ensures length (fw_inner_i d n k i) == length d)
          (decreases (n - i))
  = if i >= n || k >= n || length d <> n * n then ()
    else begin
      let d_ik = index d (i * n + k) in
      lemma_fw_inner_j_len d n k i 0 d_ik;
      lemma_fw_inner_i_len (fw_inner_j d n k i 0 d_ik) n k (i + 1)
    end

let rec lemma_fw_outer_len (d: seq int) (n k: nat)
  : Lemma (ensures length (fw_outer d n k) == length d)
          (decreases (n - k))
  = if k >= n || length d <> n * n then ()
    else begin
      lemma_fw_inner_i_len d n k 0;
      lemma_fw_outer_len (fw_inner_i d n k 0) n (k + 1)
    end
//SNIPPET_END: length_lemmas
