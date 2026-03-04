module CLRS.Ch25.FloydWarshall.Lemmas

(**
 * Interface for Floyd-Warshall correctness lemmas.
 *
 * Exposes the main theorem: fw_outer computes fw_entry at level n.
 *)

open FStar.Mul
open FStar.Seq
open CLRS.Ch25.FloydWarshall.Spec

(* SMT-pattern length lemmas *)
val lemma_fw_inner_j_len_auto (d: seq int) (n k i j: nat) (d_ik: int)
  : Lemma (ensures length (fw_inner_j d n k i j d_ik) == length d)
    [SMTPat (fw_inner_j d n k i j d_ik)]

val lemma_fw_inner_i_len_auto (d: seq int) (n k i: nat)
  : Lemma (ensures length (fw_inner_i d n k i) == length d)
    [SMTPat (fw_inner_i d n k i)]

val lemma_fw_outer_len_auto (d: seq int) (n k: nat)
  : Lemma (ensures length (fw_outer d n k) == length d)
    [SMTPat (fw_outer d n k)]

(* fw_inner_j only modifies row i, columns j..n-1 *)
val lemma_fw_inner_j_other_pos
  (d: seq int) (n k i j: nat) (d_ik: int) (pos: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\
      k < n /\ i < n /\
      pos < n * n /\ pos / n <> i)
    (ensures index (fw_inner_j d n k i j d_ik) pos == index d pos)

(* fw_inner_j correctly computes relaxation for row i *)
val lemma_fw_inner_j_correct
  (d: seq int) (n k i j: nat) (d_ik: int) (j': nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\
      k < n /\ i < n /\ j <= j' /\ j' < n)
    (ensures
      index (fw_inner_j d n k i j d_ik) (i * n + j') ==
        (let orig_ij = index d (i * n + j') in
         let orig_kj = index d (k * n + j') in
         let via = d_ik + orig_kj in
         if via < orig_ij then via else orig_ij))

(* Row k is unchanged by fw_inner_j when processing a different row *)
val lemma_fw_inner_j_preserves_row_k
  (d: seq int) (n k i j: nat) (d_ik: int) (j': nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\
      k < n /\ i < n /\ k <> i /\ j' < n)
    (ensures
      index (fw_inner_j d n k i j d_ik) (k * n + j') == index d (k * n + j'))

(* Row k preserved through the full i-loop *)
val lemma_fw_inner_i_preserves_row_k
  (d: seq int) (n k i_start: nat) (j': nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ k < n /\ j' < n /\
      index d (k * n + k) >= 0)
    (ensures
      index (fw_inner_i d n k i_start) (k * n + j') == index d (k * n + j'))

(* After fw_inner_i, entry [qi*n+qj] = min(d[qi*n+qj], d[qi*n+k] + d[k*n+qj]) *)
val lemma_fw_inner_i_correct
  (d: seq int) (n k i_start: nat) (qi qj: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ k < n /\
      qi < n /\ qj < n /\ qi >= i_start /\
      index d (k * n + k) >= 0)
    (ensures
      index (fw_inner_i d n k i_start) (qi * n + qj) ==
        (let orig = index d (qi * n + qj) in
         let via = index d (qi * n + k) + index d (k * n + qj) in
         if via < orig then via else orig))

(* Main theorem: fw_outer computes fw_entry *)
val fw_outer_computes_entry
  (adj d: seq int) (n k: nat) (qi qj: nat)
  : Lemma
    (requires
      length adj == n * n /\ length d == n * n /\ n > 0 /\
      k <= n /\ qi < n /\ qj < n /\
      (forall (k': nat) (v: nat). k' <= n /\ v < n ==> fw_entry adj n v v k' >= 0) /\
      (forall (i j: nat). i < n /\ j < n ==>
        index d (i * n + j) == fw_entry adj n i j k))
    (ensures
      index (fw_outer d n k) (qi * n + qj) == fw_entry adj n qi qj n)

//SNIPPET_START: floyd_warshall_correct
(* Top-level: fw_outer adj n 0 computes fw_entry adj n qi qj n *)
val floyd_warshall_computes_shortest_paths
  (adj: seq int) (n: nat) (qi qj: nat)
  : Lemma
    (requires
      length adj == n * n /\ n > 0 /\ qi < n /\ qj < n /\
      (forall (k: nat) (v: nat). k <= n /\ v < n ==> fw_entry adj n v v k >= 0))
    (ensures
      index (fw_outer adj n 0) (qi * n + qj) == fw_entry adj n qi qj n)
//SNIPPET_END: floyd_warshall_correct
