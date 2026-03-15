module CLRS.Ch25.FloydWarshall.Lemmas

(**
 * Floyd-Warshall Correctness Lemmas (CLRS §25.2, Equation 25.5)
 *
 * Proves that fw_outer computes fw_entry — the FW DP recurrence:
 * 1. fw_inner_j correctly relaxes row i
 * 2. fw_inner_i correctly processes one FW iteration
 * 3. fw_outer computes fw_entry at all levels
 * 4. Top-level theorem: fw_outer adj n 0 == fw_entry adj n qi qj n
 *
 * NO admits. NO assumes.
 *)

open FStar.Mul
open FStar.Seq
open CLRS.Ch25.FloydWarshall.Spec

(* ========================================================================
   § 1. Inner Loop Lemmas — fw_inner_j properties
   ======================================================================== *)

(* Auto-trigger length facts for fw_inner_j/i/outer results *)
let lemma_fw_inner_j_len_auto (d: seq int) (n k i j: nat) (d_ik: int)
  : Lemma (ensures length (fw_inner_j d n k i j d_ik) == length d)
    [SMTPat (fw_inner_j d n k i j d_ik)]
  = lemma_fw_inner_j_len d n k i j d_ik

let lemma_fw_inner_i_len_auto (d: seq int) (n k i: nat)
  : Lemma (ensures length (fw_inner_i d n k i) == length d)
    [SMTPat (fw_inner_i d n k i)]
  = lemma_fw_inner_i_len d n k i

let lemma_fw_outer_len_auto (d: seq int) (n k: nat)
  : Lemma (ensures length (fw_outer d n k) == length d)
    [SMTPat (fw_outer d n k)]
  = lemma_fw_outer_len d n k

(* fw_inner_j only modifies row i, columns j..n-1 *)
let rec lemma_fw_inner_j_other_pos
  (d: seq int) (n k i j: nat) (d_ik: int) (pos: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\
      k < n /\ i < n /\
      pos < n * n /\ pos / n <> i)
    (ensures index (fw_inner_j d n k i j d_ik) pos == index d pos)
    (decreases (n - j))
  = lemma_fw_inner_j_len d n k i j d_ik;
    if j >= n then ()
    else begin
      let d_ij = index d (i * n + j) in
      let d_kj = index d (k * n + j) in
      let via_k = d_ik + d_kj in
      let new_val = if via_k < d_ij then via_k else d_ij in
      let d' = upd d (i * n + j) new_val in
      assert (length d' == n * n);
      // pos / n <> i, so pos <> i*n+j (since (i*n+j)/n == i when j < n)
      assert (pos <> i * n + j);
      assert (index d' pos == index d pos);
      lemma_fw_inner_j_other_pos d' n k i (j + 1) d_ik pos
    end

(* fw_inner_j doesn't modify earlier columns of row i *)
let rec lemma_fw_inner_j_earlier_col
  (d: seq int) (n k i j: nat) (d_ik: int) (j': nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\
      k < n /\ i < n /\ j' < j /\ j' < n)
    (ensures index (fw_inner_j d n k i j d_ik) (i * n + j') == index d (i * n + j'))
    (decreases (n - j))
  = lemma_fw_inner_j_len d n k i j d_ik;
    if j >= n then ()
    else begin
      let d_ij = index d (i * n + j) in
      let d_kj = index d (k * n + j) in
      let via_k = d_ik + d_kj in
      let new_val = if via_k < d_ij then via_k else d_ij in
      let d' = upd d (i * n + j) new_val in
      assert (j' < j);
      assert (i * n + j' < i * n + j);
      assert (index d' (i * n + j') == index d (i * n + j'));
      lemma_fw_inner_j_earlier_col d' n k i (j + 1) d_ik j'
    end

(* Key: fw_inner_j correctly computes relaxation for row i *)
#push-options "--split_queries always"
let rec lemma_fw_inner_j_correct
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
    (decreases (n - j))
  = lemma_fw_inner_j_len d n k i j d_ik;
    if j >= n then ()
    else if j = j' then begin
      // We're at the column we want to query
      let d_ij = index d (i * n + j) in
      let d_kj = index d (k * n + j) in
      let via_k = d_ik + d_kj in
      let new_val = if via_k < d_ij then via_k else d_ij in
      let d' = upd d (i * n + j) new_val in
      // After this step, d'[i*n+j] = new_val = min(d_ij, d_ik + d_kj)
      // Remaining iterations only touch columns > j, so result[i*n+j'] = d'[i*n+j'] = new_val
      lemma_fw_inner_j_earlier_col d' n k i (j + 1) d_ik j'
    end else begin
      // j < j', recurse past this column
      let d_ij = index d (i * n + j) in
      let d_kj = index d (k * n + j) in
      let via_k = d_ik + d_kj in
      let new_val = if via_k < d_ij then via_k else d_ij in
      let d' = upd d (i * n + j) new_val in
      // d'[k*n+j''] = d[k*n+j''] for j'' >= j+1 (we only changed i*n+j)
      assert (forall (j'': nat). j'' >= j + 1 /\ j'' < n ==>
        index d' (k * n + j'') == index d (k * n + j''));
      // Also d'[i*n+j'] = d[i*n+j'] since j' > j
      assert (index d' (i * n + j') == index d (i * n + j'));
      // And d'[k*n+j'] = d[k*n+j'] 
      assert (index d' (k * n + j') == index d (k * n + j'));
      lemma_fw_inner_j_correct d' n k i (j + 1) d_ik j'
    end
#pop-options

(* ========================================================================
   § 3. fw_inner_i properties
   ======================================================================== *)

(* fw_inner_i doesn't modify rows < i_start *)
let rec lemma_fw_inner_i_earlier_row
  (d: seq int) (n k i_start: nat) (pos: nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ k < n /\
      pos < n * n /\ pos / n < i_start)
    (ensures index (fw_inner_i d n k i_start) pos == index d pos)
    (decreases (n - i_start))
  = if i_start >= n then ()
    else begin
      let d_ik = index d (i_start * n + k) in
      let d' = fw_inner_j d n k i_start 0 d_ik in
      lemma_fw_inner_j_len d n k i_start 0 d_ik;
      // pos is in a row < i_start, so fw_inner_j doesn't touch it
      lemma_fw_inner_j_other_pos d n k i_start 0 d_ik pos;
      lemma_fw_inner_i_earlier_row d' n k (i_start + 1) pos
    end

(* Key lemma: row k is unchanged by fw_inner_i when diagonal >= 0 *)
let rec lemma_fw_inner_j_preserves_row_k
  (d: seq int) (n k i j: nat) (d_ik: int) (j': nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\
      k < n /\ i < n /\ k <> i /\ j' < n)
    (ensures
      index (fw_inner_j d n k i j d_ik) (k * n + j') == index d (k * n + j'))
    (decreases (n - j))
  = lemma_fw_inner_j_len d n k i j d_ik;
    if j >= n then ()
    else begin
      let d_ij = index d (i * n + j) in
      let d_kj = index d (k * n + j) in
      let via_k = d_ik + d_kj in
      let new_val = if via_k < d_ij then via_k else d_ij in
      let d' = upd d (i * n + j) new_val in
      // k <> i, so k*n+j' <> i*n+j for any j,j'
      // Well, need (k*n+j') / n = k <> i = (i*n+j) / n
      assert (index d' (k * n + j') == index d (k * n + j'));
      lemma_fw_inner_j_preserves_row_k d' n k i (j + 1) d_ik j'
    end

let rec lemma_fw_inner_i_preserves_row_k
  (d: seq int) (n k i_start: nat) (j': nat)
  : Lemma
    (requires
      length d == n * n /\ n > 0 /\ k < n /\ j' < n /\
      // Row k has non-negative self-loop (diagonal >= 0)
      index d (k * n + k) >= 0)
    (ensures
      index (fw_inner_i d n k i_start) (k * n + j') == index d (k * n + j'))
    (decreases (n - i_start))
  = if i_start >= n then ()
    else begin
      let d_ik = index d (i_start * n + k) in
      let d' = fw_inner_j d n k i_start 0 d_ik in
      lemma_fw_inner_j_len d n k i_start 0 d_ik;
      if i_start = k then begin
        // i_start == k: fw_inner_j processes row k with d_ik = d[k*n+k]
        // d[k*n+j'] gets updated to min(d[k*n+j'], d[k*n+k] + d[k*n+j'])
        // Since d[k*n+k] >= 0, d[k*n+k] + d[k*n+j'] >= d[k*n+j'], so min = d[k*n+j']
        lemma_fw_inner_j_correct d n k k 0 d_ik j';
        assert (index d' (k * n + j') ==
          (let orig = index d (k * n + j') in
           let via = d_ik + index d (k * n + j') in
           if via < orig then via else orig));
        // d_ik = d[k*n+k] >= 0, so d_ik + d[k*n+j'] >= d[k*n+j']
        assert (d_ik + index d (k * n + j') >= index d (k * n + j'));
        assert (index d' (k * n + j') == index d (k * n + j'));
        // Also need d'[k*n+k] >= 0 for recursive call
        lemma_fw_inner_j_correct d n k k 0 d_ik k;
        assert (index d' (k * n + k) >= 0);
        lemma_fw_inner_i_preserves_row_k d' n k (i_start + 1) j'
      end else begin
        // i_start <> k: fw_inner_j doesn't touch row k
        lemma_fw_inner_j_preserves_row_k d n k i_start 0 d_ik j';
        assert (index d' (k * n + j') == index d (k * n + j'));
        // Also d'[k*n+k] unchanged
        lemma_fw_inner_j_preserves_row_k d n k i_start 0 d_ik k;
        assert (index d' (k * n + k) >= 0);
        lemma_fw_inner_i_preserves_row_k d' n k (i_start + 1) j'
      end
    end

(* ========================================================================
   § 4. fw_inner_i correctly computes one FW iteration
   ======================================================================== *)

(* After fw_inner_i d n k 0, entry [i*n+j] = min(d[i*n+j], d[i*n+k] + d[k*n+j]) *)
let rec lemma_fw_inner_i_correct
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
    (decreases (n - i_start))
  = if i_start >= n then ()
    else begin
      let d_ik = index d (i_start * n + k) in
      let d' = fw_inner_j d n k i_start 0 d_ik in
      lemma_fw_inner_j_len d n k i_start 0 d_ik;
      if i_start = qi then begin
        // This is the row we're querying
        // fw_inner_j correctly updates row i_start
        lemma_fw_inner_j_correct d n k i_start 0 d_ik qj;
        // d'[qi*n+qj] = min(d[qi*n+qj], d_ik + d[k*n+qj])
        //             = min(d[qi*n+qj], d[qi*n+k] + d[k*n+qj])
        assert (index d' (qi * n + qj) ==
          (let orig = index d (qi * n + qj) in
           let via = d_ik + index d (k * n + qj) in
           if via < orig then via else orig));
        // d_ik = d[i_start*n+k] = d[qi*n+k]
        assert (d_ik == index d (qi * n + k));
        // Remaining iterations (i_start+1..n-1) don't modify row qi
        lemma_fw_inner_i_earlier_row d' n k (i_start + 1) (qi * n + qj)
      end else begin
        // i_start < qi, this iteration processes a different row
        // d'[qi*n+qj] = d[qi*n+qj] (row qi untouched by fw_inner_j for row i_start)
        lemma_fw_inner_j_other_pos d n k i_start 0 d_ik (qi * n + qj);
        // d'[qi*n+k] = d[qi*n+k]
        lemma_fw_inner_j_other_pos d n k i_start 0 d_ik (qi * n + k);
        // d'[k*n+qj] = d[k*n+qj] (row k preserved since d[k*n+k] >= 0)
        if k = i_start then begin
          lemma_fw_inner_j_correct d n k i_start 0 d_ik qj;
          // d_ik = d[k*n+k] >= 0, so min(d[k*n+qj], d[k*n+k]+d[k*n+qj]) = d[k*n+qj]
          assert (index d' (k * n + qj) == index d (k * n + qj))
        end else
          lemma_fw_inner_j_preserves_row_k d n k i_start 0 d_ik qj;
        // d'[k*n+k] >= 0 for recursive call
        if k = i_start then begin
          lemma_fw_inner_j_correct d n k k 0 d_ik k;
          assert (index d' (k * n + k) >= 0)
        end else begin
          lemma_fw_inner_j_preserves_row_k d n k i_start 0 d_ik k;
          assert (index d' (k * n + k) == index d (k * n + k))
        end;
        lemma_fw_inner_i_correct d' n k (i_start + 1) qi qj
      end
    end

(* ========================================================================
   § 5. Main Theorem: fw_outer computes fw_entry
   ======================================================================== *)

(* Inductive step: if d matches fw_entry at level k, then after fw_inner_i,
   d matches fw_entry at level k+1 *)
#push-options "--z3rlimit 40"
let lemma_fw_step
  (adj d: seq int) (n k: nat) (qi qj: nat)
  : Lemma
    (requires
      length adj == n * n /\ length d == n * n /\ n > 0 /\ k < n /\
      qi < n /\ qj < n /\
      index d (k * n + k) >= 0 /\
      (forall (i j: nat). i < n /\ j < n ==>
        index d (i * n + j) == fw_entry adj n i j k))
    (ensures
      index (fw_inner_i d n k 0) (qi * n + qj) == fw_entry adj n qi qj (k + 1))
  = lemma_fw_inner_i_correct d n k 0 qi qj;
    // After fw_inner_i: result[qi*n+qj] = min(d[qi*n+qj], d[qi*n+k] + d[k*n+qj])
    //                                    = min(fw_entry qi qj k, fw_entry qi k k + fw_entry k qj k)
    //                                    = fw_entry qi qj (k+1)
    assert (index d (qi * n + qj) == fw_entry adj n qi qj k);
    assert (index d (qi * n + k) == fw_entry adj n qi k k);
    assert (index d (k * n + qj) == fw_entry adj n k qj k)
#pop-options

//SNIPPET_START: fw_outer_computes_entry
(* Main theorem: fw_outer computes fw_entry *)
let rec fw_outer_computes_entry
  (adj d: seq int) (n k: nat) (qi qj: nat)
  : Lemma
    (requires
      length adj == n * n /\ length d == n * n /\ n > 0 /\
      k <= n /\ qi < n /\ qj < n /\
      // Diagonal non-negative invariant at each level (no negative cycles)
      (forall (k': nat) (v: nat). k' <= n /\ v < n ==> fw_entry adj n v v k' >= 0) /\
      // d matches fw_entry at level k
      (forall (i j: nat). i < n /\ j < n ==>
        index d (i * n + j) == fw_entry adj n i j k))
    (ensures
      index (fw_outer d n k) (qi * n + qj) == fw_entry adj n qi qj n)
    (decreases (n - k))
  = if k >= n then ()
    else begin
      // d[k*n+k] == fw_entry adj n k k k >= 0 (from diagonal invariant)
      assert (index d (k * n + k) == fw_entry adj n k k k);
      assert (index d (k * n + k) >= 0);
      // After fw_inner_i d n k 0, entries match fw_entry at level k+1
      let d' = fw_inner_i d n k 0 in
      lemma_fw_inner_i_len d n k 0;
      // Prove d' matches fw_entry at level k+1 for all i,j
      let aux (i j: nat) : Lemma
        (ensures (i < n /\ j < n ==> index d' (i * n + j) == fw_entry adj n i j (k + 1)))
        = if i < n && j < n then lemma_fw_step adj d n k i j else ()
      in
      FStar.Classical.forall_intro_2 aux;
      // Need diagonal invariant at level k+1
      let diag_aux (v: nat) : Lemma
        (requires v < n)
        (ensures fw_entry adj n v v (k + 1) >= 0)
        = ()  // follows from the universal quantifier with k' = k+1
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires diag_aux);
      // Recurse
      fw_outer_computes_entry adj d' n (k + 1) qi qj
    end
//SNIPPET_END: fw_outer_computes_entry

(* ========================================================================
   § 6. Top-level Theorem
   ======================================================================== *)

//SNIPPET_START: floyd_warshall_correct
let floyd_warshall_computes_shortest_paths
  (adj: seq int) (n: nat) (qi qj: nat)
  : Lemma
    (requires
      length adj == n * n /\ n > 0 /\ qi < n /\ qj < n /\
      // Non-negative diagonal at all levels (no negative cycles)
      (forall (k: nat) (v: nat). k <= n /\ v < n ==> fw_entry adj n v v k >= 0))
    (ensures
      index (fw_outer adj n 0) (qi * n + qj) == fw_entry adj n qi qj n)
  = fw_outer_computes_entry adj adj n 0 qi qj
//SNIPPET_END: floyd_warshall_correct

//SNIPPET_START: floyd_warshall_full_correctness
(* Combined theorem: weights_bounded implies fw_outer computes shortest paths.
   Derives the fw_entry diagonal invariant from weights_bounded, then applies
   the main correctness theorem. *)
let floyd_warshall_full_correctness
  (adj: seq int) (n: nat) (qi qj: nat)
  : Lemma
    (requires
      weights_bounded adj n /\ n > 0 /\ qi < n /\ qj < n)
    (ensures
      index (fw_outer adj n 0) (qi * n + qj) == fw_entry adj n qi qj n)
  = // weights_bounded implies all fw_entry values are non-negative
    let aux (k v: nat) : Lemma
      (requires k <= n /\ v < n)
      (ensures fw_entry adj n v v k >= 0)
      = lemma_weights_bounded_nonneg_entry adj n v v k
    in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux);
    floyd_warshall_computes_shortest_paths adj n qi qj
//SNIPPET_END: floyd_warshall_full_correctness
