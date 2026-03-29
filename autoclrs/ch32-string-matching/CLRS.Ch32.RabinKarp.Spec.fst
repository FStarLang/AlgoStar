(*
   Rabin-Karp String Matching - Pure F* Specification (CLRS §32.2)

   Hash function following CLRS:
     p = P[0]·d^(m-1) + P[1]·d^(m-2) + ... + P[m-1]·d^0  (mod q)

   This is a big-endian polynomial hash: the leftmost character gets
   the highest power of d. Computed right-to-left via Horner's rule:
     hash(i,j) = (d · hash(i, j-1) + x[j-1]) mod q

   Rolling hash update (CLRS eq. 32.2):
     t_{s+1} = (d · (t_s - T[s] · d^(m-1)) + T[s+m]) mod q

   Proofs adapted from FStar/examples/algorithms/StringMatching.fst.
   The key insight is hash_inversion: extracting the most significant
   digit (leftmost character) from the hash, which enables the
   rolling hash correctness proof.
*)

module CLRS.Ch32.RabinKarp.Spec

open FStar.Mul
open FStar.Classical
module Seq = FStar.Seq

(*** Hash Function (CLRS §32.2) ***)

//SNIPPET_START: hash
/// CLRS polynomial hash via Horner's rule (right-to-left):
///   hash(x, d, q, i, j) = x[i]·d^(j-i-1) + ... + x[j-1]·d^0  (mod q)
/// Faithful to CLRS: leftmost character gets highest power.
let rec hash (x:Seq.seq nat) (d:nat) (q:nat{q <> 0})
             (i:nat) (j:nat{i <= j /\ j <= Seq.length x})
  : Tot nat (decreases j - i)
  = if i = j then 0
    else (d * hash x d q i (j - 1) + Seq.index x (j - 1)) % q

/// d^m
let rec pow (d m:nat) : nat =
  if m = 0 then 1 else pow d (m - 1) * d

/// d^exp mod q  (efficient modular exponentiation)
let rec pow_mod (d:nat) (exp:nat) (q:pos) : Tot nat (decreases exp) =
  if exp = 0 then 1 % q else (d * pow_mod d (exp - 1) q) % q

/// Rolling hash step (CLRS eq. 32.2):
///   t_{s+1} = (d · (t_s - T[s] · h) + T[s+m]) mod q
/// where h = d^(m-1) mod q.
/// Uses (ts + q - ...) to avoid negative intermediate values.
let rolling_hash_step (ts:nat) (old_char:nat) (new_char:nat)
                      (d:nat) (q:pos) (h:nat) : nat =
  (d * ((ts + q - (old_char * h) % q) % q) + new_char) % q
//SNIPPET_END: hash

(*** Hash Algebra Lemmas ***)

let hash_mod_idem (x:Seq.seq nat) (d:nat) (q:nat{q <> 0})
                  (i:nat) (j:nat{i <= j /\ j <= Seq.length x})
  : Lemma (hash x d q i j == hash x d q i j % q)
  = if i = j then ()
    else FStar.Math.Lemmas.lemma_mod_twice
           (d * hash x d q i (j - 1) + Seq.index x (j - 1)) q

let pow_lemma (d m:nat) : Lemma (d * pow d m == pow d (m + 1)) = ()

let lemma_mod_add_distr_l (a b:int) (n:pos)
  : Lemma ((a % n + b) % n = (a + b) % n)
  = FStar.Math.Lemmas.lemma_mod_add_distr b a n

let lemma_mod_add_3 (a b c:int) (p:pos)
  : Lemma (((a + b) % p + c) % p == ((a + c) % p + b) % p)
  = lemma_mod_add_distr_l (a + b) c p;
    lemma_mod_add_distr_l (a + c) b p

/// Key lemma: extract the most-significant digit from the hash.
///   hash(i,j) == (hash(i+1,j) + d^(j-i-1) · x[i]) % q
#push-options "--z3rlimit_factor 40 --ifuel 0 --fuel 2 --split_queries no"
#restart-solver
let rec hash_inversion (x:Seq.seq nat) (d:nat) (q:nat{q <> 0})
                       (i:nat) (j:nat{i < j /\ j <= Seq.length x})
  : Lemma (ensures hash x d q i j ==
                   (hash x d q (i + 1) j + pow d (j - i - 1) * Seq.index x i) % q)
          (decreases j - i)
  = if j = i + 1 then ()
    else (
      hash_inversion x d q i (j - 1);
      let h_lsd = d * hash x d q (i + 1) (j - 1) in
      let msd = pow d (j - i - 1) * Seq.index x i in
      FStar.Pure.BreakVC.break_vc ();
      let aux () : Lemma (d * hash x d q i (j - 1) % q == (h_lsd + msd) % q) =
        calc (==) {
          d * hash x d q i (j - 1) % q;
        (==) { hash_inversion x d q i (j - 1) }
          (d * ((hash x d q (i + 1) (j - 1) +
                 pow d (j - i - 2) * Seq.index x i) % q)) % q;
        (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r d
                 (hash x d q (i + 1) (j - 1) +
                  pow d (j - i - 2) * Seq.index x i) q }
          (d * (hash x d q (i + 1) (j - 1) +
                pow d (j - i - 2) * Seq.index x i)) % q;
        (==) { FStar.Math.Lemmas.distributivity_add_right d
                 (hash x d q (i + 1) (j - 1))
                 (pow d (j - i - 2) * Seq.index x i);
               pow_lemma d (j - i - 2) }
          (h_lsd + msd) % q;
        }
      in
      aux ();
      calc (==) {
        hash x d q i j;
      (==) {}
        (d * hash x d q i (j - 1) + Seq.index x (j - 1)) % q;
      (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l
               (d * hash x d q i (j - 1)) (Seq.index x (j - 1)) q }
        (d * hash x d q i (j - 1) % q + Seq.index x (j - 1)) % q;
      (==) { aux () }
        ((h_lsd + msd) % q + Seq.index x (j - 1)) % q;
      (==) { lemma_mod_add_3 h_lsd msd (Seq.index x (j - 1)) q }
        ((h_lsd + Seq.index x (j - 1)) % q + msd) % q;
      }
    )
#pop-options

let lemma_mod_add_sub_cancel (a b:int) (p:pos)
  : Lemma (((a + b) % p - b) % p == a % p)
  = FStar.Math.Lemmas.lemma_mod_add_distr (-b) (a + b) p

/// Removing the MSD: (hash(i,j) - x[i]·d^(m-1)) mod q == hash(i+1,j)
let remove_msd_lemma (x:Seq.seq nat) (d:nat) (q:nat{q <> 0})
                     (i:nat) (j:nat{i < j /\ j < Seq.length x})
                     (h:nat{h == hash x d q i j})
                     (pow_d_m:nat{pow_d_m == pow d (j - i - 1)})
  : Lemma (ensures (h - Seq.index x i * pow_d_m) % q == hash x d q (i + 1) j)
  = hash_inversion x d q i j;
    lemma_mod_add_sub_cancel (hash x d q (i + 1) j) (Seq.index x i * pow_d_m) q;
    hash_mod_idem x d q (i + 1) j

/// Proven rolling hash: remove MSD, then add new LSD.
let rolling_hash_proven (x:Seq.seq nat) (d:nat) (q:nat{q <> 0})
                        (i:nat) (j:nat{i < j /\ j < Seq.length x})
                        (h:nat{h == hash x d q i j})
                        (pow_d_m:nat{pow_d_m == pow d (j - i - 1)})
  : r:nat{r == hash x d q (i + 1) (j + 1)}
  = let h0 = (h - Seq.index x i * pow_d_m) % q in
    remove_msd_lemma x d q i j h pow_d_m;
    (d * h0 + Seq.index x j) % q

/// Equal substrings have equal hashes.
let eq_sub_seq #a (x:Seq.seq a) (i j:nat) (y:Seq.seq a) (i' j':nat) : prop =
  j - i == j' - i' /\ j <= Seq.length x /\ j' <= Seq.length y /\
  (forall (k:nat). k < j - i ==> Seq.index x (i + k) == Seq.index y (i' + k))

let rec hash_slice_lemma (x y:Seq.seq nat) (d:nat) (q:nat{q <> 0})
                         (i:nat) (j:nat{i <= j /\ j <= Seq.length x})
                         (i':nat) (j':nat{i' <= j' /\ j' <= Seq.length y})
  : Lemma (requires eq_sub_seq x i j y i' j')
          (ensures hash x d q i j == hash y d q i' j')
          (decreases j - i)
  = if i = j then () else hash_slice_lemma x y d q i (j - 1) i' (j' - 1)

(*** Connecting pow_mod and rolling_hash_step to the proven hash ***)

let rec pow_mod_correct (d:nat) (exp:nat) (q:pos)
  : Lemma (ensures pow_mod d exp q == pow d exp % q)
          (decreases exp)
  = if exp = 0 then ()
    else (pow_mod_correct d (exp - 1) q;
          FStar.Math.Lemmas.lemma_mod_mul_distr_r d (pow d (exp - 1)) q)

let lemma_mod_sub_via_add (a b:int) (q:pos)
  : Lemma ((a + q - b % q) % q == (a - b) % q)
  = FStar.Math.Lemmas.lemma_mod_sub_distr a b q;
    assert ((a - b) % q == (a - b % q) % q);
    FStar.Math.Lemmas.modulo_lemma (b % q) q;
    assert (b % q >= 0 /\ b % q < q);
    FStar.Math.Lemmas.lemma_mod_sub_distr a (b % q) q

//SNIPPET_START: rolling_hash_step_correct
/// rolling_hash_step computes the same result as the proven rolling_hash_proven.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let rolling_hash_step_correct
    (text:Seq.seq nat) (d:nat) (q:pos)
    (s:nat) (m:nat{m > 0 /\ s + m < Seq.length text})
    (current_hash:nat{current_hash == hash text d q s (s + m)})
    (h:nat{h == pow_mod d (m - 1) q})
  : Lemma (rolling_hash_step current_hash (Seq.index text s) (Seq.index text (s + m)) d q h
           == hash text d q (s + 1) (s + m + 1))
  = let old_char = Seq.index text s in
    let pow_d_m = pow d (m - 1) in
    pow_mod_correct d (m - 1) q;
    // Remove MSD using proven lemma
    remove_msd_lemma text d q s (s + m) current_hash pow_d_m;
    // Show rolling_hash_step's intermediate == proven intermediate
    FStar.Math.Lemmas.lemma_mod_mul_distr_r old_char pow_d_m q;
    lemma_mod_sub_via_add current_hash (old_char * pow_d_m) q;
    FStar.Math.Lemmas.lemma_mod_sub_distr current_hash (old_char * pow_d_m) q
#pop-options
//SNIPPET_END: rolling_hash_step_correct

(*** Pattern Matching ***)

//SNIPPET_START: matches_at
let matches_at (text pattern:Seq.seq nat) (s:nat) : prop =
  s + Seq.length pattern <= Seq.length text /\
  (forall (j:nat). j < Seq.length pattern ==>
    Seq.index text (s + j) == Seq.index pattern j)
//SNIPPET_END: matches_at

let rec check_matches_at_aux (text pattern:Seq.seq nat) (s:nat)
                             (j:nat{j <= Seq.length pattern})
  : Tot bool (decreases (Seq.length pattern - j))
  = if j >= Seq.length pattern then true
    else if s + j >= Seq.length text then false
    else Seq.index text (s + j) = Seq.index pattern j &&
         check_matches_at_aux text pattern s (j + 1)

let matches_at_dec (text pattern:Seq.seq nat) (s:nat) : bool =
  s + Seq.length pattern <= Seq.length text &&
  check_matches_at_aux text pattern s 0

let rec check_matches_at_aux_correct (text pattern:Seq.seq nat) (s:nat)
                                     (j:nat{j <= Seq.length pattern})
  : Lemma (requires s + Seq.length pattern <= Seq.length text)
          (ensures check_matches_at_aux text pattern s j <==>
                   (forall (k:nat). j <= k /\ k < Seq.length pattern ==>
                     Seq.index text (s + k) == Seq.index pattern k))
          (decreases (Seq.length pattern - j))
  = if j >= Seq.length pattern then ()
    else check_matches_at_aux_correct text pattern s (j + 1)

let matches_at_dec_correct (text pattern:Seq.seq nat) (s:nat)
  : Lemma (requires s + Seq.length pattern <= Seq.length text)
          (ensures matches_at_dec text pattern s <==> matches_at text pattern s)
  = check_matches_at_aux_correct text pattern s 0

/// Equal substrings produce equal hashes (for no-false-negatives).
let hash_match_lemma (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0}) (s:nat)
  : Lemma (requires s + Seq.length pattern <= Seq.length text /\ matches_at text pattern s)
          (ensures hash text d q s (s + Seq.length pattern) ==
                   hash pattern d q 0 (Seq.length pattern))
  = hash_slice_lemma text pattern d q s (s + Seq.length pattern) 0 (Seq.length pattern)

(*** Rabin-Karp Algorithm ***)

//SNIPPET_START: rabin_karp
/// Verify: if hashes match, check characters; otherwise reject.
let verify_match (text pattern:Seq.seq nat) (s:nat)
                 (text_hash pattern_hash:nat) : bool =
  if text_hash <> pattern_hash then false
  else matches_at_dec text pattern s

/// Rabin-Karp: scan text from position s, maintaining rolling hash.
#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 4"
let rec rabin_karp_matches (text pattern:Seq.seq nat)
                           (d:nat) (q:nat{q <> 0})
                           (s:nat) (current_hash:nat)
  : Tot (list nat) (decreases (Seq.length text - s))
  = let m = Seq.length pattern in
    if m = 0 || s + m > Seq.length text then []
    else
      let pattern_hash = hash pattern d q 0 m in
      let matches_here = verify_match text pattern s current_hash pattern_hash in
      let rest =
        if s + m = Seq.length text then []
        else
          let h = pow_mod d (m - 1) q in
          let next_hash = rolling_hash_step current_hash
                            (Seq.index text s) (Seq.index text (s + m)) d q h in
          rabin_karp_matches text pattern d q (s + 1) next_hash
      in
      if matches_here then s :: rest else rest
#pop-options

/// Top-level entry point.
let rabin_karp_find_all (text pattern:Seq.seq nat)
                        (d:nat) (q:nat{q <> 0}) : list nat =
  let m = Seq.length pattern in
  if m = 0 || m > Seq.length text then []
  else rabin_karp_matches text pattern d q 0 (hash text d q 0 m)
//SNIPPET_END: rabin_karp

(*** Correctness Proofs ***)

//SNIPPET_START: correctness
/// No false positives: every returned position is a valid match.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec rabin_karp_matches_no_false_positives
    (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
    (s:nat) (current_hash:nat)
  : Lemma (ensures (let results = rabin_karp_matches text pattern d q s current_hash in
                    forall (pos:nat). List.Tot.mem pos results ==>
                      pos >= s /\ matches_at text pattern pos))
          (decreases Seq.length text - s)
  = let m = Seq.length pattern in
    if m = 0 || s + m > Seq.length text then ()
    else (
      if verify_match text pattern s current_hash (hash pattern d q 0 m) then
        matches_at_dec_correct text pattern s;
      if s + m < Seq.length text then
        let h = pow_mod d (m - 1) q in
        let next = rolling_hash_step current_hash
                     (Seq.index text s) (Seq.index text (s + m)) d q h in
        rabin_karp_matches_no_false_positives text pattern d q (s + 1) next
    )
#pop-options

/// No false negatives: every valid match appears in results.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50 --split_queries always"
let rec rabin_karp_matches_no_false_negatives
    (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
    (s:nat) (current_hash:nat)
  : Lemma (requires (let m = Seq.length pattern in
                     m > 0 /\ s + m <= Seq.length text /\
                     current_hash == hash text d q s (s + m)))
          (ensures (let m = Seq.length pattern in
                    let results = rabin_karp_matches text pattern d q s current_hash in
                    forall (pos:nat). s <= pos /\ pos + m <= Seq.length text /\
                      matches_at text pattern pos ==> List.Tot.mem pos results))
          (decreases (Seq.length text - s))
  = let m = Seq.length pattern in
    if m = 0 || s + m > Seq.length text then ()
    else (
      // At position s: matching substrings have equal hashes, so verify_match succeeds
      let helper_at_s () : Lemma
        (requires matches_at text pattern s)
        (ensures List.Tot.mem s (rabin_karp_matches text pattern d q s current_hash))
        = hash_match_lemma text pattern d q s;
          matches_at_dec_correct text pattern s
      in
      Classical.move_requires helper_at_s ();
      // Inductive step: rolling hash gives correct hash for s+1
      if s + m < Seq.length text then (
        let h = pow_mod d (m - 1) q in
        let next = rolling_hash_step current_hash
                     (Seq.index text s) (Seq.index text (s + m)) d q h in
        rolling_hash_step_correct text d q s m current_hash h;
        assert (next == hash text d q (s + 1) (s + m + 1));
        rabin_karp_matches_no_false_negatives text pattern d q (s + 1) next
      )
    )
#pop-options

/// Main theorem: rabin_karp_find_all is correct (no false positives, no false negatives).
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let rabin_karp_find_all_no_false_positives (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
  : Lemma (forall (pos:nat). List.Tot.mem pos (rabin_karp_find_all text pattern d q) ==>
              matches_at text pattern pos)
  = let m = Seq.length pattern in
    if m = 0 || m > Seq.length text then ()
    else rabin_karp_matches_no_false_positives text pattern d q 0 (hash text d q 0 m)

let rabin_karp_find_all_no_false_negatives (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
  : Lemma (requires Seq.length pattern > 0)
          (ensures forall (pos:nat). pos + Seq.length pattern <= Seq.length text /\
                              matches_at text pattern pos ==>
              List.Tot.mem pos (rabin_karp_find_all text pattern d q))
  = let m = Seq.length pattern in
    if m > Seq.length text then ()
    else rabin_karp_matches_no_false_negatives text pattern d q 0 (hash text d q 0 m)

let rabin_karp_find_all_correct (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
  : Lemma (let results = rabin_karp_find_all text pattern d q in
           (forall (pos:nat). List.Tot.mem pos results ==> matches_at text pattern pos) /\
           (Seq.length pattern > 0 ==>
             (forall (pos:nat). pos + Seq.length pattern <= Seq.length text /\
                                matches_at text pattern pos ==> List.Tot.mem pos results)))
  = rabin_karp_find_all_no_false_positives text pattern d q;
    if Seq.length pattern > 0 then
      rabin_karp_find_all_no_false_negatives text pattern d q
#pop-options
//SNIPPET_END: correctness
