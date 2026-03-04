(*
   Longest Common Subsequence — Optimality Specification (CLRS Chapter 15)

   Proves that lcs_length computes the length of a truly longest common subsequence:
   1. Defines is_subsequence and is_common_subsequence
   2. Optimality: lcs_length x y i j >= |sub| for any common subsequence sub
   3. Witness: there exists a common subsequence of length exactly lcs_length x y i j

   NO admits. NO assumes.
*)

module CLRS.Ch15.LCS.Spec

open FStar.Seq
open FStar.Classical
open CLRS.Ch15.LCS

// ========== Subsequence Definition ==========

/// sub[0..k-1] is a subsequence of s[0..n-1].
/// Greedy-from-right: when sub[k-1] = s[n-1], always match them.
let rec is_subseq (sub: seq int) (k: nat) (s: seq int) (n: nat)
  : Tot bool (decreases k + n) =
  if k = 0 then true
  else if n = 0 then false
  else if k > length sub || n > length s then false
  else if index sub (k - 1) = index s (n - 1) then
    is_subseq sub (k - 1) s (n - 1)
  else
    is_subseq sub k s (n - 1)

/// Full-sequence wrapper
let is_subsequence (sub s: seq int) : bool =
  is_subseq sub (length sub) s (length s)

/// Common subsequence of x and y
let is_common_subsequence (sub x y: seq int) : prop =
  is_subsequence sub x /\ is_subsequence sub y

// ========== Optimality Proof ==========

/// Any common subsequence of x[0..i-1] and y[0..j-1] has length at most lcs_length x y i j.
/// Proof by induction on i + j with case split on character match.
let rec lcs_optimal (x y: seq int) (i j: nat) (sub: seq int) (k: nat)
  : Lemma
    (requires i <= length x /\ j <= length y /\
              k <= length sub /\
              is_subseq sub k x i /\ is_subseq sub k y j)
    (ensures lcs_length x y i j >= k)
    (decreases i + j)
  = if k = 0 then lcs_length_nonneg x y i j
    else if i = 0 || j = 0 then ()
    else begin
      let sk = index sub (k - 1) in
      let xi = index x (i - 1) in
      let yj = index y (j - 1) in
      if xi = yj then begin
        // lcs_length x y i j = 1 + lcs_length x y (i-1) (j-1)
        if sk = xi then
          // Both match: sub[k-1] = x[i-1] = y[j-1], recurse (k-1, i-1, j-1)
          lcs_optimal x y (i - 1) (j - 1) sub (k - 1)
        else
          // Both skip: sub[k-1] ≠ x[i-1] = y[j-1], so is_subseq sub k x (i-1) and y (j-1)
          // IH gives lcs_length(i-1,j-1) >= k, so 1 + that > k
          lcs_optimal x y (i - 1) (j - 1) sub k
      end
      else begin
        // lcs_length x y i j = max(lcs_length(i-1,j), lcs_length(i,j-1))
        if sk = xi then
          // sub[k-1] = x[i-1] ≠ y[j-1]: y skips, use original is_subseq sub k x i
          lcs_optimal x y i (j - 1) sub k
        else
          // sub[k-1] ≠ x[i-1]: x skips, use original is_subseq sub k y j
          lcs_optimal x y (i - 1) j sub k
      end
    end

// ========== Monotonicity Lemmas ==========

/// Prefix: dropping the last element of a subsequence preserves the property.
/// Weakening: extending s by one element preserves the subsequence property.
/// These are mutually recursive; we use a bool flag (true = weaken, false = prefix).
let rec is_subseq_prefix_weaken
  (sub: seq int) (k: nat) (s: seq int) (n: nat) (weaken: bool)
  : Lemma
    (requires
      (weaken == false ==> (k > 0 /\ is_subseq sub k s n)) /\
      (weaken == true ==> (is_subseq sub k s n /\ n < length s)))
    (ensures
      (weaken == false ==> is_subseq sub (k - 1) s n) /\
      (weaken == true ==> is_subseq sub k s (n + 1)))
    (decreases %[k + n; (if weaken then 1 else 0)])
  = if weaken then begin
      // Weakening
      if k = 0 then ()
      else begin
        // k > 0 and is_subseq sub k s n: n > 0, k <= |sub|, n <= |s|
        // n < |s| from requires, so n + 1 <= |s|
        if k <= length sub && n + 1 <= length s then
          if index sub (k - 1) = index s n then
            // Need is_subseq sub (k-1) s n — call prefix at same k+n
            is_subseq_prefix_weaken sub k s n false
          else
            () // sub[k-1] ≠ s[n]: is_subseq sub k s n, which we have
        else ()
      end
    end
    else begin
      // Prefix: k > 0, is_subseq sub k s n → is_subseq sub (k-1) s n
      if k = 1 then ()
      else if n = 0 then ()
      else if k <= length sub && n <= length s then begin
        if index sub (k - 1) = index s (n - 1) then begin
          // is_subseq sub (k-1) s (n-1) holds from unfolding
          // Need is_subseq sub (k-1) s n: use weakening at (k-1, n-1)
          if n - 1 < length s then
            is_subseq_prefix_weaken sub (k - 1) s (n - 1) true
          else ()
        end
        else begin
          // is_subseq sub k s (n-1) holds from unfolding
          // Get is_subseq sub (k-1) s (n-1) via prefix at (k, n-1)
          is_subseq_prefix_weaken sub k s (n - 1) false;
          // Then weaken (k-1, n-1) → (k-1, n)
          if k - 1 = 0 then ()
          else if n - 1 < length s then
            is_subseq_prefix_weaken sub (k - 1) s (n - 1) true
          else ()
        end
      end
      else ()
    end

/// Convenient wrapper: weakening
let is_subseq_weaken (sub: seq int) (k: nat) (s: seq int) (n: nat)
  : Lemma (requires is_subseq sub k s n /\ n < length s)
          (ensures is_subseq sub k s (n + 1))
  = is_subseq_prefix_weaken sub k s n true

// ========== Witness Construction ==========

/// Build an actual LCS following the DP recurrence.
let rec build_lcs (x y: seq int) (i j: nat) : Tot (seq int) (decreases i + j) =
  if i = 0 || j = 0 then empty
  else if i <= length x && j <= length y &&
          index x (i - 1) = index y (j - 1) then
    snoc (build_lcs x y (i - 1) (j - 1)) (index x (i - 1))
  else
    let l1 = lcs_length x y (i - 1) j in
    let l2 = lcs_length x y i (j - 1) in
    if l1 >= l2 then build_lcs x y (i - 1) j
    else build_lcs x y i (j - 1)

/// Length of built LCS equals lcs_length
let rec build_lcs_length (x y: seq int) (i j: nat)
  : Lemma
    (requires i <= length x /\ j <= length y)
    (ensures length (build_lcs x y i j) == lcs_length x y i j)
    (decreases i + j)
  = if i = 0 || j = 0 then ()
    else if index x (i - 1) = index y (j - 1) then begin
      build_lcs_length x y (i - 1) (j - 1);
      lcs_length_nonneg x y (i - 1) (j - 1);
      assert (length (snoc (build_lcs x y (i - 1) (j - 1)) (index x (i - 1)))
              == length (build_lcs x y (i - 1) (j - 1)) + 1)
    end
    else begin
      let l1 = lcs_length x y (i - 1) j in
      let l2 = lcs_length x y i (j - 1) in
      if l1 >= l2 then build_lcs_length x y (i - 1) j
      else build_lcs_length x y i (j - 1)
    end

/// Extensionality: is_subseq depends only on the first k elements of sub.
let rec is_subseq_ext (sub1 sub2: seq int) (k: nat) (s: seq int) (n: nat)
  : Lemma
    (requires k <= length sub1 /\ k <= length sub2 /\
              (forall (j:nat). j < k ==> index sub1 j == index sub2 j))
    (ensures is_subseq sub1 k s n == is_subseq sub2 k s n)
    (decreases k + n)
  = if k = 0 then ()
    else if n = 0 then ()
    else if k > length sub1 || n > length s then ()
    else begin
      assert (index sub1 (k - 1) == index sub2 (k - 1));
      if index sub1 (k - 1) = index s (n - 1) then
        is_subseq_ext sub1 sub2 (k - 1) s (n - 1)
      else
        is_subseq_ext sub1 sub2 k s (n - 1)
    end

/// Helper: Seq.snoc preserves indices below the original length.
let lemma_snoc_index_below (s: seq int) (v: int) (i: nat)
  : Lemma (requires i < length s)
          (ensures index (snoc s v) i == index s i)
  = lemma_index_app1 s (create 1 v) i

/// Helper: Seq.snoc sets the last index to the appended value.
let lemma_snoc_last (s: seq int) (v: int)
  : Lemma (ensures index (snoc s v) (length s) == v)
  = lemma_index_app2 s (create 1 v) (length s)

/// build_lcs is a subsequence of x
#push-options "--z3rlimit 30"
let rec build_lcs_subseq_x (x y: seq int) (i j: nat)
  : Lemma
    (requires i <= length x /\ j <= length y)
    (ensures is_subseq (build_lcs x y i j) (length (build_lcs x y i j)) x i)
    (decreases i + j)
  = if i = 0 || j = 0 then ()
    else if index x (i - 1) = index y (j - 1) then begin
      let prev = build_lcs x y (i - 1) (j - 1) in
      let v = index x (i - 1) in
      let sub = snoc prev v in
      build_lcs_subseq_x x y (i - 1) (j - 1);
      build_lcs_length x y (i - 1) (j - 1);
      lcs_length_nonneg x y (i - 1) (j - 1);
      // sub = snoc prev v, length sub = length prev + 1
      // sub[length prev] = v = x[i-1], so is_subseq matches at position i
      lemma_snoc_last prev v;
      // For the recursive part: is_subseq sub (length prev) x (i-1)
      // equals is_subseq prev (length prev) x (i-1) by extensionality
      let k = length prev in
      introduce forall (j:nat). j < k ==> index sub j == index prev j
      with introduce _ ==> _
      with _. lemma_snoc_index_below prev v j;
      is_subseq_ext sub prev k x (i - 1)
    end
    else begin
      let l1 = lcs_length x y (i - 1) j in
      let l2 = lcs_length x y i (j - 1) in
      if l1 >= l2 then begin
        build_lcs_subseq_x x y (i - 1) j;
        // IH: is_subseq (build_lcs(i-1,j)) len x (i-1)
        // Need: is_subseq (build_lcs(i-1,j)) len x i — use weakening
        let sub = build_lcs x y (i - 1) j in
        let k = length sub in
        if i - 1 < length x then
          is_subseq_weaken sub k x (i - 1)
        else ()
      end
      else begin
        build_lcs_subseq_x x y i (j - 1)
        // IH: is_subseq (build_lcs(i,j-1)) len x i — same i, no weakening needed
      end
    end
#pop-options

/// build_lcs is a subsequence of y
#push-options "--z3rlimit 30"
let rec build_lcs_subseq_y (x y: seq int) (i j: nat)
  : Lemma
    (requires i <= length x /\ j <= length y)
    (ensures is_subseq (build_lcs x y i j) (length (build_lcs x y i j)) y j)
    (decreases i + j)
  = if i = 0 || j = 0 then ()
    else if index x (i - 1) = index y (j - 1) then begin
      let prev = build_lcs x y (i - 1) (j - 1) in
      let v = index x (i - 1) in
      let sub = snoc prev v in
      build_lcs_subseq_y x y (i - 1) (j - 1);
      build_lcs_length x y (i - 1) (j - 1);
      lcs_length_nonneg x y (i - 1) (j - 1);
      // sub[length prev] = v = x[i-1] = y[j-1]
      lemma_snoc_last prev v;
      let k = length prev in
      introduce forall (j:nat). j < k ==> index sub j == index prev j
      with introduce _ ==> _
      with _. lemma_snoc_index_below prev v j;
      is_subseq_ext sub prev k y (j - 1)
    end
    else begin
      let l1 = lcs_length x y (i - 1) j in
      let l2 = lcs_length x y i (j - 1) in
      if l1 >= l2 then begin
        build_lcs_subseq_y x y (i - 1) j
        // IH: is_subseq (build_lcs(i-1,j)) len y j — same j, no weakening needed
      end
      else begin
        build_lcs_subseq_y x y i (j - 1);
        // IH: is_subseq (build_lcs(i,j-1)) len y (j-1)
        // Need: is_subseq ... y j — use weakening
        let sub = build_lcs x y i (j - 1) in
        let k = length sub in
        if j - 1 < length y then
          is_subseq_weaken sub k y (j - 1)
        else ()
      end
    end
#pop-options

// ========== Top-Level Theorems ==========

/// Optimality: lcs_length is an upper bound on all common subsequences.
let lcs_optimality (x y sub: seq int)
  : Lemma
    (requires is_common_subsequence sub x y)
    (ensures lcs_length x y (length x) (length y) >= length sub)
  = lcs_optimal x y (length x) (length y) sub (length sub)

/// Witness: there exists a common subsequence achieving lcs_length.
let lcs_witness (x y: seq int)
  : Lemma
    (ensures (let n = lcs_length x y (length x) (length y) in
              exists (sub: seq int).
                length sub == n /\
                is_subsequence sub x /\ is_subsequence sub y))
  = let sub = build_lcs x y (length x) (length y) in
    build_lcs_length x y (length x) (length y);
    build_lcs_subseq_x x y (length x) (length y);
    build_lcs_subseq_y x y (length x) (length y);
    lcs_length_nonneg x y (length x) (length y)

/// Combined: lcs_length is exactly the length of the longest common subsequence.
let lcs_length_is_longest (x y: seq int)
  : Lemma
    (ensures (let n = lcs_length x y (length x) (length y) in
              // Upper bound: no common subsequence is longer
              (forall (sub: seq int). is_common_subsequence sub x y ==>
                length sub <= n) /\
              // Achievability: some common subsequence has this length
              (exists (sub: seq int).
                length sub == n /\
                is_subsequence sub x /\ is_subsequence sub y)))
  = lcs_witness x y;
    introduce forall (sub: seq int). is_common_subsequence sub x y ==>
      length sub <= lcs_length x y (length x) (length y)
    with introduce _ ==> _
    with _. lcs_optimality x y sub
