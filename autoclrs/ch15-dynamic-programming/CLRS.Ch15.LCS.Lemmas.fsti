module CLRS.Ch15.LCS.Lemmas

open FStar.Seq
open FStar.Classical
open CLRS.Ch15.LCS.Spec

/// Any common subsequence of x[0..i-1] and y[0..j-1] has length at most lcs_length x y i j
val lcs_optimal (x y: seq int) (i j: nat) (sub: seq int) (k: nat)
  : Lemma
    (requires i <= length x /\ j <= length y /\
              k <= length sub /\
              is_subseq sub k x i /\ is_subseq sub k y j)
    (ensures lcs_length x y i j >= k)

/// Weakening: extending s by one element preserves the subsequence property
val is_subseq_weaken (sub: seq int) (k: nat) (s: seq int) (n: nat)
  : Lemma (requires is_subseq sub k s n /\ n < length s)
          (ensures is_subseq sub k s (n + 1))

/// Build an actual LCS following the DP recurrence
val build_lcs (x y: seq int) (i j: nat) : Tot (seq int)

/// Length of built LCS equals lcs_length
val build_lcs_length (x y: seq int) (i j: nat)
  : Lemma
    (requires i <= length x /\ j <= length y)
    (ensures length (build_lcs x y i j) == lcs_length x y i j)

/// Extensionality: is_subseq depends only on the first k elements of sub
val is_subseq_ext (sub1 sub2: seq int) (k: nat) (s: seq int) (n: nat)
  : Lemma
    (requires k <= length sub1 /\ k <= length sub2 /\
              (forall (j:nat). j < k ==> index sub1 j == index sub2 j))
    (ensures is_subseq sub1 k s n == is_subseq sub2 k s n)

/// build_lcs is a subsequence of x
val build_lcs_subseq_x (x y: seq int) (i j: nat)
  : Lemma
    (requires i <= length x /\ j <= length y)
    (ensures is_subseq (build_lcs x y i j) (length (build_lcs x y i j)) x i)

/// build_lcs is a subsequence of y
val build_lcs_subseq_y (x y: seq int) (i j: nat)
  : Lemma
    (requires i <= length x /\ j <= length y)
    (ensures is_subseq (build_lcs x y i j) (length (build_lcs x y i j)) y j)

/// Optimality: lcs_length is an upper bound on all common subsequences
val lcs_optimality (x y sub: seq int)
  : Lemma
    (requires is_common_subsequence sub x y)
    (ensures lcs_length x y (length x) (length y) >= length sub)

/// Witness: there exists a common subsequence achieving lcs_length
val lcs_witness (x y: seq int)
  : Lemma
    (ensures (let n = lcs_length x y (length x) (length y) in
              exists (sub: seq int).
                length sub == n /\
                is_subsequence sub x /\ is_subsequence sub y))

/// Combined: lcs_length is exactly the length of the longest common subsequence
val lcs_length_is_longest (x y: seq int)
  : Lemma
    (ensures (let n = lcs_length x y (length x) (length y) in
              (forall (sub: seq int). is_common_subsequence sub x y ==>
                length sub <= n) /\
              (exists (sub: seq int).
                length sub == n /\
                is_subsequence sub x /\ is_subsequence sub y)))
