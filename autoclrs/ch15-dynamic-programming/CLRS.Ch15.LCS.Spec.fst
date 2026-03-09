(*
   Longest Common Subsequence — Pure F* Specification (CLRS Chapter 15)

   Defines:
   1. lcs_length: the LCS recurrence (CLRS Eq. 15.9)
   2. Subsequence and common subsequence predicates
   3. DP table correctness predicates and helper lemmas

   NO admits. NO assumes.
*)

module CLRS.Ch15.LCS.Spec

open FStar.Seq

// ========== LCS Recurrence (CLRS Eq. 15.9) ==========

//SNIPPET_START: lcs_spec
let rec lcs_length (x y: seq int) (i j: nat) : Tot int (decreases i + j) =
  if i = 0 || j = 0 then 0
  else if i <= length x && j <= length y && 
          index x (i - 1) = index y (j - 1) then
    1 + lcs_length x y (i - 1) (j - 1)
  else
    let l1 = lcs_length x y (i - 1) j in
    let l2 = lcs_length x y i (j - 1) in
    if l1 >= l2 then l1 else l2
//SNIPPET_END: lcs_spec

// Convenient helpers
let lcs_at (x y: seq int) (i j: nat) : int =
  if i <= length x && j <= length y then lcs_length x y i j else 0

let tbl_idx (i j: nat) (n1: nat) : nat = op_Multiply i n1 + j

// Lemma: lcs_length is non-negative
let rec lcs_length_nonneg (x y: seq int) (i j: nat)
  : Lemma (ensures lcs_length x y i j >= 0)
          (decreases i + j)
  = if i = 0 || j = 0 then ()
    else if i <= length x && j <= length y &&
            index x (i - 1) = index y (j - 1) then
      lcs_length_nonneg x y (i - 1) (j - 1)
    else begin
      lcs_length_nonneg x y (i - 1) j;
      lcs_length_nonneg x y i (j - 1)
    end

// Lemma: relating DP recurrence to lcs_length  
let lcs_recurrence_correct (x y: seq int) (i j: nat) 
  (val_diag val_up val_left: int)
  : Lemma 
    (requires 
      i > 0 /\ j > 0 /\
      i <= length x /\ j <= length y /\
      val_diag == lcs_length x y (i - 1) (j - 1) /\
      val_up == lcs_length x y (i - 1) j /\
      val_left == lcs_length x y i (j - 1))
    (ensures 
      (if index x (i - 1) = index y (j - 1) then val_diag + 1
       else if val_up >= val_left then val_up
       else val_left) == lcs_length x y i j)
  = ()

// DP table correctness predicate:
// All cells (r,c) with r < i, or r == i and c < j, are correct
let lcs_table_correct (x y: seq int) (tbl: seq int) (m n: nat) (i j: nat) : prop =
  let n1 = n + 1 in
  length tbl == op_Multiply (m + 1) n1 /\
  i <= m + 1 /\ j <= n + 1 /\
  (forall (r c: nat). (r < i \/ (r == i /\ c < j)) ==> r <= m ==> c <= n ==>
    index tbl (op_Multiply r n1 + c) == lcs_length x y r c)

// Lemma: updating table[i*(n+1)+j] with lcs_length value preserves correctness
// and advances to (i, j+1)
#push-options "--z3rlimit 20"
let lcs_table_update_preserves (x y: seq int) (tbl: seq int) (m n i j: nat) (v: int)
  : Lemma 
    (requires 
      lcs_table_correct x y tbl m n i j /\
      i <= m /\ j <= n /\
      v == lcs_length x y i j)
    (ensures (
      let idx = op_Multiply i (n + 1) + j in
      let tbl' = upd tbl idx v in
      lcs_table_correct x y tbl' m n i (j + 1)))
  = let n1 = n + 1 in
    let idx = op_Multiply i n1 + j in
    let tbl' = upd tbl idx v in
    assert (forall (r c: nat). ((r < i \/ (r == i /\ c < j + 1)) /\ r <= m /\ c <= n) ==>
      (let idx2 = op_Multiply r n1 + c in
       index tbl' idx2 == lcs_length x y r c))
#pop-options

// Lemma: advancing to next row resets column
let lcs_table_next_row (x y: seq int) (tbl: seq int) (m n i: nat)
  : Lemma 
    (requires lcs_table_correct x y tbl m n i (n + 1) /\ i <= m)
    (ensures lcs_table_correct x y tbl m n (i + 1) 0)
  = ()

// Combined lemma for DP value correctness
let lcs_step_correct (x y: seq int) (tbl: seq int) (m n i j: nat) (value: int)
  : Lemma
    (requires
      i <= m /\ j <= n /\
      m == length x /\ n == length y /\
      lcs_table_correct x y tbl m n i j /\
      (i = 0 \/ j = 0 ==> value == 0) /\
      (i > 0 /\ j > 0 ==> (
        let n1 = n + 1 in
        let val_diag = index tbl (op_Multiply (i - 1) n1 + (j - 1)) in
        let val_up = index tbl (op_Multiply (i - 1) n1 + j) in
        let val_left = index tbl (op_Multiply i n1 + (j - 1)) in
        let xi = index x (i - 1) in
        let yj = index y (j - 1) in
        value == (if xi = yj then val_diag + 1
                  else if val_up >= val_left then val_up
                  else val_left))))
    (ensures value == lcs_length x y i j)
  = if i = 0 || j = 0 then ()
    else ()

// ========== Subsequence Definitions ==========

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
