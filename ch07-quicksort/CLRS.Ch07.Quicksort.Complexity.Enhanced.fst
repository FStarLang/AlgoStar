(*
   CLRS Chapter 7: Quicksort with Enhanced Complexity Analysis
   
   This module extends the quicksort implementation with a tick counter
   threaded through the recursive calls to prove the O(n²) worst-case bound.
   
   Key results:
   1. Partition is Θ(n) - exactly n comparisons
   2. Worst-case recurrence: T(n) = T(n-1) + n when partition is maximally unbalanced
   3. Closed form: T(n) ≤ n(n+1)/2 = O(n²)
   
   The tick counter is threaded through all recursive calls using GhostReference
   to track cumulative operations without runtime overhead.
   
   NO admits. NO assumes.
*)

module CLRS.Ch07.Quicksort.Complexity.Enhanced
#lang-pulse

open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Pure Definitions ==========

let nat_smaller (n: nat) = i:nat{i < n}

let seq_swap (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)) : GTot _ =
  Seq.swap s j i

// ========== Ghost tick increment ==========

let incr_nat (n: erased nat) : erased nat = hide (reveal n + 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Sequence predicates ==========

let larger_than (s: Seq.seq int) (lb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> lb <= Seq.index s k

let smaller_than (s: Seq.seq int) (rb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> Seq.index s k <= rb

let between_bounds (s: Seq.seq int) (lb rb: int)
  = larger_than s lb /\ smaller_than s rb

let sorted (s: Seq.seq int)
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

// ========== Permutation ==========

[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)

let permutation_same_length (s1 s2 : Seq.seq int)
  : Lemma (requires permutation s1 s2)
          (ensures Seq.length s1 == Seq.length s2)
          [SMTPat (permutation s1 s2)]
  = reveal_opaque (`%permutation) (permutation s1 s2);
    Seq.Properties.perm_len s1 s2

let compose_permutations (s1 s2 s3: Seq.seq int)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]
   = reveal_opaque (`%permutation) (permutation s1 s2);
     reveal_opaque (`%permutation) (permutation s2 s3);
     reveal_opaque (`%permutation) (permutation s1 s3);
     Seq.perm_len s1 s2;
     Seq.perm_len s1 s3;
     Seq.lemma_trans_perm s1 s2 s3 0 (Seq.length s1)

let permutation_refl (s: Seq.seq int)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]
   = reveal_opaque (`%permutation) (permutation s s)

// ========== Complexity bound predicates ==========

// Linear bound: cf - c0 = n (exactly n operations)
let complexity_exact_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n

//SNIPPET_START: complexity_bounded_quadratic
let complexity_bounded_quadratic (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= op_Multiply n (n - 1) / 2
//SNIPPET_END: complexity_bounded_quadratic

// ========== Array access helpers ==========

let op_Array_Access
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
: stt t
    (requires A.pts_to_range a l r #p s)
    (ensures fun res ->
      A.pts_to_range a l r #p s **
      pure (Seq.length s == r - l /\
            res == Seq.index s (SZ.v i - l)))
= pts_to_range_index a i #l #r #s #p

let op_Array_Assignment
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (v: t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  (#s0: Ghost.erased (Seq.seq t))
: stt unit
    (requires A.pts_to_range a l r s0)
    (ensures fun _ -> 
      exists* s.
        A.pts_to_range a l r s **
        pure(
          Seq.length s0 == r - l /\ s == Seq.upd s0 (SZ.v i - l) v
        ))
= pts_to_range_upd a i v #l #r

// ========== Swap with permutation proof ==========

let seq_swap_commute (s: Seq.seq int) (i j: nat_smaller (Seq.length s)):
  Lemma (seq_swap s i j == seq_swap s j i)
  = (
    let sij = seq_swap s i j in
    let sji = seq_swap s j i in
    assert (Seq.length sij = Seq.length sji);
    assert (forall (k:nat{k < Seq.length sij}). (Seq.index sij k == Seq.index sji k));
    Seq.lemma_eq_elim sij sji;
    ()
  )

let permutation_swap (s: Seq.seq int) (i j: nat_smaller (Seq.length s)):
  Lemma (permutation s (seq_swap s i j))
    [SMTPat (permutation s (seq_swap s i j))]
    = (
      reveal_opaque (`%permutation) (permutation s (seq_swap s i j));
      if i <= j
        then (Seq.Properties.lemma_swap_permutes s i j; seq_swap_commute s i j)
        else Seq.Properties.lemma_swap_permutes s j i)

fn swap (a: A.array int) (i j: nat) (#l:nat{l <= i /\ l <= j}) (#r:nat{i < r /\ j < r})
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a l r s0
  ensures
    exists* s. 
      A.pts_to_range a l r s **
      pure (Seq.length s0 = r - l /\
            s == seq_swap s0 (i - l) (j - l) /\
            permutation s0 s)
{
  A.pts_to_range_prop a;
  let vi = a.(SZ.uint_to_t i);
  let vj = a.(SZ.uint_to_t j);
  (a.(SZ.uint_to_t i) <- vj);
  (a.(SZ.uint_to_t j) <- vi);
  ()
}

// ========== CLRS Partition predicate ==========

let clrs_partition_pred (s:Seq.seq int) (lo:nat) (j:nat) (i_plus_1: nat) (pivot: int)
: prop
= forall (k:nat). {:pattern (Seq.index s k)}
   k < Seq.length s ==> (
    let kk = k + lo in
    (lo <= kk /\ kk < i_plus_1 ==> Seq.index s k <= pivot) /\
    (i_plus_1 <= kk /\ kk < j   ==> Seq.index s k > pivot))

// ========== CLRS Partition with Tick Counter ==========

// This partition performs exactly (hi - lo) comparisons
#push-options "--z3rlimit_factor 8 --retry 5"
fn clrs_partition_with_ticks
  (a: A.array int)
  (lo: nat)
  (hi:(hi:nat{lo < hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires (
    A.pts_to_range a lo hi s0 **
    GR.pts_to ctr c0 **
    pure (
      hi <= A.length a /\
      Seq.length s0 = hi - lo /\
      between_bounds s0 lb rb
      )
  )
  returns p: nat
  ensures exists* s (cf: nat).
    A.pts_to_range a lo hi s **
    GR.pts_to ctr cf **
    pure (
      Seq.length s = hi - lo /\ Seq.length s0 = hi - lo /\
      lo <= p /\ p < hi /\ hi <= A.length a /\
      (forall (k:nat). k < Seq.length s ==> (
         let kk = k + lo in
         (lo <= kk /\ kk < p ==> Seq.index s k <= Seq.index s (p - lo)) /\
         (kk == p                ==> Seq.index s k == Seq.index s (p - lo)) /\
         (p < kk /\ kk < hi      ==> Seq.index s k > Seq.index s (p - lo))
       )) /\
      lb <= Seq.index s (p - lo) /\ Seq.index s (p - lo) <= rb /\
      between_bounds s lb rb /\
      permutation s0 s /\
      // Complexity: exactly (hi - lo - 1) comparisons (all elements except pivot)
      complexity_exact_linear cf (reveal c0) (hi - lo - 1)
    )
{
  let pivot = a.(SZ.uint_to_t (hi - 1));
  let mut i_plus_1 = lo;
  let mut j = lo;
  
  while (let vj = !j; (vj < hi - 1))
    invariant exists* s (vc: nat). (
      A.pts_to_range a lo hi s **
      GR.pts_to ctr vc **
      live i_plus_1 ** live j **
      pure (
        lo <= !j /\ !j <= hi - 1 /\
        lo <= !i_plus_1 /\ !i_plus_1 <= !j /\
        lb <= pivot /\ pivot <= rb /\
        Seq.length s = hi - lo /\
        Seq.index s (hi - 1 - lo) = pivot /\
        clrs_partition_pred s lo (!j) (!i_plus_1) pivot /\
        permutation s0 s /\
        between_bounds s lb rb /\
        // Tick counter: exactly (!j - lo) comparisons so far
        vc == reveal c0 + (!j - lo)
      ))
  { 
    let vj = !j;
    let aj = a.(SZ.uint_to_t vj);
    
    // This is the comparison: aj <= pivot
    // Increment tick counter for this comparison
    tick ctr;
    
    if (aj <= pivot) {
      let vi_plus_1 = !i_plus_1;
      swap a vi_plus_1 vj;
      i_plus_1 := vi_plus_1 + 1;
      j := vj + 1;
    } else {
      j := vj + 1;
    };
  };
  
  let vi_plus_1 = !i_plus_1;
  swap a vi_plus_1 (hi - 1);
  
  vi_plus_1
}
#pop-options

// ========== Helper lemmas for bounds ==========

let transfer_larger_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (lb: int)
: Lemma
    (requires 
      forall (k: int). l <= k /\ k < r ==> (lb <= Seq.index s (k - shift))
    )
    (ensures larger_than (Seq.slice s (l - shift) (r - shift)) lb)
= assert (forall (k: int). l <= k /\ k < r ==> (lb <= Seq.index s (k - shift)));
  assert (forall (k: int). l <= (k+shift) /\ (k+shift) < r ==> (lb <= Seq.index s ((k+shift) - shift)));
  assert (forall (k: int). l - shift <= k /\ k < r - shift ==> (lb <= Seq.index s k));
  ()

let transfer_smaller_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (rb: int)
: Lemma
    (requires 
      forall (k: int). l <= k /\ k < r ==> (Seq.index s (k - shift) <= rb)
    )
    (ensures smaller_than (Seq.slice s (l - shift) (r - shift)) rb)
= assert (forall (k: int). l <= k /\ k < r ==> (Seq.index s (k - shift) <= rb));
  assert (forall (k: int). l <= (k+shift) /\ (k+shift) < r ==> (Seq.index s ((k+shift) - shift) <= rb));
  assert (forall (k: int). l - shift <= k /\ k < r - shift ==> (Seq.index s k <= rb));
  ()

// ========== Partition wrapper with tick counter ==========

#push-options "--z3rlimit_factor 8 --retry 5"
fn clrs_partition_wrapper_with_ticks
  (a: A.array int)
  (lo: nat)
  (hi:(hi:nat{lo < hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires (
    A.pts_to_range a lo hi s0 **
    GR.pts_to ctr c0 **
    pure (
      hi <= A.length a /\
      Seq.length s0 = hi - lo /\
      between_bounds s0 lb rb
      )
  )
  returns p: nat
  ensures exists* s1 s_pivot s2 (cf: nat). (
    A.pts_to_range a lo   p     s1 **
    A.pts_to_range a p    (p+1) s_pivot **
    A.pts_to_range a (p+1) hi   s2 **
    GR.pts_to ctr cf **
    pure (
      lo <= p /\ p < hi /\ hi <= A.length a /\
      Seq.length s1 == p - lo /\ Seq.length s_pivot == 1 /\ Seq.length s2 == hi - (p+1) /\
      lb <= Seq.index s_pivot 0 /\ Seq.index s_pivot 0 <= rb /\
      between_bounds s1 lb (Seq.index s_pivot 0) /\
      between_bounds s2 (Seq.index s_pivot 0) rb /\
      permutation s0 (Seq.append s1 (Seq.append s_pivot s2)) /\
      complexity_exact_linear cf (reveal c0) (hi - lo - 1)
   ))
{
  let p = clrs_partition_with_ticks a lo hi lb rb ctr #c0;
  with s. assert (A.pts_to_range a lo hi s);
  with cf_partition. assert (GR.pts_to ctr cf_partition);

  pts_to_range_split a lo p hi;
  with s_left. assert (A.pts_to_range a lo p s_left);
  with s_right_plus. assert (A.pts_to_range a p hi s_right_plus);
  
  pts_to_range_split a p (p+1) hi;
  with s_pivot. assert (A.pts_to_range a p (p+1) s_pivot);
  with s_right. assert (A.pts_to_range a (p+1) hi s_right);

  transfer_smaller_slice s lo lo p (Seq.index s_pivot 0);
  transfer_larger_slice s lo lo p lb;
  
  transfer_smaller_slice s lo (p+1) hi rb;
  transfer_larger_slice s lo (p+1) hi (Seq.index s_pivot 0);
  
  p
}
#pop-options

// ========== Lemmas for combining sorted sequences ==========

let append_permutations_3 (s1 s2 s3 s1' s3': Seq.seq int):
  Lemma
    (requires permutation s1 s1' /\ permutation s3 s3')
    (ensures permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')))
= reveal_opaque (`%permutation) (permutation s1 s1');
  reveal_opaque (`%permutation) (permutation s2 s2);
  reveal_opaque (`%permutation) (permutation s3 s3');
  Seq.Properties.append_permutations s2 s3 s2 s3';
  reveal_opaque (`%permutation) (permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')));
  Seq.Properties.append_permutations s1 (Seq.append s2 s3) s1' (Seq.append s2 s3')

let append_permutations_3_squash (s1 s2 s3 s1' s3': Seq.seq int)
  (_ : squash (permutation s1 s1' /\ permutation s3 s3'))
  : squash (permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')))
= append_permutations_3 s1 s2 s3 s1' s3'

#push-options "--retry 5"
let lemma_sorted_append
  (s1 s2 : Seq.seq int)
  (l1 r1 l2 r2 : int)
  : Lemma
    (requires sorted s1 /\ between_bounds s1 l1 r1 /\
              sorted s2 /\ between_bounds s2 l2 r2 /\
              r1 >= l1 /\ r2 >= l2 /\
              r1 <= l2)
    (ensures sorted (Seq.append s1 s2) /\ between_bounds (Seq.append s1 s2) l1 r2)
  = ()

let lemma_sorted_append_squash
  (s1 s2 : Seq.seq int)
  (l1 r1 l2 r2 : int)
    (_ : squash (sorted s1 /\ between_bounds s1 l1 r1 /\
              sorted s2 /\ between_bounds s2 l2 r2 /\
              r1 >= l1 /\ r2 >= l2 /\
              r1 <= l2))
    : squash (sorted (Seq.append s1 s2) /\ between_bounds (Seq.append s1 s2) l1 r2)
  = lemma_sorted_append s1 s2 l1 r1 l2 r2
#pop-options

// ========== QuickSort specification predicates ==========

unfold
let pure_pre_quicksort (a: A.array int) (lo: nat) (hi:(hi:nat{lo <= hi})) (lb rb: int) (s0: Seq.seq int)
  = hi <= A.length a /\
    between_bounds s0 lb rb /\
    Seq.length s0 = hi - lo /\
    lo <= A.length a /\
    lb <= rb

unfold
let pure_post_quicksort (a: A.array int) (lo: nat) (hi:(hi:nat{lo <= hi})) (lb rb: int) (s0 s: Seq.seq int)
  = hi <= A.length a /\
    Seq.length s0 = hi - lo /\
    Seq.length s = hi - lo /\
    sorted s /\
    between_bounds s lb rb /\
    permutation s0 s

// ========== Ghost proof function ==========

ghost
fn quicksort_proof
  (a: A.array int)
  (lo: nat)
  (p: (p:nat{lo <= p}))
  (hi:(hi:nat{p < hi}))
  (lb rb pivot_val: int)
  (#s0: erased (Seq.seq int))
  (s_left s_pivot s_right : Seq.seq int)
  requires
    (exists* s_left'. (A.pts_to_range a lo p s_left' ** pure (pure_post_quicksort a lo p lb pivot_val s_left s_left'))) **
    (exists* s_right'. (A.pts_to_range a (p+1) hi s_right' ** pure (pure_post_quicksort a (p+1) hi pivot_val rb s_right s_right'))) **
    A.pts_to_range a p (p+1) s_pivot **
    pure (Seq.length s0 == hi - lo
          /\ Seq.length s_pivot == 1
          /\ lb <= pivot_val /\ pivot_val <= rb
          /\ Seq.index s_pivot 0 == pivot_val
          /\ permutation s0 (Seq.append s_left (Seq.append s_pivot s_right)))
  ensures
    exists* s.
      A.pts_to_range a lo hi s **
      pure (pure_post_quicksort a lo hi lb rb s0 s)
{
  with s_left'. assert (A.pts_to_range a lo p s_left');
  with s_right'. assert (A.pts_to_range a (p+1) hi s_right');

  pts_to_range_join a p (p+1) hi;
  pts_to_range_join a lo p hi;

  let _ = append_permutations_3_squash s_left s_pivot s_right s_left' s_right' ();
  let _ = lemma_sorted_append_squash s_pivot s_right' pivot_val pivot_val pivot_val rb ();
  let _ = lemma_sorted_append_squash s_left' (Seq.append s_pivot s_right') lb pivot_val pivot_val rb ();
  ()
}

// ========== Complexity lemmas ==========

// Key lemma: For worst-case, we need to track cumulative operations
// T(n) = (n-1) + T(n-1) when partition is maximally unbalanced (process n-1 elements, pivot doesn't count)

// Recurrence for worst-case: sum from i=0 to n-1 of i = n(n-1)/2
let rec worst_case_ticks (n: nat) : nat =
  if n <= 1 then 0
  else (n - 1) + worst_case_ticks (n - 1)

let rec lemma_worst_case_formula (n: nat)
  : Lemma (ensures op_Multiply 2 (worst_case_ticks n) == op_Multiply n (n - 1))
          (decreases n)
  = if n <= 1 then ()
    else (
      lemma_worst_case_formula (n - 1)
      // Proof by induction:
      // IH: 2 * worst_case_ticks (n-1) == (n-1) * (n-2)
      // Goal: 2 * worst_case_ticks n == n * (n-1)
      // 
      // 2 * worst_case_ticks n
      // = 2 * ((n-1) + worst_case_ticks (n-1))
      // = 2 * (n - 1) + 2 * worst_case_ticks (n-1)
      // = 2 * (n - 1) + (n-1) * (n-2)         [by IH]
      // = (n-1) * (2 + (n-2))
      // = (n-1) * n
      // = n * (n-1)
    )

let lemma_worst_case_quadratic (n: nat)
  : Lemma (ensures worst_case_ticks n <= op_Multiply n (n - 1) / 2)
  = lemma_worst_case_formula n

// Helper lemma for the recursive case: prove that the sum of partition cost + recursive costs
// is bounded by n*(n-1)/2
let lemma_quicksort_complexity_bound (n n_left n_right: nat) (c_partition: nat)
  : Lemma
    (requires
      n > 0 /\
      n_left + 1 + n_right == n /\  // left + pivot + right = total
      c_partition == n - 1)          // partition processes n-1 elements
    (ensures
      c_partition + op_Multiply n_left (n_left - 1) / 2 + op_Multiply n_right (n_right - 1) / 2
      <= op_Multiply n (n - 1) / 2)
  = // In the worst case, n_left = n-1 and n_right = 0
    // c_partition + (n-1)*(n-2)/2 + 0
    // = (n-1) + (n-1)*(n-2)/2
    // = (n-1) * (1 + (n-2)/2)
    // = (n-1) * (2 + n - 2) / 2
    // = (n-1) * n / 2
    // <= n * (n-1) / 2
    ()

// ========== Quicksort with Tick Counter ==========

//SNIPPET_START: clrs_quicksort_with_ticks_sig
fn rec clrs_quicksort_with_ticks
  (a: A.array int) 
  (lo: nat) 
  (hi:(hi:nat{lo <= hi})) 
  (lb rb: erased int) 
  (#s0: Ghost.erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to_range a lo hi s0 **
    GR.pts_to ctr c0 **
    pure (pure_pre_quicksort a lo hi lb rb s0)
  ensures exists* s (cf: nat).
    A.pts_to_range a lo hi s **
    GR.pts_to ctr cf **
    pure (
      pure_post_quicksort a lo hi lb rb s0 s /\
      complexity_bounded_quadratic cf (reveal c0) (hi - lo)
    )
//SNIPPET_END: clrs_quicksort_with_ticks_sig
{
  if (lo < hi)
  {
    // Partition: costs exactly (hi - lo) comparisons
    let p = clrs_partition_wrapper_with_ticks a lo hi lb rb ctr;
    
    with s_left. assert (A.pts_to_range a lo p s_left);
    with s_pivot. assert (A.pts_to_range a p (p+1) s_pivot);
    with s_right. assert (A.pts_to_range a (p+1) hi s_right);
    with c_after_partition. assert (GR.pts_to ctr c_after_partition);
    
    // Recursively sort left partition
    clrs_quicksort_with_ticks a lo p lb (hide (Seq.index s_pivot 0)) ctr #c_after_partition;
    
    with c_after_left. assert (GR.pts_to ctr c_after_left);
    
    // Recursively sort right partition
    clrs_quicksort_with_ticks a (p+1) hi (hide (Seq.index s_pivot 0)) rb ctr #c_after_left;
    
    with s_left'. assert (A.pts_to_range a lo p s_left');
    with s_right'. assert (A.pts_to_range a (p+1) hi s_right');
    with c_final. assert (GR.pts_to ctr c_final);
    
    let _ = append_permutations_3_squash s_left s_pivot s_right s_left' s_right' ();

    quicksort_proof a lo p hi lb rb (Seq.index s_pivot 0) #s0 s_left' s_pivot s_right';
    
    // Prove complexity bound - call lemma with concrete values
    lemma_quicksort_complexity_bound (hi - lo) (p - lo) (hi - (p + 1)) (hi - lo - 1);
    assert (pure (complexity_bounded_quadratic c_final (reveal c0) (hi - lo)));
    ()
  }
  else
  {
    // Base case: empty range, no operations
    ()
  }
}

// ========== Top-level theorem ==========

// Main theorem: Quicksort performs at most n(n-1)/2 comparisons in worst case
// This is Θ(n²) asymptotic complexity
let quicksort_worst_case_theorem (n: nat)
  : Lemma (ensures worst_case_ticks n <= op_Multiply n (n - 1) / 2)
  = lemma_worst_case_quadratic n
