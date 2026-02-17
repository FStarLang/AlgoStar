(*
   CLRS Chapter 7: Quicksort Implementation in Pulse
   
   This implements the CLRS partition and quicksort algorithms with full
   functional correctness specifications.
*)

module CLRS.Ch07.Quicksort
#lang-pulse

open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT

(** Core definitions and utility functions **)

let nat_smaller (n: nat) = i:nat{i < n}

let seq_swap (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)) : GTot _ =
  Seq.swap s j i

(** Ghost functions to compute bounds **)

let rec seq_min (s: Seq.seq int) : GTot int (decreases (Seq.length s)) =
  if Seq.length s = 0 then 0
  else if Seq.length s = 1 then Seq.index s 0
  else let h = Seq.index s 0 in
       let t = seq_min (Seq.tail s) in
       if h < t then h else t

let rec seq_max (s: Seq.seq int) : GTot int (decreases (Seq.length s)) =
  if Seq.length s = 0 then 0
  else if Seq.length s = 1 then Seq.index s 0
  else let h = Seq.index s 0 in
       let t = seq_max (Seq.tail s) in
       if h > t then h else t

let rec lemma_seq_min_is_min (s: Seq.seq int) (i: nat{i < Seq.length s})
  : Lemma (ensures seq_min s <= Seq.index s i) (decreases (Seq.length s))
  = if Seq.length s <= 1 then ()
    else if i = 0 then ()
    else lemma_seq_min_is_min (Seq.tail s) (i - 1)

let rec lemma_seq_max_is_max (s: Seq.seq int) (i: nat{i < Seq.length s})
  : Lemma (ensures Seq.index s i <= seq_max s) (decreases (Seq.length s))
  = if Seq.length s <= 1 then ()
    else if i = 0 then ()
    else lemma_seq_max_is_max (Seq.tail s) (i - 1)

(** Sequence predicates for specification **)

let larger_than (s: Seq.seq int) (lb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> lb <= Seq.index s k

let smaller_than (s: Seq.seq int) (rb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> Seq.index s k <= rb

let between_bounds (s: Seq.seq int) (lb rb: int)
  = larger_than s lb /\ smaller_than s rb

//SNIPPET_START: sorted
let sorted (s: Seq.seq int)
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j
//SNIPPET_END: sorted

(** Lemma connecting min/max to between_bounds **)

let lemma_between_bounds_from_min_max (s: Seq.seq int)
  : Lemma (ensures between_bounds s (seq_min s) (seq_max s))
  = if Seq.length s = 0 then ()
    else (
      let aux_larger (k: nat{k < Seq.length s}) : Lemma
        (ensures seq_min s <= Seq.index s k)
        = lemma_seq_min_is_min s k
      in
      let aux_smaller (k: nat{k < Seq.length s}) : Lemma
        (ensures Seq.index s k <= seq_max s)
        = lemma_seq_max_is_max s k
      in
      FStar.Classical.forall_intro aux_larger;
      FStar.Classical.forall_intro aux_smaller
    )

(** Lemmas for combining sorted sequences **)

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
  = ()
#pop-options

(** Permutation reasoning **)

[@@"opaque_to_smt"]
let permutation s1 s2 : prop = (Seq.Properties.permutation int s1 s2)

let permutation_same_length (s1 s2 : Seq.seq int)
  : Lemma (requires permutation s1 s2)
          (ensures Seq.length s1 == Seq.length s2)
          [SMTPat (permutation s1 s2)]
  = 
  reveal_opaque (`%permutation) (permutation s1 s2);
  Seq.Properties.perm_len s1 s2

let append_permutations_3 (s1 s2 s3 s1' s3': Seq.seq int):
  Lemma
    (requires permutation s1 s1' /\ permutation s3 s3')
    (ensures permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')))
= (
  reveal_opaque (`%permutation) (permutation s1 s1');
  reveal_opaque (`%permutation) (permutation s2 s2);
  reveal_opaque (`%permutation) (permutation s3 s3');
  Seq.Properties.append_permutations s2 s3 s2 s3';
  reveal_opaque (`%permutation) (permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')));
  Seq.Properties.append_permutations s1 (Seq.append s2 s3) s1' (Seq.append s2 s3')
  )

let append_permutations_3_squash (s1 s2 s3 s1' s3': Seq.seq int)
  (_ : squash (permutation s1 s1' /\ permutation s3 s3'))
  : squash (permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')))
= append_permutations_3 s1 s2 s3 s1' s3'

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

let compose_permutations (s1 s2 s3: Seq.seq int)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]
   = (
      reveal_opaque (`%permutation) (permutation s1 s2);
      reveal_opaque (`%permutation) (permutation s2 s3);
      reveal_opaque (`%permutation) (permutation s1 s3);
      Seq.perm_len s1 s2;
      Seq.perm_len s1 s3;
      Seq.lemma_trans_perm s1 s2 s3 0 (Seq.length s1);
      ()
   )

let permutation_refl (s: Seq.seq int)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]
   =
   (
      reveal_opaque (`%permutation) (permutation s s);
      ()
   )

(** Array access helpers using pts_to_range **)

let op_Array_Access
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
: stt t
    (requires
      A.pts_to_range a l r #p s)
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

(** Swap operation with permutation proof **)

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

(** CLRS Partition predicate: elements <= pivot on left, > pivot on right **)

// For CLRS partition: all elements before i_plus_1 are <= pivot
// all elements from i_plus_1 to j are > pivot
//SNIPPET_START: clrs_partition_pred
let clrs_partition_pred (s:Seq.seq int) (lo:nat) (j:nat) (i_plus_1: nat) (pivot: int)
: prop
= forall (k:nat). {:pattern (Seq.index s k)}
   k < Seq.length s ==> (
    let kk = k + lo in
    (lo <= kk /\ kk < i_plus_1 ==> Seq.index s k <= pivot) /\
    (i_plus_1 <= kk /\ kk < j   ==> Seq.index s k > pivot))
//SNIPPET_END: clrs_partition_pred

(** CLRS Partition Algorithm
    
    Partitions array A[lo..hi) using A[hi-1] as pivot.
    Returns pivot position p such that:
    - All elements in A[lo..p) are <= pivot
    - A[p] == pivot
    - All elements in A[p+1..hi) are > pivot
**)

//SNIPPET_START: clrs_partition_sig
#push-options "--z3rlimit_factor 8 --retry 5"
fn clrs_partition (a: A.array int) (lo: nat) (hi:(hi:nat{lo < hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  requires (
    A.pts_to_range a lo hi s0 **
    pure (
      hi <= A.length a /\
      Seq.length s0 = hi - lo /\
      between_bounds s0 lb rb
      )
  )
  returns p: nat // pivot position
  ensures exists* s.
    A.pts_to_range a lo hi s **
    pure (
      Seq.length s = hi - lo /\ Seq.length s0 = hi - lo
      /\ lo <= p /\ p < hi /\ hi <= A.length a
      /\ (forall (k:nat). k < Seq.length s ==> (
           let kk = k + lo in
           (lo <= kk /\ kk < p ==> Seq.index s k <= Seq.index s (p - lo)) /\
           (kk == p                ==> Seq.index s k == Seq.index s (p - lo)) /\
           (p < kk /\ kk < hi      ==> Seq.index s k > Seq.index s (p - lo))
         ))
      /\ lb <= Seq.index s (p - lo) /\ Seq.index s (p - lo) <= rb
      /\ between_bounds s lb rb
      /\ permutation s0 s
    )
//SNIPPET_END: clrs_partition_sig
{
  // pivot = A[hi-1]
  let pivot = a.(SZ.uint_to_t (hi - 1));
  
  // i = lo - 1 (we use i_plus_1 = lo to avoid negative)
  let mut i_plus_1 = lo;
  
  // for j = lo to hi-2
  let mut j = lo;
  
  while (let vj = !j; (vj < hi - 1))
    invariant exists* s. (
      A.pts_to_range a lo hi s **
      live i_plus_1 ** live j **
      pure (
        lo <= !j /\ !j <= hi - 1 /\
        lo <= !i_plus_1 /\ !i_plus_1 <= !j /\
        lb <= pivot /\ pivot <= rb /\
        Seq.length s = hi - lo /\
        Seq.index s (hi - 1 - lo) = pivot
        /\ clrs_partition_pred s lo (!j) (!i_plus_1) pivot
        /\ permutation s0 s
        /\ between_bounds s lb rb
      ))
  { 
    let vj = !j;
    let aj = a.(SZ.uint_to_t vj);
    
    // if A[j] <= pivot
    if (aj <= pivot) {
      // i = i + 1; swap A[i] and A[j]
      let vi_plus_1 = !i_plus_1;
      swap a vi_plus_1 vj;
      i_plus_1 := vi_plus_1 + 1;
      j := vj + 1;
    } else {
      j := vj + 1;
    };
  };
  
  // swap A[i+1] and A[hi-1]
  let vi_plus_1 = !i_plus_1;
  swap a vi_plus_1 (hi - 1);
  
  // return i + 1
  vi_plus_1
}
#pop-options

(** Helper lemmas for transferring bounds to slices **)

#restart-solver
#push-options "--retry 10"
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

#push-options "--z3rlimit_factor 4 --split_queries no"
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
#pop-options
#pop-options

(** Partition wrapper that splits ownership for recursive calls **)

#push-options "--z3rlimit_factor 8 --retry 5"
fn clrs_partition_wrapper (a: A.array int) (lo: nat) (hi:(hi:nat{lo < hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  requires (
    A.pts_to_range a lo hi s0 **
    pure (
      hi <= A.length a /\
      Seq.length s0 = hi - lo /\
      between_bounds s0 lb rb
      )
  )
  returns p: nat // pivot position
  ensures exists* s1 s_pivot s2. (
    A.pts_to_range a lo   p     s1 **
    A.pts_to_range a p    (p+1) s_pivot **
    A.pts_to_range a (p+1) hi   s2 **
    pure (
      lo <= p /\ p < hi /\ hi <= A.length a /\
      Seq.length s1 == p - lo /\ Seq.length s_pivot == 1 /\ Seq.length s2 == hi - (p+1) /\
      lb <= Seq.index s_pivot 0 /\ Seq.index s_pivot 0 <= rb /\
      between_bounds s1 lb (Seq.index s_pivot 0) /\
      between_bounds s2 (Seq.index s_pivot 0) rb /\
      permutation s0 (Seq.append s1 (Seq.append s_pivot s2))
   ))
{
  let p = clrs_partition a lo hi lb rb #s0;
  with s. assert (A.pts_to_range a lo hi s);

  pts_to_range_split a lo p hi;
  with s_left. assert (A.pts_to_range a lo p s_left);
  with s_right_plus. assert (A.pts_to_range a p hi s_right_plus);
  
  pts_to_range_split a p (p+1) hi;
  with s_pivot. assert (A.pts_to_range a p (p+1) s_pivot);
  with s_right. assert (A.pts_to_range a (p+1) hi s_right);

  assert (pure (Seq.length s_left == p - lo));
  assert (pure (Seq.length s_pivot == 1));
  assert (pure (Seq.length s_right == hi - (p+1)));
  
  assert pure (squash (permutation s0 (Seq.append s_left (Seq.append s_pivot s_right))));
  
  transfer_smaller_slice s lo lo p (Seq.index s_pivot 0);
  transfer_larger_slice s lo lo p lb;
  assert (pure (between_bounds s_left lb (Seq.index s_pivot 0)));
  
  transfer_smaller_slice s lo (p+1) hi rb;
  transfer_larger_slice s lo (p+1) hi (Seq.index s_pivot 0);
  assert (pure (between_bounds s_right (Seq.index s_pivot 0) rb));
  
  p
}
#pop-options

(** QuickSort specification predicates **)

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

(** Ghost proof function to combine sorted sub-arrays **)

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

(** CLRS QuickSort Algorithm
    
    Recursively sorts A[lo..hi):
    1. If lo < hi, partition around pivot
    2. Recursively sort left partition
    3. Recursively sort right partition
**)

//SNIPPET_START: clrs_quicksort_sig
fn rec clrs_quicksort 
  (a: A.array int) 
  (lo: nat) 
  (hi:(hi:nat{lo <= hi})) 
  (lb rb: erased int) 
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a lo hi s0
  requires pure (pure_pre_quicksort a lo hi lb rb s0)
  ensures exists* s. (A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))
//SNIPPET_END: clrs_quicksort_sig
{
  if (lo < hi)
  {
    let p = clrs_partition_wrapper a lo hi lb rb;
    with s_left. assert (A.pts_to_range a lo p s_left);
    with s_pivot. assert (A.pts_to_range a p (p+1) s_pivot);
    with s_right. assert (A.pts_to_range a (p+1) hi s_right);

    clrs_quicksort a lo p lb (hide (Seq.index s_pivot 0));
    clrs_quicksort a (p+1) hi (hide (Seq.index s_pivot 0)) rb;
    
    with s_left'. assert (A.pts_to_range a lo p s_left');
    with s_right'. assert (A.pts_to_range a (p+1) hi s_right');
    
    let _ = append_permutations_3_squash s_left s_pivot s_right s_left' s_right' ();

    quicksort_proof a lo p hi lb rb (Seq.index s_pivot 0) #s0 s_left' s_pivot s_right';
  }
}

(** Top-level API function - sorts entire array **)

//SNIPPET_START: quicksort_sig
fn quicksort 
  (a: A.array int)
  (len: SZ.t)
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to a s0
  requires pure (Seq.length s0 == A.length a /\ A.length a == SZ.v len /\ SZ.v len > 0)
  ensures exists* s. (A.pts_to a s ** pure (sorted s /\ permutation s0 s))
//SNIPPET_END: quicksort_sig
{
  if (SZ.gt len 1sz) {
    // Array has more than one element - need to sort
    // Convert pts_to to pts_to_range
    A.pts_to_range_intro a 1.0R s0;
    
    // Compute bounds from the sequence (ghost)
    lemma_between_bounds_from_min_max s0;
    
    // Call quicksort with range [0, len) and computed bounds
    clrs_quicksort a 0 (SZ.v len) (hide (seq_min s0)) (hide (seq_max s0));
    
    // Convert back to pts_to
    with s'. assert (A.pts_to_range a 0 (A.length a) s');
    A.pts_to_range_elim a 1.0R s';
    ()
  } else {
    // Single element is sorted
    ()
  }
}

(** Example: Sort a specific array range with known bounds **)

fn quicksort_bounded
  (a: A.array int)
  (lo: nat)
  (hi: (hi:nat{lo <= hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a lo hi s0
  requires pure (
    hi <= A.length a /\
    Seq.length s0 = hi - lo /\
    between_bounds s0 lb rb /\
    lb <= rb
  )
  ensures exists* s. (
    A.pts_to_range a lo hi s **
    pure (sorted s /\ permutation s0 s)
  )
{
  clrs_quicksort a lo hi lb rb;
}
