module CLRS.Ch15.MatrixChain.Lemmas

open FStar.Seq
open FStar.Mul
open FStar.Classical

open CLRS.Ch15.MatrixChain.Spec

/// Cost of a single split at k
let split_cost (p: seq int) (i k j: nat) (left: int) (right: int) : int
  = left + right +
    (if i < length p && k + 1 < length p && j + 1 < length p
     then index p i * index p (k + 1) * index p (j + 1)
     else 0)

/// Minimum over split points k = start..j-1
val min_splits (p: seq int) (i j: nat) (start: nat{start >= i}) (acc: int) : Tot int

/// Optimal scalar multiplication count for A_i · ... · A_j (CLRS Eq. 15.7)
val mc_cost (p: seq int) (i j: nat) : Tot int

val mc_cost_base (p: seq int) (i: nat)
  : Lemma (mc_cost p i i == 0)

val min_splits_le_acc (p: seq int) (i j: nat) (start: nat{start >= i}) (acc: int)
  : Lemma (ensures min_splits p i j start acc <= acc)

val min_splits_acc_ge
  (p: seq int) (i j: nat) (start: nat{start >= i}) (acc1 acc2: int)
  : Lemma
      (requires
        start < j /\ i < j /\ length p > j + 1 /\
        (let c = split_cost p i start j (mc_cost p i start) (mc_cost p (start+1) j) in
         acc1 >= c /\ acc2 >= c))
      (ensures min_splits p i j start acc1 == min_splits p i j start acc2)

val min_splits_mono
  (p: seq int) (i j: nat) (start: nat{start >= i}) (acc1 acc2: int)
  : Lemma
      (requires acc1 >= acc2)
      (ensures min_splits p i j start acc1 >= min_splits p i j start acc2)

val min_splits_acc_irrelevant
  (p: seq int) (i j: nat) (start: nat{start >= i}) (acc1 acc2: int)
  : Lemma
      (requires min_splits p i j start acc1 <= acc2 /\ acc2 <= acc1)
      (ensures min_splits p i j start acc1 == min_splits p i j start acc2)

val mc_cost_pair (p: seq int) (i: nat)
  : Lemma (requires i + 2 < length p)
          (ensures mc_cost p i (i + 1) == index p i * index p (i + 1) * index p (i + 2))

let safe_index (#a:Type) (s:seq a) (i:nat{i < length s}) : a = index s i

/// Predicate: DP table correct for all subproblems with chain length < l
let dp_correct_upto (table: seq int) (dims: seq int) (n l: nat) : prop =
  length table == n * n /\
  length dims == n + 1 /\
  (forall (i j: nat). i < n /\ j < n /\ i <= j /\ j - i < l ==>
    index table (i * n + j) == mc_cost dims i j)

/// Predicate: all costs for subproblems of size < max_len bounded by bound
let all_costs_bounded (dims: seq int) (n: nat) (max_len: nat) (bound: int) : prop =
  forall (i j: nat). i < n /\ j < n /\ i <= j /\ j - i < max_len ==>
    mc_cost dims i j <= bound

val lemma_mc_inner_k_eq_min_splits
  (table: seq int) (dims: seq int) (n i j: nat) (k: nat{k >= i}) (acc: int)
  : Lemma
      (requires
        i < n /\ j < n /\ i < j /\
        length table == n * n /\ length dims == n + 1 /\
        k <= j /\
        (forall (i' j': nat). i' < n /\ j' < n /\ i' <= j' /\ j' - i' < j - i ==>
          index table (i' * n + j') == mc_cost dims i' j'))
      (ensures mc_inner_k table dims n i j k acc == min_splits dims i j k acc)

val lemma_mc_inner_k_computes_mc_cost
  (table: seq int) (dims: seq int) (n i j: nat)
  : Lemma
      (requires
        i < n /\ j < n /\ i < j /\
        length table == n * n /\ length dims == n + 1 /\
        (forall (i' j': nat). i' < n /\ j' < n /\ i' <= j' /\ j' - i' < j - i ==>
          index table (i' * n + j') == mc_cost dims i' j') /\
        mc_cost dims i j <= 1000000000)
      (ensures mc_inner_k table dims n i j i 1000000000 == mc_cost dims i j)

val lemma_2d_index_unique (i0 j0 i j n: nat)
  : Lemma (requires i0 < n /\ j0 < n /\ i < n /\ j < n /\ (i0 <> i \/ j0 <> j))
          (ensures i0 * n + j0 <> i * n + j)

val lemma_mc_inner_i_preserves_smaller_i
  (table: seq int) (dims: seq int) (n l start_i i0 j0: nat)
  : Lemma
      (requires l >= 2 /\ length table == n * n /\ length dims == n + 1 /\
               n > 0 /\ i0 < n /\ j0 < n /\ i0 < start_i)
      (ensures (let t' = mc_inner_i table dims n l start_i in
                length t' == n * n /\
                index t' (i0 * n + j0) == index table (i0 * n + j0)))

val lemma_mc_inner_i_preserves_shorter
  (table: seq int) (dims: seq int) (n l i: nat) (i0 j0: nat)
  : Lemma
      (requires l >= 2 /\ length table == n * n /\ length dims == n + 1 /\
               n > 0 /\ i0 < n /\ j0 < n /\ j0 - i0 + 1 <> l)
      (ensures (let t' = mc_inner_i table dims n l i in
                length t' == n * n /\
                index t' (i0 * n + j0) == index table (i0 * n + j0)))

val lemma_mc_inner_i_fills_correctly
  (table: seq int) (dims: seq int) (n l i0: nat) (start_i: nat)
  : Lemma
      (requires
        l >= 2 /\ l <= n /\ length table == n * n /\ length dims == n + 1 /\
        n > 0 /\ i0 < n /\ i0 + l <= n /\ start_i <= i0 /\
        dp_correct_upto table dims n (l - 1) /\
        all_costs_bounded dims n l 1000000000)
      (ensures
        (let t' = mc_inner_i table dims n l start_i in
         let j0 = i0 + l - 1 in
         j0 < n /\ length t' == n * n /\
         i0 * n + j0 < n * n /\
         index t' (i0 * n + j0) == mc_cost dims i0 j0))

val lemma_mc_inner_i_correct
  (table: seq int) (dims: seq int) (n l: nat)
  : Lemma
      (requires
        l >= 2 /\ l <= n /\
        length table == n * n /\ length dims == n + 1 /\
        n > 0 /\
        dp_correct_upto table dims n (l - 1) /\
        all_costs_bounded dims n l 1000000000)
      (ensures dp_correct_upto (mc_inner_i table dims n l 0) dims n l)

val lemma_mc_outer_correct
  (table: seq int) (dims: seq int) (n l: nat)
  : Lemma
      (requires
        l >= 2 /\ l <= n + 1 /\
        length table == n * n /\ length dims == n + 1 /\
        n > 0 /\
        dp_correct_upto table dims n (l - 1) /\
        all_costs_bounded dims n n 1000000000)
      (ensures dp_correct_upto (mc_outer table dims n l) dims n n)

val lemma_initial_table_correct (dims: seq int) (n: nat)
  : Lemma
      (requires n > 0 /\ length dims == n + 1)
      (ensures dp_correct_upto (Seq.create (n * n) 0) dims n 1)

/// Main theorem: the bottom-up DP result equals the recursive optimum
val mc_spec_equiv (dims: seq int) (n: nat)
  : Lemma (requires
            n > 0 /\ length dims == n + 1 /\
            all_costs_bounded dims n n 1000000000)
          (ensures mc_result dims n == mc_cost dims 0 (n - 1))

/// A parenthesization of the matrix chain A_i · ... · A_j
noeq
type paren : nat -> nat -> Type =
  | PLeaf : (i:nat) -> paren i i
  | PSplit : #i:nat -> #j:nat{j > i} -> (k:nat{k >= i /\ k < j})
             -> paren i k -> paren (k+1) j -> paren i j

/// Cost of a parenthesization under dimension array p
val paren_cost (p: seq int) (#i #j: nat) (t: paren i j) : Tot int

val min_splits_le_split_at_k
  (p: seq int) (i j: nat) (start: nat{start >= i}) (acc: int) (k: nat)
  : Lemma
    (requires start <= k /\ k < j /\ i < j /\ length p > j + 1)
    (ensures min_splits p i j start acc <=
             split_cost p i k j (mc_cost p i k) (mc_cost p (k+1) j))

val mc_cost_le_split_at_k (p: seq int) (i j k: nat)
  : Lemma
    (requires i <= k /\ k < j /\ length p > j + 1)
    (ensures mc_cost p i j <=
             split_cost p i k j (mc_cost p i k) (mc_cost p (k+1) j))

val split_cost_mono (p: seq int) (i k j: nat) (l1 r1 l2 r2: int)
  : Lemma (requires l1 <= l2 /\ r1 <= r2)
          (ensures split_cost p i k j l1 r1 <= split_cost p i k j l2 r2)

/// Upper bound: mc_cost <= cost of any parenthesization
val mc_cost_le_paren_cost (p: seq int) (#i #j: nat) (t: paren i j)
  : Lemma
    (requires length p > j + 1)
    (ensures mc_cost p i j <= paren_cost p t)

val find_optimal_k (p: seq int) (i j: nat) (start: nat{start >= i})
                    (acc: int) (best_k: nat{best_k >= i /\ best_k < j})
  : Tot (k:nat{k >= i /\ k < j})

val find_optimal_k_correct
  (p: seq int) (i j: nat) (start: nat{start >= i})
  (acc: int) (best_k: nat{best_k >= i /\ best_k < j})
  : Lemma
    (requires i < j /\ length p > j + 1 /\ start <= j /\
             acc == split_cost p i best_k j (mc_cost p i best_k) (mc_cost p (best_k + 1) j))
    (ensures (let k = find_optimal_k p i j start acc best_k in
              min_splits p i j start acc ==
              split_cost p i k j (mc_cost p i k) (mc_cost p (k + 1) j)))

val mc_cost_eq_optimal_split (p: seq int) (i j: nat)
  : Lemma
    (requires i < j /\ length p > j + 1)
    (ensures (let first = split_cost p i i j (mc_cost p i i) (mc_cost p (i + 1) j) in
              let k = find_optimal_k p i j (i + 1) first i in
              mc_cost p i j ==
              split_cost p i k j (mc_cost p i k) (mc_cost p (k + 1) j)))

val optimal_paren (p: seq int) (i: nat) (j: nat{i <= j /\ length p > j + 1})
  : Tot (t:paren i j{paren_cost p t == mc_cost p i j})

val mc_cost_achievable (p: seq int) (i j: nat)
  : Lemma
    (requires i <= j /\ length p > j + 1)
    (ensures exists (t: paren i j). paren_cost p t == mc_cost p i j)

val left_paren (i: nat) (j: nat{j >= i})
  : Tot (paren i j)

val left_paren_cost_bound (p: seq int) (i: nat) (j: nat{j >= i}) (d: nat)
  : Lemma
    (requires
      length p > j + 1 /\
      (forall (idx: nat). idx < length p ==> index p idx >= 0 /\ index p idx <= d))
    (ensures paren_cost p (left_paren i j) <= (j - i) * d * d * d)

val mc_cost_bounded (p: seq int) (i: nat) (j: nat{j >= i}) (d: nat)
  : Lemma
    (requires
      length p > j + 1 /\
      (forall (idx: nat). idx < length p ==> index p idx >= 0 /\ index p idx <= d))
    (ensures mc_cost p i j <= (j - i) * d * d * d)

val discharge_all_costs_bounded (dims: seq int) (n: nat) (d: nat)
  : Lemma
    (requires
      n > 0 /\
      length dims == n + 1 /\
      (forall (idx: nat). idx < length dims ==> index dims idx >= 0 /\ index dims idx <= d) /\
      (n - 1) * d * d * d <= 1000000000)
    (ensures all_costs_bounded dims n n 1000000000)
