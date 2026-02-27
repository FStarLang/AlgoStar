(*
   Matrix Chain Multiplication - Pure F* Specification (CLRS Chapter 15)
   
   Defines the recursive optimal substructure (CLRS Equation 15.7) and
   proves it equivalent to the imperative mirror spec in CLRS.Ch15.MatrixChain.
   
   CLRS recurrence (0-based): Given dimensions p[0..n], matrix A_i has dims p[i]×p[i+1].
     mc_cost(p, i, j) = 0                                                     if i = j
     mc_cost(p, i, j) = min_{i ≤ k < j} { mc_cost(p,i,k) + mc_cost(p,k+1,j)
                                           + p[i] * p[k+1] * p[j+1] }        if i < j
*)

module CLRS.Ch15.MatrixChain.Spec

open FStar.Seq
open FStar.Mul
open FStar.Classical

open CLRS.Ch15.MatrixChain

// ========== Recursive Specification (CLRS Eq. 15.7) ==========

//SNIPPET_START: mc_cost
/// Cost of a single split at k: multiply A_{i..k} (cost `left`) with
/// A_{k+1..j} (cost `right`), plus the multiplication p[i]×p[k+1]×p[j+1].
let split_cost (p: seq int) (i k j: nat)
  (left: int) (right: int) : int
  = left + right +
    (if i < length p && k + 1 < length p && j + 1 < length p
     then index p i * index p (k + 1) * index p (j + 1)
     else 0)

/// Minimum over split points k = start..j-1.
/// Mutually recursive with mc_cost: for each k, we call mc_cost on
/// strictly smaller subproblems [i,k] and [k+1,j].
let rec min_splits (p: seq int) (i j: nat) (start: nat{start >= i}) (acc: int)
  : Tot int (decreases %[(j - i); 0; (j - start)])
  = if start >= j || i >= j || length p <= j + 1 then acc
    else begin
      let left = mc_cost p i start in
      let right = mc_cost p (start + 1) j in
      let c = split_cost p i start j left right in
      let acc' = if c < acc then c else acc in
      min_splits p i j (start + 1) acc'
    end

/// Optimal scalar multiplication count for multiplying A_i · A_{i+1} · ... · A_j.
/// Base case: i = j (single matrix) → 0 multiplications.
/// Recursive case: try every split k ∈ [i, j); seed the accumulator with the
/// cost of splitting at k = i, then minimize over k = i+1 .. j-1.
and mc_cost (p: seq int) (i j: nat)
  : Tot int (decreases %[(j - i); 1; 0])
  = if i >= j || length p <= j + 1 then 0
    else
      let first = split_cost p i i j (mc_cost p i i) (mc_cost p (i + 1) j) in
      min_splits p i j (i + 1) first
//SNIPPET_END: mc_cost

// ========== Basic Properties ==========

let mc_cost_base (p: seq int) (i: nat)
  : Lemma (mc_cost p i i == 0) = ()

/// min_splits is at most the accumulator (it can only decrease)
let rec min_splits_le_acc (p: seq int) (i j: nat) (start: nat{start >= i}) (acc: int)
  : Lemma (ensures min_splits p i j start acc <= acc)
          (decreases %[(j - i); 0; (j - start)])
  = if start >= j || i >= j || length p <= j + 1 then ()
    else begin
      let left = mc_cost p i start in
      let right = mc_cost p (start + 1) j in
      let c = split_cost p i start j left right in
      let acc' = if c < acc then c else acc in
      min_splits_le_acc p i j (start + 1) acc'
    end

/// When both accumulators are >= the first candidate cost,
/// min_splits produces the same result regardless of the accumulator.
let min_splits_acc_ge
  (p: seq int) (i j: nat) (start: nat{start >= i}) (acc1 acc2: int)
  : Lemma
      (requires
        start < j /\ i < j /\ length p > j + 1 /\
        (let c = split_cost p i start j (mc_cost p i start) (mc_cost p (start+1) j) in
         acc1 >= c /\ acc2 >= c))
      (ensures min_splits p i j start acc1 == min_splits p i j start acc2)
  = let left = mc_cost p i start in
    let right = mc_cost p (start + 1) j in
    let c = split_cost p i start j left right in
    assert (acc1 >= c /\ acc2 >= c)
    // Both min(acc1,c) = c = min(acc2,c), so both proceed with same acc from start+1

/// Monotonicity: if acc1 >= acc2, then min_splits with acc1 >= min_splits with acc2
let rec min_splits_mono
  (p: seq int) (i j: nat) (start: nat{start >= i}) (acc1 acc2: int)
  : Lemma
      (requires acc1 >= acc2)
      (ensures min_splits p i j start acc1 >= min_splits p i j start acc2)
      (decreases %[(j - i); 0; (j - start)])
  = if start >= j || i >= j || length p <= j + 1 then ()
    else begin
      let left = mc_cost p i start in
      let right = mc_cost p (start + 1) j in
      let c = split_cost p i start j left right in
      let acc1' = if c < acc1 then c else acc1 in
      let acc2' = if c < acc2 then c else acc2 in
      assert (acc1' >= acc2');
      min_splits_mono p i j (start + 1) acc1' acc2'
    end

/// When the result is strictly less than the accumulator, the accumulator
/// value doesn't matter (as long as it's >= the result).
let rec min_splits_acc_irrelevant
  (p: seq int) (i j: nat) (start: nat{start >= i}) (acc1 acc2: int)
  : Lemma
      (requires
        min_splits p i j start acc1 <= acc2 /\ acc2 <= acc1)
      (ensures min_splits p i j start acc1 == min_splits p i j start acc2)
      (decreases %[(j - i); 0; (j - start)])
  = if start >= j || i >= j || length p <= j + 1 then ()
    else begin
      let left = mc_cost p i start in
      let right = mc_cost p (start + 1) j in
      let c = split_cost p i start j left right in
      let acc1' = if c < acc1 then c else acc1 in
      let acc2' = if c < acc2 then c else acc2 in
      // We need to show min_splits(start+1, acc1') == min_splits(start+1, acc2')
      // and that the precondition holds recursively
      
      if c < acc2 then begin
        // c < acc2 <= acc1, so acc1' = c and acc2' = c
        assert (acc1' == c);
        assert (acc2' == c);
        // Trivially equal since both are c
        ()
      end else if c < acc1 then begin
        // acc2 <= c < acc1, so acc1' = c and acc2' = acc2
        assert (acc1' == c);
        assert (acc2' == acc2);
        // We know: min_splits(start, acc1) = min_splits(start+1, c) <= acc2
        // And: acc2 <= c
        // Need: min_splits(start+1, c) <= acc2 /\ acc2 <= c
        assert (min_splits p i j start acc1 == min_splits p i j (start + 1) c);
        assert (min_splits p i j (start + 1) c <= acc2);
        assert (acc2 <= c);
        min_splits_acc_irrelevant p i j (start + 1) c acc2
      end else begin
        // c >= acc1, so acc1' = acc1 and acc2' = acc2
        assert (acc1' == acc1);
        assert (acc2' == acc2);
        // min_splits(start, acc1) = min_splits(start+1, acc1) by definition
        // Need: min_splits(start+1, acc1) <= acc2 /\ acc2 <= acc1 (already have acc2 <= acc1)
        assert (min_splits p i j start acc1 == min_splits p i j (start + 1) acc1);
        min_splits_acc_irrelevant p i j (start + 1) acc1 acc2
      end
    end

/// mc_cost for a 2-matrix chain
let mc_cost_pair (p: seq int) (i: nat)
  : Lemma (requires i + 2 < length p)
          (ensures mc_cost p i (i + 1) ==
                   index p i * index p (i + 1) * index p (i + 2))
  = ()

// ========== Equivalence: DP table ↔ mc_cost ==========

/// Safe array access with explicit bounds proof
let safe_index (#a:Type) (s:seq a) (i:nat{i < length s}) : a = index s i

/// Predicate: the DP table is correct for all subproblems with chain length < l.
/// For all i ≤ j < n with j − i < l, table[i·n + j] = mc_cost(dims, i, j).
//SNIPPET_START: dp_correct
let dp_correct_upto (table: seq int) (dims: seq int) (n l: nat) : prop =
  length table == n * n /\
  length dims == n + 1 /\
  (forall (i j: nat). i < n /\ j < n /\ i <= j /\ j - i < l ==>
    index table (i * n + j) == mc_cost dims i j)
//SNIPPET_END: dp_correct

/// Predicate: all costs for subproblems of size < max_len are bounded by bound
let all_costs_bounded (dims: seq int) (n: nat) (max_len: nat) (bound: int) : prop =
  forall (i j: nat). i < n /\ j < n /\ i <= j /\ j - i < max_len ==>
    mc_cost dims i j <= bound

/// When the table correctly reflects mc_cost for all strictly smaller subproblems,
/// mc_inner_k (which reads from the table) produces the same result as min_splits
/// (which calls mc_cost directly).
let rec lemma_mc_inner_k_eq_min_splits
  (table: seq int) (dims: seq int) (n i j: nat) (k: nat{k >= i}) (acc: int)
  : Lemma
      (requires
        i < n /\ j < n /\ i < j /\
        length table == n * n /\ length dims == n + 1 /\
        k <= j /\
        (forall (i' j': nat). i' < n /\ j' < n /\ i' <= j' /\ j' - i' < j - i ==>
          index table (i' * n + j') == mc_cost dims i' j'))
      (ensures mc_inner_k table dims n i j k acc == min_splits dims i j k acc)
      (decreases (j - k))
  = if k >= j then ()
    else begin
      // table[i*n+k] == mc_cost dims i k  (since k - i < j - i)
      assert (index table (i * n + k) == mc_cost dims i k);
      // table[(k+1)*n+j] == mc_cost dims (k+1) j  (since j-(k+1) < j-i)
      assert (index table ((k + 1) * n + j) == mc_cost dims (k + 1) j);
      let q = index table (i * n + k) + index table ((k + 1) * n + j) +
              index dims i * index dims (k + 1) * index dims (j + 1) in
      let new_min = if q < acc then q else acc in
      lemma_mc_inner_k_eq_min_splits table dims n i j (k + 1) new_min
    end

/// Bridge: mc_inner_k with sentinel 1000000000 computes mc_cost.
/// mc_inner_k iterates k=i..j-1 with acc=1000000000.
/// mc_cost seeds acc with first split cost, then iterates k=i+1..j-1.
/// They agree when mc_cost is <= 1000000000 (practical bound for finite problems).
let lemma_mc_inner_k_computes_mc_cost
  (table: seq int) (dims: seq int) (n i j: nat)
  : Lemma
      (requires
        i < n /\ j < n /\ i < j /\
        length table == n * n /\ length dims == n + 1 /\
        (forall (i' j': nat). i' < n /\ j' < n /\ i' <= j' /\ j' - i' < j - i ==>
          index table (i' * n + j') == mc_cost dims i' j') /\
        mc_cost dims i j <= 1000000000)  // Sentinel is large enough
      (ensures mc_inner_k table dims n i j i 1000000000 == mc_cost dims i j)
  = lemma_mc_inner_k_eq_min_splits table dims n i j i 1000000000;
    // Now: mc_inner_k == min_splits dims i j i 1000000000
    // And: mc_cost dims i j = min_splits dims i j (i+1) first
    //   where first = split_cost(dims, i, i, j, mc_cost(dims, i, i), mc_cost(dims, i+1, j))
    //              = split_cost(dims, i, i, j, 0, mc_cost(dims, i+1, j))
    
    // Unfold min_splits dims i j i 1000000000 one step:
    let left = mc_cost dims i i in
    let right = mc_cost dims (i + 1) j in
    let first = split_cost dims i i j left right in
    assert (left == 0);  // by mc_cost_base
    let acc' = if first < 1000000000 then first else 1000000000 in
    assert (min_splits dims i j i 1000000000 == min_splits dims i j (i + 1) acc');
    
    // By definition of mc_cost:
    assert (mc_cost dims i j == min_splits dims i j (i + 1) first);
    
    // We know: mc_cost dims i j <= 1000000000 (from precondition)
    // And: mc_cost dims i j = min_splits dims i j (i+1) first (by definition)
    // So: min_splits dims i j (i+1) first <= 1000000000
    
    min_splits_le_acc dims i j (i + 1) first;
    // This gives: min_splits(i+1, first) <= first
    
    if first <= 1000000000 then begin
      // acc' = first, so min_splits(i+1, acc') = min_splits(i+1, first) = mc_cost dims i j
      assert (acc' == first);
      ()
    end else begin
      // first > 1000000000 and acc' = 1000000000
      // We need: min_splits(i+1, first) == min_splits(i+1, 1000000000)
      // We know: min_splits(i+1, first) = mc_cost dims i j <= 1000000000 < first
      // So: min_splits(i+1, first) <= 1000000000 <= first
      // Use min_splits_acc_irrelevant
      assert (min_splits dims i j (i + 1) first <= 1000000000);
      assert (1000000000 <= first);
      min_splits_acc_irrelevant dims i j (i + 1) first 1000000000
    end

// ========== 2D-index uniqueness ==========

let lemma_2d_index_unique (i0 j0 i j n: nat)
  : Lemma (requires i0 < n /\ j0 < n /\ i < n /\ j < n /\ (i0 <> i \/ j0 <> j))
          (ensures i0 * n + j0 <> i * n + j)
  = if i0 = i then ()  // j0 <> j, so i0*n+j0 <> i*n+j trivially
    else begin
      // i0 <> i. i0*n+j0 in [i0*n, i0*n+n-1], i*n+j in [i*n, i*n+n-1].
      // These ranges are disjoint when i0 <> i.
      assert (i0 * n + j0 < (i0 + 1) * n);
      assert (i * n + j < (i + 1) * n);
      if i0 < i then assert (i0 * n + j0 < i * n)
      else assert (i * n + j < i0 * n)
    end

// ========== Table stability under mc_inner_i ==========

/// mc_inner_i starting at start_i only writes to positions (i', j') where i' >= start_i.
/// So positions (i0, j0) where i0 < start_i are preserved.
let rec lemma_mc_inner_i_preserves_smaller_i
  (table: seq int) (dims: seq int) (n l start_i i0 j0: nat)
  : Lemma
      (requires
        l >= 2 /\ length table == n * n /\ length dims == n + 1 /\
        n > 0 /\ i0 < n /\ j0 < n /\ i0 < start_i)
      (ensures (let t' = mc_inner_i table dims n l start_i in
                length t' == n * n /\
                index t' (i0 * n + j0) == index table (i0 * n + j0)))
      (decreases (n - l + 1 - start_i))
  = lemma_mc_inner_i_len table dims n l start_i;
    if start_i + l > n then ()
    else begin
      let j = start_i + l - 1 in
      let min_cost = mc_inner_k table dims n start_i j start_i 1000000000 in
      let table' = Seq.upd table (start_i * n + j) min_cost in
      // start_i <> i0 (because i0 < start_i), so the write doesn't affect (i0, j0)
      lemma_2d_index_unique i0 j0 start_i j n;
      assert (index table' (i0 * n + j0) == index table (i0 * n + j0));
      // Recursive call still has i0 < start_i + 1
      if i0 < start_i + 1 then
        lemma_mc_inner_i_preserves_smaller_i table' dims n l (start_i + 1) i0 j0
      else ()
    end

/// mc_inner_i for chain length l only writes to positions (i', i'+l-1)
/// where i' >= start_i. Entries with j0 - i0 + 1 ≠ l are untouched.
let rec lemma_mc_inner_i_preserves_shorter
  (table: seq int) (dims: seq int) (n l i: nat) (i0 j0: nat)
  : Lemma
      (requires
        l >= 2 /\ length table == n * n /\ length dims == n + 1 /\
        n > 0 /\ i0 < n /\ j0 < n /\ j0 - i0 + 1 <> l)
      (ensures (let t' = mc_inner_i table dims n l i in
                length t' == n * n /\
                index t' (i0 * n + j0) == index table (i0 * n + j0)))
      (decreases (n - l + 1 - i))
  = lemma_mc_inner_i_len table dims n l i;
    if i + l > n then ()
    else begin
      let j = i + l - 1 in
      let min_cost = mc_inner_k table dims n i j i 1000000000 in
      let table' = Seq.upd table (i * n + j) min_cost in
      // j - i = l - 1, so j - i + 1 = l, but j0 - i0 + 1 <> l,
      // therefore (i0, j0) <> (i, j)
      assert (i0 <> i \/ j0 <> j);
      lemma_2d_index_unique i0 j0 i j n;
      assert (index table' (i0 * n + j0) == index table (i0 * n + j0));
      lemma_mc_inner_i_preserves_shorter table' dims n l (i + 1) i0 j0
    end

// ========== Helper: mc_inner_i fills correctly ==========

/// Helper: at position i (where i+l-1 < n), mc_inner_i writes the correct value
/// to table[i][i+l-1] and preserves it in subsequent steps.
#push-options "--split_queries always"
let rec lemma_mc_inner_i_fills_correctly
  (table: seq int) (dims: seq int) (n l i0: nat) (start_i: nat)
  : Lemma
      (requires
        l >= 2 /\ l <= n /\ length table == n * n /\ length dims == n + 1 /\
        n > 0 /\ i0 < n /\ i0 + l <= n /\ start_i <= i0 /\
        dp_correct_upto table dims n (l - 1) /\
        all_costs_bounded dims n l 1000000000)  // Bound ensures sentinel works
      (ensures
        (let t' = mc_inner_i table dims n l start_i in
         let j0 = i0 + l - 1 in
         j0 < n /\ length t' == n * n /\
         i0 * n + j0 < n * n /\  // Explicit bound
         index t' (i0 * n + j0) == mc_cost dims i0 j0))
      (decreases (i0 - start_i))
  = lemma_mc_inner_i_len table dims n l start_i;
    let j0 = i0 + l - 1 in
    lemma_index_in_bounds i0 j0 n;
    if start_i + l > n then begin
      // mc_inner_i returns table unchanged, but this contradicts start_i <= i0 < n with i0+l <= n
      assert (i0 + l <= n);
      assert (start_i <= i0);
      assert (start_i + l <= i0 + l);
      assert (start_i + l <= n);
      assert (False)  // contradiction
    end else if start_i = i0 then begin
      // This is the step that writes to (i0, j0)
      let j = start_i + l - 1 in
      assert (j == j0);
      let min_cost = mc_inner_k table dims n start_i j start_i 1000000000 in
      let table' = Seq.upd table (start_i * n + j) min_cost in
      
      // Show that mc_inner_k computes mc_cost correctly
      // Need to verify preconditions of lemma_mc_inner_k_computes_mc_cost
      assert (start_i < n /\ j < n /\ start_i < j);
      assert (length table == n * n /\ length dims == n + 1);
      
      
      // For all subproblems (i', j') with j' - i' < j - start_i = l - 1,
      // table[i'][j'] == mc_cost dims i' j'
      introduce forall (i':nat) (j':nat).
        (i' < n /\ j' < n /\ i' <= j' /\ j' - i' < j - start_i) ==>
          index table (i' * n + j') == mc_cost dims i' j'
      with introduce _ ==> _ with _.
        (lemma_index_in_bounds i' j' n);
      
      // Use the cost bound to establish the sentinel precondition
      assert (start_i < n /\ start_i + l <= n);
      assert (j == start_i + l - 1);
      assert (j - start_i == l - 1);
      assert (j - start_i < l);  // l - 1 < l
      // By all_costs_bounded: forall i j. j - i < l ==> mc_cost dims i j <= 1000000000
      assert (mc_cost dims start_i j <= 1000000000);
      
      lemma_mc_inner_k_computes_mc_cost table dims n start_i j;
      assert (min_cost == mc_cost dims start_i j);
      lemma_index_in_bounds start_i j n;
      assert (index table' (start_i * n + j) == mc_cost dims i0 j0);
      
      // Now table' has the correct value at (i0, j0)
      // The recursive call mc_inner_i table' dims n l (start_i + 1) will preserve it
      // because i0 = start_i < start_i + 1, so by lemma_mc_inner_i_preserves_smaller_i:
      let t' = mc_inner_i table' dims n l (start_i + 1) in
      if start_i + 1 + l > n then begin
        assert (t' == table')
      end else begin
        assert (i0 < start_i + 1);
        lemma_mc_inner_i_preserves_smaller_i table' dims n l (start_i + 1) i0 j0;
        assert (index t' (i0 * n + j0) == index table' (i0 * n + j0));
        ()
      end
    end else begin
      // start_i < i0. First iteration processes (start_i, start_i + l - 1)
      let j = start_i + l - 1 in
      let min_cost = mc_inner_k table dims n start_i j start_i 1000000000 in
      let table' = Seq.upd table (start_i * n + j) min_cost in
      
      // (i0, j0) <> (start_i, j) because start_i < i0
      assert (start_i <> i0);
      lemma_2d_index_unique start_i j i0 j0 n;
      assert (index table' (i0 * n + j0) == index table (i0 * n + j0));
      
      // Recurse: subsequent iterations starting from start_i + 1
      // table' still satisfies dp_correct_upto ... (l-1) because we only wrote at chain length l-1
      introduce forall (i':nat) (j':nat).
        (i' < n /\ j' < n /\ i' <= j' /\ j' - i' < l - 1) ==>
          index table' (i' * n + j') == mc_cost dims i' j'
      with introduce _ ==> _ with _. begin
        lemma_index_in_bounds i' j' n;
        if i' = start_i && j' = j then
          ()  // j - start_i = l - 1, contradiction with j' - i' < l - 1
        else
          lemma_2d_index_unique i' j' start_i j n
          // So table'[i'][j'] == table[i'][j'] == mc_cost... (by dp_correct_upto)
      end;
      assert (dp_correct_upto table' dims n (l - 1));
      assert (all_costs_bounded dims n l 1000000000);  // Still holds
      assert (start_i < i0);  // Termination: i0 - (start_i + 1) < i0 - start_i
      lemma_mc_inner_i_fills_correctly table' dims n l i0 (start_i + 1)
    end
#pop-options

/// After mc_inner_i table dims n l 0:
///   - entries for chain lengths < l-1 are preserved (by preserves_shorter)
///   - entries for chain length l-1 are filled correctly
/// dp_correct_upto advances from (l-1) to l.
#push-options "--z3rlimit 60"
let lemma_mc_inner_i_correct
  (table: seq int) (dims: seq int) (n l: nat)
  : Lemma
      (requires
        l >= 2 /\ l <= n /\
        length table == n * n /\ length dims == n + 1 /\
        n > 0 /\
        dp_correct_upto table dims n (l - 1) /\
        all_costs_bounded dims n l 1000000000)
      (ensures
        dp_correct_upto (mc_inner_i table dims n l 0) dims n l)
  = let t' = mc_inner_i table dims n l 0 in
    lemma_mc_inner_i_len table dims n l 0;
    assert (length t' == n * n);
    let aux (i0 j0: nat)
      : Lemma (requires i0 < n /\ j0 < n /\ i0 <= j0 /\ j0 - i0 < l)
              (ensures (lemma_index_in_bounds i0 j0 n;
                       index t' (i0 * n + j0) == mc_cost dims i0 j0))
      = lemma_index_in_bounds i0 j0 n;
        if j0 - i0 + 1 = l then begin
          assert (j0 == i0 + l - 1);
          assert (i0 + l <= n);
          lemma_mc_inner_i_fills_correctly table dims n l i0 0
        end else begin
          lemma_mc_inner_i_preserves_shorter table dims n l 0 i0 j0
        end
    in
    introduce forall (i0: nat) (j0: nat).
      (i0 < n /\ j0 < n /\ i0 <= j0 /\ j0 - i0 < l) ==>
        index t' (i0 * n + j0) == mc_cost dims i0 j0
    with introduce _ ==> _
    with _. aux i0 j0
#pop-options

// ========== mc_outer correctness ==========

let rec lemma_mc_outer_correct
  (table: seq int) (dims: seq int) (n l: nat)
  : Lemma
      (requires
        l >= 2 /\ l <= n + 1 /\
        length table == n * n /\ length dims == n + 1 /\
        n > 0 /\
        dp_correct_upto table dims n (l - 1) /\
        all_costs_bounded dims n n 1000000000)  // Bound holds for all sizes
      (ensures
        dp_correct_upto (mc_outer table dims n l) dims n n)
      (decreases (n + 1 - l))
  = if l > n then ()
    else begin
      assert (all_costs_bounded dims n l 1000000000);  // l <= n
      lemma_mc_inner_i_correct table dims n l;
      let table' = mc_inner_i table dims n l 0 in
      lemma_mc_inner_i_len table dims n l 0;
      lemma_mc_outer_correct table' dims n (l + 1)
    end

// ========== Main Theorem ==========

/// The initial all-zeros table is correct for chain length 1:
/// table[i*n+i] = 0 = mc_cost(dims, i, i) for all i.
let lemma_initial_table_correct (dims: seq int) (n: nat)
  : Lemma
      (requires n > 0 /\ length dims == n + 1)
      (ensures dp_correct_upto (Seq.create (n * n) 0) dims n 1)
  = ()

//SNIPPET_START: mc_spec_equiv
/// **Main theorem**: the bottom-up DP result equals the recursive optimum.
///   mc_result dims n == mc_cost dims 0 (n − 1)
let mc_spec_equiv (dims: seq int) (n: nat)
  : Lemma (requires
            n > 0 /\ length dims == n + 1 /\
            all_costs_bounded dims n n 1000000000)  // Costs fit in sentinel
          (ensures mc_result dims n == mc_cost dims 0 (n - 1))
  = let table = Seq.create (n * n) 0 in
    lemma_initial_table_correct dims n;
    if n = 1 then ()
    else begin
      // dp_correct_upto table dims n 1  (from initial_table_correct)
      // mc_outer processes chain lengths 2..n
      // requires dp_correct_upto ... (l-1) = dp_correct_upto ... 1
      assert (all_costs_bounded dims n n 1000000000);  // From precondition
      lemma_mc_outer_correct table dims n 2;
      let final_table = mc_outer table dims n 2 in
      lemma_mc_outer_len table dims n 2;
      assert (dp_correct_upto final_table dims n n);
      // n - 1 - 0 = n - 1 < n, so entry (0, n-1) is correct
      assert (index final_table (0 * n + (n - 1)) == mc_cost dims 0 (n - 1))
    end
//SNIPPET_END: mc_spec_equiv

// ========== Parenthesization Type and Optimality ==========

/// A parenthesization of the matrix chain A_i · ... · A_j.
/// PLeaf i: single matrix (no cost).
/// PSplit k left right: split at k, multiplying (A_i..A_k) × (A_{k+1}..A_j).
noeq
type paren : nat -> nat -> Type =
  | PLeaf : (i:nat) -> paren i i
  | PSplit : #i:nat -> #j:nat{j > i} -> (k:nat{k >= i /\ k < j})
             -> paren i k -> paren (k+1) j -> paren i j

/// Cost of a parenthesization under dimension array p.
let rec paren_cost (p: seq int) (#i #j: nat) (t: paren i j)
  : Tot int (decreases t)
  = match t with
    | PLeaf _ -> 0
    | PSplit k left right ->
      split_cost p i k j (paren_cost p left) (paren_cost p right)

// ---------- Upper Bound: mc_cost <= paren_cost ----------

/// For any split point k in [start, j), min_splits <= split_cost at k.
/// When min_splits reaches k, the accumulator is <= split_cost at k
/// (because it takes the min), and subsequent iterations only decrease.
let rec min_splits_le_split_at_k
  (p: seq int) (i j: nat) (start: nat{start >= i}) (acc: int) (k: nat)
  : Lemma
    (requires start <= k /\ k < j /\ i < j /\ length p > j + 1)
    (ensures min_splits p i j start acc <=
             split_cost p i k j (mc_cost p i k) (mc_cost p (k+1) j))
    (decreases (k - start))
  = let c = split_cost p i start j (mc_cost p i start) (mc_cost p (start + 1) j) in
    let acc' = if c < acc then c else acc in
    if start = k then
      min_splits_le_acc p i j (start + 1) acc'
    else
      min_splits_le_split_at_k p i j (start + 1) acc' k

/// mc_cost(i,j) <= split_cost at any valid split point k in [i, j).
let mc_cost_le_split_at_k (p: seq int) (i j k: nat)
  : Lemma
    (requires i <= k /\ k < j /\ length p > j + 1)
    (ensures mc_cost p i j <=
             split_cost p i k j (mc_cost p i k) (mc_cost p (k+1) j))
  = let first = split_cost p i i j (mc_cost p i i) (mc_cost p (i + 1) j) in
    if k = i then
      min_splits_le_acc p i j (i + 1) first
    else
      min_splits_le_split_at_k p i j (i + 1) first k

/// split_cost is monotone in its left/right cost arguments.
let split_cost_mono (p: seq int) (i k j: nat) (l1 r1 l2 r2: int)
  : Lemma (requires l1 <= l2 /\ r1 <= r2)
          (ensures split_cost p i k j l1 r1 <= split_cost p i k j l2 r2)
  = ()

/// **Upper bound**: mc_cost <= cost of any parenthesization.
let rec mc_cost_le_paren_cost (p: seq int) (#i #j: nat) (t: paren i j)
  : Lemma
    (requires length p > j + 1)
    (ensures mc_cost p i j <= paren_cost p t)
    (decreases t)
  = match t with
    | PLeaf _ -> ()
    | PSplit k left right ->
      mc_cost_le_paren_cost p left;
      mc_cost_le_paren_cost p right;
      mc_cost_le_split_at_k p i j k;
      split_cost_mono p i k j
        (mc_cost p i k) (mc_cost p (k+1) j)
        (paren_cost p left) (paren_cost p right)

// ---------- Achievability: optimal parenthesization exists ----------

/// Mirrors min_splits but returns the split point achieving the minimum.
let rec find_optimal_k (p: seq int) (i j: nat) (start: nat{start >= i})
                        (acc: int) (best_k: nat{best_k >= i /\ best_k < j})
  : Tot (k:nat{k >= i /\ k < j}) (decreases (j - start))
  = if start >= j || i >= j || length p <= j + 1 then best_k
    else
      let c = split_cost p i start j (mc_cost p i start) (mc_cost p (start + 1) j) in
      if c < acc then find_optimal_k p i j (start + 1) c start
      else find_optimal_k p i j (start + 1) acc best_k

/// Correctness: min_splits == split_cost at the k returned by find_optimal_k.
/// Invariant: acc == split_cost at best_k (maintained through iteration).
let rec find_optimal_k_correct
  (p: seq int) (i j: nat) (start: nat{start >= i})
  (acc: int) (best_k: nat{best_k >= i /\ best_k < j})
  : Lemma
    (requires i < j /\ length p > j + 1 /\ start <= j /\
             acc == split_cost p i best_k j (mc_cost p i best_k) (mc_cost p (best_k + 1) j))
    (ensures (let k = find_optimal_k p i j start acc best_k in
              min_splits p i j start acc ==
              split_cost p i k j (mc_cost p i k) (mc_cost p (k + 1) j)))
    (decreases (j - start))
  = if start >= j then ()
    else
      let c = split_cost p i start j (mc_cost p i start) (mc_cost p (start + 1) j) in
      if c < acc then
        find_optimal_k_correct p i j (start + 1) c start
      else
        find_optimal_k_correct p i j (start + 1) acc best_k

/// mc_cost(i,j) equals split_cost at the optimal split point.
let mc_cost_eq_optimal_split (p: seq int) (i j: nat)
  : Lemma
    (requires i < j /\ length p > j + 1)
    (ensures (let first = split_cost p i i j (mc_cost p i i) (mc_cost p (i + 1) j) in
              let k = find_optimal_k p i j (i + 1) first i in
              mc_cost p i j ==
              split_cost p i k j (mc_cost p i k) (mc_cost p (k + 1) j)))
  = let first = split_cost p i i j (mc_cost p i i) (mc_cost p (i + 1) j) in
    find_optimal_k_correct p i j (i + 1) first i;
    assert (mc_cost p i j == min_splits p i j (i + 1) first)

/// Construct a parenthesization achieving mc_cost.
#push-options "--z3rlimit 20"
let rec optimal_paren (p: seq int) (i: nat) (j: nat{i <= j /\ length p > j + 1})
  : Tot (t:paren i j{paren_cost p t == mc_cost p i j}) (decreases (j - i))
  = if i = j then PLeaf i
    else
      let first = split_cost p i i j (mc_cost p i i) (mc_cost p (i + 1) j) in
      let k = find_optimal_k p i j (i + 1) first i in
      mc_cost_eq_optimal_split p i j;
      assert (mc_cost p i j == split_cost p i k j (mc_cost p i k) (mc_cost p (k + 1) j));
      let left = optimal_paren p i k in
      let right = optimal_paren p (k + 1) j in
      assert (paren_cost p left == mc_cost p i k);
      assert (paren_cost p right == mc_cost p (k + 1) j);
      PSplit k left right
#pop-options

/// **Achievability**: there exists a parenthesization with cost equal to mc_cost.
let mc_cost_achievable (p: seq int) (i j: nat)
  : Lemma
    (requires i <= j /\ length p > j + 1)
    (ensures exists (t: paren i j). paren_cost p t == mc_cost p i j)
  = let t = optimal_paren p i j in
    assert (paren_cost p t == mc_cost p i j)

// ========== Bounding mc_cost when dimensions are bounded ==========

/// A left-leaning parenthesization: always split at the leftmost position.
/// This gives a concrete parenthesization whose cost is easy to bound.
let rec left_paren (i: nat) (j: nat{j >= i})
  : Tot (paren i j) (decreases (j - i))
  = if i = j then PLeaf i
    else PSplit #i #j i (PLeaf i) (left_paren (i + 1) j)

/// Helper: product of three non-negative ints each bounded by d is at most d^3.
private let product_bound_3 (a b c d: nat)
  : Lemma (requires a <= d /\ b <= d /\ c <= d)
          (ensures a * b * c <= d * d * d)
  = // a*b <= d*b  (since a <= d, b >= 0)
    FStar.Math.Lemmas.lemma_mult_le_right b a d;
    // d*b <= d*d  (since b <= d, d >= 0)
    FStar.Math.Lemmas.lemma_mult_le_left d b d;
    // So a*b <= d*d by transitivity
    // (a*b)*c <= (d*d)*c  (since a*b <= d*d, c >= 0)
    FStar.Math.Lemmas.lemma_mult_le_right c (a * b) (d * d);
    // (d*d)*c <= (d*d)*d  (since c <= d, d*d >= 0)
    FStar.Math.Lemmas.lemma_mult_le_left (d * d) c d

/// Helper: (n-1)*d*d*d + d*d*d == n*d*d*d, used in the inductive step.
private let arith_distribute (n: nat) (d: nat)
  : Lemma (requires n >= 1)
          (ensures (n - 1) * d * d * d + d * d * d == n * d * d * d)
  = FStar.Math.Lemmas.distributivity_add_left (n - 1) 1 d;
    FStar.Math.Lemmas.distributivity_add_left ((n - 1) * d) d d;
    FStar.Math.Lemmas.distributivity_add_left ((n - 1) * d * d) (d * d) d

/// Helper: monotonicity of x * d * d * d in x.
private let cube_mono (x y: int) (d: nat)
  : Lemma (requires x >= 0 /\ x <= y)
          (ensures x * d * d * d <= y * d * d * d)
  = FStar.Math.Lemmas.lemma_mult_le_right d x y;
    FStar.Math.Lemmas.lemma_mult_le_right d (x * d) (y * d);
    FStar.Math.Lemmas.lemma_mult_le_right d (x * d * d) (y * d * d)

/// The cost of the left-leaning parenthesization is bounded by (j - i) * D^3
/// when all dimension entries in p are non-negative and bounded by D.
#push-options "--z3rlimit 20"
let rec left_paren_cost_bound (p: seq int) (i: nat) (j: nat{j >= i}) (d: nat)
  : Lemma
    (requires
      length p > j + 1 /\
      (forall (idx: nat). idx < length p ==> index p idx >= 0 /\ index p idx <= d))
    (ensures paren_cost p (left_paren i j) <= (j - i) * d * d * d)
    (decreases (j - i))
  = if i = j then ()
    else begin
      left_paren_cost_bound p (i + 1) j d;
      // IH: paren_cost p (left_paren (i+1) j) <= (j - i - 1) * d * d * d
      // The multiplication term p[i]*p[i+1]*p[j+1] <= d*d*d:
      product_bound_3 (index p i) (index p (i + 1)) (index p (j + 1)) d;
      // Arithmetic: (j-i-1)*d*d*d + d*d*d == (j-i)*d*d*d
      arith_distribute (j - i) d
    end
#pop-options

/// **mc_cost is bounded**: mc_cost p i j <= (j - i) * D^3 when all dims
/// are non-negative and bounded by D.
let mc_cost_bounded (p: seq int) (i: nat) (j: nat{j >= i}) (d: nat)
  : Lemma
    (requires
      length p > j + 1 /\
      (forall (idx: nat). idx < length p ==> index p idx >= 0 /\ index p idx <= d))
    (ensures mc_cost p i j <= (j - i) * d * d * d)
  = left_paren_cost_bound p i j d;
    mc_cost_le_paren_cost p (left_paren i j)

/// **Discharge all_costs_bounded**: if all dimension entries are non-negative
/// and bounded by D, and (n-1)*D^3 fits within the sentinel (1000000000),
/// then all mc_cost values for subproblems of size < n are bounded by the sentinel.
/// This makes it trivial to satisfy the `all_costs_bounded` precondition of `mc_spec_equiv`.
let discharge_all_costs_bounded (dims: seq int) (n: nat) (d: nat)
  : Lemma
    (requires
      n > 0 /\
      length dims == n + 1 /\
      (forall (idx: nat). idx < length dims ==> index dims idx >= 0 /\ index dims idx <= d) /\
      (n - 1) * d * d * d <= 1000000000)
    (ensures all_costs_bounded dims n n 1000000000)
  = introduce forall (i j: nat).
      (i < n /\ j < n /\ i <= j /\ j - i < n) ==> mc_cost dims i j <= 1000000000
    with introduce _ ==> _ with _.
      (mc_cost_bounded dims i j d;
       // mc_cost dims i j <= (j - i) * d * d * d
       // (j - i) <= (n - 1) since i < n, j < n, i <= j
       cube_mono (j - i) (n - 1) d)
