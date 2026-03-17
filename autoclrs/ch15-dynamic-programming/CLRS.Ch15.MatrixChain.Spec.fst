(*
   Matrix Chain Multiplication — Pure F* Specification (CLRS Chapter 15)
   
   Defines the imperative mirror spec for the DP algorithm:
   - mc_inner_k: process split points k..j-1 with accumulator
   - mc_inner_i: process starting positions for chain length l
   - mc_outer: process chain lengths l=2..n
   - mc_result: the final optimal cost

   These mirror the three nested loops of CLRS MATRIX-CHAIN-ORDER
   and are used to state postconditions for the Pulse implementation.

   NO admits. NO assumes.
*)

module CLRS.Ch15.MatrixChain.Spec

open FStar.Seq
open FStar.Mul

// ========== Pure Specification (imperative mirror) ==========

//SNIPPET_START: mc_spec
// mc_inner_k: process split points k..j-1, accumulating min cost
let rec mc_inner_k (table: seq int) (dims: seq int) (n i j k: nat) (min_acc: int)
  : Tot int (decreases (j - k))
  = if k >= j || i >= n || j >= n || length table <> n * n || length dims <> n + 1 then min_acc
    else
      let cost_ik = index table (i * n + k) in
      let cost_k1j = index table ((k + 1) * n + j) in
      let dim_i = index dims i in
      let dim_k1 = index dims (k + 1) in
      let dim_j1 = index dims (j + 1) in
      let q = cost_ik + cost_k1j + dim_i * dim_k1 * dim_j1 in
      let new_min = if q < min_acc then q else min_acc in
      mc_inner_k table dims n i j (k + 1) new_min

// mc_inner_i: process starting positions i..n-l, updating table for chain length l
let rec mc_inner_i (table: seq int) (dims: seq int) (n l i: nat)
  : Tot (seq int) (decreases (n - l + 1 - i))
  = if l < 2 || i + l > n || length table <> n * n || length dims <> n + 1 then table
    else
      let j = i + l - 1 in
      let min_cost = mc_inner_k table dims n i j i 1000000000 in
      let table' = upd table (i * n + j) min_cost in
      mc_inner_i table' dims n l (i + 1)

// mc_outer: process chain lengths l=l..n
let rec mc_outer (table: seq int) (dims: seq int) (n l: nat)
  : Tot (seq int) (decreases (n + 1 - l))
  = if l > n || length table <> n * n || length dims <> n + 1 then table
    else
      let table' = mc_inner_i table dims n l 0 in
      mc_outer table' dims n (l + 1)
//SNIPPET_END: mc_spec

// Length preservation lemmas
let rec lemma_mc_inner_i_len (table: seq int) (dims: seq int) (n l i: nat)
  : Lemma (ensures length (mc_inner_i table dims n l i) == length table)
          (decreases (n - l + 1 - i))
  = if l < 2 || i + l > n || length table <> n * n || length dims <> n + 1 then ()
    else begin
      let j = i + l - 1 in
      let min_cost = mc_inner_k table dims n i j i 1000000000 in
      lemma_mc_inner_i_len (upd table (i * n + j) min_cost) dims n l (i + 1)
    end

let rec lemma_mc_outer_len (table: seq int) (dims: seq int) (n l: nat)
  : Lemma (ensures length (mc_outer table dims n l) == length table)
          (decreases (n + 1 - l))
  = if l > n || length table <> n * n || length dims <> n + 1 then ()
    else begin
      lemma_mc_inner_i_len table dims n l 0;
      lemma_mc_outer_len (mc_inner_i table dims n l 0) dims n (l + 1)
    end

// The final result
let mc_result (dims: seq int) (n: nat) : int =
  if n = 0 || length dims <> n + 1 then 0
  else begin
    let table = create (n * n) 0 in
    let final_table = mc_outer table dims n 2 in
    lemma_mc_outer_len table dims n 2;
    assert (length final_table == n * n);
    index final_table (n - 1)
  end

// Bounds checking lemma for 2D indexing
let lemma_index_in_bounds (i j n: nat)
  : Lemma (requires i < n /\ j < n)
          (ensures i * n + j < n * n)
  = ()

let lemma_table_size_positive (n: nat{n > 0})
  : Lemma (n * n > 0)
  = ()

// ========== Non-negativity ==========

// Predicate: all table entries are non-negative
let table_nonneg (table: seq int) : prop =
  forall (idx: nat). idx < length table ==> index table idx >= 0

// Predicate: all dimension values are non-negative
let dims_nonneg (dims: seq int) : prop =
  forall (idx: nat). idx < length dims ==> index dims idx >= 0

// mc_inner_k result is non-negative when inputs are non-negative
let rec mc_inner_k_nonneg (table: seq int) (dims: seq int) (n i j k: nat) (min_acc: int)
  : Lemma
      (requires min_acc >= 0 /\ table_nonneg table /\ dims_nonneg dims)
      (ensures mc_inner_k table dims n i j k min_acc >= 0)
      (decreases (j - k))
  = if k >= j || i >= n || j >= n || length table <> n * n || length dims <> n + 1 then ()
    else begin
      let cost_ik = index table (i * n + k) in
      let cost_k1j = index table ((k + 1) * n + j) in
      let dim_i = index dims i in
      let dim_k1 = index dims (k + 1) in
      let dim_j1 = index dims (j + 1) in
      assert (i * n + k < n * n);
      assert ((k + 1) * n + j < n * n);
      assert (cost_ik >= 0);
      assert (cost_k1j >= 0);
      assert (dim_i >= 0);
      assert (dim_k1 >= 0);
      assert (dim_j1 >= 0);
      let q = cost_ik + cost_k1j + dim_i * dim_k1 * dim_j1 in
      let new_min = if q < min_acc then q else min_acc in
      mc_inner_k_nonneg table dims n i j (k + 1) new_min
    end

// upd preserves table non-negativity when the written value is non-negative
let lemma_upd_nonneg (table: seq int) (idx: nat) (v: int)
  : Lemma (requires table_nonneg table /\ idx < length table /\ v >= 0)
          (ensures table_nonneg (upd table idx v))
  = ()

// mc_inner_i preserves table non-negativity
let rec mc_inner_i_nonneg (table: seq int) (dims: seq int) (n l i: nat)
  : Lemma
      (requires table_nonneg table /\ dims_nonneg dims)
      (ensures table_nonneg (mc_inner_i table dims n l i))
      (decreases (n - l + 1 - i))
  = if l < 2 || i + l > n || length table <> n * n || length dims <> n + 1 then ()
    else begin
      let j = i + l - 1 in
      let min_cost = mc_inner_k table dims n i j i 1000000000 in
      mc_inner_k_nonneg table dims n i j i 1000000000;
      assert (min_cost >= 0);
      lemma_mc_inner_i_len table dims n l i;
      let table' = upd table (i * n + j) min_cost in
      lemma_upd_nonneg table (i * n + j) min_cost;
      mc_inner_i_nonneg table' dims n l (i + 1)
    end

// mc_outer preserves table non-negativity
let rec mc_outer_nonneg (table: seq int) (dims: seq int) (n l: nat)
  : Lemma
      (requires table_nonneg table /\ dims_nonneg dims)
      (ensures table_nonneg (mc_outer table dims n l))
      (decreases (n + 1 - l))
  = if l > n || length table <> n * n || length dims <> n + 1 then ()
    else begin
      mc_inner_i_nonneg table dims n l 0;
      lemma_mc_inner_i_len table dims n l 0;
      mc_outer_nonneg (mc_inner_i table dims n l 0) dims n (l + 1)
    end

// mc_result is non-negative when all dimensions are non-negative
let mc_result_nonneg (dims: seq int) (n: nat)
  : Lemma
      (requires n > 0 /\ length dims == n + 1 /\ dims_nonneg dims)
      (ensures mc_result dims n >= 0)
  = let table = create (n * n) 0 in
    assert (table_nonneg table);
    mc_outer_nonneg table dims n 2;
    lemma_mc_outer_len table dims n 2;
    let final_table = mc_outer table dims n 2 in
    assert (length final_table == n * n);
    assert (n - 1 < n * n);
    assert (table_nonneg final_table)
