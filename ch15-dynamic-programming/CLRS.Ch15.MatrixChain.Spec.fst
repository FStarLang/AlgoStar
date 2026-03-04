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
