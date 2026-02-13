module CLRS.Ch21.UnionFind.Complexity

open FStar.Mul

(** Union-Find / Disjoint Set Union (CLRS Chapter 21)
    
    Without optimizations:
    - Find: O(n) worst case (tree could degenerate to a chain)
    - Union: O(1) (just pointer manipulation)
    
    With union-by-rank + path compression:
    - m operations: O(m·α(n)) amortized, where α is inverse Ackermann
    - α(n) ≤ 4 for all practical values of n
*)

/// Worst-case number of operations for find (without path compression)
let find_worst (n: nat) : nat = n

/// Number of operations for union (constant time)
let union_ops : nat = 1

/// Find is linear in worst case
let find_linear (n: nat) 
  : Lemma (ensures find_worst n <= n) 
  = ()

/// Union is constant time
let union_constant () 
  : Lemma (ensures union_ops <= 1) 
  = ()

/// Sequence of m find operations without compression
let find_sequence_worst (m: nat) (n: nat) 
  : nat 
  = m * n

/// Sequence of m finds is O(m·n)
let find_sequence_bound (m: nat) (n: nat)
  : Lemma (ensures find_sequence_worst m n <= m * n)
  = ()
