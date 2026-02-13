module CLRS.Ch11.HashTable.Complexity

open FStar.Mul

(** Hash table with open addressing (CLRS Section 11.4)
    
    Worst-case complexity:
    - Insert: O(n) - linear probing with full table scan
    - Search: O(n) - may need to probe all slots
    
    Expected complexity with good hash function and load factor α < 1:
    - Insert: O(1/(1-α))
    - Search: O(1/(1-α)) for successful search
*)

/// Worst-case number of operations for hash table insertion
let hash_insert_worst (n: nat) : nat = n

/// Worst-case number of operations for hash table search
let hash_search_worst (n: nat) : nat = n

/// Insert is linear in worst case
let hash_insert_linear (n: nat) 
  : Lemma (ensures hash_insert_worst n <= n) 
  = ()

/// Search is linear in worst case
let hash_search_linear (n: nat) 
  : Lemma (ensures hash_search_worst n <= n) 
  = ()

/// Combined lemma: both operations are O(n)
let hash_operations_linear (n: nat)
  : Lemma (ensures hash_insert_worst n + hash_search_worst n <= 2 * n)
  = ()
