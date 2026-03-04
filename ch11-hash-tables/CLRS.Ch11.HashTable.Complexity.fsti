module CLRS.Ch11.HashTable.Complexity

(**
   Complexity bound predicates for hash table operations.

   CLRS §11.4: Open addressing with linear probing.
   Worst-case: each operation (insert, search, delete) probes at most m slots,
   where m is the table size — O(m) per operation.

   These predicates are verified directly in the Impl postconditions
   via a ghost tick counter (GhostReference.ref nat) that increments
   once per probe.
*)

//SNIPPET_START: ht_complexity_bounds
(** Insert complexity: at most n probes *)
let hash_insert_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= n

(** Search complexity: at most n probes *)
let hash_search_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= n

(** Delete complexity: at most n probes *)
let hash_delete_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= n
//SNIPPET_END: ht_complexity_bounds
