module CLRS.Ch11.HashTable.Complexity

(**
   Complexity proofs for hash table operations.

   The O(m) worst-case bounds (where m = table size) are verified directly
   in the CLRS.Ch11.HashTable.Impl postconditions via ghost tick counters.
   Each postcondition includes: cf >= c0 /\ cf - c0 <= SZ.v size

   This module provides the named predicates (hash_insert_complexity_bounded,
   hash_search_complexity_bounded, hash_delete_complexity_bounded) as
   defined in the .fsti for documentation and client use.
*)
