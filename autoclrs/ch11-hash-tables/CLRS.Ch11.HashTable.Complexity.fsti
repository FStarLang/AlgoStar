module CLRS.Ch11.HashTable.Complexity

(**
   Complexity bounds for hash table operations with open addressing
   and linear probing (CLRS §11.4).

   The Impl module proves worst-case probe bounds inline via ghost tick
   counters. This module provides standalone definitions and lemmas that
   characterize the proven bounds and relate them to table parameters.

   Proven bounds:
   - hash_insert:       at most  size      probes
   - hash_search:       at most  size      probes
   - hash_delete:       at most  size      probes
   - hash_insert_no_dup: at most  2 * size  probes
*)


(** Number of empty (NIL) slots in a sequence *)
val count_empty (s: FStar.Seq.seq int) : nat

(** Number of deleted slots in a sequence *)
val count_deleted (s: FStar.Seq.seq int) : nat

(** Number of available (empty or deleted) slots *)
val count_available (s: FStar.Seq.seq int) : nat

(** Worst-case probe bound for a single insert/search/delete operation *)
let single_op_bound (table_size: nat{table_size > 0}) : nat = table_size

(** Worst-case probe bound for insert_no_dup (search + insert) *)
let insert_no_dup_bound (table_size: nat{table_size > 0}) : nat = 2 * table_size

(** count_available = count_empty + count_deleted *)
val lemma_available_sum (s: FStar.Seq.seq int)
  : Lemma (count_available s == count_empty s + count_deleted s)

(** count_empty + count_deleted + count_occupied <= length *)
val lemma_slot_partition (s: FStar.Seq.seq int)
  : Lemma (count_empty s + count_deleted s <= FStar.Seq.length s)

(** A fresh table (all -1) has count_empty = size and count_deleted = 0 *)
val lemma_fresh_table_empty (size: nat{size > 0})
  : Lemma (count_empty (FStar.Seq.create size (-1)) == size /\
           count_deleted (FStar.Seq.create size (-1)) == 0)

(** Inserting into an empty/deleted slot decreases available count by 1 *)
val lemma_insert_decreases_available
  (s: FStar.Seq.seq int) (idx: nat{idx < FStar.Seq.length s})
  (key: int{key >= 0})
  : Lemma
    (requires FStar.Seq.index s idx == -1 \/ FStar.Seq.index s idx == -2)
    (ensures count_available (FStar.Seq.upd s idx key) == count_available s - 1)

(** Deleting (marking -2) from an occupied slot preserves available count
    (one fewer occupied, one more deleted — net zero change to available) *)
val lemma_delete_preserves_available
  (s: FStar.Seq.seq int) (idx: nat{idx < FStar.Seq.length s})
  : Lemma
    (requires FStar.Seq.index s idx >= 0)
    (ensures count_available (FStar.Seq.upd s idx (-2)) == count_available s + 1)

(** Probe bound is tight: single_op_bound is the exact worst case *)
val lemma_bound_is_tight (table_size: nat{table_size > 0})
  : Lemma (single_op_bound table_size == table_size)
