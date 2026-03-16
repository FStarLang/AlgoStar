module CLRS.Ch11.HashTable.Complexity

(**
   Complexity bounds for hash table operations with open addressing
   and linear probing (CLRS §11.4).

   Provides:
   - Slot counting functions (empty, deleted, available)
   - Partition lemmas relating slot counts to table size
   - Lemmas about how insert/delete affect available slot counts
*)

open FStar.Mul

module Seq = FStar.Seq

(** Count empty slots (value == -1) in s[0..i) *)
let rec count_empty_aux (s: Seq.seq int) (i: nat{i <= Seq.length s}) : Tot nat (decreases i) =
  if i = 0 then 0
  else
    let v = Seq.index s (i - 1) in
    (if v = -1 then 1 else 0) + count_empty_aux s (i - 1)

let count_empty (s: Seq.seq int) : nat = count_empty_aux s (Seq.length s)

(** Count deleted slots (value == -2) in s[0..i) *)
let rec count_deleted_aux (s: Seq.seq int) (i: nat{i <= Seq.length s}) : Tot nat (decreases i) =
  if i = 0 then 0
  else
    let v = Seq.index s (i - 1) in
    (if v = -2 then 1 else 0) + count_deleted_aux s (i - 1)

let count_deleted (s: Seq.seq int) : nat = count_deleted_aux s (Seq.length s)

(** Count available (empty or deleted) slots *)
let rec count_available_aux (s: Seq.seq int) (i: nat{i <= Seq.length s}) : Tot nat (decreases i) =
  if i = 0 then 0
  else
    let v = Seq.index s (i - 1) in
    (if v = -1 || v = -2 then 1 else 0) + count_available_aux s (i - 1)

let count_available (s: Seq.seq int) : nat = count_available_aux s (Seq.length s)

// ========== Lemmas ==========

(** Helper: count_available_aux = count_empty_aux + count_deleted_aux *)
let rec lemma_available_sum_aux (s: Seq.seq int) (i: nat{i <= Seq.length s})
  : Lemma
    (ensures count_available_aux s i == count_empty_aux s i + count_deleted_aux s i)
    (decreases i)
  = if i = 0 then ()
    else lemma_available_sum_aux s (i - 1)

let lemma_available_sum (s: Seq.seq int)
  : Lemma (count_available s == count_empty s + count_deleted s)
  = lemma_available_sum_aux s (Seq.length s)

(** Helper: all counts are bounded by length *)
let rec lemma_slot_partition_aux (s: Seq.seq int) (i: nat{i <= Seq.length s})
  : Lemma
    (ensures count_empty_aux s i + count_deleted_aux s i <= i)
    (decreases i)
  = if i = 0 then ()
    else lemma_slot_partition_aux s (i - 1)

let lemma_slot_partition (s: Seq.seq int)
  : Lemma (count_empty s + count_deleted s <= Seq.length s)
  = lemma_slot_partition_aux s (Seq.length s)

(** Fresh table: all slots are -1 *)
let rec lemma_fresh_table_empty_aux (size: nat{size > 0}) (i: nat{i <= size})
  : Lemma
    (ensures count_empty_aux (Seq.create size (-1)) i == i /\
             count_deleted_aux (Seq.create size (-1)) i == 0)
    (decreases i)
  = if i = 0 then ()
    else lemma_fresh_table_empty_aux size (i - 1)

let lemma_fresh_table_empty (size: nat{size > 0})
  : Lemma (count_empty (Seq.create size (-1)) == size /\
           count_deleted (Seq.create size (-1)) == 0)
  = lemma_fresh_table_empty_aux size size

(** Helper: updating a slot only affects the count at that position *)
let rec lemma_count_available_upd_other
  (s: Seq.seq int) (idx: nat{idx < Seq.length s}) (v: int) (i: nat{i <= Seq.length s})
  : Lemma
    (requires idx >= i)
    (ensures count_available_aux (Seq.upd s idx v) i == count_available_aux s i)
    (decreases i)
  = if i = 0 then ()
    else lemma_count_available_upd_other s idx v (i - 1)

let rec lemma_count_available_upd
  (s: Seq.seq int) (idx: nat{idx < Seq.length s}) (v: int) (i: nat{i <= Seq.length s})
  : Lemma
    (ensures
      count_available_aux (Seq.upd s idx v) i ==
      (if idx < i then
        count_available_aux s i
        - (if Seq.index s idx = -1 || Seq.index s idx = -2 then 1 else 0)
        + (if v = -1 || v = -2 then 1 else 0)
       else count_available_aux s i))
    (decreases i)
  = if i = 0 then ()
    else if idx < i - 1 then lemma_count_available_upd s idx v (i - 1)
    else if idx = i - 1 then lemma_count_available_upd_other s idx v (i - 1)
    else lemma_count_available_upd s idx v (i - 1)

(** Insert: replacing an empty/deleted slot with a key >= 0 decreases available by 1 *)
let lemma_insert_decreases_available
  (s: Seq.seq int) (idx: nat{idx < Seq.length s}) (key: int{key >= 0})
  : Lemma
    (requires Seq.index s idx == -1 \/ Seq.index s idx == -2)
    (ensures count_available (Seq.upd s idx key) == count_available s - 1)
  = lemma_count_available_upd s idx key (Seq.length s)

(** Delete: replacing an occupied slot (>= 0) with -2 increases available by 1 *)
let lemma_delete_preserves_available
  (s: Seq.seq int) (idx: nat{idx < Seq.length s})
  : Lemma
    (requires Seq.index s idx >= 0)
    (ensures count_available (Seq.upd s idx (-2)) == count_available s + 1)
  = lemma_count_available_upd s idx (-2) (Seq.length s)

(** Trivial: single_op_bound is tight *)
let lemma_bound_is_tight (table_size: nat{table_size > 0})
  : Lemma (single_op_bound table_size == table_size)
  = ()
