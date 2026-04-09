(**
  Bridge lemmas connecting array-level C specifications (SinglyLinkedList.c)
  to the pure functional specifications in CLRS.Ch10.SinglyLinkedList.Spec.

  The C implementation represents a singly linked list as a contiguous
  array a[0..n), while the F* spec uses list int.  This module defines
  the abstraction function and proves that the C operations' ensures
  clauses imply the corresponding list-level properties.
*)
module CLRS.Ch10.SinglyLinkedList.C.BridgeLemmas

open FStar.Seq
module L = FStar.List.Tot
open CLRS.Ch10.SinglyLinkedList.Spec

(** Abstraction: convert array segment a[from..n) to a list *)
let rec seq_to_list_from (s: seq int) (from: nat) (n: nat{from <= n /\ n <= length s})
  : Tot (list int) (decreases (n - from))
  = if from >= n then []
    else index s from :: seq_to_list_from s (from + 1) n

(** Convenience: convert a[0..n) to list *)
let seq_to_list (s: seq int) (n: nat{n <= length s}) : list int =
  seq_to_list_from s 0 n

(** Length of seq_to_list_from *)
let rec lemma_seq_to_list_from_length (s: seq int) (from: nat) (n: nat{from <= n /\ n <= length s})
  : Lemma (ensures L.length (seq_to_list_from s from n) == n - from)
          (decreases (n - from))
  = if from >= n then ()
    else lemma_seq_to_list_from_length s (from + 1) n

(** Length of seq_to_list *)
let lemma_seq_to_list_length (s: seq int) (n: nat{n <= length s})
  : Lemma (ensures L.length (seq_to_list s n) == n)
  = lemma_seq_to_list_from_length s 0 n

(** seq_to_list_from only depends on elements in [from, n) *)
let rec lemma_seq_to_list_from_pointwise
  (s1 s2: seq int) (from: nat) (n: nat{from <= n /\ n <= length s1 /\ n <= length s2})
  : Lemma
    (requires forall (j: nat). from <= j /\ j < n ==> index s1 j == index s2 j)
    (ensures seq_to_list_from s1 from n == seq_to_list_from s2 from n)
    (decreases (n - from))
  = if from >= n then ()
    else lemma_seq_to_list_from_pointwise s1 s2 (from + 1) n

(** ========== Bridge for LIST-INSERT ========== *)

(**
  After list_insert, the C code ensures:
    a[0] == x
    forall j. 0 < j <= old_count ==> a[j] == old_a[j-1]
  This is equivalent to: seq_to_list new_a (count+1) == x :: seq_to_list old_a count
*)
let rec lemma_shifted_right
  (s_old s_new: seq int) (from: nat) (n: nat{from <= n /\ n <= length s_old /\ n < length s_new})
  : Lemma
    (requires forall (j: nat). from < j /\ j <= n ==> index s_new j == index s_old (j - 1))
    (ensures seq_to_list_from s_new (from + 1) (n + 1) == seq_to_list_from s_old from n)
    (decreases (n - from))
  = if from >= n then ()
    else lemma_shifted_right s_old s_new (from + 1) n

let bridge_insert (s_old s_new: seq int) (n: nat) (x: int)
  : Lemma
    (requires
      n < length s_old /\
      length s_new == length s_old /\
      index s_new 0 == x /\
      (forall (j: nat). 0 < j /\ j <= n ==> index s_new j == index s_old (j - 1)))
    (ensures seq_to_list s_new (n + 1) == list_insert_head (seq_to_list s_old n) x)
  = lemma_shifted_right s_old s_new 0 n

(** ========== Bridge for LIST-SEARCH ========== *)

(**
  When list_search returns 0, the C code ensures:
    forall j. j < n ==> a[j] != k
  This means k is not in the list.
*)
let rec bridge_search_not_found_from
  (s: seq int) (from: nat) (n: nat{from <= n /\ n <= length s}) (k: int)
  : Lemma
    (requires forall (j: nat). from <= j /\ j < n ==> index s j <> k)
    (ensures not (L.mem k (seq_to_list_from s from n)))
    (decreases (n - from))
  = if from >= n then ()
    else bridge_search_not_found_from s (from + 1) n k

let bridge_search_not_found (s: seq int) (n: nat{n <= length s}) (k: int)
  : Lemma
    (requires forall (j: nat). j < n ==> index s j <> k)
    (ensures not (list_search (seq_to_list s n) k))
  = bridge_search_not_found_from s 0 n k

(**
  When list_search returns nonzero, the C code's list_find_from ensures:
    idx < n /\ a[idx] == k
  This means k is in the list.
*)
let rec bridge_search_found_from
  (s: seq int) (from: nat) (n: nat{from <= n /\ n <= length s}) (k: int) (idx: nat)
  : Lemma
    (requires from <= idx /\ idx < n /\ index s idx == k)
    (ensures L.mem k (seq_to_list_from s from n))
    (decreases (n - from))
  = if from = idx then ()
    else bridge_search_found_from s (from + 1) n k idx

let bridge_search_found (s: seq int) (n: nat{n <= length s}) (k: int) (idx: nat)
  : Lemma
    (requires idx < n /\ index s idx == k)
    (ensures list_search (seq_to_list s n) k)
  = bridge_search_found_from s 0 n k idx

(** ========== Bridge for LIST-DELETE ========== *)

(**
  The C shift_left ensures:
    forall j. j < pos ==> a[j] == old_a[j]         (prefix preserved)
    forall j. pos < j < n ==> a[j-1] == old_a[j]   (shifted left)
  Combined with finding k at position idx, the result matches
  CLRS.Ch10.SinglyLinkedList.Spec.list_delete.
*)

(** Helper: seq_to_list_from of prefix is unchanged when prefix elements match *)
let rec lemma_prefix_unchanged
  (s_old s_new: seq int) (from: nat) (pos: nat) (n: nat)
  : Lemma
    (requires
      from <= pos /\ pos <= n /\ n <= length s_old /\ n <= length s_new /\
      (forall (j: nat). from <= j /\ j < pos ==> index s_new j == index s_old j))
    (ensures seq_to_list_from s_new from pos == seq_to_list_from s_old from pos)
    (decreases (pos - from))
  = if from >= pos then ()
    else lemma_prefix_unchanged s_old s_new (from + 1) pos n

(** Helper: after shift_left at pos, elements in [pos, n-1) match old [pos+1, n) *)
let rec lemma_shifted_left
  (s_old s_new: seq int) (pos: nat) (n: nat{pos < n /\ n <= length s_old /\ n <= length s_new})
  : Lemma
    (requires forall (j: nat). pos < j /\ j < n ==> index s_new (j - 1) == index s_old j)
    (ensures seq_to_list_from s_new pos (n - 1) == seq_to_list_from s_old (pos + 1) n)
    (decreases (n - pos))
  = if pos + 1 >= n then ()
    else (
      assert (index s_new pos == index s_old (pos + 1));
      lemma_shifted_left s_old s_new (pos + 1) n
    )

(** Main delete bridge: after finding k at idx and shifting left,
    the result is list_delete applied to the original list *)
let rec lemma_delete_at_index
  (s: seq int) (from: nat) (n: nat{from <= n /\ n <= length s})
  (s': seq int) (k: int) (idx: nat)
  : Lemma
    (requires
      n <= length s' /\
      from <= idx /\ idx < n /\
      index s idx == k /\
      (forall (j: nat). from <= j /\ j < idx ==> index s j <> k) /\
      (forall (j: nat). from <= j /\ j < idx ==> index s' j == index s j) /\
      (forall (j: nat). idx < j /\ j < n ==> index s' (j - 1) == index s j))
    (ensures seq_to_list_from s' from (n - 1) == list_delete (seq_to_list_from s from n) k)
    (decreases (n - from))
  = if from >= n then ()
    else if from = idx then (
      // At the position where k was found: hd = k, so list_delete drops it
      // and we need seq_to_list_from s' idx (n-1) == seq_to_list_from s (idx+1) n
      lemma_shifted_left s s' idx n
    )
    else (
      // Before idx: hd != k, so list_delete recurses on the tail
      assert (index s from <> k);
      assert (index s' from == index s from);
      lemma_delete_at_index s (from + 1) n s' k idx
    )

let bridge_delete (s_old s_new: seq int) (n: nat) (k: int) (idx: nat)
  : Lemma
    (requires
      0 < n /\ n <= length s_old /\ n <= length s_new /\
      idx < n /\
      index s_old idx == k /\
      (forall (j: nat). j < idx ==> index s_old j <> k) /\
      (forall (j: nat). j < idx ==> index s_new j == index s_old j) /\
      (forall (j: nat). idx < j /\ j < n ==> index s_new (j - 1) == index s_old j))
    (ensures seq_to_list s_new (n - 1) == list_delete (seq_to_list s_old n) k)
  = lemma_delete_at_index s_old 0 n s_new k idx

(** Bridge for delete not-found case: list is unchanged *)
let bridge_delete_not_found (s: seq int) (n: nat{n <= length s}) (k: int)
  : Lemma
    (requires forall (j: nat). j < n ==> index s j <> k)
    (ensures list_delete (seq_to_list s n) k == seq_to_list s n)
  = bridge_search_not_found s n k;
    lemma_delete_not_found (seq_to_list s n) k
