module CLRS.Common.Predicates

open FStar.Seq

(** Bounds predicates **)

let larger_than (#a:Type) (compare: a -> a -> Tot bool) (s: seq a) (lb: a) 
  = forall (k: nat). k < length s ==> compare lb (index s k)

let smaller_than (#a:Type) (compare: a -> a -> Tot bool) (s: seq a) (rb: a)
  = forall (k: nat). k < length s ==> compare (index s k) rb

let between_bounds (#a:Type) (compare: a -> a -> Tot bool) (s: seq a) (lb rb: a)
  = larger_than compare s lb /\ smaller_than compare s rb

(** Sortedness predicates **)

let sorted (#a:Type) (compare: a -> a -> Tot bool) (s: seq a)
  = forall (i j: nat). i <= j /\ j < length s ==> compare (index s i) (index s j)

(** Permutation predicates **)

[@@"opaque_to_smt"]
let is_permutation (#a:eqtype) (s1 s2: seq a) : prop 
  = FStar.Seq.Properties.permutation a s1 s2

(** Heap predicates **)

let parent_index (i: nat{i > 0}) : nat = (i - 1) / 2

let left_child_index (i: nat) : nat = op_Star 2 i + 1

let right_child_index (i: nat) : nat = op_Star 2 i + 2

let max_heap_property (#a:Type) (compare: a -> a -> Tot bool) (s: seq a) (heap_size: nat) (i: nat) : prop
  = i < heap_size /\ heap_size <= length s /\ (
    let left = left_child_index i in
    let right = right_child_index i in
    (left < heap_size ==> compare (index s left) (index s i)) /\
    (right < heap_size ==> compare (index s right) (index s i))
  )

let is_max_heap (#a:Type) (compare: a -> a -> Tot bool) (s: seq a) (heap_size: nat) : prop
  = heap_size <= length s /\
    (forall (i: nat). i < heap_size ==> max_heap_property compare s heap_size i)
