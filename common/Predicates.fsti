module CLRS.Common.Predicates

open FStar.Seq

(** Bounds predicates **)

/// Predicate: all elements in sequence are >= lb
val larger_than (#a:Type) (compare: a -> a -> Tot bool) (s: seq a) (lb: a) : prop

/// Predicate: all elements in sequence are <= rb
val smaller_than (#a:Type) (compare: a -> a -> Tot bool) (s: seq a) (rb: a) : prop

/// Predicate: all elements in sequence are between lb and rb (inclusive)
val between_bounds (#a:Type) (compare: a -> a -> Tot bool) (s: seq a) (lb rb: a) : prop

(** Sortedness predicates **)

/// Predicate: sequence is sorted according to the comparator
/// compare x y should return true if x <= y
val sorted (#a:Type) (compare: a -> a -> Tot bool) (s: seq a) : prop

(** Permutation predicates **)

/// Predicate: two sequences are permutations of each other
[@@"opaque_to_smt"]
val is_permutation (#a:eqtype) (s1 s2: seq a) : prop

(** Heap predicates **)

/// Helper: compute parent index in a heap
val parent_index (i: nat{i > 0}) : nat

/// Helper: compute left child index in a heap
val left_child_index (i: nat) : nat

/// Helper: compute right child index in a heap
val right_child_index (i: nat) : nat

/// Predicate: max-heap property holds at index i
/// For a max-heap, parent >= children
/// heap_size is the current size of the heap (may be < length s)
val max_heap_property (#a:Type) (compare: a -> a -> Tot bool) (s: seq a) (heap_size: nat) (i: nat) : prop

/// Predicate: entire sequence satisfies max-heap property
val is_max_heap (#a:Type) (compare: a -> a -> Tot bool) (s: seq a) (heap_size: nat) : prop
