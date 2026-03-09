(*
   Binary Search — Pure Specification (CLRS Exercise 2.3-5)

   Contains the pure definitions used by the binary search implementation:
   - is_sorted: sortedness predicate for sequences
   - log2f: floor of log base 2 (for complexity bounds)
   - complexity_bounded_log: O(log n) complexity predicate

   NO admits. NO assumes.
*)

module CLRS.Ch04.BinarySearch.Spec
open FStar.Seq
module Seq = FStar.Seq

// ========== Definitions ==========

let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i < j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

// ========== Pure helper: log2 floor ==========

let rec log2f (n: int) : Tot nat (decreases (if n > 0 then n else 0)) =
  if Prims.op_LessThanOrEqual n 1 then 0
  else Prims.op_Addition 1 (log2f (Prims.op_Division n 2))

// ========== Complexity bound predicate ==========

let complexity_bounded_log (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= log2f n + 1
