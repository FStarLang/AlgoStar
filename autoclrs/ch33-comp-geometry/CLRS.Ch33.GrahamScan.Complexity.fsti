(*
   Graham Scan — CLRS Chapter 33, Section 33.3

   Complexity interface for Graham scan.
*)

module CLRS.Ch33.GrahamScan.Complexity

val find_bottom_ops (n: nat) : nat
val polar_cmp_ops : nat
val pop_while_ops (top: nat) : nat
val polar_sort_ops_insertion (n: nat) : nat
val graham_scan_loop_ops (n: nat) : nat
val graham_scan_ops (n: nat) : nat

val graham_scan_quadratic (n: nat) : Lemma
  (requires n > 0)
  (ensures graham_scan_ops n <= 4 * n * n)

val scan_linear (n: nat) : Lemma
  (ensures graham_scan_loop_ops n <= 2 * n)
