(*
   Jarvis's March (Gift Wrapping) — CLRS Chapter 33, Section 33.3

   Complexity interface for Jarvis march.
*)

module CLRS.Ch33.JarvisMarch.Complexity
open FStar.Mul

val find_leftmost_ops (n: nat) : nat
val find_next_ops (n: nat) : nat
val jarvis_march_ops (n h: nat) : nat

val jarvis_march_quadratic_bound (n h: nat) : Lemma
  (requires n > 1 /\ h <= n)
  (ensures jarvis_march_ops n h <= n * n)

val helpers_linear (n: nat) : Lemma
  (requires n > 1)
  (ensures find_leftmost_ops n <= n /\ find_next_ops n <= n)
