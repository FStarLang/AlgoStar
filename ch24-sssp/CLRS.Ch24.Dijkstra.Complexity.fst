(*
   Dijkstra's Algorithm — Complexity Implementation

   Re-exports complexity bounds from CLRS.Ch24.Dijkstra.
*)

module CLRS.Ch24.Dijkstra.Complexity

open FStar.Mul

module D = CLRS.Ch24.Dijkstra

let dijkstra_quadratic_bound (n: nat) : Lemma
  (ensures dijkstra_iterations n <= 3 * n * n)
  =
  D.dijkstra_quadratic_bound n

let dijkstra_complexity_is_quadratic (cf c0 n: nat) : Lemma
  (requires dijkstra_complexity_bounded cf c0 n)
  (ensures cf - c0 <= 3 * n * n)
  =
  D.dijkstra_complexity_is_quadratic cf c0 n
