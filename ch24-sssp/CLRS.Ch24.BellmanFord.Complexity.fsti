module CLRS.Ch24.BellmanFord.Complexity

(*
   Interface for Bellman-Ford complexity analysis.

   Proves O(V³) complexity for adjacency-matrix representation.
   - Total iterations: v + (v-1)·v² + v² = v + v³
   - Asymptotic: ≤ 2v³ for v ≥ 1
*)

open FStar.Mul

/// Total iteration count: initialization + (v-1) relaxation rounds + detection
val bellman_ford_iterations (v: nat) : nat

/// Upper bound: iterations ≤ v³ + v² + v
val bellman_ford_bound (v: nat) : Lemma
  (ensures bellman_ford_iterations v <= v * v * v + v * v + v)

/// Asymptotic O(V³) bound: iterations ≤ 2v³ for v ≥ 1
val bellman_ford_cubic (v: nat) : Lemma
  (requires v >= 1)
  (ensures bellman_ford_iterations v <= 2 * v * v * v)

/// Dominant term: iterations ≥ v³ for v ≥ 2
val bellman_ford_dominant_term (v: nat) : Lemma
  (requires v >= 2)
  (ensures bellman_ford_iterations v >= v * v * v)
