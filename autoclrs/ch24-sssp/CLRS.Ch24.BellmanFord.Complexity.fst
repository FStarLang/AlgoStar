module CLRS.Ch24.BellmanFord.Complexity


(*
 * Complexity analysis for Bellman-Ford algorithm with adjacency matrix representation.
 *
 * CLRS Bellman-Ford structure:
 * 1. Initialization: O(V) - initialize distances for all vertices
 * 2. Main relaxation: (V-1) rounds × V² edge checks = O(V³) total
 * 3. Negative cycle detection: O(V²) - check all edges once more
 *
 * Total: O(V³) for adjacency matrix representation
 * Note: With adjacency list, this would be O(VE) since we only check actual edges
 *)

(** 
 * Total iterations count for Bellman-Ford with adjacency matrix:
 * - Initialization: v iterations
 * - Main relaxation: (v-1) rounds of v² edge checks each
 * - Negative cycle detection: v² edge checks
 *)
let bellman_ford_iterations (v: nat) : nat =
  v + (if v >= 1 then (v - 1) * v * v else 0) + v * v

(**
 * Main complexity bound: prove the total is at most v³ + v² + v
 *)
let bellman_ford_bound (v: nat) : Lemma
  (ensures bellman_ford_iterations v <= v * v * v + v * v + v)
  =
  if v = 0 then (
    // Base case: v = 0
    // bellman_ford_iterations 0 = 0 + 0 + 0 = 0
    // 0 ≤ 0, trivial
    ()
  ) else (
    // v >= 1 case
    // bellman_ford_iterations v = v + (v-1)*v² + v²
    // Need to show: v + (v-1)*v² + v² ≤ v³ + v² + v
    
    // Simplify LHS:
    // v + (v-1)*v² + v²
    // = v + v³ - v² + v²
    // = v + v³
    
    // We need: v + v³ ≤ v³ + v² + v
    // which simplifies to: v³ ≤ v³ + v²
    // This is true for v ≥ 0 since v² ≥ 0
    
    assert (bellman_ford_iterations v == v + (v - 1) * v * v + v * v);
    assert ((v - 1) * v * v + v * v == v * v * v);
    assert (bellman_ford_iterations v == v + v * v * v);
    assert (v + v * v * v <= v * v * v + v * v + v)
  )

(**
 * Asymptotic O(V³) bound: for v ≥ 1, total iterations ≤ 2v³
 *)
let bellman_ford_cubic (v: nat) : Lemma
  (requires v >= 1)
  (ensures bellman_ford_iterations v <= 2 * v * v * v)
  =
  // From bellman_ford_bound, we know:
  // bellman_ford_iterations v = v + v³ (when v ≥ 1)
  
  // Case analysis:
  if v = 1 then begin
    // v = 1: bellman_ford_iterations 1 = 1 + 1 = 2
    // 2v³ = 2 * 1 = 2
    // So 2 ≤ 2 ✓
    assert (bellman_ford_iterations 1 == 2);
    assert (2 * 1 * 1 * 1 == 2)
  end else begin
    // v ≥ 2: v + v³ ≤ 2v³ ⟺ v ≤ v³
    // For v ≥ 2: v ≤ v² ≤ v³
    assert (v >= 2);
    assert (v <= v * v);  // For v ≥ 2: v ≤ v²
    assert (v * v <= v * v * v);  // v² ≤ v³
    assert (v <= v * v * v);  // v ≤ v³
    assert (v + v * v * v <= 2 * v * v * v);
    bellman_ford_bound v;
    assert (bellman_ford_iterations v == v + v * v * v)
  end

(**
 * Additional helper: show that for large v, the v³ term dominates
 *)
let bellman_ford_dominant_term (v: nat) : Lemma
  (requires v >= 2)
  (ensures bellman_ford_iterations v >= v * v * v)
  =
  // For v ≥ 2, we have v ≥ 1, so:
  // bellman_ford_iterations v = v + (v-1)*v² + v²
  //                           = v + v³ - v² + v²
  //                           = v + v³
  //                           ≥ v³
  assert (bellman_ford_iterations v == v + (v - 1) * v * v + v * v);
  assert ((v - 1) * v * v + v * v == v * v * v);
  assert (bellman_ford_iterations v == v + v * v * v);
  assert (v + v * v * v >= v * v * v)
