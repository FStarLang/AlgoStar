module CLRS.Ch35.VertexCover.Complexity

(**
 * Complexity analysis for APPROX-VERTEX-COVER.
 *
 * The implementation uses a nested loop over all vertex pairs (u, v) with u < v,
 * yielding O(V²) time complexity. This is correct for the adjacency-matrix
 * representation used. CLRS achieves O(V+E) with adjacency lists.
 *
 * partial_iterations tracks per-row accumulation for linking to the Pulse
 * implementation via ghost counters.
 *)


(*** Complexity definitions and proofs ***)

// Exact iteration count: v*(v-1)/2 for the nested loop over (u,v) with u < v
let vertex_cover_iterations (v: nat) : nat = v * (v - 1) / 2

// The nested loop performs at most v*v iterations
let vertex_cover_quadratic (v: nat)
  : Lemma (ensures vertex_cover_iterations v <= v * v)
  = ()

// Tighter bound: iterations are at most v*(v-1)/2
let vertex_cover_tight_bound (v: nat)
  : Lemma (ensures vertex_cover_iterations v <= v * v / 2)
  = ()

(*** Partial iteration counts for Pulse linking ***)

// Cumulative inner-loop iterations after processing rows 0..(rows_done-1).
// Row k contributes (n - k - 1) iterations (v from k+1 to n-1).
let rec partial_iterations (n: nat) (rows_done: nat) : Tot nat (decreases rows_done) =
  if rows_done = 0 || rows_done > n then 0
  else partial_iterations n (rows_done - 1) + (n - rows_done)

let partial_iterations_zero (n: nat)
  : Lemma (ensures partial_iterations n 0 = 0)
  = ()

let partial_iterations_step (n: nat) (k: nat)
  : Lemma (requires k < n)
          (ensures partial_iterations n (k + 1) = partial_iterations n k + (n - k - 1))
  = ()

// Closed-form formula for partial_iterations, avoiding division
let rec partial_iterations_formula (n: nat) (k: nat)
  : Lemma (requires k <= n)
          (ensures 2 * partial_iterations n k = k * (2 * n - k - 1))
          (decreases k)
  = if k = 0 then ()
    else partial_iterations_formula n (k - 1)

let partial_iterations_total (n: nat)
  : Lemma (ensures partial_iterations n n = vertex_cover_iterations n)
  = partial_iterations_formula n n
