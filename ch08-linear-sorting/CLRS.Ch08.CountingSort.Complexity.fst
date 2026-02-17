module CLRS.Ch08.CountingSort.Complexity

open FStar.Mul

/// The total number of iterations performed by counting sort
/// on an array of n elements with keys in range [0..k]
///
/// Phase 1: Count occurrences - n iterations over input array
/// Phase 2: Write sorted output - (k+1) bucket iterations + n element writes
/// Total: n + (k+1) + n = 2n + k + 1
//SNIPPET_START: counting_sort_iterations
let counting_sort_iterations (n k: nat) : nat = 
  2 * n + k + 1
//SNIPPET_END: counting_sort_iterations

//SNIPPET_START: counting_sort_linear
let counting_sort_linear (n k: nat) : Lemma
  (ensures counting_sort_iterations n k <= 2 * (n + k) + 1)
  = ()
//SNIPPET_END: counting_sort_linear

/// For fixed k, counting sort is O(n)
/// This shows that when the range k is constant, the algorithm is linear in n
let counting_sort_linear_n (n k: nat) : Lemma
  (ensures counting_sort_iterations n k <= 3 * n + k + 1)
  = ()

/// Lower bound showing counting sort is Ω(n+k)
/// Combined with the upper bound, this proves counting sort is Θ(n+k)
let counting_sort_lower_bound (n k: nat) : Lemma
  (ensures counting_sort_iterations n k >= n + k)
  = ()
