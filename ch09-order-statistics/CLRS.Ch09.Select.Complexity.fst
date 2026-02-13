(*
   Copyright 2025

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module CLRS.Ch09.Select.Complexity

open FStar.Mul

(**
 * Complexity Analysis for Partial Selection Sort
 *
 * This module proves the O(nk) complexity bound for the partial selection sort
 * algorithm used in CLRS.Ch09.Select. The algorithm finds the k smallest elements
 * by performing k rounds of selection, where each round finds the minimum of the
 * remaining unsorted portion.
 *
 * Comparison with CLRS Chapter 9:
 * --------------------------------
 * CLRS Chapter 9 presents RANDOMIZED-SELECT with O(n) expected time complexity.
 * This implementation uses partial selection sort with O(nk) worst-case time.
 * 
 * For k = O(1) (finding a constant number of smallest elements), both approaches
 * are O(n). However, for k = n/2 (finding the median), this implementation is
 * O(n²) worst-case, while RANDOMIZED-SELECT achieves O(n) expected time.
 *
 * The trade-off:
 * - Partial selection sort: O(nk) worst-case, deterministic, simple to verify
 * - RANDOMIZED-SELECT: O(n) expected, O(n²) worst-case, requires probabilistic analysis
 *)

(**
 * Exact comparison count for partial selection sort.
 *
 * In round i (0 ≤ i < k), the algorithm scans from position i to n-1,
 * performing n-i comparisons. However, we use a simplified model where
 * each round performs n-1 comparisons (an overestimate that simplifies
 * the analysis).
 *
 * The actual count would be:
 *   Σ_{i=0}^{k-1} (n - i - 1) = k*n - k(k+1)/2 - k
 *
 * Our simplified model:
 *   k * (n - 1)
 *)
let rec select_comparisons (n k: nat) : nat =
  if k = 0 || n <= 1 then 0
  else (n - 1) + select_comparisons n (k - 1)

(**
 * The simple upper bound: select_comparisons n k ≤ k * n
 *
 * Proof by induction on k:
 * - Base case (k=0): 0 ≤ 0
 * - Base case (n≤1): 0 ≤ k * 1 = k
 * - Inductive case: 
 *     select_comparisons n k 
 *   = (n-1) + select_comparisons n (k-1)
 *   ≤ (n-1) + (k-1)*n             [by IH]
 *   = n - 1 + k*n - n
 *   = k*n - 1
 *   ≤ k*n
 *)
let rec select_bound (n k: nat) : Lemma
  (requires k <= n)
  (ensures select_comparisons n k <= k * n)
  (decreases k)
  =
  if k = 0 || n <= 1 then ()
  else begin
    select_bound n (k - 1);
    // After recursive call, we know: select_comparisons n (k-1) <= (k-1) * n
    // We need to show: (n-1) + select_comparisons n (k-1) <= k * n
    // This follows from: (n-1) + (k-1)*n = n - 1 + k*n - n = k*n - 1 <= k*n
    assert (select_comparisons n (k - 1) <= (k - 1) * n);
    assert ((n - 1) + (k - 1) * n == k * n - 1);
    assert (select_comparisons n k == (n - 1) + select_comparisons n (k - 1))
  end

(**
 * A more precise bound using the actual comparison count.
 *
 * The exact number of comparisons is:
 *   Σ_{i=0}^{k-1} (n - i - 1) = k*n - k - k(k-1)/2
 *                              = k*n - k - k²/2 + k/2
 *                              = k*n - k²/2 - k/2
 *                              = k*n - k(k+1)/2
 *
 * For our simplified model with n-1 comparisons per round:
 *   k * (n - 1) = k*n - k
 *)
let select_comparisons_exact (n k: nat) : Lemma
  (requires k <= n)
  (ensures select_comparisons n k == k * (n - 1))
  =
  let rec lemma (n k: nat) : Lemma
    (requires k <= n)
    (ensures select_comparisons n k == k * (n - 1))
    (decreases k)
    =
    if k = 0 || n <= 1 then ()
    else begin
      lemma n (k - 1);
      assert (select_comparisons n (k - 1) == (k - 1) * (n - 1));
      assert (select_comparisons n k == (n - 1) + select_comparisons n (k - 1));
      assert ((n - 1) + (k - 1) * (n - 1) == k * (n - 1))
    end
  in
  lemma n k

(**
 * Consequence: The algorithm is O(nk).
 *
 * Special cases:
 * - k = 1 (minimum): O(n)
 * - k = O(1) (constant smallest elements): O(n)
 * - k = n/2 (median): O(n²)
 * - k = n (full sort): O(n²)
 *)
let select_complexity_class (n k: nat) : Lemma
  (requires k <= n)
  (ensures select_comparisons n k <= k * n)
  =
  select_bound n k
