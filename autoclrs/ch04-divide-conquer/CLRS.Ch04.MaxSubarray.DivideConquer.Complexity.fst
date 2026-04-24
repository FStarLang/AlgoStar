(*
   Maximum Subarray D&C — Complexity Analysis

   Proves O(n log n) complexity via the Master Theorem (case 2):
   T(n) = 2T(n/2) + n, solution T(n) <= 4n(log2_ceil(n) + 1)

   NO admits. NO assumes.
*)

module CLRS.Ch04.MaxSubarray.DivideConquer.Complexity

//SNIPPET_START: dc_ops_count
// Operation count for D&C algorithm
// T(n) = 2T(n/2) + cn for n > 1, T(1) = c
let rec dc_ops_count (n: nat) : Tot nat =
  if n <= 1 then 1
  else
    let half_ops = dc_ops_count (n / 2) in
    let double_half = half_ops + half_ops in
    double_half + n
//SNIPPET_END: dc_ops_count

// log2 ceiling function for complexity bounds
let rec log2_ceil (n: pos) : Tot nat (decreases n) =
  if n = 1 then 0
  else 1 + log2_ceil ((n + 1) / 2)

// Key property: 2^(log2_ceil n - 1) < n <= 2^(log2_ceil n)
let rec lemma_log2_ceil_bounds (n: pos)
  : Lemma (ensures (log2_ceil n = 0 /\ n = 1) \/
                    (log2_ceil n > 0 /\ pow2 (log2_ceil n - 1) < n /\ n <= pow2 (log2_ceil n)))
          (decreases n)
  =
  if n = 1 then ()
  else (
    let n' = (n + 1) / 2 in
    if n' > 0 then lemma_log2_ceil_bounds n'
  )

// log2_ceil is monotone
let rec log2_ceil_monotone (a b: pos)
  : Lemma (requires a <= b) (ensures log2_ceil a <= log2_ceil b) (decreases b)
  = if a = b then ()
    else if b = 1 then ()
    else if a = 1 then ()
    else begin
      assert ((a + 1) / 2 <= (b + 1) / 2);
      log2_ceil_monotone ((a + 1) / 2) ((b + 1) / 2)
    end

// log2_ceil(n) >= 1 + log2_ceil(n/2) for n >= 2
let log2_ceil_halving (n: pos{n >= 2})
  : Lemma (ensures log2_ceil n >= 1 + log2_ceil (n / 2))
  = assert (n / 2 >= 1);
    log2_ceil_monotone (n / 2) ((n + 1) / 2)

//SNIPPET_START: dc_complexity_bound
// Prove: T(n) = O(n log n) via Master Theorem case 2
// T(n) = 2T(n/2) + n, solution T(n) <= 4n(log2_ceil(n) + 1)
let rec lemma_dc_complexity_bound (n: pos) 
  : Lemma (ensures dc_ops_count n <= op_Star 4 (op_Star n (log2_ceil n + 1)))
          (decreases n)
//SNIPPET_END: dc_complexity_bound
  = if n = 1 then ()
    else begin
      let h = n / 2 in
      assert (h >= 1);
      lemma_dc_complexity_bound h;
      assert (op_Star 8 h <= op_Star 4 n);
      log2_ceil_halving n
    end
