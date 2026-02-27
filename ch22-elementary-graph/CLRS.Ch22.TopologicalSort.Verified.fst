(**
 * CLRS Chapter 22: Topological Sort — Fully Verified Implementation
 *
 * Task P2.5.2: Prove Kahn's algorithm produces a valid topological order
 *
 * This file extends the basic implementation to PROVE that the output
 * satisfies `is_topological_order adj n output`:
 * - For every edge (u,v) in the graph, u appears before v in the output
 *
 * Key proof strategy:
 * 1. Track in-degree correctness throughout execution
 * 2. Prove queue contains only vertices whose predecessors are in output
 * 3. Show strong_order_inv: every vertex in output has all predecessors earlier
 * 4. Connect strong_order_inv to is_topological_order
 *
 * Zero admits: all correctness arguments fully proved including pigeonhole.
 *)
module CLRS.Ch22.TopologicalSort.Verified

open CLRS.Ch22.TopologicalSort.Spec
open CLRS.Ch22.TopologicalSort.Lemmas
open FStar.Mul

(**
 * Pure proof: strong_order_inv implies topological ordering on int sequences
 *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"

// Distinctness for int sequences
let all_distinct_int (order: Seq.seq int) : prop =
  forall (i j: nat). i < Seq.length order /\ j < Seq.length order /\ i <> j ==>
    Seq.index order i <> Seq.index order j

// All elements are valid vertices for int sequences
let all_valid_vertices_int (order: Seq.seq int) (n: nat) : prop =
  forall (i: nat). i < Seq.length order ==> 
    Seq.index order i >= 0 /\ Seq.index order i < n

// Find position in an int sequence
let rec position_in_order_int_aux (order: Seq.seq int) (v: nat) (pos: nat) 
  : Tot (option nat) (decreases (Seq.length order - pos))
  = if pos >= Seq.length order then None
    else if Seq.index order pos = v then Some pos
    else position_in_order_int_aux order v (pos + 1)

let position_in_order_int (order: Seq.seq int) (v: nat) : option nat =
  position_in_order_int_aux order v 0

// appears_before for int sequences (matching the implementation which uses int, not nat)
let appears_before_int (order: Seq.seq int) (u v: nat) : prop =
  Some? (position_in_order_int order u) /\
  Some? (position_in_order_int order v) /\
  Some?.v (position_in_order_int order u) < Some?.v (position_in_order_int order v)

// Topological order property for int sequences  
let is_topological_order_int (adj: Seq.seq int) (n: nat) (order: Seq.seq int) : prop =
  Seq.length order == n /\
  Seq.length adj == n * n /\
  (forall (u v: nat). has_edge n adj u v ==> appears_before_int order u v)

(**
 * Key lemmas about position_in_order_int
 *)

let rec lemma_position_in_order_int_correct (order: Seq.seq int) (v: nat) (start: nat)
  : Lemma
    (requires start <= Seq.length order)
    (ensures (
      let result = position_in_order_int_aux order v start in
      (Some? result ==> (let pos = Some?.v result in 
                         pos >= start /\ pos < Seq.length order /\ Seq.index order pos == v)) /\
      (None? result ==> (forall (i: nat). start <= i /\ i < Seq.length order ==> Seq.index order i <> v))))
    (decreases (Seq.length order - start))
  = if start >= Seq.length order then ()
    else if Seq.index order start = v then ()
    else lemma_position_in_order_int_correct order v (start + 1)

let rec lemma_distinct_has_position_int_aux (order: Seq.seq int) (v: nat) (pos: nat) (start: nat)
  : Lemma
    (requires 
      pos < Seq.length order /\
      start <= Seq.length order /\
      Seq.index order pos == v /\
      all_distinct_int order)
    (ensures (
      let result = position_in_order_int_aux order v start in
      if start <= pos 
      then result == Some pos
      else (Some? result ==> False)))
    (decreases (Seq.length order - start))
  = if start >= Seq.length order then ()
    else if start = pos then ()
    else if Seq.index order start = v then ()
    else lemma_distinct_has_position_int_aux order v pos (start + 1)

let lemma_distinct_has_position_int (order: Seq.seq int) (v: nat) (pos: nat)
  : Lemma
    (requires 
      pos < Seq.length order /\
      Seq.index order pos == v /\
      all_distinct_int order)
    (ensures position_in_order_int order v == Some pos)
  = lemma_distinct_has_position_int_aux order v pos 0

#pop-options

(**
 * Helper lemma: If output has length n, is distinct, and all elements are < n,
 * then every vertex v < n appears exactly once in output (permutation property)
 *)
 
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"

// Count how many times v appears in seq[0..len)
let rec count_occurrences (s: Seq.seq int) (len: nat) (v: int) 
  : Tot nat (decreases len)
  = if len = 0 || len > Seq.length s then 0
    else if Seq.index s (len - 1) = v then 1 + count_occurrences s (len - 1) v
    else count_occurrences s (len - 1) v

let lemma_distinct_at_most_once (s: Seq.seq int) (len: nat) (v: int) (pos: nat)
  : Lemma
    (requires 
      len <= Seq.length s /\
      all_distinct_int s /\
      pos < len /\
      Seq.index s pos = v)
    (ensures (forall (i: nat). i < len /\ i <> pos ==> Seq.index s i <> v))
  = ()

let rec lemma_all_distinct_count_le_one (s: Seq.seq int) (len: nat) (v: int)
  : Lemma
    (requires all_distinct_int s /\ len <= Seq.length s)
    (ensures count_occurrences s len v <= 1)
    (decreases len)
  = if len = 0 || len > Seq.length s then ()
    else if Seq.index s (len - 1) = v then begin
      // s[len-1] == v, and s is distinct
      // So v doesn't appear in s[0..len-1)
      lemma_distinct_at_most_once s len v (len - 1);
      // Therefore count in s[0..len-1) is 0
      let rec aux (m: nat)
        : Lemma (requires m <= len - 1)
                (ensures count_occurrences s m v == 0)
                (decreases m)
        = if m = 0 then ()
          else begin
            assert (Seq.index s (m - 1) <> v);
            aux (m - 1)
          end
      in
      aux (len - 1);
      assert (count_occurrences s (len - 1) v == 0)
    end
    else lemma_all_distinct_count_le_one s (len - 1) v

let rec lemma_count_zero_means_not_present (s: Seq.seq int) (len: nat) (v: int)
  : Lemma
    (requires len <= Seq.length s /\ count_occurrences s len v == 0)
    (ensures forall (i: nat). i < len ==> Seq.index s i <> v)
    (decreases len)
  = if len = 0 then ()
    else begin
      assert (Seq.index s (len - 1) <> v);
      lemma_count_zero_means_not_present s (len - 1) v
    end

let rec lemma_count_one_means_exists_unique (s: Seq.seq int) (len: nat) (v: int)
  : Lemma
    (requires len <= Seq.length s /\ count_occurrences s len v == 1)
    (ensures exists (j: nat). j < len /\ Seq.index s j == v)
    (decreases len)
  = if len = 0 then ()
    else if Seq.index s (len - 1) = v then ()
    else lemma_count_one_means_exists_unique s (len - 1) v

// Sum of count(w) for w = 0,...,k-1
private let rec sum_counts (s: Seq.seq int) (len k: nat) : Tot nat (decreases k) =
  if k = 0 then 0
  else count_occurrences s len (k - 1) + sum_counts s len (k - 1)

// When last element is not in {0,...,k-1}, removing it doesn't change sum_counts
private let rec lemma_sum_counts_same_last (s: Seq.seq int) (len: nat) (k: nat)
  : Lemma
    (requires len > 0 /\ len <= Seq.length s /\
      (Seq.index s (len - 1) < 0 \/ Seq.index s (len - 1) >= k))
    (ensures sum_counts s len k = sum_counts s (len - 1) k)
    (decreases k)
  = if k = 0 then ()
    else begin
      assert (Seq.index s (len - 1) <> k - 1);
      lemma_sum_counts_same_last s len (k - 1)
    end

// Removing last element decreases sum by exactly 1
private let rec lemma_sum_counts_remove_last (s: Seq.seq int) (len: nat) (k: nat)
  : Lemma
    (requires len > 0 /\ len <= Seq.length s /\
      Seq.index s (len - 1) >= 0 /\ Seq.index s (len - 1) < k)
    (ensures sum_counts s len k = 1 + sum_counts s (len - 1) k)
    (decreases k)
  = let w = Seq.index s (len - 1) in
    if k = 0 then ()
    else if w = k - 1 then
      lemma_sum_counts_same_last s len (k - 1)
    else
      lemma_sum_counts_remove_last s len (k - 1)

// Total count equals sequence length when all elements are in {0,...,k-1}
private let rec lemma_sum_counts_total (s: Seq.seq int) (len k: nat)
  : Lemma
    (requires len <= Seq.length s /\ (forall (i:nat). i < len ==> Seq.index s i >= 0 /\ Seq.index s i < k))
    (ensures sum_counts s len k = len)
    (decreases len)
  = if len = 0 then begin
      let rec aux (m:nat) : Lemma (requires m <= k) (ensures sum_counts s 0 m = 0) (decreases m)
        = if m = 0 then () else aux (m - 1)
      in aux k
    end
    else begin
      lemma_sum_counts_total s (len - 1) k;
      lemma_sum_counts_remove_last s len k
    end

// Sum of counts bounded by k (each count <= 1 by distinctness)
private let rec lemma_sum_counts_bounded_by_k (s: Seq.seq int) (len k: nat)
  : Lemma
    (requires len <= Seq.length s /\ all_distinct_int s)
    (ensures sum_counts s len k <= k)
    (decreases k)
  = if k = 0 then ()
    else begin
      lemma_all_distinct_count_le_one s len (k - 1);
      lemma_sum_counts_bounded_by_k s len (k - 1)
    end

// If count(v) = 0 for some v < k, then sum <= k - 1
private let rec lemma_sum_counts_skip_bounded (s: Seq.seq int) (len k: nat) (v: nat)
  : Lemma
    (requires len <= Seq.length s /\ v < k /\ all_distinct_int s /\ count_occurrences s len v = 0)
    (ensures sum_counts s len k <= k - 1)
    (decreases k)
  = if k = 0 then ()
    else if v = k - 1 then
      lemma_sum_counts_bounded_by_k s len (k - 1)
    else begin
      lemma_all_distinct_count_le_one s len (k - 1);
      lemma_sum_counts_skip_bounded s len (k - 1) v
    end

// Pigeonhole: if sequence has n distinct elements all < n, it contains each element 0..n-1 exactly once
let lemma_permutation_contains_all (s: Seq.seq int) (n: nat) (v: nat)
  : Lemma
    (requires 
      Seq.length s == n /\
      all_distinct_int s /\
      all_valid_vertices_int s n /\
      v < n)
    (ensures exists (j: nat). j < n /\ Seq.index s j == v)
  = lemma_all_distinct_count_le_one s n v;
    if count_occurrences s n v = 1 then
      lemma_count_one_means_exists_unique s n v
    else begin
      lemma_count_zero_means_not_present s n v;
      // Counting argument: sum_{w=0}^{n-1} count(w) = n but <= n-1 since count(v)=0
      lemma_sum_counts_total s n n;
      lemma_sum_counts_skip_bounded s n n v
      // n = sum_counts <= n-1, contradiction
    end

// Pigeonhole for partial sequences: if each v < n appears in first count elements
// but count < n, contradiction.
let lemma_pigeonhole_count_occurrences (s: Seq.seq int) (count n: nat)
  : Lemma
    (requires
      count < n /\ count <= Seq.length s /\
      (forall (i:nat). i < count ==> Seq.index s i >= 0 /\ Seq.index s i < n) /\
      (forall (v: nat). v < n ==> count_occurrences s count v >= 1))
    (ensures False)
  = lemma_sum_counts_total s count n;
    let rec aux (k: nat) : Lemma (requires k <= n) (ensures sum_counts s count k >= k) (decreases k) =
      if k = 0 then () else (aux (k-1); assert (count_occurrences s count (k-1) >= 1))
    in aux n

#pop-options

(**
 * Main theorem: strong_order_inv implies topological ordering
 *)
 
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"

let lemma_strong_order_implies_topo_order_int
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int)
  : Lemma
    (requires 
      Seq.length output == n /\
      Seq.length adj == n * n /\
      all_distinct_int output /\
      all_valid_vertices_int output n /\
      strong_order_inv adj n output n)
    (ensures is_topological_order_int adj n output)
  = let order = output in
    let aux (u: nat) (v: nat)
      : Lemma
        (requires has_edge n adj u v)
        (ensures appears_before_int order u v)
      = // has_edge means u < n, v < n, and adj[u*n+v] != 0
        assert (u < n /\ v < n);
        FStar.Math.Lemmas.nat_times_nat_is_nat u n;
        let idx : nat = u * n + v in
        assert (idx < n * n);
        assert (Seq.index adj idx <> 0);
        
        // By permutation lemma, v appears exactly once in output
        lemma_permutation_contains_all output n v;
        
        let f (j: nat{j < n /\ Seq.index output j == v})
          : GTot (squash (appears_before_int order u v))
          = // From strong_order_inv at position j:
            // forall (u: nat). u < n /\ edge(u, output[j]) ==> exists k < j. output[k] == u
            assert (strong_order_inv adj n output n);
            assert (j < n);
            assert (Seq.index output j == v);
            assert (v >= 0 /\ v < n);
            assert (u < n /\ u * n + v < n * n);
            assert (Seq.index adj (u * n + v) <> 0);
            // Therefore exists k < j. output[k] == u
            
            let g (k: nat{k < j /\ Seq.index output k == u})
              : GTot (squash (appears_before_int order u v))
              = lemma_distinct_has_position_int order u k;
                lemma_distinct_has_position_int order v j;
                assert (position_in_order_int order u == Some k);
                assert (position_in_order_int order v == Some j);
                assert (k < j);
                ()
            in
            FStar.Classical.exists_elim
              (appears_before_int order u v)
              #nat
              #(fun k -> k < j /\ Seq.index output k == u)
              ()
              g
        in
        FStar.Classical.exists_elim
          (appears_before_int order u v)
          #nat
          #(fun j -> j < n /\ Seq.index output j == v)
          ()
          f
    in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)

#pop-options

(**
 * Bridge to the spec: int-based order implies nat-based order
 *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"

// Convert int sequence to nat sequence when all elements are valid
let seq_int_to_nat (s: Seq.seq int) (n: nat)
  : Pure (Seq.seq nat)
    (requires Seq.length s == n /\ all_valid_vertices_int s n)
    (ensures fun r -> 
      Seq.length r == n /\
      (forall (i: nat). i < n ==> Seq.index r i == Seq.index s i))
  = let f (i: nat{i < n}) : nat = 
      let x = Seq.index s i in
      assert (x >= 0 /\ x < n);
      x
    in
    Seq.init n f

let rec lemma_position_aux_same (s_int: Seq.seq int) (s_nat: Seq.seq nat) (n: nat) (v: nat) (pos: nat)
  : Lemma
    (requires 
      Seq.length s_int == n /\
      Seq.length s_nat == n /\
      pos <= n /\
      (forall (i: nat). i < n ==> Seq.index s_int i == Seq.index s_nat i))
    (ensures position_in_order_int_aux s_int v pos == position_in_order_aux s_nat v pos)
    (decreases (n - pos))
  = if pos >= n then ()
    else begin
      assert (Seq.index s_int pos == Seq.index s_nat pos);
      if Seq.index s_int pos = v then ()
      else lemma_position_aux_same s_int s_nat n v (pos + 1)
    end

let lemma_position_same_int_nat (s_int: Seq.seq int) (s_nat: Seq.seq nat) (n: nat) (v: nat)
  : Lemma
    (requires 
      Seq.length s_int == n /\
      Seq.length s_nat == n /\
      (forall (i: nat). i < n ==> Seq.index s_int i == Seq.index s_nat i))
    (ensures position_in_order_int s_int v == position_in_order s_nat v)
  = lemma_position_aux_same s_int s_nat n v 0

let lemma_int_order_implies_nat_order (adj: Seq.seq int) (n: nat) (output: Seq.seq int)
  : Lemma
    (requires 
      Seq.length output == n /\
      all_valid_vertices_int output n /\
      is_topological_order_int adj n output)
    (ensures is_topological_order adj n (seq_int_to_nat output n))
  = let order_nat = seq_int_to_nat output n in
    let aux (u v: nat)
      : Lemma (requires has_edge n adj u v)
              (ensures appears_before order_nat u v)
      = assert (appears_before_int output u v);
        lemma_position_same_int_nat output order_nat n u;
        lemma_position_same_int_nat output order_nat n v
    in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)

#pop-options

(**
 * Summary theorem: The main proof obligation for P2.5.2
 *
 * IF the Pulse implementation maintains:
 * - strong_order_inv throughout execution
 * - distinctness of the output
 * - output is a permutation of 0..n-1
 *
 * THEN the output satisfies is_topological_order.
 *
 * All lemmas are fully proved, including:
 * 1. Pigeonhole principle: n distinct values in [0,n) is a permutation (line 253)
 * 2. Position finding is same for int vs nat sequences (line 377)
 *
 * The core correctness argument - that strong_order_inv implies topological
 * ordering - is fully proven without admits.
 *)
 
let theorem_kahns_algorithm_correct
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int)
  : Lemma
    (requires 
      n > 0 /\
      Seq.length output == n /\
      Seq.length adj == n * n /\
      all_distinct_int output /\
      all_valid_vertices_int output n /\
      strong_order_inv adj n output n)
    (ensures is_topological_order adj n (seq_int_to_nat output n))
  = lemma_strong_order_implies_topo_order_int adj n output;
    lemma_int_order_implies_nat_order adj n output

(**
 * DAG Completeness: Kahn's algorithm processes ALL vertices in a DAG.
 *
 * If every non-output vertex has positive remaining in-degree and the graph
 * is a DAG, then all vertices must be in the output.
 *
 * Proof: build backward predecessor chain. Walk with visited set.
 * After at most n steps we revisit a vertex, giving a directed cycle.
 * This contradicts the DAG property.
 *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* Backward chain: chain(0) = v0, chain(k+1) = predecessor of chain(k) *)
let rec build_chain_value
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat) (v0: nat) (k: nat)
  : Pure nat
    (requires
      v0 < n /\ count <= Seq.length output /\ Seq.length adj == n * n /\ n > 0 /\
      not (is_in_output output count v0) /\
      (forall (w: nat). w < n /\ not (is_in_output output count w) ==>
        count_remaining_preds adj n output count w n > 0))
    (ensures fun v -> v < n /\ not (is_in_output output count v))
    (decreases k)
  = if k = 0 then v0
    else
      let prev = build_chain_value adj n output count v0 (k - 1) in
      find_non_output_predecessor_full adj n output count prev

(* Consecutive chain values have a directed edge *)
let lemma_chain_edge
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat) (v0: nat) (k: nat)
  : Lemma
    (requires
      v0 < n /\ k < n /\ count <= Seq.length output /\ Seq.length adj == n * n /\ n > 0 /\
      not (is_in_output output count v0) /\
      (forall (w: nat). w < n /\ not (is_in_output output count w) ==>
        count_remaining_preds adj n output count w n > 0))
    (ensures has_edge n adj
      (build_chain_value adj n output count v0 (k + 1))
      (build_chain_value adj n output count v0 k))
  = ()

(* Chain subsequence gives has_path *)
let rec lemma_chain_has_path
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat) (v0: nat) (i j: nat)
  : Lemma
    (requires
      v0 < n /\ i <= j /\ j <= n /\ count <= Seq.length output /\ Seq.length adj == n * n /\ n > 0 /\
      not (is_in_output output count v0) /\
      (forall (w: nat). w < n /\ not (is_in_output output count w) ==>
        count_remaining_preds adj n output count w n > 0))
    (ensures has_path adj n
      (build_chain_value adj n output count v0 j)
      (build_chain_value adj n output count v0 i) (j - i))
    (decreases (j - i))
  = if j = i then ()
    else begin
      lemma_chain_edge adj n output count v0 (j - 1);
      if j - i > 1 then
        lemma_chain_has_path adj n output count v0 i (j - 1)
    end

#pop-options

(* Find duplicate in chain using boolean visited set.
   Walk positions 0, 1, ..., marking visited. Stop when a repeat is found.
   Terminates: count_visited increases each step until n, then pigeonhole forces repeat. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"

private let rec count_visited (visited: Seq.seq bool) (m: nat)
  : Pure nat (requires m <= Seq.length visited) (ensures fun c -> c <= m) (decreases m)
  = if m = 0 then 0
    else (if Seq.index visited (m - 1) then 1 else 0) + count_visited visited (m - 1)

private let rec lemma_count_visited_set (visited: Seq.seq bool) (m pos: nat)
  : Lemma
    (requires m <= Seq.length visited /\ pos < Seq.length visited /\ not (Seq.index visited pos))
    (ensures count_visited (Seq.upd visited pos true) m ==
      count_visited visited m + (if pos < m then 1 else 0))
    (decreases m)
  = if m = 0 then ()
    else lemma_count_visited_set visited (m - 1) pos

let rec find_chain_duplicate
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat) (v0: nat)
  (k: nat) (visited: Seq.seq bool)
  : Pure (nat & nat)
    (requires
      v0 < n /\ k <= n /\ count <= Seq.length output /\ Seq.length adj == n * n /\ n > 0 /\
      not (is_in_output output count v0) /\
      (forall (w: nat). w < n /\ not (is_in_output output count w) ==>
        count_remaining_preds adj n output count w n > 0) /\
      Seq.length visited == n /\
      count_visited visited n == k /\
      (forall (v: nat). v < n /\ Seq.index visited v ==>
        (exists (j: nat). j < k /\ build_chain_value adj n output count v0 j == v)) /\
      (forall (j: nat). j < k ==> Seq.index visited (build_chain_value adj n output count v0 j)))
    (ensures fun (i, j) ->
      i <= n /\ j <= n /\ i < j /\
      build_chain_value adj n output count v0 i ==
      build_chain_value adj n output count v0 j)
    (decreases (n - k))
  = let vk = build_chain_value adj n output count v0 k in
    if Seq.index visited vk then begin
      // vk already visited → find the earlier occurrence
      let rec find_earlier (p: nat)
        : Pure nat
          (requires p <= k /\
            (exists (j: nat). j >= p /\ j < k /\ build_chain_value adj n output count v0 j == vk))
          (ensures fun j -> j >= p /\ j < k /\
            build_chain_value adj n output count v0 j == vk)
          (decreases (k - p))
        = if build_chain_value adj n output count v0 p = vk then p
          else begin
            // The witness j from the precondition satisfies j >= p /\ j < k /\ bcv j == vk.
            // Since bcv p <> vk, j <> p, hence j >= p + 1.
            assert (exists (j: nat). j >= p + 1 /\ j < k /\ build_chain_value adj n output count v0 j == vk);
            find_earlier (p + 1)
          end
      in
      (find_earlier 0, k)
    end
    else begin
      // k < n (visited has k true entries out of n, found a false → k < n)
      let visited' = Seq.upd visited vk true in
      lemma_count_visited_set visited n vk;
      find_chain_duplicate adj n output count v0 (k + 1) visited'
    end

#pop-options

(* Main cycle lemma *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

let lemma_non_output_implies_cycle
  (adj: Seq.seq int) (n: nat) (output: Seq.seq int) (count: nat) (v0: nat)
  : Lemma
    (requires
      v0 < n /\ count <= Seq.length output /\ Seq.length adj == n * n /\ n > 0 /\
      not (is_in_output output count v0) /\
      (forall (w: nat). w < n /\ not (is_in_output output count w) ==>
        count_remaining_preds adj n output count w n > 0))
    (ensures has_cycle adj n)
  = let visited0 = Seq.create n false in
    let rec aux (m: nat)
      : Lemma (requires m <= n) (ensures count_visited (Seq.create n false) m == 0) (decreases m)
      = if m = 0 then () else aux (m - 1)
    in aux n;
    let (i, j) = find_chain_duplicate adj n output count v0 0 visited0 in
    lemma_chain_has_path adj n output count v0 i j;
    ()

#pop-options
