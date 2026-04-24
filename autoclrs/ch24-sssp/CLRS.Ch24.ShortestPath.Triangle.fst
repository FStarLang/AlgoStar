module CLRS.Ch24.ShortestPath.Triangle

(*
   Stabilization of sp_dist_k and Triangle Inequality for Non-Negative Weights

   Main results:
   1. sp_dist_k_stabilize:
        For non-negative weights, sp_dist_k(v, n) == sp_dist_k(v, n−1).
        Proof by pigeonhole: if the n-th iteration still improves a distance,
        there exists a chain of n+1 predecessor vertices; pigeonhole gives a
        repeated vertex; the resulting cycle has non-negative weight and can
        be contracted — contradiction.

   2. sp_dist_triangle_ineq:
        For non-negative weights, sp_dist(s, v) ≤ sp_dist(s, u) + w(u, v).
        This is the triangle inequality on the shortest-path metric, which is
        the key lemma enabling Dijkstra's "no underestimate" property.

   Uses FStar.Fin.pigeonhole and builds auxiliary chain_vertex / chain_seq
   constructions for the contraction argument.
*)

open FStar.List.Tot
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec

let inf = SP.inf

// ============================================================
// Part 1: sp_dist_k considers each predecessor (shifted triangle)
// ============================================================

// min_over_predecessors is <= any specific candidate it considers
let rec min_over_predecessors_le_candidate
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat{k > 0})
  (best: int) (u0 u: nat)
  : Lemma
    (requires u >= u0 /\ u < n /\ u * n + v < Seq.length weights /\
             SP.sp_dist_k weights n s u (k-1) < inf /\
             Seq.index weights (u * n + v) < inf)
    (ensures SP.min_over_predecessors weights n s v k best u0 <=
             SP.sp_dist_k weights n s u (k-1) + Seq.index weights (u * n + v))
    (decreases (n - u0))
  = if u0 >= n then ()
    else begin
      let w = if u0 * n + v < Seq.length weights then Seq.index weights (u0 * n + v) else inf in
      let via_u0 = SP.sp_dist_k weights n s u0 (k - 1) in
      let candidate = if via_u0 < inf && w < inf then via_u0 + w else inf in
      let new_best = if candidate < best then candidate else best in
      if u0 = u then begin
        assert (candidate == SP.sp_dist_k weights n s u (k-1) + Seq.index weights (u * n + v));
        assert (new_best <= candidate);
        SP.min_over_predecessors_improves weights n s v k new_best (u0 + 1)
      end else
        min_over_predecessors_le_candidate weights n s v k new_best (u0 + 1) u
    end

// sp_dist_k(s, v, k+1) <= sp_dist_k(s, u, k) + w(u, v) — the "shifted" triangle inequality
let sp_dist_k_via_predecessor
  (weights: Seq.seq int) (n: nat) (s u v: nat) (k: nat)
  : Lemma
    (requires n > 0 /\ u < n /\ v < n /\ s < n /\
             Seq.length weights == n * n /\
             SP.sp_dist_k weights n s u k < inf /\
             Seq.index weights (u * n + v) < inf)
    (ensures SP.sp_dist_k weights n s v (k + 1) <=
             SP.sp_dist_k weights n s u k + Seq.index weights (u * n + v))
  = let without = SP.sp_dist_k weights n s v k in
    min_over_predecessors_le_candidate weights n s v (k+1) without 0 u;
    SP.min_over_predecessors_improves weights n s v (k+1) without 0

// ============================================================
// Part 2: sp_dist_k non-negativity for non-negative weights
// ============================================================

let rec min_over_predecessors_non_neg
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat{k > 0})
  (best: int) (u: nat)
  : Lemma
    (requires best >= 0 /\
             (forall (i:nat). i < Seq.length weights ==> Seq.index weights i >= 0) /\
             (forall (u':nat). u' < n ==> SP.sp_dist_k weights n s u' (k-1) >= 0))
    (ensures SP.min_over_predecessors weights n s v k best u >= 0)
    (decreases (n - u))
  = if u >= n then ()
    else begin
      let w = if u * n + v < Seq.length weights then Seq.index weights (u * n + v) else inf in
      let via_u = SP.sp_dist_k weights n s u (k - 1) in
      let candidate = if via_u < inf && w < inf then via_u + w else inf in
      let new_best = if candidate < best then candidate else best in
      assert (new_best >= 0);
      min_over_predecessors_non_neg weights n s v k new_best (u + 1)
    end

let rec sp_dist_k_non_neg
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat)
  : Lemma
    (requires (forall (i:nat). i < Seq.length weights ==> Seq.index weights i >= 0))
    (ensures SP.sp_dist_k weights n s v k >= 0)
    (decreases %[k; 1])
  = if k = 0 then ()
    else begin
      sp_dist_k_non_neg weights n s v (k - 1);
      let without = SP.sp_dist_k weights n s v (k - 1) in
      assert (without >= 0);
      // Need: forall u'. u' < n ==> sp_dist_k(s, u', k-1) >= 0
      let aux (u': nat) : Lemma (requires u' < n) (ensures SP.sp_dist_k weights n s u' (k-1) >= 0)
        = sp_dist_k_non_neg weights n s u' (k - 1) in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      min_over_predecessors_non_neg weights n s v k without 0
    end

// sp_dist(s, s) == 0 for non-negative weights
let sp_dist_self_zero
  (weights: Seq.seq int) (n source: nat)
  : Lemma
    (requires n > 0 /\ source < n /\ Seq.length weights == n * n /\
             (forall (i:nat). i < Seq.length weights ==> Seq.index weights i >= 0))
    (ensures SP.sp_dist weights n source source == 0)
  = // sp_dist_k(s, s, 0) = 0. By monotonicity, sp_dist(s,s) <= 0. By non-negativity, >= 0.
    sp_dist_k_non_neg weights n source source (n - 1);
    let rec mono (k: nat) : Lemma (ensures SP.sp_dist_k weights n source source k <= 0) (decreases k)
      = if k = 0 then () else begin
          mono (k - 1);
          SP.sp_dist_k_monotone weights n source source (k - 1)
        end
    in
    mono (n - 1)

// ============================================================
// Part 3: sp_dist_k stabilization (chain + pigeonhole argument)
// ============================================================

module Fin = FStar.Fin

// Monotonicity extended to multiple steps
let rec sp_dist_k_monotone_multi
  (weights: Seq.seq int) (n: nat) (s v: nat) (k1 k2: nat)
  : Lemma (requires k1 >= k2)
          (ensures SP.sp_dist_k weights n s v k1 <= SP.sp_dist_k weights n s v k2)
          (decreases (k1 - k2))
  = if k1 = k2 then ()
    else begin
      SP.sp_dist_k_monotone weights n s v (k1 - 1);
      sp_dist_k_monotone_multi weights n s v (k1 - 1) k2
    end

// When min_over_predecessors improves on best, find a witness predecessor
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
[@@"opaque_to_smt"]
let rec find_improving_predecessor
  (weights: Seq.seq int) (n: pos) (s v: Fin.under n) (k: nat{k > 0})
  (best: int) (u0: nat)
  : Ghost (Fin.under n)
    (requires Seq.length weights == n * n /\
              best <= inf /\
              SP.min_over_predecessors weights n s v k best u0 < best)
    (ensures fun u ->
      SP.sp_dist_k weights n s u (k-1) < inf /\
      Seq.index weights (u * n + v) < inf /\
      SP.sp_dist_k weights n s u (k-1) + Seq.index weights (u * n + v) <=
        SP.min_over_predecessors weights n s v k best u0)
    (decreases (n - u0))
  = if u0 >= n then begin
      assert false; 0
    end else begin
      assert (u0 * n + v < n * n);
      let w = Seq.index weights (u0 * n + v) in
      let via_u0 = SP.sp_dist_k weights n s u0 (k - 1) in
      let candidate = if via_u0 < inf && w < inf then via_u0 + w else inf in
      if candidate < best then begin
        // candidate < best <= inf, so candidate <= inf
        SP.min_over_predecessors_improves weights n s v k candidate (u0 + 1);
        if SP.min_over_predecessors weights n s v k candidate (u0 + 1) < candidate then
          find_improving_predecessor weights n s v k candidate (u0 + 1)
        else
          u0
      end else begin
        SP.min_over_predecessors_improves weights n s v k best (u0 + 1);
        find_improving_predecessor weights n s v k best (u0 + 1)
      end
    end
#pop-options

// Build the chain of improving predecessors.
// chain_vertex(0) = v, chain_vertex(m+1) = predecessor of chain_vertex(m).
// Property: chain_vertex(m) has strict improvement at level (n-m).
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec chain_vertex
  (weights: Seq.seq int) (n: pos) (s v: Fin.under n) (m: nat)
  : Ghost (Fin.under n)
    (requires m <= n /\ Seq.length weights == n * n /\
              (forall (i:nat). i < n * n ==> Seq.index weights i >= 0) /\
              SP.sp_dist_k weights n s v n < SP.sp_dist_k weights n s v (n - 1))
    (ensures fun c ->
      SP.sp_dist_k weights n s c (n - m) < inf /\
      (m < n ==> SP.sp_dist_k weights n s c (n - m) < SP.sp_dist_k weights n s c (n - m - 1)))
    (decreases m)
  = if m = 0 then begin
      SP.sp_dist_k_bounded weights n s v (n - 1);
      v
    end
    else begin
      let prev = chain_vertex weights n s v (m - 1) in
      SP.sp_dist_k_bounded weights n s prev (n - m);
      let c = find_improving_predecessor weights n s prev (n - m + 1) 
                (SP.sp_dist_k weights n s prev (n - m)) 0 in
      if m < n then begin
        SP.sp_dist_k_bounded weights n s c (n - m - 1);
        if SP.sp_dist_k weights n s c (n - m - 1) < inf then
          SP.sp_dist_k_triangle weights n s c prev (n - m)
      end;
      c
    end
#pop-options

// B-inequality: we re-derive chain_vertex(m+1) to get the B-property
#push-options "--z3rlimit 20 --fuel 2 --ifuel 0"
let chain_B_property
  (weights: Seq.seq int) (n: pos) (s v: Fin.under n) (m: nat)
  : Lemma
    (requires m < n /\ Seq.length weights == n * n /\
              (forall (i:nat). i < n * n ==> Seq.index weights i >= 0) /\
              SP.sp_dist_k weights n s v n < SP.sp_dist_k weights n s v (n - 1))
    (ensures (
      let prev = chain_vertex weights n s v m in
      let next = chain_vertex weights n s v (m + 1) in
      SP.sp_dist_k weights n s next (n - m - 1) + Seq.index weights (next * n + prev) 
        <= SP.sp_dist_k weights n s prev (n - m) /\
      Seq.index weights (next * n + prev) >= 0))
  = let prev = chain_vertex weights n s v m in
    let next = chain_vertex weights n s v (m + 1) in
    SP.sp_dist_k_bounded weights n s prev (n - m - 1);
    SP.sp_dist_k_bounded weights n s prev (n - m);
    // chain_vertex(m+1) unfolds to find_improving_predecessor(prev, n-m, sp_dist_k(s,prev,n-m-1), 0)
    // find_improving_predecessor (opaque) gives:
    //   sp_dist_k(s, next, n-m-1) + w(next, prev) <= min_over_predecessors(sp_dist_k(s,prev,n-m-1), 0)
    //   = sp_dist_k(s, prev, n-m) [by definition of sp_dist_k]
    ()
#pop-options

// Telescoping: sp_dist_k(s, chain[i], n-i) >= sp_dist_k(s, chain[j], n-j) for i < j
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let rec chain_telescoping
  (weights: Seq.seq int) (n: pos) (s v: Fin.under n) (i j: nat)
  : Lemma
    (requires i < j /\ j <= n /\ Seq.length weights == n * n /\
              (forall (k:nat). k < n * n ==> Seq.index weights k >= 0) /\
              SP.sp_dist_k weights n s v n < SP.sp_dist_k weights n s v (n - 1))
    (ensures SP.sp_dist_k weights n s (chain_vertex weights n s v i) (n - i) >=
             SP.sp_dist_k weights n s (chain_vertex weights n s v j) (n - j))
    (decreases (j - i))
  = if j = i + 1 then
      chain_B_property weights n s v i
    else begin
      chain_B_property weights n s v (j - 1);
      chain_telescoping weights n s v i (j - 1)
    end
#pop-options

// Build the chain as a sequence for pigeonhole
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec build_chain_seq
  (weights: Seq.seq int) (n: pos) (s v: Fin.under n) (len: nat)
  : Ghost (Seq.seq (Fin.under n))
    (requires len <= n + 1 /\ Seq.length weights == n * n /\
              (forall (i:nat). i < n * n ==> Seq.index weights i >= 0) /\
              SP.sp_dist_k weights n s v n < SP.sp_dist_k weights n s v (n - 1))
    (ensures fun seq -> Seq.length seq == len /\
      (forall (i: nat). i < len ==> Seq.index seq i == chain_vertex weights n s v i))
    (decreases len)
  = if len = 0 then Seq.empty #(Fin.under n)
    else begin
      let prev_seq = build_chain_seq weights n s v (len - 1) in
      let last_v : Fin.under n = chain_vertex weights n s v (len - 1) in
      let suffix : Seq.seq (Fin.under n) = Seq.create 1 last_v in
      let result = Seq.append prev_seq suffix in
      assert (Seq.length result == Seq.length prev_seq + 1);
      assert (Seq.length result == len);
      let aux (i: nat{i < len}) 
        : Lemma (Seq.index result i == chain_vertex weights n s v i)
        = if i < len - 1 then begin
            Seq.lemma_index_app1 prev_seq suffix i;
            assert (Seq.index result i == Seq.index prev_seq i)
          end else begin
            Seq.lemma_index_app2 prev_seq suffix i;
            assert (Seq.index result i == Seq.index suffix (i - Seq.length prev_seq));
            assert (i - Seq.length prev_seq == 0);
            assert (Seq.index result i == last_v)
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      result
    end
#pop-options

// Main stabilization lemma
#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"
let sp_dist_k_stabilize
  (weights: Seq.seq int) (n: nat) (s v: nat)
  : Lemma
    (requires n > 0 /\ s < n /\ v < n /\ Seq.length weights == n * n /\
             (forall (i:nat). i < Seq.length weights ==> Seq.index weights i >= 0))
    (ensures SP.sp_dist_k weights n s v n == SP.sp_dist_k weights n s v (n - 1))
  = SP.sp_dist_k_monotone weights n s v (n - 1);
    if SP.sp_dist_k weights n s v n < SP.sp_dist_k weights n s v (n - 1) then begin
      // Build chain of n+1 vertices and apply pigeonhole
      let chain_seq = build_chain_seq weights n s v (n + 1) in
      let (i, j) = Fin.pigeonhole #n chain_seq in
      // i < j, chain[i] = chain[j], both < n+1
      let x = chain_vertex weights n s v i in
      assert (x == chain_vertex weights n s v j);
      // Telescoping: sp_dist_k(s, x, n-i) >= sp_dist_k(s, x, n-j)
      chain_telescoping weights n s v i j;
      // Monotonicity: sp_dist_k(s, x, n-i) <= sp_dist_k(s, x, n-j) since n-i > n-j
      sp_dist_k_monotone_multi weights n s x (n - i) (n - j);
      // So sp_dist_k(s, x, n-i) == sp_dist_k(s, x, n-j)
      // And sp_dist_k(s, x, n-i-1) is squeezed between:
      sp_dist_k_monotone_multi weights n s x (n - i) (n - i - 1);
      sp_dist_k_monotone_multi weights n s x (n - i - 1) (n - j);
      // sp_dist_k(s, x, n-i) <= sp_dist_k(s, x, n-i-1) <= sp_dist_k(s, x, n-j) = sp_dist_k(s, x, n-i)
      // So sp_dist_k(s, x, n-i) = sp_dist_k(s, x, n-i-1)
      // But strict improvement at i: sp_dist_k(s, x, n-i) < sp_dist_k(s, x, n-i-1). Contradiction!
      assert (SP.sp_dist_k weights n s x (n - i) < SP.sp_dist_k weights n s x (n - i - 1));
      assert (SP.sp_dist_k weights n s x (n - i) == SP.sp_dist_k weights n s x (n - i - 1));
      assert false
    end
#pop-options

let sp_dist_triangle_ineq
  (weights: Seq.seq int) (n source u v: nat)
  : Lemma
    (requires
      n > 0 /\ u < n /\ v < n /\ source < n /\
      Seq.length weights == n * n /\
      (forall (i:nat). i < Seq.length weights ==> Seq.index weights i >= 0) /\
      Seq.index weights (u * n + v) < inf /\
      SP.sp_dist weights n source u < inf)
    (ensures SP.sp_dist weights n source v <=
             SP.sp_dist weights n source u + Seq.index weights (u * n + v))
  = // sp_dist(s,v) = sp_dist_k(s,v,n-1)
    // sp_dist_k(s,v,n) <= sp_dist_k(s,u,n-1) + w(u,v) = sp_dist(s,u) + w(u,v)
    // sp_dist_k(s,v,n) == sp_dist_k(s,v,n-1) (stabilization)
    // Therefore sp_dist(s,v) <= sp_dist(s,u) + w(u,v)
    sp_dist_k_via_predecessor weights n source u v (n - 1);
    sp_dist_k_stabilize weights n source v
