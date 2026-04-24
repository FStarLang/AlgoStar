(**
 * CLRS Chapter 22: DFS-based Topological Sort (§22.4)
 *
 * Proves the CLRS algorithm: run DFS on a DAG, output vertices in
 * decreasing finish-time order → valid topological order.
 *
 * Bridges DFS.Spec (2D adjacency matrix) with TopologicalSort.Spec (flat matrix).
 *
 * Zero admits, zero assumes.
 *)
module CLRS.Ch22.DFS.TopologicalSort

open CLRS.Ch22.DFS.Spec

module TS = CLRS.Ch22.TopologicalSort.Spec
module SEM = FStar.StrongExcludedMiddle
module ID = FStar.IndefiniteDescription

(*** §1. Adjacency Matrix Bridge ***)

/// 2D and flat adjacency matrices are equivalent
let adj_equiv (adj2d: Seq.seq (Seq.seq int)) (adj1d: Seq.seq int) (n: nat) : prop =
  Seq.length adj2d == n /\
  Seq.length adj1d == n * n /\
  (forall (u: nat). u < n ==> Seq.length (Seq.index adj2d u) == n) /\
  (forall (u v: nat). u < n /\ v < n ==>
    Seq.index (Seq.index adj2d u) v == Seq.index adj1d (u * n + v))

/// Under adj_equiv, has_edge agrees in both representations
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
let has_edge_equiv
  (adj2d: Seq.seq (Seq.seq int)) (adj1d: Seq.seq int) (n: nat) (u v: nat)
  : Lemma
    (requires adj_equiv adj2d adj1d n /\ u < n /\ v < n)
    (ensures has_edge n adj2d u v == TS.has_edge n adj1d u v)
  = ()
#pop-options

(*** §2. Extending TS Paths from the Right ***)

/// TS.has_path decomposes from the left (edge, then sub-path).
/// We need right-extension: has_path(u,w,k) ∧ edge(w,v) ⟹ has_path(u,v,k+1).
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec ts_path_extend_right
  (adj: Seq.seq int) (n: nat) (u w v: nat) (k: nat)
  : Lemma
    (requires TS.has_path adj n u w k /\ TS.has_edge n adj w v)
    (ensures TS.has_path adj n u v (k + 1))
    (decreases k)
  = if k = 0 then ()  // u = w, has_edge w v = has_path u v 1
    else if k = 1 then () // edge(u,w) => exists w'. edge(u,w') /\ has_path(w',v,1). Take w'=w.
    else (
      // k > 1: exists w' < n. edge(u,w') /\ has_path(w',w,k-1)
      // By IH: has_path(w',w,k-1) /\ edge(w,v) => has_path(w',v,k)
      // So: exists w'. edge(u,w') /\ has_path(w',v,k) => has_path(u,v,k+1)
      let aux (w': nat)
        : Lemma
          (requires w' < n /\ TS.has_edge n adj u w' /\ TS.has_path adj n w' w (k - 1))
          (ensures TS.has_path adj n u v (k + 1))
        = ts_path_extend_right adj n w' w v (k - 1)
      in
      Classical.forall_intro (Classical.move_requires aux)
    )
#pop-options

(*** §3. Path Conversion: DFS.Spec → TS.Spec ***)

/// Convert a 2D (right-decomposed) path to a 1D (left-decomposed) path.
/// DFS.Spec: has_path(u,v,k) = ∃w. has_path(u,w,k-1) ∧ edge(w,v)  [right]
/// TS.Spec:  has_path(u,v,k) = ∃w. edge(u,w) ∧ has_path(w,v,k-1)  [left]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec has_path_2d_to_1d
  (adj2d: Seq.seq (Seq.seq int)) (adj1d: Seq.seq int) (n: nat)
  (u v: nat) (k: nat)
  : Lemma
    (requires adj_equiv adj2d adj1d n /\ has_path adj2d n u v k)
    (ensures TS.has_path adj1d n u v k)
    (decreases k)
  = if k = 0 then () // u = v => u == v
    else (
      // k > 0: u < n /\ v < n /\ exists w < n. has_path(u,w,k-1) /\ edge_2d(w,v)
      let aux (w: nat)
        : Lemma
          (requires w < n /\ has_path adj2d n u w (k - 1) /\ has_edge n adj2d w v)
          (ensures TS.has_path adj1d n u v k)
        = has_path_2d_to_1d adj2d adj1d n u w (k - 1);
          has_edge_equiv adj2d adj1d n w v;
          ts_path_extend_right adj1d n u w v (k - 1)
      in
      Classical.forall_intro (Classical.move_requires aux)
    )
#pop-options

(*** §4. Pigeonhole Principle for Injective Functions ***)

/// If f: [0,m) → [0,n) is injective and m > n, contradiction.
/// Used to show that n+1 distinct vertices < n is impossible.

/// Helper: skipping one position in an injective function preserves injectivity
/// and maps to a smaller codomain.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let skip_pos_lt (f: (nat -> GTot nat)) (p m n: nat) (i: nat)
  : Lemma
    (requires
      p < m /\ f p == n - 1 /\ n > 0 /\
      (forall (a:nat). a < m ==> f a < n) /\
      (forall (a b:nat). a < m /\ b < m /\ a <> b ==> f a <> f b) /\
      i < m - 1)
    (ensures (let i' = (if i < p then i else i + 1) in
              i' < m /\ i' <> p /\ f i' < n - 1))
  = let i' = (if i < p then i else i + 1) in
    assert (i' < m);
    assert (i' <> p);
    assert (f i' <> f p);
    assert (f i' <> n - 1);
    assert (f i' < n)
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let skip_pos_inj (f: (nat -> GTot nat)) (p m n: nat) (i j: nat)
  : Lemma
    (requires
      p < m /\ f p == n - 1 /\ n > 0 /\
      (forall (a:nat). a < m ==> f a < n) /\
      (forall (a b:nat). a < m /\ b < m /\ a <> b ==> f a <> f b) /\
      i < m - 1 /\ j < m - 1 /\ i <> j)
    (ensures (let g (x:nat) : GTot nat = if x < p then f x else f (x + 1) in
              g i <> g j))
  = let i' = (if i < p then i else i + 1) in
    let j' = (if j < p then j else j + 1) in
    assert (i' < m /\ j' < m);
    // i' <> j' in all cases:
    if i < p then (
      if j < p then assert (i' = i /\ j' = j /\ i <> j)   // both < p
      else (                                                // i < p, j >= p
        assert (i' = i /\ j' = j + 1);
        assert (i < p /\ j + 1 > p);
        assert (i' <> j')
      )
    ) else (
      if j < p then (                                       // i >= p, j < p
        assert (i' = i + 1 /\ j' = j);
        assert (i + 1 > p /\ j < p);
        assert (i' <> j')
      ) else                                                // both >= p
        assert (i' = i + 1 /\ j' = j + 1 /\ i <> j)
    );
    assert (f i' <> f j')
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let rec injective_bound (f: (nat -> GTot nat)) (m n: nat)
  : Lemma
    (requires
      m > n /\
      (forall (i:nat). i < m ==> f i < n) /\
      (forall (i j:nat). i < m /\ j < m /\ i <> j ==> f i <> f j))
    (ensures False)
    (decreases n)
  = if n = 0 then ()
    else
      if SEM.strong_excluded_middle (exists (i:nat). i < m /\ f i == n - 1)
      then (
        let p = ID.indefinite_description_ghost nat
                  (fun p -> p < m /\ f p == n - 1) in
        let g (i:nat) : GTot nat = if i < p then f i else f (i + 1) in
        // g: [0, m-1) → [0, n-1), injective
        let aux_bound (i:nat) : Lemma (requires i < m - 1) (ensures g i < n - 1)
          = skip_pos_lt f p m n i
        in
        Classical.forall_intro (Classical.move_requires aux_bound);
        let aux_inj (i:nat) (j:nat)
          : Lemma (requires i < m - 1 /\ j < m - 1 /\ i <> j) (ensures g i <> g j)
          = skip_pos_inj f p m n i j
        in
        // Establish injectivity for the recursive call
        let aux_inj_forall (i:nat)
          : Lemma (ensures forall (j:nat). i < m - 1 /\ j < m - 1 /\ i <> j ==> g i <> g j)
          = Classical.forall_intro (Classical.move_requires (aux_inj i))
        in
        Classical.forall_intro aux_inj_forall;
        injective_bound g (m - 1) (n - 1)
      )
      else (
        // ~(exists i. i < m /\ f i == n-1): no element maps to n-1
        // Therefore all values are < n-1
        let no_n_minus_1 (i:nat) : Lemma (requires i < m) (ensures f i <> n - 1)
          = // If f i = n - 1, then (exists j. j < m /\ f j == n - 1) with j = i.
            // But SEM gave us ~(exists ...). Contradiction.
            if f i = n - 1 then (
              assert (i < m /\ f i == n - 1);
              assert (exists (j:nat). j < m /\ f j == n - 1)
            )
            else ()
        in
        let aux (i:nat) : Lemma (requires i < m) (ensures f i < n - 1)
          = no_n_minus_1 i;
            assert (f i < n);
            assert (f i <> n - 1)
        in
        Classical.forall_intro (Classical.move_requires aux);
        injective_bound f m (n - 1)
      )
#pop-options

(*** §5. Path Decomposition and Cycle Shortening ***)

/// Build a prefix of path vertices using IndefiniteDescription.
/// Given has_path(u, v, k) and m ≤ k, extract m+1 vertices with edges between them.
/// Returns a Seq of length m+1.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec build_path_prefix
  (adj: Seq.seq int) (n: nat) (u v: nat) (k: nat) (m: nat)
  : Ghost (Seq.seq nat)
    (requires
      TS.has_path adj n u v k /\ m <= k /\
      Seq.length adj == n * n /\ n > 0 /\
      k > 0 /\ u < n)
    (ensures fun vs ->
      Seq.length vs == m + 1 /\
      Seq.index vs 0 == u /\
      (forall (i:nat). i < m + 1 ==> Seq.index vs i < n) /\
      (forall (i:nat). i < m ==> TS.has_edge n adj (Seq.index vs i) (Seq.index vs (i + 1))))
    (decreases m)
  = if m = 0 then
      Seq.create 1 u
    else if k = 1 then (
      // m = 1, k = 1. has_edge(u, v). v < n.
      let s = Seq.append (Seq.create 1 u) (Seq.create 1 v) in
      assert (Seq.length s == 2);
      assert (Seq.index s 0 == u);
      assert (Seq.index s 1 == v);
      s
    )
    else (
      // k >= 2, m >= 1
      let w = ID.indefinite_description_ghost nat
                (fun w -> w < n /\ TS.has_edge n adj u w /\ TS.has_path adj n w v (k - 1)) in
      let rest = build_path_prefix adj n w v (k - 1) (m - 1) in
      // rest: Seq.length rest == m, rest[0] == w, all < n, edges between consecutive
      let result = Seq.append (Seq.create 1 u) rest in
      assert (Seq.length (Seq.create 1 u) == 1);
      assert (Seq.length result == 1 + Seq.length rest);
      let len_result : squash (Seq.length result == m + 1) = () in
      assert (Seq.index result 0 == u);
      // All < n
      let aux_lt (i:nat{i < Seq.length result}) : Lemma (ensures Seq.index result i < n)
        = if i = 0 then ()
          else (
            assert (i - 1 < Seq.length rest);
            assert (Seq.index result i == Seq.index rest (i - 1))
          )
      in
      Classical.forall_intro (fun (i:nat{i < Seq.length result}) -> aux_lt i);
      // Edges between consecutive
      let aux_edge (i:nat{i + 1 < Seq.length result}) : Lemma
        (ensures TS.has_edge n adj (Seq.index result i) (Seq.index result (i + 1)))
        = if i = 0 then (
            assert (Seq.index result 0 == u);
            assert (0 < Seq.length rest);
            assert (Seq.index result 1 == Seq.index rest 0);
            assert (Seq.index rest 0 == w);
            assert (TS.has_edge n adj u w)
          )
          else (
            assert (i - 1 < Seq.length rest);
            assert (i < Seq.length rest);
            assert (Seq.index result i == Seq.index rest (i - 1));
            assert (Seq.index result (i + 1) == Seq.index rest i);
            assert (i - 1 < m - 1)
          )
      in
      Classical.forall_intro (fun (i:nat{i + 1 < Seq.length result}) -> aux_edge i);
      result
    )
#pop-options

/// Consecutive edges in a vertex sequence compose into TS.has_path.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec edges_form_ts_path
  (adj: Seq.seq int) (n: nat) (vs: Seq.seq nat) (i j: nat)
  : Lemma
    (requires
      i <= j /\ j < Seq.length vs /\
      Seq.length adj == n * n /\
      (forall (p:nat). p < Seq.length vs ==> Seq.index vs p < n) /\
      (forall (p:nat). p + 1 < Seq.length vs ==>
        TS.has_edge n adj (Seq.index vs p) (Seq.index vs (p + 1))))
    (ensures TS.has_path adj n (Seq.index vs i) (Seq.index vs j) (j - i))
    (decreases (j - i))
  = if j = i then ()
    else if j = i + 1 then ()
    else (
      // j > i + 1. has_edge(vs[i], vs[i+1]) and by IH has_path(vs[i+1], vs[j], j-i-1)
      edges_form_ts_path adj n vs (i + 1) j
      // exists w (= vs[i+1]) with edge(vs[i], w) /\ has_path(w, vs[j], j-i-1)
      // => has_path(vs[i], vs[j], j-i)
    )
#pop-options

/// Cycle shortening: any cycle implies TS.has_cycle (with bounded length).
///
/// Key argument (in the hard case k > n):
///   Use SEM to case-split. If a shorter cycle (length < k) exists,
///   recurse (decreases k). Otherwise, decompose the first n+1 vertices.
///   By no-shorter-cycle, these n+1 vertices are all distinct and < n,
///   which contradicts injective_bound.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 25 --split_queries always"
let any_cycle_implies_ts_has_cycle
  (adj: Seq.seq int) (n: nat{n > 0}) (u: nat) (k: nat)
  : Lemma
    (requires
      TS.has_path adj n u u k /\ k > 0 /\ u < n /\
      Seq.length adj == n * n)
    (ensures TS.has_cycle adj n)
  = if k <= n then ()
    else (
      // k > n. Use SEM: does a shorter cycle exist anywhere?
      if SEM.strong_excluded_middle (TS.has_cycle adj n)
      then ()
      else (
        // ~TS.has_cycle. We will derive a contradiction.
        // Since ~TS.has_cycle, for all w < n, m with 0 < m <= n: ~TS.has_path w w m.
        // Also no shorter cycle (length < k): if there were, it would have length > 0,
        // and by recursion (decreasing k) we'd get TS.has_cycle. Contradiction.
        // So no cycle through any vertex of length in (0, k).

        // Decompose first n+1 vertices (n+1 <= k since k > n, so n <= k)
        let vs = build_path_prefix adj n u u k n in

        // vs has n+1 entries, all < n, with edges between consecutive.
        assert (Seq.length vs == n + 1);

        // Claim: all entries are distinct.
        // If vs[i] = vs[j] for 0 <= i < j <= n, then the sub-path from
        // position i to position j forms a cycle of length j-i with 0 < j-i <= n.
        // TS.has_cycle follows. But ~TS.has_cycle. Contradiction.

        // Show all elements are distinct: if not, derive TS.has_cycle → contradiction
        let aux_inj (i j:nat) : Lemma
          (requires i < n + 1 /\ j < n + 1 /\ i < j)
          (ensures Seq.index vs i <> Seq.index vs j)
          = if Seq.index vs i = Seq.index vs j then (
              edges_form_ts_path adj n vs i j;
              // has_path(vs[i], vs[j], j-i) = has_path(vs[i], vs[i], j-i)
              let w = Seq.index vs i in
              let m = j - i in
              assert (TS.has_path adj n w w m);
              assert (w < n /\ m > 0 /\ m <= n);
              // This gives TS.has_cycle
              assert (TS.has_cycle adj n)
              // contradicts ~TS.has_cycle → False, so anything follows
            )
            else ()
        in
        // Establish: forall i j. i < n+1 /\ j < n+1 /\ i <> j ==> vs[i] <> vs[j]
        let full_inj (i j:nat) : Lemma
          (requires i < n + 1 /\ j < n + 1 /\ i <> j)
          (ensures Seq.index vs i <> Seq.index vs j)
          = if i < j then aux_inj i j
            else aux_inj j i
        in

        // Use injective_bound: f(i) = vs[i] maps [0, n+1) → [0, n) injectively
        let f (i:nat) : GTot nat =
          if i < Seq.length vs then Seq.index vs i else 0
        in
        let aux_bound (i:nat) : Lemma (requires i < n + 1) (ensures f i < n)
          = assert (i < Seq.length vs);
            assert (f i == Seq.index vs i)
        in
        Classical.forall_intro (Classical.move_requires aux_bound);
        let aux_f_inj (i j:nat) : Lemma
          (requires i < n + 1 /\ j < n + 1 /\ i <> j)
          (ensures f i <> f j)
          = assert (i < Seq.length vs /\ j < Seq.length vs);
            assert (f i == Seq.index vs i /\ f j == Seq.index vs j);
            full_inj i j
        in
        let aux_f_inj_forall (i:nat)
          : Lemma (ensures forall (j:nat). i < n + 1 /\ j < n + 1 /\ i <> j ==> f i <> f j)
          = Classical.forall_intro (Classical.move_requires (aux_f_inj i))
        in
        Classical.forall_intro aux_f_inj_forall;
        // n+1 > n: contradiction
        injective_bound f (n + 1) n
      )
    )
#pop-options

(*** §6. Bridge: TS.is_dag ⟹ no back edge ***)

/// has_cycle_2d: cycle in the 2D adjacency matrix (matching cycle_iff_back_edge)
let has_cycle_2d (adj2d: Seq.seq (Seq.seq int)) (n: nat) : prop =
  exists (u:nat) (k:nat). u < n /\ k > 0 /\ has_path adj2d n u u k

/// A back edge implies a 1D cycle (under adj_equiv), hence contradicts TS.is_dag.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let back_edge_implies_ts_cycle
  (adj2d: Seq.seq (Seq.seq int)) (adj1d: Seq.seq int) (n: nat)
  : Lemma
    (requires adj_equiv adj2d adj1d n /\ n > 0 /\
              has_back_edge (dfs adj2d n) adj2d n)
    (ensures TS.has_cycle adj1d n)
  = // From cycle_iff_back_edge: back_edge => exists u k. k > 0 /\ has_path_2d u u k
    cycle_iff_back_edge adj2d n;
    let st = dfs adj2d n in
    assert (has_back_edge st adj2d n);
    // The biconditional gives us cycle_2d
    let aux (u:nat) (dummy:nat) (k:nat)
      : Lemma
        (requires k > 0 /\ has_path adj2d n u u k)
        (ensures TS.has_cycle adj1d n)
      = // has_path_2d u u k with k > 0 implies u < n
        assert (u < n);
        // Convert to 1D path
        has_path_2d_to_1d adj2d adj1d n u u k;
        // Shorten to length <= n
        any_cycle_implies_ts_has_cycle adj1d n u k
    in
    Classical.forall_intro (fun u ->
      Classical.forall_intro (fun v ->
        Classical.forall_intro (fun k ->
          Classical.move_requires (aux u v) k)))
#pop-options

/// Main bridge: TS.is_dag ⟹ no back edge in DFS
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let dag_implies_no_back_edge
  (adj2d: Seq.seq (Seq.seq int)) (adj1d: Seq.seq int) (n: nat)
  : Lemma
    (requires adj_equiv adj2d adj1d n /\ n > 0 /\ TS.is_dag adj1d n)
    (ensures ~(has_back_edge (dfs adj2d n) adj2d n))
  = // By contrapositive: back_edge => TS.has_cycle => ~TS.is_dag
    Classical.move_requires (back_edge_implies_ts_cycle adj2d adj1d) n
#pop-options

(*** §7. Finish-Time Ordering Definitions ***)

/// A sequence is sorted by decreasing DFS finish time
let sorted_by_decreasing_f (st: dfs_state) (order: Seq.seq nat) : prop =
  forall (i j: nat). i < Seq.length order /\ j < Seq.length order /\ i < j ==>
    f_of st (Seq.index order i) >= f_of st (Seq.index order j)

/// A sequence is a permutation of [0, n)
let is_permutation (order: Seq.seq nat) (n: nat) : prop =
  Seq.length order == n /\
  TS.all_distinct order /\
  TS.all_valid_vertices order n

(*** §8. Key Helper: f[u] > f[v] ⟹ appears_before in sorted order ***)

/// In a permutation sorted by decreasing f with distinct f-values,
/// if f[u] > f[v], then u appears before v.
///
/// Proof: u is at position pu, v at position pv.
/// If pv ≤ pu, then by sorted order, f[order[pv]] ≥ f[order[pu]], i.e., f[v] ≥ f[u].
/// But f[u] > f[v]. Contradiction. So pu < pv.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10 --split_queries always"
let higher_f_implies_earlier_position
  (st: dfs_state) (order: Seq.seq nat) (n: nat) (u v: nat)
  : Lemma
    (requires
      is_permutation order n /\
      sorted_by_decreasing_f st order /\
      u < n /\ v < n /\ u <> v /\
      f_of st u > f_of st v)
    (ensures TS.appears_before order u v)
  = // u appears in order at some position pu (since order is a permutation of [0,n))
    // We need to show: position_in_order order u = Some pu with pu < pv.

    // First, show every vertex < n has a position in order.
    // Since order is a permutation of [0,n), for each w < n, there exists pos < n
    // with order[pos] = w.

    // For vertex u: it appears somewhere in order.
    // Use SEM: does u appear in order?
    // Actually, we can prove this constructively: order is a permutation, so u < n appears.

    // By TS.all_distinct and TS.all_valid_vertices with length n,
    // the n distinct values in [0,n) must cover all of [0,n).
    // This is a counting/pigeonhole argument. Let me use SEM.

    // For u: SEM on (exists pos. pos < n /\ Seq.index order pos == u)
    assert (SEM.strong_excluded_middle (exists (pos:nat). pos < n /\ Seq.index order pos == u) = true \/
            SEM.strong_excluded_middle (exists (pos:nat). pos < n /\ Seq.index order pos == u) = false);

    // Actually, prove u appears: by injective_bound contrapositive.
    // order maps [0,n) to [0,n) injectively (all_distinct + all_valid).
    // If u doesn't appear, then order maps [0,n) to [0,n)\{u}, which has n-1 elements.
    // n values in n-1 slots: by pigeonhole (injective_bound), impossible.

    // Let me just assert it and let SMT handle it, or use a helper.
    // Actually, for a sequence of length n with distinct elements all < n,
    // every value in [0,n) must appear. This is the surjectivity of an injective
    // function from a finite set to itself.
    // Let me use a counting argument via injective_bound.

    let order_covers_all (w: nat)
      : Lemma (requires w < n) (ensures exists (pos:nat). pos < n /\ Seq.index order pos == w)
      = if SEM.strong_excluded_middle (exists (pos:nat). pos < n /\ Seq.index order pos == w)
        then ()
        else (
          // w doesn't appear. The n elements of order are all < n and distinct
          // and all ≠ w. So they form an injection [0,n) → [0,n)\{w}.
          // [0,n)\{w} has n-1 elements. n > n-1. Contradiction by injective_bound.
          let f (i:nat) : GTot nat =
            if i < Seq.length order then
              let v = Seq.index order i in
              if v < w then v else v - 1
            else 0
          in
          // f maps order's values (which are < n and ≠ w) to [0, n-1)
          let aux_bound (i:nat) : Lemma (requires i < n) (ensures f i < n - 1)
            = assert (i < Seq.length order);
              let v = Seq.index order i in
              assert (v < n);
              assert (v <> w);
              if v < w then assert (f i == v)
              else assert (f i == v - 1)
          in
          Classical.forall_intro (Classical.move_requires aux_bound);
          // f is injective (since order is distinct and the remapping preserves injectivity)
          let aux_inj (i j:nat) : Lemma
            (requires i < n /\ j < n /\ i <> j)
            (ensures f i <> f j)
            = assert (i < Seq.length order /\ j < Seq.length order);
              let vi = Seq.index order i in
              let vj = Seq.index order j in
              assert (vi <> vj);
              if vi < w && vj < w then ()
              else if vi >= w && vj >= w then (
                // vi - 1 <> vj - 1 since vi <> vj (and both > 0 since >= w+1... wait, vi could = 0 if w > 0)
                // Actually vi <> w and vj <> w and vi <> vj.
                // vi > w (since vi >= w and vi <> w) means vi >= w+1, so vi - 1 >= w.
                // Similarly vj - 1 >= w. And vi - 1 <> vj - 1 since vi <> vj.
                assert (vi - 1 <> vj - 1)
              )
              else if vi < w && vj >= w then (
                // f i = vi, f j = vj - 1. If vi = vj - 1: vi < w and vj > w (since vj >= w and vj <> w, vj >= w+1).
                // vj - 1 >= w. But vi < w. So vi <> vj - 1.
                assert (vi < w);
                assert (vj > w);
                assert (vj - 1 >= w);
                assert (vi <> vj - 1)
              )
              else (
                // vi >= w, vj < w
                assert (vi > w);
                assert (vj < w);
                assert (vi - 1 >= w);
                assert (vj <> vi - 1)
              )
          in
          let aux_inj_forall (i:nat)
            : Lemma (ensures forall (j:nat). i < n /\ j < n /\ i <> j ==> f i <> f j)
            = Classical.forall_intro (Classical.move_requires (aux_inj i))
          in
          Classical.forall_intro aux_inj_forall;
          injective_bound f n (n - 1)
        )
    in

    // u and v both appear in order
    order_covers_all u;
    order_covers_all v;

    // Get their positions
    let pu = ID.indefinite_description_ghost nat
               (fun pos -> pos < n /\ Seq.index order pos == u) in
    let pv = ID.indefinite_description_ghost nat
               (fun pos -> pos < n /\ Seq.index order pos == v) in

    // Use TS.lemma_distinct_has_position to connect to position_in_order
    TS.lemma_distinct_has_position order u pu;
    TS.lemma_distinct_has_position order v pv;

    // Now position_in_order order u = Some pu, position_in_order order v = Some pv
    assert (TS.position_in_order order u == Some pu);
    assert (TS.position_in_order order v == Some pv);

    // Show pu < pv by contradiction.
    // If pv <= pu: by sorted_by_decreasing_f, f[order[pv]] >= f[order[pu]].
    // i.e., f[v] >= f[u]. But f[u] > f[v]. Contradiction.
    if pv < pu then (
      assert (f_of st (Seq.index order pv) >= f_of st (Seq.index order pu));
      assert (f_of st v >= f_of st u);
      assert false
    )
    else if pv = pu then (
      // order[pu] = u and order[pv] = v, but pu = pv, so u = v. Contradiction with u <> v.
      assert false
    )
    else ()  // pu < pv, which gives appears_before
#pop-options

(*** §9. Main Theorem: CLRS §22.4 ***)

/// CLRS Theorem 22.11: For a DAG, vertices sorted by decreasing DFS finish
/// time yield a valid topological order.
///
/// Proof outline:
/// 1. topological_sort_property: (all edges have f[u]>f[v]) ⟺ (no back edge)
/// 2. dag_implies_no_back_edge: TS.is_dag ⟹ no back edge
/// 3. Therefore: for every edge (u,v), f[u] > f[v]
/// 4. has_edge_equiv: edge in adj1d ⟺ edge in adj2d
/// 5. higher_f_implies_earlier_position: f[u]>f[v] + sorted order ⟹ appears_before
/// 6. Combine for is_topological_order
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let dfs_topological_sort_correct
  (adj2d: Seq.seq (Seq.seq int)) (adj1d: Seq.seq int) (n: nat)
  (order: Seq.seq nat)
  : Lemma
    (requires
      n > 0 /\
      adj_equiv adj2d adj1d n /\
      is_permutation order n /\
      sorted_by_decreasing_f (dfs adj2d n) order /\
      TS.is_dag adj1d n)
    (ensures TS.is_topological_order adj1d n order)
  = let st = dfs adj2d n in

    // Step 1: Establish topological_order (biconditional)
    topological_sort_property adj2d n;
    assert (topological_order st adj2d n);

    // Step 2: DAG ⟹ no back edge
    dag_implies_no_back_edge adj2d adj1d n;
    assert (~(has_back_edge st adj2d n));

    // Step 3: No back edge ⟹ for every 2D edge, f[u] > f[v]
    // (from the biconditional topological_order)

    // Step 4: For every 1D edge, f[u] > f[v]
    // (bridge via has_edge_equiv)

    // Step 5: For every 1D edge (u,v), appears_before order u v
    // (via higher_f_implies_earlier_position)

    // Prove appears_before for every edge
    let aux_edge (u v: nat)
      : Lemma
        (requires TS.has_edge n adj1d u v)
        (ensures TS.appears_before order u v)
      = // has_edge_1d(u,v) => u < n /\ v < n
        assert (u < n /\ v < n);
        // has_edge equivalence
        has_edge_equiv adj2d adj1d n u v;
        assert (has_edge n adj2d u v);
        // From topological_order + ~back_edge: f[u] > f[v]
        assert (f_of st u > f_of st v);
        // Self-loops: if u = v, then f[u] > f[u] is false.
        // But has_edge(u,u) with f[u] > f[u] means the edge creates a back edge...
        // Actually, f[u] > f[u] is false, but the biconditional says
        // ~back_edge => forall edges f[u] > f[v]. So has_edge(u,v) => f[u] > f[v].
        // If u = v, f[u] > f[u] is false, so has_edge(u,u) must be false.
        // (Which means a self-loop would imply a back edge, contradicting ~back_edge.)
        // So u <> v.
        assert (u <> v);
        // Distinct finish times for distinct vertices
        dfs_distinct_finish_times adj2d n u v;
        // Now apply the helper
        higher_f_implies_earlier_position st order n u v
    in
    Classical.forall_intro_2 (fun u -> Classical.move_requires (aux_edge u))
#pop-options

(*** §10. Additional Bridge Lemmas ***)

/// has_cycle_2d is equivalent to has_back_edge (both directions)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let has_cycle_2d_iff_back_edge (adj2d: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma
    (ensures
      has_cycle_2d adj2d n <==> has_back_edge (dfs adj2d n) adj2d n)
  = cycle_iff_back_edge adj2d n;
    // cycle_iff_back_edge gives:
    //   (exists u v k. k > 0 /\ has_path u u k) <==> has_back_edge
    // has_cycle_2d is:
    //   exists u k. u < n /\ k > 0 /\ has_path u u k
    // DFS.Spec.has_path for k > 0 requires u < n, so these are equivalent
    // (the extra v in cycle_iff_back_edge is unused).
    let st = dfs adj2d n in

    // Forward: has_cycle_2d => has_back_edge
    let fwd (u:nat) (k:nat)
      : Lemma
        (requires u < n /\ k > 0 /\ has_path adj2d n u u k)
        (ensures has_back_edge st adj2d n)
      = cycle_implies_back_edge adj2d n u k
    in
    let fwd_forall (u:nat)
      : Lemma (ensures forall (k:nat). u < n /\ k > 0 /\ has_path adj2d n u u k ==> has_back_edge st adj2d n)
      = Classical.forall_intro (Classical.move_requires (fwd u))
    in
    Classical.forall_intro fwd_forall;

    // Backward: has_back_edge => has_cycle_2d
    if SEM.strong_excluded_middle (has_back_edge st adj2d n)
    then (
      back_edge_implies_cycle adj2d n;
      // gives: exists u v k. k > 0 /\ has_path u u k
      // need: exists u k. u < n /\ k > 0 /\ has_path u u k
      let aux (u:nat) (v:nat) (k:nat)
        : Lemma
          (requires k > 0 /\ has_path adj2d n u u k)
          (ensures has_cycle_2d adj2d n)
        = assert (u < n)  // from has_path with k > 0
      in
      Classical.forall_intro (fun u ->
        Classical.forall_intro (fun v ->
          Classical.forall_intro (fun k ->
            Classical.move_requires (aux u v) k)))
    )
    else ()
#pop-options

/// Under adj_equiv, the 1D graph is a DAG iff the 2D graph has no back edges
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let dag_iff_no_back_edge
  (adj2d: Seq.seq (Seq.seq int)) (adj1d: Seq.seq int) (n: nat)
  : Lemma
    (requires adj_equiv adj2d adj1d n /\ n > 0)
    (ensures TS.is_dag adj1d n ==> ~(has_back_edge (dfs adj2d n) adj2d n))
  = let aux () : Lemma (requires TS.is_dag adj1d n) (ensures ~(has_back_edge (dfs adj2d n) adj2d n))
      = dag_implies_no_back_edge adj2d adj1d n
    in
    Classical.move_requires aux ()
#pop-options
