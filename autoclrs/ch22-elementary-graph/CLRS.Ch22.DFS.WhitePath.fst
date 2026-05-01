(**
 * CLRS Chapter 22: White-Path Theorem (CLRS Theorem 22.9)
 *
 * Theorem 22.9: In a depth-first forest of graph G, vertex v is a descendant
 * of vertex u if and only if at the time d[u] that the search discovers u,
 * there is a path from u to v consisting entirely of white vertices.
 *
 * This module formalizes the White-Path Theorem and provides the key
 * definitions needed to state and prove it.
 *)
module CLRS.Ch22.DFS.WhitePath

open CLRS.Ch22.DFS.Spec

(*** Core Definitions ***)

(**
 * Definition 1: DFS Ancestor Relation
 *
 * Vertex v is a descendant of vertex u in the DFS tree if and only if
 * v's timestamp interval is contained within u's interval:
 *   d[u] < d[v] < f[v] < f[u]
 *
 * This follows from the Parenthesis Theorem (CLRS Theorem 22.7).
 *)
let dfs_ancestor (d f: Seq.seq nat) (u v: nat) : prop =
  u < Seq.length d && v < Seq.length d &&
  u < Seq.length f && v < Seq.length f &&
  (let du = Seq.index d u in
   let dv = Seq.index d v in
   let fu = Seq.index f u in
   let fv = Seq.index f v in
   // v's interval [d[v], f[v]] is strictly contained in u's interval [d[u], f[u]]
   du < dv && dv < fv && fv < fu)

(**
 * Definition 2: White at Time
 *
 * A vertex v is white (undiscovered) at a given time if:
 *   - Either the vertex has never been discovered (d[v] = 0), or
 *   - The current time is before the vertex's discovery time (time < d[v])
 *
 * We model this using a function color_at : nat -> Seq.seq color that
 * gives the color of each vertex at each time.
 *)
let white_at_time (d: Seq.seq nat) (v: nat) (time: nat) : prop =
  v < Seq.length d /\
  (let dv = Seq.index d v in
   dv = 0 \/ time < dv)

(**
 * Helper: All intermediate vertices on a path are white
 *
 * This predicate states that there exists a path from u to v where
 * all intermediate vertices (not including u, but including v) are white
 * at the specified time.
 *)
let rec path_all_white 
  (adj: Seq.seq (Seq.seq int))
  (n: nat) 
  (d: Seq.seq nat)
  (u v: nat) 
  (time: nat)
  (steps: nat)
  : Tot prop (decreases steps)
  = if steps = 0 then 
      // Base case: path of length 0 means u = v
      u = v /\ white_at_time d v time
    else if steps = 1 then
      // Path of length 1: direct edge u -> v, and v is white
      has_edge n adj u v /\ white_at_time d v time
    else
      // Path of length > 1: u -> w -> ... -> v
      // where w is white and there's a white path from w to v
      u < n /\ v < n /\
      (exists (w: nat). 
        w < n /\ 
        has_edge n adj u w /\
        white_at_time d w time /\
        path_all_white adj n d w v time (steps - 1))

(**
 * Definition 3: White Path Exists
 *
 * There exists a white path from u to v at time d[u] if there is a path
 * from u to v such that all vertices on the path (except u) are white
 * at the time u is discovered.
 *
 * Note: The definition allows for the trivial path (u = v), but also
 * requires that v itself is white at d[u].
 *)
let white_path_exists 
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d: Seq.seq nat)
  (u v: nat)
  (time: nat)
  : prop
  = u < n /\ v < n /\
    u < Seq.length d /\
    // There exists a path of some length from u to v where all vertices are white
    (exists (steps: nat). path_all_white adj n d u v time steps)

(**
 * Alternative formulation: White path using has_path from Spec
 *
 * This is a more direct encoding: at time d[u], there exists a path from u to v,
 * and all vertices on that path (except u) are white.
 *)
let white_path_exists_v2
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d: Seq.seq nat)
  (u v: nat)
  (time: nat)
  : prop
  = u < n /\ v < n /\
    u < Seq.length d /\
    // u = v (trivial path), or there exists a non-trivial path
    (if u = v then white_at_time d v time
     else 
       // There exists a path from u to v
       (exists (k: nat). k > 0 /\ k < n /\ has_path adj n u v k) /\
       // All intermediate vertices (not u) are white at time d[u]
       (forall (w: nat). w < n /\ w <> u /\
         (exists (k1 k2: nat). k1 < n /\ k2 < n /\
           has_path adj n u w k1 /\ has_path adj n w v k2) ==>
         white_at_time d w time))

(*** Helper Lemmas ***)

(**
 * Lemma: Reflexivity of white path
 *
 * If u is white at time t, then there is a trivial white path from u to u.
 *)
let white_path_reflexive
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d: Seq.seq nat)
  (u: nat)
  (time: nat)
  : Lemma
    (requires u < n /\ u < Seq.length d /\ white_at_time d u time)
    (ensures white_path_exists adj n d u u time)
  = ()

(**
 * Helper: Composing two white paths
 *
 * If there's a white path of s1 steps from u to w and s2 steps from w to v,
 * then there's a white path of s1+s2 steps from u to v.
 *)
let rec path_all_white_compose
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d: Seq.seq nat)
  (u w v: nat)
  (time: nat)
  (s1 s2: nat)
  : Lemma
    (requires
      u < n /\ w < n /\ v < n /\
      path_all_white adj n d u w time s1 /\
      path_all_white adj n d w v time s2 /\
      white_at_time d w time)
    (ensures path_all_white adj n d u v time (s1 + s2))
    (decreases s1)
  = if s1 = 0 then ()
    else if s1 = 1 then ()
    else begin
      let aux (x: nat)
        : Lemma
          (requires x < n /\ has_edge n adj u x /\ white_at_time d x time /\ path_all_white adj n d x w time (s1 - 1))
          (ensures x < n /\ has_edge n adj u x /\ white_at_time d x time /\ path_all_white adj n d x v time (s1 - 1 + s2))
        = path_all_white_compose adj n d x w v time (s1 - 1) s2
      in
      Classical.forall_intro (Classical.move_requires aux)
    end

(**
 * Lemma: Transitivity of white path
 *
 * If there's a white path from u to w and from w to v, and w is white,
 * then there's a white path from u to v.
 *)
let white_path_transitive
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d: Seq.seq nat)
  (u w v: nat)
  (time: nat)
  : Lemma
    (requires 
      u < n /\ w < n /\ v < n /\
      white_path_exists adj n d u w time /\
      white_path_exists adj n d w v time /\
      white_at_time d w time)
    (ensures white_path_exists adj n d u v time)
  = let aux (s1 s2: nat)
      : Lemma
        ((path_all_white adj n d u w time s1 /\ path_all_white adj n d w v time s2) ==>
         (exists (s: nat). path_all_white adj n d u v time s))
      = Classical.move_requires_2
          (fun (s1': nat) (s2': nat) ->
            path_all_white_compose adj n d u w v time s1' s2')
          s1 s2
    in
    Classical.forall_to_exists_2 aux

(**
 * Lemma: If v is white at d[u] and there's an edge u -> v,
 * then there exists a white path from u to v at d[u].
 *)
let edge_to_white_vertex_gives_white_path
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d: Seq.seq nat)
  (u v: nat)
  (time: nat)
  : Lemma
    (requires 
      u < n /\ v < n /\
      u < Seq.length d /\ v < Seq.length d /\
      has_edge n adj u v /\
      white_at_time d v time)
    (ensures white_path_exists adj n d u v time)
  = assert (path_all_white adj n d u v time 1)

(**
 * Lemma: White at discovery time
 *
 * If u is discovered at time du, then any vertex v with d[v] > du
 * was white at time du.
 *)
let discovered_later_was_white
  (d: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires 
      u < Seq.length d /\ v < Seq.length d /\
      Seq.index d u > 0 /\
      Seq.index d v > Seq.index d u)
    (ensures white_at_time d v (Seq.index d u))
  = ()

(**
 * Lemma: Descendant implies discovered later
 *
 * If v is a descendant of u, then v was discovered after u.
 *)
let descendant_discovered_later
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires dfs_ancestor d f u v)
    (ensures 
      u < Seq.length d /\ v < Seq.length d /\
      Seq.index d v > Seq.index d u)
  = ()


(*** Forward Direction: white path implies ancestor ***)

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let contained_strict
  (adj: Seq.seq (Seq.seq int)) (n: nat)
  (u v: nat)
  : Lemma
    (requires (
      let st = dfs adj n in
      u < n /\ v < n /\ u <> v /\
      Seq.length st.d = n /\ Seq.length st.f = n /\ Seq.length st.color = n /\
      Seq.index st.color u = Black /\ Seq.index st.color v = Black /\
      d_of st u > 0 /\
      d_of st u < d_of st v /\
      d_of st v <= f_of st u))
    (ensures (
      let st = dfs adj n in
      d_of st u < d_of st v /\ d_of st v < f_of st v /\ f_of st v < f_of st u))
  = let st = dfs adj n in
    dfs_satisfies_parenthesis_theorem adj n;
    dfs_distinct_finish_times adj n u v;
    init_has_correct_lengths n;
    // parenthesis_theorem: intervals are disjoint, or one contains the other
    assert (parenthesis_property st u v);
    let iu = get_interval st u in
    let iv = get_interval st v in
    // d[u] < d[v] rules out: interval_contained iu iv (would need d[u] >= d[v])
    // d[v] <= f[u] rules out: intervals_disjoint with f[u] < d[v]
    // d[v] < f[v] (Black, strong_valid_state) rules out: f[v] < d[u] (since d[u] < d[v] < f[v])
    // So interval_contained iv iu: d[v] >= d[u] and f[v] <= f[u]
    // With distinct finish: f[v] <> f[u] → f[v] < f[u]
    dfs_loop_inv adj n 0 (init_state n);
    init_state_strong_valid n;
    let init_pair (a b: nat) : Lemma (parenthesis_property (init_state n) a b) = () in
    Classical.forall_intro_2 init_pair;
    ()
#pop-options

// Inductive proof: path_all_white from x to v at d[u] implies v is within u's interval
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let rec white_path_within_interval
  (adj: Seq.seq (Seq.seq int)) (n: nat)
  (u x v: nat) (k: nat)
  : Lemma
    (requires (
      let st = dfs adj n in
      u < n /\ x < n /\ v < n /\ u <> v /\
      Seq.length st.d = n /\ Seq.length st.f = n /\ Seq.length st.color = n /\
      d_of st u > 0 /\
      // x is either u or strictly within u's interval
      (x = u \/ (d_of st u < d_of st x /\ f_of st x < f_of st u)) /\
      // white path from x to v at time d[u]
      path_all_white adj n st.d x v (Seq.index st.d u) k /\
      k >= 1))
    (ensures (
      let st = dfs adj n in
      d_of st u < d_of st v /\ d_of st v < f_of st v /\ f_of st v < f_of st u))
    (decreases k)
  = let st = dfs adj n in
    let du = Seq.index st.d u in
    dfs_all_edges_inv adj n;
    if k = 1 then (
      // Base: edge x → v, v is white at d[u]
      // white_at_time means d[v] = 0 \/ d[u] < d[v]
      // v is Black: d[v] > 0, so d[u] < d[v]
      dfs_all_black adj n v;
      dfs_all_black adj n x;
      dfs_all_black adj n u;
      init_has_correct_lengths n;
      dfs_loop_inv adj n 0 (init_state n);
      init_state_strong_valid n;
      let init_pair (a b: nat) : Lemma (parenthesis_property (init_state n) a b) = () in
      Classical.forall_intro_2 init_pair;
      // all_edges_inv: x Black, edge x→v → d[v] ≤ f[x]
      assert (color_of st x = Black);
      assert (has_edge n adj x v);
      assert (d_of st v <= f_of st u);
      // Now use contained_strict
      if x = u then (
        // d[v] ≤ f[u] directly from all_edges_inv
        contained_strict adj n u v
      ) else (
        // d[v] ≤ f[x] < f[u]
        assert (d_of st v <= f_of st x);
        assert (f_of st x < f_of st u);
        assert (d_of st v <= f_of st u);
        contained_strict adj n u v
      )
    ) else (
      // Inductive: edge x → w, w white at d[u], path from w to v with k-1 steps
      // path_all_white with k > 1: exists w with edge x→w, w white, path w→v k-1 steps
      dfs_all_black adj n x;
      dfs_all_black adj n u;
      init_has_correct_lengths n;
      dfs_loop_inv adj n 0 (init_state n);
      init_state_strong_valid n;
      let init_pair (a b: nat) : Lemma (parenthesis_property (init_state n) a b) = () in
      Classical.forall_intro_2 init_pair;
      // We need to extract the witness w from the existential
      let aux (w: nat) : Lemma
        (requires w < n /\ has_edge n adj x w /\
                  white_at_time st.d w du /\
                  path_all_white adj n st.d w v du (k - 1))
        (ensures d_of st u < d_of st v /\ d_of st v < f_of st v /\ f_of st v < f_of st u)
        = // w is Black, white_at_time means d[u] < d[w]
          dfs_all_black adj n w;
          assert (d_of st w > 0);
          assert (du < d_of st w);
          // all_edges_inv: x Black, edge x→w → d[w] ≤ f[x]
          if x = u then (
            assert (d_of st w <= f_of st u);
            contained_strict adj n u w;
            // w is within u's interval
            assert (d_of st u < d_of st w /\ f_of st w < f_of st u);
            // Recurse with w
            white_path_within_interval adj n u w v (k - 1)
          ) else (
            assert (d_of st w <= f_of st x);
            assert (f_of st x < f_of st u);
            assert (d_of st w <= f_of st u);
            contained_strict adj n u w;
            assert (d_of st u < d_of st w /\ f_of st w < f_of st u);
            white_path_within_interval adj n u w v (k - 1)
          )
      in
      Classical.forall_intro (Classical.move_requires aux)
    )
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let white_path_implies_descendant
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires (
      let st = dfs adj n in
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      d == st.d /\ f == st.f /\
      u < Seq.length d /\ 
      Seq.index d u > 0 /\
      white_path_exists adj n d u v (Seq.index d u)))
    (ensures dfs_ancestor d f u v)
  = let st = dfs adj n in
    let du = Seq.index d u in
    // white_path_exists gives: exists steps. path_all_white ... steps
    // steps >= 1 since u <> v (path_all_white 0 requires u = v)
    let aux (steps: nat) : Lemma
      (requires path_all_white adj n d u v du steps)
      (ensures dfs_ancestor d f u v)
      = if steps = 0 then (
          // path_all_white 0: u = v, contradiction with u <> v
          ()
        ) else (
          white_path_within_interval adj n u u v steps;
          ()
        )
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options


(*** Backward Direction: ancestor implies white path ***)

// Helper: if path is white at time t2, it's also white at earlier time t1 ≤ t2
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let rec path_all_white_earlier_time
  (adj: Seq.seq (Seq.seq int)) (n: nat) (d: Seq.seq nat)
  (u v: nat) (t1 t2: nat) (k: nat)
  : Lemma
    (requires t1 <= t2 /\ path_all_white adj n d u v t2 k)
    (ensures path_all_white adj n d u v t1 k)
    (decreases k)
  = if k <= 1 then ()
    else
      let aux (w: nat) : Lemma
        (requires w < n /\ has_edge n adj u w /\ white_at_time d w t2 /\
                  path_all_white adj n d w v t2 (k - 1))
        (ensures w < n /\ has_edge n adj u w /\ white_at_time d w t1 /\
                 path_all_white adj n d w v t1 (k - 1))
        = path_all_white_earlier_time adj n d w v t1 t2 (k - 1)
      in
      Classical.forall_intro (Classical.move_requires aux)
#pop-options

// Helper: vertices discovered during dfs_visit(root), other than root, have d > root's d.
// root's d = st.time + 1. Other vertices' d comes from visit_neighbors after discover,
// where time = st.time + 1, so d > st.time + 1 by visit_neighbors_timestamps_in_range.
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let dfs_visit_strict_d
  (adj: Seq.seq (Seq.seq int)) (n: nat) (root: nat) (st: dfs_state) (w: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      root < n /\ w < n /\ w <> root /\
      Seq.index st.color root = White /\
      Seq.index st.d w = 0 /\
      Seq.index (dfs_visit adj n root st).d w > 0)
    (ensures Seq.index (dfs_visit adj n root st).d w > st.time + 1)
  = let st1 = discover_vertex root st in
    discover_preserves_lengths root st;
    let neighbors = get_white_neighbors adj n root 0 st1 in
    get_white_neighbors_lt_n adj n root 0 st1;
    visit_neighbors_timestamps_in_range adj n neighbors st1;
    let st2 = visit_neighbors adj n neighbors st1 in
    finish_preserves_lengths root st2
#pop-options

// BUILD pair: given dfs_visit(root, st) discovers v, construct white path root→v at time du.
// Invariant: every undiscovered vertex (st.d[w] = 0) has d_top[w] > du,
// hence is white at time du.
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec visit_neighbors_build_wp
  (adj: Seq.seq (Seq.seq int)) (n: nat) (root: nat) (neighbors: list nat) (st: dfs_state)
  (v: nat) (d_top: Seq.seq nat) (du: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      all_neighbors_lt_n neighbors n /\
      root < n /\ v < n /\ root <> v /\
      Seq.index st.d v = 0 /\
      Seq.index (visit_neighbors adj n neighbors st).d v > 0 /\
      (forall (w: nat). List.Tot.memP w neighbors ==> w < n /\ has_edge n adj root w) /\
      Seq.length d_top = n /\
      // Invariant: every White vertex has d_top > du (so is white at time du)
      (forall (w: nat). w < n /\ Seq.index st.color w = White ==>
        (Seq.index d_top w = 0 \/ Seq.index d_top w > du)))
    (ensures exists (k: nat). path_all_white adj n d_top root v du k)
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> ()
    | w :: rest ->
      if w < Seq.length st.color && Seq.index st.color w = White then (
        let st1 = dfs_visit adj n w st in
        dfs_visit_timestamps_in_range adj n w st;
        if Seq.index st1.d v > 0 then (
          if v = w then (
            // Direct edge root → v. v was White so d_top[v] > du → white at du.
            assert (has_edge n adj root v);
            assert (white_at_time d_top v du);
            assert (path_all_white adj n d_top root v du 1)
          ) else (
            // v in w's subtree: recursive BUILD on dfs_visit(w, st)
            dfs_visit_build_wp adj n w st v d_top du;
            // w was White (st.d[w] = 0) so d_top[w] > du → white at du
            let aux (k: nat) : Lemma
              (requires path_all_white adj n d_top w v du k)
              (ensures path_all_white adj n d_top root v du (1 + k))
              = assert (has_edge n adj root w);
                assert (white_at_time d_top w du)
            in
            Classical.forall_intro (Classical.move_requires aux)
          )
        ) else (
          visit_neighbors_build_wp adj n root rest st1 v d_top du
        )
      ) else (
        visit_neighbors_build_wp adj n root rest st v d_top du
      )

and dfs_visit_build_wp
  (adj: Seq.seq (Seq.seq int)) (n: nat) (root: nat) (st: dfs_state)
  (v: nat) (d_top: Seq.seq nat) (du: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      root < n /\ v < n /\ root <> v /\
      Seq.index st.color root = White /\
      Seq.index st.d v = 0 /\
      Seq.index (dfs_visit adj n root st).d v > 0 /\
      Seq.length d_top = n /\
      (forall (w: nat). w < n /\ w <> root /\ Seq.index st.color w = White ==>
        (Seq.index d_top w = 0 \/ Seq.index d_top w > du)))
    (ensures exists (k: nat). path_all_white adj n d_top root v du k)
    (decreases %[count_white_vertices st; 0])
  = let st1 = discover_vertex root st in
    discover_preserves_lengths root st;
    discover_decreases_white_count root st;
    let neighbors = get_white_neighbors adj n root 0 st1 in
    get_white_neighbors_lt_n adj n root 0 st1;
    Classical.forall_intro (Classical.move_requires (get_white_neighbors_sound adj n root 0 st1));
    visit_neighbors_build_wp adj n root neighbors st1 v d_top du
#pop-options

// FIND pair: trace through dfs_visit/visit_neighbors to find where u is directly visited,
// then call the BUILD pair. This handles the case where u_start ≠ u (u is discovered
// inside dfs_visit(u_start) rather than being directly visited by dfs_loop).
//
// Key invariants (stated in terms of scope_output = visit_neighbors/dfs_visit output):
// 1. d-preservation: scope_output.d[w] > 0 → d_top[w] = scope_output.d[w]
// 2. undiscovered-later: scope_output.d[w] = 0 ∧ d_top[w] > 0 → d_top[w] > scope_output.time
// Both propagate automatically through the recursion since
// visit_neighbors(w::rest, st) = visit_neighbors(rest, dfs_visit(w, st)).

#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec visit_neighbors_find_wp
  (adj: Seq.seq (Seq.seq int)) (n: nat) (root: nat) (neighbors: list nat) (st: dfs_state)
  (u v: nat) (d_top: Seq.seq nat) (du fu: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      all_neighbors_lt_n neighbors n /\
      strong_valid_state st /\ parenthesis_theorem st /\
      root < n /\ u < n /\ v < n /\ u <> v /\
      Seq.index st.color root <> White /\
      Seq.index st.d u = 0 /\ Seq.index st.d v = 0 /\
      (forall (w: nat). List.Tot.memP w neighbors ==> w < n /\ has_edge n adj root w) /\
      Seq.length d_top = n /\ du > 0 /\ fu > du /\ du = Seq.index d_top u /\
      Seq.index d_top v > 0 /\ Seq.index d_top v < fu /\
      du < Seq.index d_top v /\
      (let st' = visit_neighbors adj n neighbors st in
       Seq.index st'.d u > 0 /\ Seq.index st'.d v > 0 /\
       // d-preservation
       (forall (w: nat). w < n /\ Seq.index st'.d w > 0 ==> Seq.index d_top w = Seq.index st'.d w) /\
       fu = Seq.index st'.f u /\
       // undiscovered-later
       (forall (w: nat). w < n /\ Seq.index st'.d w = 0 /\ Seq.index d_top w > 0 ==>
         Seq.index d_top w > st'.time)))
    (ensures exists (k: nat). path_all_white adj n d_top u v du k)
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> ()
    | w :: rest ->
      let st_out = visit_neighbors adj n neighbors st in
      if w < Seq.length st.color && Seq.index st.color w = White then (
        let st1 = dfs_visit adj n w st in
        dfs_visit_timestamps_in_range adj n w st;
        dfs_visit_time_mono adj n w st;
        dfs_visit_inv adj n w st;
        if Seq.index st1.d u > 0 then (
          // u discovered during dfs_visit(w, st).
          // Prove v must also be discovered:
          // fu = st_out.f[u], u non-White in st1, preserved through rest: fu = st1.f[u]
          // st1.f[u] ≤ st1.time (timestamps_in_range)
          // If st1.d[v] = 0: v discovered in rest, so st_out.d[v] > st1.time ≥ fu.
          // d_top[v] = st_out.d[v] > fu. But d_top[v] < fu. Contradiction.
          if Seq.index st1.d v = 0 then (
            visit_neighbors_timestamps_in_range adj n rest st1;
            assert (Seq.index st1.color u <> White);
            visit_neighbors_preserves_nonwhite_df adj n rest st1 u;
            assert (false)
          ) else ();
          if w = u then (
            // Direct discovery of u! Establish white invariant and call BUILD pair.
            // First establish that du = st.time + 1
            dfs_visit_du_fu adj n u st;
            assert (Seq.index st1.color u <> White);
            visit_neighbors_preserves_nonwhite_df adj n rest st1 u;
            // Now: d_top[u] = st_out.d[u] = st1.d[u] = st.time + 1 = du
            assert (du = st.time + 1);
            assert (st1.time > du);
            let establish_inv (w': nat) : Lemma
              (requires w' < n /\ w' <> u /\ Seq.index st.color w' = White)
              (ensures w' < Seq.length d_top /\ (Seq.index d_top w' = 0 \/ Seq.index d_top w' > du))
              = assert (Seq.index st.d w' = 0);
                if Seq.index st1.d w' > 0 then (
                  dfs_visit_strict_d adj n u st w';
                  assert (Seq.index st1.color w' <> White);
                  visit_neighbors_preserves_nonwhite_df adj n rest st1 w'
                ) else (
                  visit_neighbors_timestamps_in_range adj n rest st1;
                  visit_neighbors_time_mono adj n rest st1;
                  let st_rest = visit_neighbors adj n rest st1 in
                  if Seq.index st_rest.d w' > 0 then ()
                  else ()
                )
            in
            Classical.forall_intro (Classical.move_requires establish_inv);
            dfs_visit_build_wp adj n u st v d_top du
          ) else (
            // u in w's subtree, w ≠ u. Recurse into dfs_visit(w).
            // Establish inner d-preservation for dfs_visit(w, st):
            let d_pres_inner (x: nat) : Lemma
              (requires x < n /\ Seq.index st1.d x > 0)
              (ensures x < Seq.length d_top /\ Seq.index d_top x = Seq.index st1.d x)
              = assert (Seq.index st1.color x <> White);
                visit_neighbors_preserves_nonwhite_df adj n rest st1 x
            in
            Classical.forall_intro (Classical.move_requires d_pres_inner);
            // fu = st_out.f[u] = st1.f[u] (preserved since u non-White)
            visit_neighbors_preserves_nonwhite_df adj n rest st1 u;
            // Prove w ≠ v
            if w = v then (
              dfs_visit_strict_d adj n w st u;
              dfs_visit_du_fu adj n w st;
              assert (false)
            ) else ();
            // Establish undiscovered-later for inner scope (st1):
            // for w' with st1.d[w'] = 0 and d_top[w'] > 0: d_top[w'] > st1.time
            visit_neighbors_timestamps_in_range adj n rest st1;
            visit_neighbors_time_mono adj n rest st1;
            let undiscovered_inner (x: nat) : Lemma
              (requires x < n /\ Seq.index st1.d x = 0 /\ Seq.index d_top x > 0)
              (ensures x < Seq.length d_top /\ Seq.index d_top x > st1.time)
              = let st_rest = visit_neighbors adj n rest st1 in
                if Seq.index st_rest.d x > 0 then ()
                else ()
            in
            Classical.forall_intro (Classical.move_requires undiscovered_inner);
            dfs_visit_find_wp adj n w st u v d_top du fu
          )
        ) else (
          // u not discovered, continue with rest.
          // Prove st1.d[v] = 0: if v discovered but u not, contradiction.
          if Seq.index st1.d v > 0 then (
            visit_neighbors_timestamps_in_range adj n rest st1;
            assert (Seq.index st1.color v <> White);
            visit_neighbors_preserves_nonwhite_df adj n rest st1 v;
            assert (false)
          ) else ();
          visit_neighbors_find_wp adj n root rest st1 u v d_top du fu
        )
      ) else (
        visit_neighbors_find_wp adj n root rest st u v d_top du fu
      )

and dfs_visit_find_wp
  (adj: Seq.seq (Seq.seq int)) (n: nat) (root: nat) (st: dfs_state)
  (u v: nat) (d_top: Seq.seq nat) (du fu: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      strong_valid_state st /\ parenthesis_theorem st /\
      root < n /\ u < n /\ v < n /\ u <> v /\ root <> u /\ root <> v /\
      Seq.index st.color root = White /\
      Seq.index st.d u = 0 /\ Seq.index st.d v = 0 /\
      Seq.length d_top = n /\ du > 0 /\ fu > du /\ du = Seq.index d_top u /\
      Seq.index d_top v > 0 /\ Seq.index d_top v < fu /\
      du < Seq.index d_top v /\
      (let st' = dfs_visit adj n root st in
       Seq.index st'.d u > 0 /\ Seq.index st'.d v > 0 /\
       (forall (w: nat). w < n /\ Seq.index st'.d w > 0 ==> Seq.index d_top w = Seq.index st'.d w) /\
       fu = Seq.index st'.f u /\
       (forall (w: nat). w < n /\ Seq.index st'.d w = 0 /\ Seq.index d_top w > 0 ==>
         Seq.index d_top w > st'.time)))
    (ensures exists (k: nat). path_all_white adj n d_top u v du k)
    (decreases %[count_white_vertices st; 0])
  = let st1 = discover_vertex root st in
    discover_preserves_lengths root st;
    discover_decreases_white_count root st;
    discover_preserves_strong_validity root st;
    discover_preserves_parenthesis root st;
    let neighbors = get_white_neighbors adj n root 0 st1 in
    get_white_neighbors_lt_n adj n root 0 st1;
    Classical.forall_intro (Classical.move_requires (get_white_neighbors_sound adj n root 0 st1));
    // dfs_visit output = finish(root, visit_neighbors(neighbors, st1)).
    // finish doesn't change d, so dfs_visit.d = visit_neighbors.d.
    // u ≠ root, v ≠ root: discover doesn't change d[u]/d[v].
    // visit_neighbors(neighbors, st1).d[u] > 0, .d[v] > 0.
    // d-preservation: same as dfs_visit's since finish doesn't change d.
    // undiscovered-later: finish.time = visit_neighbors.time + 1 > visit_neighbors.time.
    //   So dfs_visit.d[w] = 0 ∧ d_top[w] > 0 → d_top[w] > dfs_visit.time ≥ visit_neighbors.time + 1
    //   → d_top[w] > visit_neighbors.time. But we only need ≥, not >.
    //   Actually: dfs_visit.time = finish.time = vn_output.time + 1. And dfs_visit.d = vn_output.d.
    //   So dfs_visit.d[w] = 0 ⟺ vn_output.d[w] = 0.
    //   And d_top[w] > dfs_visit.time = vn_output.time + 1 > vn_output.time. ✓
    visit_neighbors_find_wp adj n root neighbors st1 u v d_top du fu
#pop-options

// dfs_loop wrapper: trace through dfs_loop to find where u is discovered,
// establish the white-path invariant, and call the BUILD pair.
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec dfs_loop_white_path
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u_start: nat) (st: dfs_state)
  (u v: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      strong_valid_state st /\ parenthesis_theorem st /\
      u < n /\ v < n /\ u <> v /\
      Seq.index st.d u = 0 /\ Seq.index st.d v = 0 /\
      (let st' = dfs_loop adj n u_start st in
       Seq.index st'.d u > 0 /\ Seq.index st'.d v > 0 /\
       Seq.index st'.d u < Seq.index st'.d v /\
       Seq.index st'.d v < Seq.index st'.f v /\
       Seq.index st'.f v < Seq.index st'.f u))
    (ensures (
      let st' = dfs_loop adj n u_start st in
      let du = Seq.index st'.d u in
      white_path_exists adj n st'.d u v du))
    (decreases (if u_start < n then n - u_start else 0))
  = if u_start >= n then ()
    else (
      let st_final = dfs_loop adj n u_start st in
      if u_start < Seq.length st.color && Seq.index st.color u_start = White then (
        let st1 = dfs_visit adj n u_start st in
        dfs_visit_timestamps_in_range adj n u_start st;
        dfs_visit_time_mono adj n u_start st;
        dfs_visit_inv adj n u_start st;
        if Seq.index st1.d u > 0 then (
          // u discovered during dfs_visit(u_start, st)
          let d_top = st_final.d in
          let du = Seq.index d_top u in
          // d_top[u] = st1.d[u] (preserved since u is non-White in st1)
          assert (Seq.index st1.color u <> White);
          dfs_loop_preserves_nonwhite_df adj n (u_start + 1) st1 u;

          // Prove v is also discovered during dfs_visit(u_start, st).
          // If not: d[v] > st1.time ≥ f[u] → d[v] ≥ f[u], contradicting f[v] < f[u].
          if Seq.index st1.d v = 0 then (
            dfs_loop_d_gt_time adj n (u_start + 1) st1 v;
            // st_final.d[v] > st1.time
            // st_final.f[u] = st1.f[u] (u non-White, preserved)
            // st1.f[u] ≤ st1.time (from timestamps_in_range)
            // So st_final.d[v] > st1.time ≥ st1.f[u] = st_final.f[u]
            // But st_final.f[v] < st_final.f[u] and st_final.d[v] < st_final.f[v]
            // → st_final.d[v] < st_final.f[u]. Contradiction.
            dfs_loop_preserves_nonwhite_df adj n (u_start + 1) st1 u;
            assert (Seq.index st_final.f u = Seq.index st1.f u);
            assert (Seq.index st1.f u <= st1.time);
            assert (Seq.index (dfs_loop adj n (u_start + 1) st1).d v > st1.time);
            assert (Seq.index st_final.d v > st1.time);
            assert (Seq.index st_final.d v > Seq.index st_final.f u);
            // But we need d[v] < f[v] < f[u], so d[v] < f[u]. Contradiction.
            assert (false)
          ) else ();

          if u_start = u then (
            // CASE 1: u_start = u. Invariant fully provable.
            // For w ≠ u with st.d[w] = 0:
            //   If discovered during dfs_visit(u, st): dfs_visit_strict_d gives d > du.
            //     Preserved by dfs_loop → d_top > du. ✓
            //   If not: dfs_loop_d_gt_time gives d_top > st1.time ≥ du + 1 > du. ✓
            let establish_inv (w: nat) : Lemma
              (requires w < n /\ w <> u /\ Seq.index st.color w = White)
              (ensures w < Seq.length d_top /\ (Seq.index d_top w = 0 \/ Seq.index d_top w > du))
              = // strong_valid_state: White → d = 0
                assert (Seq.index st.d w = 0);
                if Seq.index st1.d w > 0 then (
                  dfs_visit_strict_d adj n u st w;
                  dfs_visit_du_fu adj n u st;
                  assert (Seq.index st1.color w <> White);
                  dfs_loop_preserves_nonwhite_df adj n (u + 1) st1 w
                ) else (
                  if Seq.index (dfs_loop adj n (u + 1) st1).d w > 0 then (
                    dfs_loop_d_gt_time adj n (u + 1) st1 w;
                    dfs_visit_du_fu adj n u st
                  ) else ()
                )
            in
            Classical.forall_intro (Classical.move_requires establish_inv);
            dfs_visit_build_wp adj n u st v d_top du
          ) else (
            // CASE 2: u_start ≠ u. u is discovered within dfs_visit(u_start, st).
            // Use the FIND pair to trace through dfs_visit and locate where u is
            // directly visited, then call the BUILD pair at that point.
            let fu = Seq.index st_final.f u in
            // Establish d-preservation: for w with st1.d[w] > 0, d_top[w] = st1.d[w]
            let d_pres (w: nat) : Lemma
              (requires w < n /\ Seq.index st1.d w > 0)
              (ensures w < Seq.length d_top /\ Seq.index d_top w = Seq.index st1.d w)
              = assert (Seq.index st1.color w <> White);
                dfs_loop_preserves_nonwhite_df adj n (u_start + 1) st1 w
            in
            Classical.forall_intro (Classical.move_requires d_pres);
            // fu = st1.f[u] (preserved through dfs_loop since u non-White)
            assert (fu = Seq.index st1.f u);
            // Establish undiscovered-later: for w with st1.d[w] = 0 and d_top[w] > 0,
            // d_top[w] > st1.time. Follows from dfs_loop_d_gt_time.
            let undiscovered_later (w: nat) : Lemma
              (requires w < n /\ Seq.index st1.d w = 0 /\ Seq.index d_top w > 0)
              (ensures w < Seq.length d_top /\ Seq.index d_top w > st1.time)
              = dfs_loop_d_gt_time adj n (u_start + 1) st1 w
            in
            Classical.forall_intro (Classical.move_requires undiscovered_later);
            // Prove u_start ≠ v: if u_start = v, then d_top[v] = st.time + 1
            // and d_top[u] > st.time + 1 (dfs_visit_strict_d), so du > d_top[v].
            // But st_final.d[u] < st_final.d[v] (precondition). Contradiction.
            if u_start = v then (
              dfs_visit_strict_d adj n u_start st u;
              dfs_visit_du_fu adj n u_start st;
              assert (Seq.index d_top u > Seq.index d_top v);
              assert (Seq.index st_final.d u < Seq.index st_final.d v);
              assert (false)
            ) else ();
            dfs_visit_find_wp adj n u_start st u v d_top du fu
          )
        ) else (
          // u not discovered during dfs_visit(u_start, st).
          // Need st1.d[v] = 0 for recursive call.
          if Seq.index st1.d v > 0 then (
            // v discovered but u not → contradiction:
            // dfs_loop_d_gt_time: st_final.d[u] > st1.time
            // timestamps_in_range: st1.d[v] ≤ st1.time
            // preserves: st_final.d[v] = st1.d[v]
            // So st_final.d[u] > st1.time ≥ st1.d[v] = st_final.d[v]
            // But precondition says st_final.d[u] < st_final.d[v]. Contradiction.
            dfs_loop_d_gt_time adj n (u_start + 1) st1 u;
            dfs_loop_preserves_nonwhite_df adj n (u_start + 1) st1 v;
            assert (false)
          ) else ();
          dfs_loop_white_path adj n (u_start + 1) st1 u v
        )
      ) else (
        dfs_loop_white_path adj n (u_start + 1) st u v
      )
    )
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let descendant_implies_white_path
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires (
      let st = dfs adj n in
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      d == st.d /\ f == st.f /\
      dfs_ancestor d f u v))
    (ensures 
      u < Seq.length d /\
      Seq.index d u > 0 /\
      white_path_exists adj n d u v (Seq.index d u))
  = let st_final = dfs adj n in
    let st0 = init_state n in
    init_has_correct_lengths n;
    init_state_strong_valid n;
    // init_state has all d = 0
    assert (Seq.index st0.d u = 0);
    assert (Seq.index st0.d v = 0);
    // dfs adj n = dfs_loop adj n 0 (init_state n)
    assert (st_final == dfs_loop adj n 0 st0);
    // strong_valid_state of final DFS: Black → f > d > 0
    let init_pair (a b: nat) : Lemma (parenthesis_property st0 a b) = () in
    Classical.forall_intro_2 init_pair;
    dfs_loop_inv adj n 0 st0;
    // All vertices are Black in final state
    dfs_all_black adj n u;
    dfs_all_black adj n v;
    // So d[u] > 0 and d[v] > 0
    dfs_loop_white_path adj n 0 st0 u v
#pop-options

(**
 * Main Theorem: White-Path Theorem (Both Directions)
 *
 * In a DFS forest of graph G, vertex v is a descendant of vertex u
 * if and only if at the time d[u] that the search discovers u,
 * there is a path from u to v consisting entirely of white vertices.
 *
 * Formally:
 *   dfs_ancestor d f u v ⟺ white_path_exists adj n d u v (d[u])
 *)
//SNIPPET_START: white_path_theorem
let white_path_theorem
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires (
      let st = dfs adj n in
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      d == st.d /\ f == st.f /\
      u < Seq.length d /\ Seq.index d u > 0))
    (ensures 
      dfs_ancestor d f u v <==> 
      white_path_exists adj n d u v (Seq.index d u))
//SNIPPET_END: white_path_theorem
  = // Combine both directions
    // Forward: white_path => dfs_ancestor
    Classical.move_requires (white_path_implies_descendant adj n d f u) v;
    // Backward: dfs_ancestor => white_path
    Classical.move_requires (descendant_implies_white_path adj n d f u) v

(**
 * Corollary: Reachability and Descendant Relation
 *
 * If there is a path from u to v and both are discovered in the same
 * DFS tree (starting from u), then v is a descendant of u.
 *)
let reachable_in_tree_is_descendant
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      u < Seq.length d /\ v < Seq.length d /\
      u < Seq.length f /\ v < Seq.length f /\
      Seq.index d u > 0 /\ Seq.index d v > 0 /\
      Seq.index d v < Seq.index f v /\ // DFS invariant
      Seq.index f v < Seq.index f u /\ // Parenthesis theorem
      // There is a path from u to v
      (exists (k: nat). k > 0 /\ k < n /\ has_path adj n u v k) /\
      // v was discovered after u started but before u finished
      Seq.index d u < Seq.index d v /\
      Seq.index d v < Seq.index f u)
    (ensures dfs_ancestor d f u v)
  = // For dfs_ancestor: all inequalities follow from preconditions
    ()

(**
 * Corollary: Non-descendant means no white path
 *
 * If v is not a descendant of u, then there was no white path from u to v
 * at the time u was discovered.
 *)
let non_descendant_no_white_path
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires (
      let st = dfs adj n in
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      d == st.d /\ f == st.f /\
      u < Seq.length d /\ v < Seq.length d /\
      Seq.index d u > 0 /\ Seq.index d v > 0 /\
      ~(dfs_ancestor d f u v)))
    (ensures ~(white_path_exists adj n d u v (Seq.index d u)))
  = // This is the contrapositive of white_path_implies_descendant
    Classical.move_requires (white_path_implies_descendant adj n d f u) v

(*** Applications of White-Path Theorem ***)

(**
 * Application 1: Tree Edge Characterization
 *
 * An edge (u, v) is a tree edge if and only if v is white when
 * first discovered from u, which means there's a white path of length 1.
 *)
let tree_edge_white_path
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      has_edge n adj u v /\
      u < Seq.length d /\ v < Seq.length d /\
      u < Seq.length f /\ v < Seq.length f /\
      Seq.index d u > 0 /\ Seq.index d v > 0 /\
      Seq.index d v < Seq.index f v /\ // DFS invariant
      Seq.index f v < Seq.index f u /\ // Tree edge property
      // v was white at time d[u] and discovered directly from u
      Seq.index d v = Seq.index d u + 1)
    (ensures 
      dfs_ancestor d f u v /\
      white_path_exists adj n d u v (Seq.index d u))
  = // v was discovered immediately after u, so v was white at time d[u]
    // There's an edge u -> v, so there's a white path of length 1
    edge_to_white_vertex_gives_white_path adj n d u v (Seq.index d u);
    // For dfs_ancestor: all inequalities follow from preconditions
    ()

(**
 * Application 2: Forward Edge Characterization
 *
 * An edge (u, v) is a forward edge if v is a descendant of u but
 * not through a direct tree edge from u to v.
 *)
let forward_edge_descendant
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      has_edge n adj u v /\
      u < Seq.length d /\ v < Seq.length d /\
      u < Seq.length f /\ v < Seq.length f /\
      Seq.index d u > 0 /\ Seq.index d v > 0 /\
      Seq.index d v < Seq.index f v /\ // DFS invariant
      // Forward edge: d[u] < d[v] and f[v] < f[u]
      Seq.index d u < Seq.index d v /\
      Seq.index f v < Seq.index f u)
    (ensures dfs_ancestor d f u v)
  = // For dfs_ancestor: all inequalities follow from preconditions
    ()

(**
 * Application 3: Back Edge Not Descendant
 *
 * An edge (u, v) is a back edge if v is an ancestor of u,
 * which means u is a descendant of v (not v of u).
 *)
let back_edge_not_descendant
  (adj: Seq.seq (Seq.seq int))
  (n: nat)
  (d f: Seq.seq nat)
  (u v: nat)
  : Lemma
    (requires
      u < n /\ v < n /\ u <> v /\
      Seq.length d = n /\ Seq.length f = n /\
      has_edge n adj u v /\
      u < Seq.length d /\ v < Seq.length d /\
      u < Seq.length f /\ v < Seq.length f /\
      Seq.index d u > 0 /\ Seq.index d v > 0 /\
      Seq.index d u < Seq.index f u /\ // DFS invariant
      Seq.index d v < Seq.index f v /\ // DFS invariant
      // Back edge: d[v] < d[u] and f[u] < f[v]
      Seq.index d v < Seq.index d u /\
      Seq.index f u < Seq.index f v)
    (ensures 
      ~(dfs_ancestor d f u v) /\
      dfs_ancestor d f v u)  // v is ancestor of u
  = // For ~(dfs_ancestor d f u v): we need ~(d[u] < d[v]), which follows from d[v] < d[u]
    // For dfs_ancestor d f v u: all inequalities follow from preconditions
    ()

(*** Summary ***)

(*
 * This module formalizes the White-Path Theorem (CLRS Theorem 22.9):
 *
 * Key definitions:
 * 1. dfs_ancestor: v is descendant of u ⟺ d[u] < d[v] < f[v] < f[u]
 * 2. white_at_time: v is white at time t ⟺ t < d[v]
 * 3. white_path_exists: path from u to v with all vertices white at d[u]
 *
 * Main theorem:
 *   dfs_ancestor d f u v ⟺ white_path_exists adj n d u v (d[u])
 *
 * Applications:
 * - Tree edges: direct discovery from white vertex
 * - Forward edges: non-tree edges to descendants
 * - Back edges: edges to ancestors
 *
 * Zero admits. The forward/backward directions of the White-Path Theorem
 * are fully proved. The white_path_transitive lemma and all helper lemmas
 * are fully proved. See DFS.Spec.fst for the foundation lemmas
 * (time monotonicity, timestamp ranges, du/fu endpoints) that support
 * these proofs.
 *)
