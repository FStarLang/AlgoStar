(**
 * CLRS Chapter 22: BFS — Lemma Interface
 *
 * Key lemma signatures for BFS correctness, consolidating results from:
 * - BFS.Spec (level-set properties, edge property CLRS Lemma 22.1)
 * - BFS.DistanceSpec (shortest-path distance, CLRS Theorem 22.5)
 *
 * Zero admits.
 *)
module CLRS.Ch22.BFS.Lemmas

open FStar.Mul

(*** Lemmas from BFS.Spec ***)

/// Source is visited at level 0 (from BFS.Spec)
val source_visited_0 (n: nat) (adj: Seq.seq int) (source: nat)
  : Lemma
    (requires source < n)
    (ensures
      CLRS.Ch22.BFS.Spec.is_visited n adj source 0 source = true /\
      CLRS.Ch22.BFS.Spec.is_frontier n adj source 0 source = true)

/// Source has BFS distance 0 (from BFS.Spec)
val source_dist_zero (n: nat) (adj: Seq.seq int) (source: nat)
  : Lemma
    (requires source < n)
    (ensures CLRS.Ch22.BFS.Spec.bfs_distance n adj source source = 0)

/// CLRS Lemma 22.1: edge from frontier vertex implies visited at next level
val edge_implies_next_visited (n: nat) (adj: Seq.seq int) (source: nat) (k: nat) (u v: nat)
  : Lemma
    (requires
      CLRS.Ch22.BFS.Spec.is_frontier n adj source k u = true /\
      CLRS.Ch22.BFS.Spec.has_edge n adj u v = true /\
      v < n /\ u < n)
    (ensures CLRS.Ch22.BFS.Spec.is_visited n adj source (k + 1) v = true)

(*** Lemmas from BFS.DistanceSpec ***)

/// BFS computes shortest-path distances (CLRS Theorem 22.5)
val bfs_correctness (n: nat) (adj: Seq.seq bool) (source: nat{source < n}) (v: nat{v < n})
  : Lemma
    (requires Seq.length adj = n * n)
    (ensures
      (let d_bfs = Seq.index (CLRS.Ch22.BFS.DistanceSpec.bfs_distances n adj source) v in
       let d_shortest = CLRS.Ch22.BFS.DistanceSpec.shortest_path_dist n adj source v in
       d_bfs == d_shortest))

/// Visited vertex implies path exists (easy direction of Thm 22.5)
val visited_implies_path_exists (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                                (v: nat{v < n}) (k: nat)
  : Lemma
    (requires
      Seq.length adj = n * n /\ k <= n /\
      Seq.index (CLRS.Ch22.BFS.DistanceSpec.bfs_steps n adj source k).visited v)
    (ensures
      exists (p: list nat).
        CLRS.Ch22.BFS.DistanceSpec.path_from_to n adj source v p /\
        CLRS.Ch22.BFS.DistanceSpec.path_length p <= k)

/// Path implies vertex visited (hard direction helper)
val path_implies_visited (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                         (v: nat{v < n}) (p: list nat)
  : Lemma
    (requires CLRS.Ch22.BFS.DistanceSpec.path_from_to n adj source v p)
    (ensures
      Seq.index (CLRS.Ch22.BFS.DistanceSpec.bfs_steps n adj source
        (CLRS.Ch22.BFS.DistanceSpec.path_length p)).visited v)

/// Shortest-path property: vertex first visited at step k implies no shorter path
val shortest_path_property (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                           (v: nat{v < n}) (k: nat)
  : Lemma
    (requires
      k <= n /\
      (let st = CLRS.Ch22.BFS.DistanceSpec.bfs_steps n adj source k in
       Seq.index st.visited v) /\
      (k = 0 || (let prev_st = CLRS.Ch22.BFS.DistanceSpec.bfs_steps n adj source (k - 1) in
                 not (Seq.index prev_st.visited v))))
    (ensures
      (forall (p: list nat).
        CLRS.Ch22.BFS.DistanceSpec.path_from_to n adj source v p ==>
        CLRS.Ch22.BFS.DistanceSpec.path_length p >= k))

/// Transitive reachability
val reachable_trans (n: nat) (adj: Seq.seq bool) (s: nat) (u: nat) (v: nat)
  : Lemma
    (requires
      CLRS.Ch22.BFS.DistanceSpec.reachable n adj s u /\
      CLRS.Ch22.BFS.DistanceSpec.reachable n adj u v)
    (ensures CLRS.Ch22.BFS.DistanceSpec.reachable n adj s v)
