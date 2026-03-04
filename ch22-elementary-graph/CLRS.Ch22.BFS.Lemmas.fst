(**
 * CLRS Chapter 22: BFS — Lemma Proofs
 *
 * Consolidates key BFS correctness lemmas from:
 * - BFS.Spec: level-set properties, edge property (CLRS Lemma 22.1)
 * - BFS.DistanceSpec: shortest-path optimality (CLRS Theorem 22.5)
 *
 * All lemmas are fully proved — zero admits.
 *)
module CLRS.Ch22.BFS.Lemmas

open FStar.Mul

module BS = CLRS.Ch22.BFS.Spec
module BD = CLRS.Ch22.BFS.DistanceSpec

(*** Lemmas from BFS.Spec ***)

let source_visited_0 (n: nat) (adj: Seq.seq int) (source: nat)
  : Lemma
    (requires source < n)
    (ensures BS.is_visited n adj source 0 source = true /\
             BS.is_frontier n adj source 0 source = true)
  = BS.source_visited_0 n adj source

let source_dist_zero (n: nat) (adj: Seq.seq int) (source: nat)
  : Lemma
    (requires source < n)
    (ensures BS.bfs_distance n adj source source = 0)
  = BS.source_dist_zero n adj source

let edge_implies_next_visited (n: nat) (adj: Seq.seq int) (source: nat) (k: nat) (u v: nat)
  : Lemma
    (requires
      BS.is_frontier n adj source k u = true /\
      BS.has_edge n adj u v = true /\
      v < n /\ u < n)
    (ensures BS.is_visited n adj source (k + 1) v = true)
  = BS.edge_implies_next_visited n adj source k u v

(*** Lemmas from BFS.DistanceSpec ***)

let bfs_correctness (n: nat) (adj: Seq.seq bool) (source: nat{source < n}) (v: nat{v < n})
  : Lemma
    (requires Seq.length adj = n * n)
    (ensures
      (let d_bfs = Seq.index (BD.bfs_distances n adj source) v in
       let d_shortest = BD.shortest_path_dist n adj source v in
       d_bfs == d_shortest))
  = BD.bfs_correctness n adj source v

#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let visited_implies_path_exists (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                                (v: nat{v < n}) (k: nat)
  : Lemma
    (requires
      Seq.length adj = n * n /\ k <= n /\
      Seq.index (BD.bfs_steps n adj source k).visited v)
    (ensures
      exists (p: list nat).
        BD.path_from_to n adj source v p /\
        BD.path_length p <= k)
  = BD.visited_implies_path_exists n adj source v k
#pop-options

let path_implies_visited (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                         (v: nat{v < n}) (p: list nat)
  : Lemma
    (requires BD.path_from_to n adj source v p)
    (ensures Seq.index (BD.bfs_steps n adj source (BD.path_length p)).visited v)
  = BD.path_implies_visited n adj source v p

let shortest_path_property (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                           (v: nat{v < n}) (k: nat)
  : Lemma
    (requires
      k <= n /\
      (let st = BD.bfs_steps n adj source k in
       Seq.index st.visited v) /\
      (k = 0 || (let prev_st = BD.bfs_steps n adj source (k - 1) in
                 not (Seq.index prev_st.visited v))))
    (ensures
      (forall (p: list nat). BD.path_from_to n adj source v p ==> BD.path_length p >= k))
  = BD.shortest_path_property n adj source v k

let reachable_trans (n: nat) (adj: Seq.seq bool) (s: nat) (u: nat) (v: nat)
  : Lemma
    (requires BD.reachable n adj s u /\ BD.reachable n adj u v)
    (ensures BD.reachable n adj s v)
  = BD.reachable_trans n adj s u v
