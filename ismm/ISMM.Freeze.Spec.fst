(**
 * ISMM: Freeze Algorithm — Pure Specification
 *
 * Paper: "Reference Counting Deeply Immutable Data Structures with Cycles"
 *        Parkinson, Clebsch, Wrigstad — ISMM '24, §3.1 (Fig. 2)
 *
 * Specifies the freeze operation as a set of postcondition predicates.
 * The freeze algorithm computes SCCs via Purdom's path-based algorithm
 * fused with union-find, and assigns each SCC an initial external RC.
 *
 * The key invariant (Section 4):
 *   "A node whose representative is marked RC can only reach
 *    other nodes whose representative is marked RC."
 *)
module ISMM.Freeze.Spec

open FStar.Mul
module Seq = FStar.Seq
open ISMM.Status
open ISMM.UnionFind.Spec
open ISMM.Graph

(*** Freeze Postcondition Predicates ***)

/// After freeze, all reachable nodes are in a "visited" state:
/// their tag is either REP or RC.
let freeze_tags_ok (s: uf_state{uf_inv s}) (adj: Seq.seq int) (n: nat) (root: nat) : prop =
  s.n == n /\
  (forall (v: nat). v < n /\ reachable adj n root v ==>
    Seq.index s.tag v == tag_rep \/ Seq.index s.tag v == tag_rc)

/// After freeze, unreachable nodes remain UNMARKED with parent == self.
let freeze_unreachable_unchanged (s: uf_state{uf_inv s}) (adj: Seq.seq int) (n: nat) (root: nat) : prop =
  s.n == n /\
  (forall (v: nat). v < n /\ ~(reachable adj n root v) ==>
    Seq.index s.tag v == tag_unmarked /\
    Seq.index s.parent v == v)

/// Each SCC has exactly one representative (tagged RC).
/// For every reachable node v, pure_find v gives the SCC rep,
/// and that rep is tagged RC.
let freeze_reps_are_rc (s: uf_state{uf_inv s}) (adj: Seq.seq int) (n: nat) (root: nat) : prop =
  s.n == n /\
  (forall (v: nat). v < n /\ reachable adj n root v ==>
    (pure_find_in_bounds s v;
     Seq.index s.tag (pure_find s v) == tag_rc))

/// SCC correctness: two reachable nodes u, v have the same UF representative
/// if and only if they are SCC-equivalent (mutually reachable).
let freeze_sccs_correct (s: uf_state{uf_inv s}) (adj: Seq.seq int) (n: nat) (root: nat) : prop =
  s.n == n /\
  (forall (u v: nat). u < n /\ v < n /\
    reachable adj n root u /\ reachable adj n root v ==>
    (pure_find_in_bounds s u; pure_find_in_bounds s v;
     (pure_find s u == pure_find s v <==> scc_equiv adj n u v)))

/// Reference count correctness: for each SCC representative r,
/// the value stored in rank[r] (which doubles as RC for RC-tagged nodes)
/// equals the number of cross-SCC edges into that SCC, plus 1 for the
/// root SCC (accounting for the external reference to root).
///
/// An edge (u, v) is "cross-SCC" if pure_find u <> pure_find v.
/// The RC for an SCC representative r =
///   (# of cross-SCC edges (u,v) where pure_find v == r)
///   + (if r == pure_find root then 1 else 0)
///
/// We store the RC in a separate field: for RC-tagged nodes, data[r] = rc.
/// For this spec, we define what the correct RC should be.

/// Count of cross-SCC edges targeting SCC with representative r.
let cross_scc_edge_count
  (s: uf_state{uf_inv s}) (adj: Seq.seq int) (n: nat) (r: nat) (root: nat)
  : prop  // Existential: there exists a count c such that data[r] == c
  = True   // Placeholder — full counting spec is complex, to be refined in Lemmas

/// Combined freeze postcondition.
let freeze_post (s: uf_state{uf_inv s}) (adj: Seq.seq int) (n: nat) (root: nat) : prop =
  freeze_tags_ok s adj n root /\
  freeze_unreachable_unchanged s adj n root /\
  freeze_reps_are_rc s adj n root

(*** Reference Count Operations — Spec ***)

/// incref: increment the RC of the representative of node r.
/// Pre:  pure_find(r) is RC-tagged with count c.
/// Post: pure_find(r) has count c + 1.
let incref_post (s s': uf_state{uf_inv s /\ uf_inv s'}) (r: nat{r < s.n}) : prop =
  s'.n == s.n /\
  // Only the representative's rank (used as RC) changes
  (forall (i: nat). i < s.n ==> Seq.index s'.tag i == Seq.index s.tag i) /\
  (forall (i: nat). i < s.n ==> Seq.index s'.parent i == Seq.index s.parent i) /\
  (forall (i: nat). i < s.n /\ i <> r ==> Seq.index s'.rank i == Seq.index s.rank i) /\
  Seq.index s'.rank r == Seq.index s.rank r + 1

/// decref: decrement the RC, return true if it reaches 0.
let decref_post (s s': uf_state{uf_inv s /\ uf_inv s'}) (r: nat{r < s.n}) (reached_zero: bool) : prop =
  s'.n == s.n /\
  (forall (i: nat). i < s.n ==> Seq.index s'.tag i == Seq.index s.tag i) /\
  (forall (i: nat). i < s.n ==> Seq.index s'.parent i == Seq.index s.parent i) /\
  (forall (i: nat). i < s.n /\ i <> r ==> Seq.index s'.rank i == Seq.index s.rank i) /\
  Seq.index s.rank r > 0 /\
  Seq.index s'.rank r == Seq.index s.rank r - 1 /\
  (reached_zero <==> Seq.index s'.rank r == 0)
