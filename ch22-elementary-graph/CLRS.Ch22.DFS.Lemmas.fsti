(**
 * CLRS Chapter 22: DFS — Lemma Interface
 *
 * Key lemma signatures for DFS correctness, consolidating results from:
 * - DFS.Spec (parenthesis theorem Thm 22.7, edge classification, cycle detection)
 * - DFS.WhitePath (white-path theorem Thm 22.9)
 *
 * Zero admits.
 *)
module CLRS.Ch22.DFS.Lemmas

open CLRS.Ch22.DFS.Spec
open FStar.Mul

(*** Parenthesis Theorem (CLRS Theorem 22.7) ***)

/// The parenthesis theorem holds for the result of DFS
val dfs_parenthesis_property (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma (ensures parenthesis_theorem (dfs adj n))

(*** DFS Completeness ***)

/// After DFS, all vertices are non-White (visited)
val dfs_loop_visits_all (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n)
    (ensures (let st' = dfs_loop adj n u st in
              (forall (i: nat). u <= i /\ i < n ==>
                i < Seq.length st'.color /\ Seq.index st'.color i <> White) /\
              (forall (i: nat). i < Seq.length st.color /\ Seq.index st.color i <> White ==>
                i < Seq.length st'.color /\ Seq.index st'.color i <> White)))

(*** White-Path Theorem (CLRS Theorem 22.9) ***)

/// White-path theorem: v is a DFS descendant of u iff a white path exists
/// at time d[u] from u to v
val white_path_theorem
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
      CLRS.Ch22.DFS.WhitePath.dfs_ancestor d f u v <==>
      CLRS.Ch22.DFS.WhitePath.white_path_exists adj n d u v (Seq.index d u))
