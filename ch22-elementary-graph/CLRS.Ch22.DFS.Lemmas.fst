(**
 * CLRS Chapter 22: DFS — Lemma Proofs
 *
 * Consolidates key DFS correctness lemmas from:
 * - DFS.Spec: parenthesis theorem (CLRS Thm 22.7), completeness, edge classification
 * - DFS.WhitePath: white-path theorem (CLRS Thm 22.9)
 *
 * All lemmas are fully proved — zero admits.
 *)
module CLRS.Ch22.DFS.Lemmas

open CLRS.Ch22.DFS.Spec
open FStar.Mul

module WP = CLRS.Ch22.DFS.WhitePath

let dfs_parenthesis_property (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma (ensures parenthesis_theorem (dfs adj n))
  = dfs_parenthesis_property adj n

let dfs_loop_visits_all (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n)
    (ensures (let st' = dfs_loop adj n u st in
              (forall (i: nat). u <= i /\ i < n ==>
                i < Seq.length st'.color /\ Seq.index st'.color i <> White) /\
              (forall (i: nat). i < Seq.length st.color /\ Seq.index st.color i <> White ==>
                i < Seq.length st'.color /\ Seq.index st'.color i <> White)))
  = dfs_loop_visits_all adj n u st

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
      WP.dfs_ancestor d f u v <==>
      WP.white_path_exists adj n d u v (Seq.index d u))
  = WP.white_path_theorem adj n d f u v
