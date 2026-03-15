(*
   CLRS Chapter 23: MST Existence Theorem

   Proves that every connected graph with valid edges has a minimum spanning tree.
   This fills a key gap identified in the reviews: all prior theorems assumed
   MST existence as a precondition.

   Key results:
   - spanning_tree_exists: connected graph → spanning tree exists
   - mst_exists: connected graph → MST exists

   The spanning tree existence follows directly from the strengthened
   theorem_kruskal_produces_spanning_tree (which no longer requires MST existence).
   MST existence uses weight-based strong induction: given any spanning tree,
   either it's MST or a strictly lighter one exists (by classical logic),
   and the process terminates because weights are bounded below.
*)

module CLRS.Ch23.MST.Existence

open FStar.List.Tot
open CLRS.Ch23.MST.Spec

//SNIPPET_START: spanning_tree_exists
/// Every connected graph with valid edges has a spanning tree.
val spanning_tree_exists (g: graph)
  : Lemma (requires g.n > 0 /\ all_connected g.n g.edges /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v))
          (ensures exists (t: list edge). is_spanning_tree g t)
//SNIPPET_END: spanning_tree_exists

//SNIPPET_START: mst_exists
/// Every connected graph with valid edges has a minimum spanning tree.
val mst_exists (g: graph)
  : Lemma (requires g.n > 0 /\ all_connected g.n g.edges /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v))
          (ensures exists (t: list edge). is_mst g t)
//SNIPPET_END: mst_exists
