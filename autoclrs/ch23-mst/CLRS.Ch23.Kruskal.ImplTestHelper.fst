(*
   Proves the MST theorem for the concrete 3-vertex triangle test graph.
   NO admits.
*)
module CLRS.Ch23.Kruskal.ImplTestHelper

open FStar.Mul
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Kruskal.Spec
open CLRS.Ch23.Kruskal.Impl

module Seq = FStar.Seq

let test_adj : Seq.seq int = Seq.seq_of_list [0; 1; 3; 1; 0; 2; 3; 2; 0]

#push-options "--fuel 10 --ifuel 10 --z3rlimit 800"

let test_symmetric () : Lemma (symmetric_adj test_adj 3) =
  assert_norm (Seq.length test_adj == 9);
  assert_norm (Seq.equal test_adj (Seq.seq_of_list [0;1;3;1;0;2;3;2;0]))

let test_no_self_loops () : Lemma (no_self_loops_adj test_adj 3) =
  assert_norm (Seq.length test_adj == 9);
  assert_norm (Seq.equal test_adj (Seq.seq_of_list [0;1;3;1;0;2;3;2;0]))

let test_connected () : Lemma (all_connected 3 (adj_array_to_graph test_adj 3).edges) =
  let g = adj_array_to_graph test_adj 3 in
  let es = g.edges in
  // Edge (0,1,1): adj[0*3+1] = 1 > 0, 0 < 1
  let e01 : edge = {u=0; v=1; w=1} in
  // Edge (1,2,2): adj[1*3+2] = 2 > 0, 1 < 2
  let e12 : edge = {u=1; v=2; w=2} in
  edge_eq_reflexive e01;
  edge_eq_reflexive e12;
  // Paths: v=0: [], v=1: [e01], v=2: [e01; e12]
  assert (is_path_from_to [] 0 0);
  assert (subset_edges [] es);
  assert (is_path_from_to [e01] 0 1);
  assert (is_path_from_to [e01; e12] 0 2)

/// The MST theorem: pure_kruskal produces MST for the test graph
let test_mst () : Lemma
  (is_mst (adj_array_to_graph test_adj 3) (pure_kruskal (adj_array_to_graph test_adj 3)))
  = test_symmetric ();
    test_no_self_loops ();
    test_connected ();
    pure_kruskal_is_mst test_adj 3

#pop-options
