(*
   Proves the MST theorem for the concrete 3-vertex triangle test graph
   using the pure Prim specification.
   NO admits.
*)
module CLRS.Ch23.Prim.ImplTestHelper

open FStar.Mul
open FStar.Seq
open FStar.List.Tot
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Prim.Spec

module Seq = FStar.Seq

let test_adj : adj_matrix = Seq.seq_of_list [
  Seq.seq_of_list [0; 1; 3];
  Seq.seq_of_list [1; 0; 2];
  Seq.seq_of_list [3; 2; 0]
]

#push-options "--fuel 10 --ifuel 10 --z3rlimit 800"

let test_well_formed () : Lemma (well_formed_adj test_adj 3) =
  assert_norm (Seq.length test_adj == 3);
  assert_norm (Seq.length (Seq.index test_adj 0) == 3);
  assert_norm (Seq.length (Seq.index test_adj 1) == 3);
  assert_norm (Seq.length (Seq.index test_adj 2) == 3);
  introduce forall (u: nat). u < 3 ==> Seq.length (Seq.index test_adj u) = 3
  with introduce _ ==> _ with _. (if u = 0 then () else if u = 1 then () else ());
  assert_norm (Seq.index (Seq.index test_adj 0) 0 = 0);
  assert_norm (Seq.index (Seq.index test_adj 0) 1 = 1);
  assert_norm (Seq.index (Seq.index test_adj 0) 2 = 3);
  assert_norm (Seq.index (Seq.index test_adj 1) 0 = 1);
  assert_norm (Seq.index (Seq.index test_adj 1) 1 = 0);
  assert_norm (Seq.index (Seq.index test_adj 1) 2 = 2);
  assert_norm (Seq.index (Seq.index test_adj 2) 0 = 3);
  assert_norm (Seq.index (Seq.index test_adj 2) 1 = 2);
  assert_norm (Seq.index (Seq.index test_adj 2) 2 = 0);
  well_formed_adj_intro test_adj 3

let test_connected () : Lemma (all_connected 3 (adj_to_edges test_adj 3)) =
  test_well_formed ();
  adj_to_graph_edges test_adj 3;
  let g = adj_to_graph test_adj 3 in
  let es = g.edges in
  // Establish has_edge for concrete edges
  assert_norm (Seq.index (Seq.index test_adj 0) 1 = 1);
  assert_norm (1 <> infinity);
  assert_norm (Seq.length (Seq.index test_adj 0) == 3);
  has_edge_intro test_adj 3 0 1;
  adj_to_graph_has_edge test_adj 3 0 1;
  assert_norm (Seq.index (Seq.index test_adj 1) 2 = 2);
  assert_norm (2 <> infinity);
  assert_norm (Seq.length (Seq.index test_adj 1) == 3);
  has_edge_intro test_adj 3 1 2;
  adj_to_graph_has_edge test_adj 3 1 2;
  let e01 : edge = {u=0; v=1; w=1} in
  let e12 : edge = {u=1; v=2; w=2} in
  edge_eq_reflexive e01;
  edge_eq_reflexive e12;
  // Build paths using graph edges
  assert (is_path_from_to [] 0 0);
  assert (subset_edges [] es);
  assert (is_path_from_to [e01] 0 1);
  assert (subset_edges [e01] es);
  assert (is_path_from_to [e01; e12] 0 2);
  assert (subset_edges [e01; e12] es)

let test_valid_edges () : Lemma
  (forall (e: edge). mem_edge e (adj_to_graph test_adj 3).edges ==>
    e.u < 3 /\ e.v < 3 /\ e.u <> e.v)
  = let aux (e: edge) : Lemma
      (requires mem_edge e (adj_to_graph test_adj 3).edges)
      (ensures e.u < 3 /\ e.v < 3 /\ e.u <> e.v)
      = adj_to_graph_edges_valid test_adj 3 e
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// The MST theorem: pure_prim produces MST for the test graph
let test_prim_mst () : Lemma
  (is_mst (adj_to_graph test_adj 3) (pure_prim test_adj 3 0))
  = test_well_formed ();
    test_connected ();
    test_valid_edges ();
    pure_prim_is_mst test_adj 3 0

#pop-options
