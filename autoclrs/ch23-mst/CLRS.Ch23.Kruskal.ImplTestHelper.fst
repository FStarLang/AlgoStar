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

#push-options "--fuel 10 --ifuel 10 --z3rlimit 10"

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

/// Prove is_mst for any sadj that equals test_adj
open CLRS.Ch23.Kruskal.Defs
let test_is_mst_imperative (sadj: Seq.seq int) (seu sev: Seq.seq int) (ec: nat)
  : Lemma
    (requires Seq.equal sadj test_adj /\
              kruskal_mst_result sadj seu sev 3 ec /\
              result_is_forest_adj sadj seu sev 3 ec /\
              ec <= Seq.length seu /\ ec <= Seq.length sev /\
              (forall (k:nat). k < ec ==>
                Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
                Seq.index seu k < 3 /\ Seq.index sev k < 3))
    (ensures is_mst (adj_array_to_graph sadj 3)
      (weighted_edges_from_arrays sadj seu sev 3 ec 0))
  = test_symmetric ();
    test_no_self_loops ();
    test_connected ();
    assert (symmetric_adj sadj 3);
    assert (no_self_loops_adj sadj 3);
    assert (all_connected 3 (adj_array_to_graph sadj 3).edges);
    kruskal_mst_result_elim sadj seu sev 3 ec

/// If all edges connect vertices in {0,1}, no path from {0,1} can reach vertex 2
let rec no_path_to_2 (path: list edge) (start: nat) (e0 e1: edge)
  : Lemma
    (requires
      subset_edges path [e0; e1] /\
      (e0.u = 0 \/ e0.u = 1) /\ (e0.v = 0 \/ e0.v = 1) /\
      (e1.u = 0 \/ e1.u = 1) /\ (e1.v = 0 \/ e1.v = 1) /\
      (start = 0 \/ start = 1))
    (ensures is_path_from_to path start 2 == false)
    (decreases path)
  = match path with
    | [] -> ()
    | e :: rest ->
      if e.u = start then no_path_to_2 rest e.v e0 e1
      else if e.v = start then no_path_to_2 rest e.u e0 e1
      else ()

/// Two edges connecting only {0,1} can't satisfy all_connected 3
let both_01_not_connected (e0 e1: edge)
  : Lemma
    (requires
      (e0.u = 0 \/ e0.u = 1) /\ (e0.v = 0 \/ e0.v = 1) /\
      (e1.u = 0 \/ e1.u = 1) /\ (e1.v = 0 \/ e1.v = 1))
    (ensures ~(all_connected 3 [e0; e1]))
  = let aux (path: list edge)
      : Lemma (~(is_path_from_to path 0 2 /\ subset_edges path [e0; e1]))
      = if subset_edges path [e0; e1] then no_path_to_2 path 0 e0 e1
        else ()
    in
    FStar.Classical.forall_intro aux

/// Witness: [{u=0;v=1;w=1}; {u=1;v=2;w=2}] is a spanning tree with weight 3
let kruskal_witness_spanning_tree ()
  : Lemma
    (let g = adj_array_to_graph test_adj 3 in
     let t : list edge = [{u=0;v=1;w=1}; {u=1;v=2;w=2}] in
     is_spanning_tree g t /\ total_weight t == 3)
  = let e01 : edge = {u=0; v=1; w=1} in
    let e12 : edge = {u=1; v=2; w=2} in
    let t : list edge = [e01; e12] in
    edge_eq_reflexive e01; edge_eq_reflexive e12;
    assert (is_path_from_to ([] <: list edge) 0 0);
    assert (subset_edges ([] <: list edge) t);
    assert (is_path_from_to [e01] 0 1);
    assert (subset_edges [e01] t);
    assert (is_path_from_to [e01; e12] 0 2);
    assert (subset_edges [e01; e12] t);
    acyclic_when_unreachable 3 [] e12;
    acyclic_when_unreachable 3 [e12] e01

#pop-options

#push-options "--fuel 10 --ifuel 10 --z3rlimit 375 --split_queries always"
/// From is_mst of the concrete graph, derive the unique MST edges.
/// The MST is 0--1--2 with weight 3.
let kruskal_mst_edges (es: list edge)
  : Lemma
    (requires is_mst (adj_array_to_graph test_adj 3) es)
    (ensures mem_edge {u=0;v=1;w=1} es /\ mem_edge {u=1;v=2;w=2} es /\
             total_weight es == 3)
  = kruskal_witness_spanning_tree ();
    assert_norm ((adj_array_to_graph test_adj 3).edges ==
      [{u=0;v=1;w=1}; {u=0;v=2;w=3}; {u=1;v=2;w=2}]);
    match es with
    | [hd; hd2] ->
      // Eliminate the duplicate-(0,1) case via reachability
      (match edge_eq hd {u=0;v=1;w=1}, edge_eq hd2 {u=0;v=1;w=1} with
       | true, true ->
         edge_eq_endpoints hd {u=0;v=1;w=1};
         edge_eq_endpoints hd2 {u=0;v=1;w=1};
         both_01_not_connected hd hd2
       | _, _ -> ())
    | _ -> ()

#pop-options
