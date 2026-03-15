(*
   CLRS Chapter 23: MST Existence Theorem — Proofs

   Proves that every connected graph with valid edges has a minimum spanning tree.
   Uses the strengthened theorem_kruskal_produces_spanning_tree (no MST precondition)
   for spanning tree existence, then weight-based strong induction for MST existence.
*)

module CLRS.Ch23.MST.Existence

open FStar.List.Tot
open FStar.Mul
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Kruskal.Spec

(*** Spanning Tree Existence ***)

let spanning_tree_exists (g: graph)
  : Lemma (requires g.n > 0 /\ all_connected g.n g.edges /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v))
          (ensures exists (t: list edge). is_spanning_tree g t)
  = theorem_kruskal_produces_spanning_tree g

(*** Weight Lower Bound Infrastructure ***)

/// Minimum edge weight in a non-empty edge list
let rec min_weight_in_list (es: list edge)
  : Pure int (requires Cons? es) (ensures fun _ -> True)
  = match es with
  | [e] -> e.w
  | e :: rest ->
    let m = min_weight_in_list rest in
    if e.w <= m then e.w else m

/// Any edge in the list has weight >= min_weight_in_list
let rec min_weight_bound (e: edge) (es: list edge)
  : Lemma (requires Cons? es /\ mem_edge e es)
          (ensures e.w >= min_weight_in_list es)
          (decreases es)
  = match es with
  | [x] -> edge_eq_endpoints e x
  | x :: rest ->
    if edge_eq e x then
      edge_eq_endpoints e x
    else begin
      assert (mem_edge e rest);
      min_weight_bound e rest
    end

/// Total weight of edges >= length * min_weight, when all edges come from a source list
#push-options "--z3rlimit 20"
let rec total_weight_lower_bound (t: list edge) (source: list edge)
  : Lemma (requires Cons? source /\ subset_edges t source)
          (ensures total_weight t >= (length t) * (min_weight_in_list source))
          (decreases t)
  = match t with
  | [] -> ()
  | e :: rest ->
    assert (mem_edge e source);
    assert (subset_edges rest source);
    min_weight_bound e source;
    total_weight_lower_bound rest source
#pop-options

(*** MST Existence: Trivial Case (single vertex) ***)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let mst_trivial (g: graph)
  : Lemma (requires g.n = 1 /\ Nil? g.edges)
          (ensures exists (t: list edge). is_mst g t)
  = // Show [] is a spanning tree of a 1-vertex graph
    // all_connected 1 []: vertex 0 is reachable from 0 via empty path
    assert (is_path_from_to ([] #edge) 0 0);
    assert (subset_edges ([] #edge) ([] #edge));
    assert (reachable ([] #edge) 0 0);
    // acyclic 1 []: no edges means no cycles
    introduce forall (v: nat) (cycle: list edge).
      v < 1 /\ subset_edges cycle ([] #edge) /\ Cons? cycle /\ all_edges_distinct cycle ==>
      ~(is_path_from_to cycle v v)
    with introduce _ ==> _ with _. begin
      match cycle with
      | hd :: _ -> assert (mem_edge hd ([] #edge) = false)
    end;
    // is_spanning_tree checks
    assert (subset_edges ([] #edge) g.edges);
    assert (length ([] #edge) = g.n - 1);
    assert (g.n > 0);
    assert (is_spanning_tree g ([] #edge));
    // [] is MST: any spanning tree of 1-vertex graph has 0 edges
    introduce forall (t: list edge). is_spanning_tree g t ==> total_weight ([] #edge) <= total_weight t
    with introduce _ ==> _ with _. begin
      assert (length t = 0)
    end
#pop-options

(*** MST Existence: General Case via Weight Induction ***)

/// Connected graph with no edges must have exactly 1 vertex
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let connected_no_edges_means_one_vertex (g: graph)
  : Lemma (requires g.n > 0 /\ all_connected g.n g.edges /\ Nil? g.edges)
          (ensures g.n = 1)
  = if g.n >= 2 then begin
      // Vertex 1 must be reachable from 0 (all_connected)
      assert (reachable ([] #edge) 0 1);
      // But reachable requires a path that is subset of [], i.e., path = []
      // is_path_from_to [] 0 1 = (0 = 1) = false
      FStar.Classical.exists_elim False
        #(list edge)
        #(fun path -> subset_edges path ([] #edge) /\ is_path_from_to path 0 1) ()
        (fun (path: list edge{subset_edges path ([] #edge) /\ is_path_from_to path 0 1}) ->
          match path with
          | [] -> ()
          | hd :: _ -> assert (mem_edge hd ([] #edge) = false)
        )
    end
#pop-options

/// Strong induction on weight: if a spanning tree with bounded weight exists, MST exists
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let rec mst_exists_aux (g: graph) (fuel: nat)
  : Lemma
    (requires
      Cons? g.edges /\ g.n > 0 /\
      (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v) /\
      (exists (t: list edge). is_spanning_tree g t /\
        total_weight t - (g.n - 1) * (min_weight_in_list g.edges) <= fuel))
    (ensures exists (t: list edge). is_mst g t)
    (decreases fuel)
  = let lb = (g.n - 1) * (min_weight_in_list g.edges) in
    // Weight bound: any spanning tree has weight >= lb
    let weight_bound (t': list edge)
      : Lemma (requires is_spanning_tree g t')
              (ensures total_weight t' >= lb)
      = total_weight_lower_bound t' g.edges
    in
    // Extract spanning tree from existential
    FStar.Classical.exists_elim
      (exists (mst: list edge). is_mst g mst)
      #(list edge)
      #(fun t -> is_spanning_tree g t /\ total_weight t - lb <= fuel) ()
      (fun (t: list edge{is_spanning_tree g t /\ total_weight t - lb <= fuel}) ->
        if fuel = 0 then begin
          // Base case: total_weight t <= lb, and all spanning trees have weight >= lb
          // So t has minimum weight and is MST
          introduce forall (t': list edge).
            is_spanning_tree g t' ==> total_weight t <= total_weight t'
          with introduce _ ==> _ with _. weight_bound t'
        end else begin
          // Inductive case: fuel > 0
          // By excluded middle: either t is MST or it's not
          FStar.Classical.excluded_middle (is_mst g t);
          // Handle the ~(is_mst g t) case: find a lighter tree and recurse
          let handle_not_mst ()
            : Lemma (requires ~(is_mst g t))
                    (ensures exists (mst: list edge). is_mst g mst)
            = // From ~(is_mst g t) + is_spanning_tree g t:
              // ~(forall t'. is_spanning_tree g t' ==> total_weight t <= total_weight t')
              // Use excluded_middle on the existential, then contradiction to derive it
              FStar.Classical.excluded_middle
                (exists (t': list edge). is_spanning_tree g t' /\ total_weight t' < total_weight t);
              // If ~(exists lighter): all spanning trees >= t's weight, so t IS MST (contradiction)
              let derive_mst ()
                : Lemma (requires ~(exists (t': list edge). is_spanning_tree g t' /\ total_weight t' < total_weight t))
                        (ensures is_mst g t)
                = introduce forall (t': list edge).
                    is_spanning_tree g t' ==> total_weight t <= total_weight t'
                  with introduce _ ==> _ with _. ()
              in
              FStar.Classical.move_requires derive_mst ();
              // Context now has: ~(exists lighter) ==> is_mst g t
              // Combined with ~(is_mst g t): ~(~(exists lighter)), i.e., exists lighter
              // Z3 should derive: exists lighter
              assert (exists (t': list edge). is_spanning_tree g t' /\ total_weight t' < total_weight t);
              // Extract lighter tree and recurse
              FStar.Classical.exists_elim
                (exists (mst: list edge). is_mst g mst)
                #(list edge)
                #(fun t' -> is_spanning_tree g t' /\ total_weight t' < total_weight t) ()
                (fun (t': list edge{is_spanning_tree g t' /\ total_weight t' < total_weight t}) ->
                  weight_bound t';
                  assert (total_weight t' >= lb);
                  assert (total_weight t' - lb >= 0);
                  let fuel' : nat = total_weight t' - lb in
                  assert (fuel' < fuel);
                  mst_exists_aux g fuel'
                )
          in
          FStar.Classical.move_requires handle_not_mst ()
          // Context now has: ~(is_mst g t) ==> (exists mst. is_mst g mst)
          // Also: (is_mst g t) \/ ~(is_mst g t) (from excluded_middle)
          // And trivially: is_mst g t ==> exists mst. is_mst g mst
          // Z3 combines to get: exists mst. is_mst g mst
        end
      )
#pop-options

(*** Main Theorem ***)

let mst_exists (g: graph)
  : Lemma (requires g.n > 0 /\ all_connected g.n g.edges /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v))
          (ensures exists (t: list edge). is_mst g t)
  = if Nil? g.edges then begin
      connected_no_edges_means_one_vertex g;
      mst_trivial g
    end else begin
      spanning_tree_exists g;
      let t0 = pure_kruskal g in
      theorem_kruskal_produces_spanning_tree g;
      total_weight_lower_bound t0 g.edges;
      let lb = (g.n - 1) * (min_weight_in_list g.edges) in
      let fuel : nat = total_weight t0 - lb in
      mst_exists_aux g fuel
    end
