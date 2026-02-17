(*
   CLRS Chapter 23: Minimum Spanning Trees - Cut Property Theorem
   
   This module formalizes the key MST theorem (CLRS Theorem 23.1):
   For any cut (S, V-S) of a graph G, if (u,v) is a light edge crossing
   the cut that respects edge set A, then A ∪ {(u,v)} is safe for some MST.
*)

module CLRS.Ch23.MST.Spec

open FStar.List.Tot

(*** Basic Graph Definitions ***)

//SNIPPET_START: graph_defs
// Weighted edge: two vertices and a weight
noeq type edge = {
  u: nat;
  v: nat;
  w: int;
}

// A graph: n vertices (0 to n-1) and a list of edges
noeq type graph = {
  n: nat;  // number of vertices
  edges: list edge;
}
//SNIPPET_END: graph_defs

// Edge equality (ignoring direction for undirected graphs)
let edge_eq (e1 e2: edge) : bool =
  (e1.u = e2.u && e1.v = e2.v && e1.w = e2.w) ||
  (e1.u = e2.v && e1.v = e2.u && e1.w = e2.w)

// Edge equality is reflexive
let edge_eq_reflexive (e: edge) 
  : Lemma (edge_eq e e = true)
  = ()

// Edge equality is symmetric
let edge_eq_symmetric (e1 e2: edge)
  : Lemma (edge_eq e1 e2 = edge_eq e2 e1)
  = ()

// Check if edge is in edge set
let rec mem_edge (e: edge) (es: list edge) : bool =
  match es with
  | [] -> false
  | hd :: tl -> edge_eq e hd || mem_edge e tl

// An edge is in a list that starts with it
let mem_edge_hd (e: edge) (tl: list edge)
  : Lemma (mem_edge e (e :: tl) = true)
  = edge_eq_reflexive e

// Edge set subset
let rec subset_edges (a b: list edge) : bool =
  match a with
  | [] -> true
  | hd :: tl -> mem_edge hd b && subset_edges tl b

// Total weight of edge set
let rec total_weight (es: list edge) : int =
  match es with
  | [] -> 0
  | e :: rest -> e.w + total_weight rest

(*** Path and Reachability ***)

// A path is a list of edges where consecutive edges share endpoints
let rec is_path_from_to (edges: list edge) (start: nat) (finish: nat) : bool =
  match edges with
  | [] -> start = finish
  | e :: rest ->
    if e.u = start then is_path_from_to rest e.v finish
    else if e.v = start then is_path_from_to rest e.u finish
    else false

// Reachable via a set of edges
let reachable (es: list edge) (u v: nat) : prop =
  exists (path: list edge). 
    subset_edges path es /\ is_path_from_to path u v

// All vertices reachable from vertex 0
let all_connected (n: nat) (es: list edge) : prop =
  forall (v: nat). v < n ==> reachable es 0 v

(*** Cycles and Acyclicity ***)

// A cycle is a non-empty path from a vertex back to itself
// with at least one edge
let is_cycle (edges: list edge) (v: nat) : prop =
  Cons? edges /\ is_path_from_to edges v v

// Acyclic: no vertex has a cycle
let acyclic (n: nat) (es: list edge) : prop =
  forall (v: nat) (cycle: list edge).
    v < n /\ subset_edges cycle es /\ Cons? cycle ==>
    ~(is_path_from_to cycle v v)

(*** Spanning Tree ***)

//SNIPPET_START: spanning_tree_mst
// A spanning tree: connects all vertices, acyclic, has exactly n-1 edges
let is_spanning_tree (g: graph) (es: list edge) : prop =
  g.n > 0 /\
  subset_edges es g.edges /\
  length es = g.n - 1 /\
  all_connected g.n es /\
  acyclic g.n es

(*** Minimum Spanning Tree ***)

// MST: spanning tree with minimum total weight
let is_mst (g: graph) (mst: list edge) : prop =
  is_spanning_tree g mst /\
  (forall (t: list edge). 
    is_spanning_tree g t ==> total_weight mst <= total_weight t)
//SNIPPET_END: spanning_tree_mst

(*** Cut Definitions ***)

// A cut S partitions vertices into S and V-S
// Represented as a predicate: vertex -> bool
type cut = nat -> bool

// An edge crosses the cut if endpoints are on different sides
let crosses_cut (e: edge) (s: cut) : bool =
  s e.u <> s e.v

// Filter edges that cross the cut
let rec crossing_edges (es: list edge) (s: cut) : list edge =
  match es with
  | [] -> []
  | e :: rest ->
    if crosses_cut e s then e :: crossing_edges rest s
    else crossing_edges rest s

//SNIPPET_START: cut_defs
// Light edge: minimum weight among edges crossing the cut
let is_light_edge (e: edge) (s: cut) (g: graph) : prop =
  mem_edge e g.edges /\
  crosses_cut e s /\
  (forall (e': edge). 
    mem_edge e' g.edges /\ crosses_cut e' s ==> e.w <= e'.w)

// A cut respects edge set A: no edge in A crosses the cut
let rec respects (a: list edge) (s: cut) : bool =
  match a with
  | [] -> true
  | e :: rest -> not (crosses_cut e s) && respects rest s
//SNIPPET_END: cut_defs

(*** Helper Lemmas ***)

// Basic facts about edge membership
let rec mem_edge_append (e: edge) (l1 l2: list edge)
  : Lemma (mem_edge e (l1 @ l2) <==> (mem_edge e l1 || mem_edge e l2))
  = match l1 with
    | [] -> ()
    | hd :: tl -> mem_edge_append e tl l2

let rec subset_edges_append (a b c: list edge)
  : Lemma (requires subset_edges a b)
          (ensures subset_edges a (b @ c))
  = match a with
    | [] -> ()
    | hd :: tl -> 
      mem_edge_append hd b c;
      subset_edges_append tl b c

let rec subset_edges_cons (a: list edge) (e: edge) (b: list edge)
  : Lemma (requires subset_edges a b)
          (ensures subset_edges a (e :: b))
  = match a with
    | [] -> ()
    | hd :: tl -> 
      // hd is in b, so hd is in (e :: b)
      assert (mem_edge hd b);
      // Recurse for tail
      subset_edges_cons tl e b

let rec subset_edges_reflexive (a: list edge)
  : Lemma (subset_edges a a)
  = match a with
    | [] -> ()
    | hd :: tl -> 
      mem_edge_hd hd tl;
      // Need to show: subset_edges tl (hd :: tl)
      // First show: subset_edges tl tl
      subset_edges_reflexive tl;
      // Then show: subset_edges tl tl ==> subset_edges tl (hd :: tl)
      subset_edges_cons tl hd tl

// If two edges are equal and one is in a list, so is the other
let rec mem_edge_eq (e1 e2: edge) (es: list edge)
  : Lemma (requires edge_eq e1 e2 /\ mem_edge e1 es)
          (ensures mem_edge e2 es)
  = match es with
    | [] -> ()
    | hd :: tl ->
      if edge_eq e1 hd then ()
      else mem_edge_eq e1 e2 tl

// If an edge is in a, and a is subset of b, then edge is in b
let rec mem_edge_subset (e: edge) (a b: list edge)
  : Lemma (requires mem_edge e a /\ subset_edges a b)
          (ensures mem_edge e b)
  = match a with
    | [] -> ()
    | hd :: tl ->
      if edge_eq e hd then begin
        // e and hd are the same edge
        // subset_edges (hd :: tl) b implies mem_edge hd b
        // So mem_edge e b must hold
        mem_edge_eq hd e b
      end else begin
        // e is not hd, so e must be in tl
        // subset_edges (hd :: tl) b implies subset_edges tl b
        mem_edge_subset e tl b
      end

let rec subset_edges_transitive (a b c: list edge)
  : Lemma (requires subset_edges a b /\ subset_edges b c)
          (ensures subset_edges a c)
  = match a with
    | [] -> ()
    | hd :: tl ->
      // hd is in b (from subset_edges a b)
      // b is subset of c, so hd is in c
      mem_edge_subset hd b c;
      subset_edges_transitive tl b c

(* Adding an edge to a set *)
let add_edge (e: edge) (es: list edge) : list edge =
  if mem_edge e es then es else e :: es

let mem_edge_add (e e': edge) (es: list edge)
  : Lemma (mem_edge e' (add_edge e es) <==> (edge_eq e e' || mem_edge e' es))
  = if mem_edge e es then begin
      // add_edge e es = es, so mem_edge e' (add_edge e es) = mem_edge e' es
      // Need: mem_edge e' es <==> (edge_eq e e' || mem_edge e' es)
      // If edge_eq e e' then mem_edge_eq gives mem_edge e' es from mem_edge e es
      if edge_eq e e' then mem_edge_eq e e' es else ()
    end else begin
      edge_eq_symmetric e e'
    end

(*** Graph Theory Lemmas for Cut Property ***)

// If adding edge e to acyclic tree creates a cycle,
// then e connects two previously connected components
let lemma_adding_edge_creates_cycle (n: nat) (t: list edge) (e: edge)
  : Lemma (requires acyclic n t /\ 
                    e.u < n /\ e.v < n /\
                    ~(mem_edge e t) /\
                    ~(acyclic n (e :: t)))
          (ensures reachable t e.u e.v)
  = admit() // Complex graph theory: if adding edge creates cycle,
            // then endpoints were already connected

// If adding edge (u,v) to tree T creates a cycle C,
// and (u,v) crosses cut S, then C contains another edge crossing S
let lemma_cycle_crosses_cut_twice 
    (n: nat) (t: list edge) (e: edge) (s: cut) (cycle: list edge)
  : Lemma (requires e.u < n /\ e.v < n /\
                    crosses_cut e s /\
                    subset_edges cycle (e :: t) /\
                    mem_edge e cycle /\
                    Cons? cycle /\
                    is_path_from_to cycle e.u e.u)
          (ensures (exists (e': edge). 
                     mem_edge e' cycle /\ 
                     mem_edge e' t /\ 
                     crosses_cut e' s))
  = admit() // Complex: path crossing cut must re-cross it

// Replacing one edge with another of less/equal weight preserves connectivity
let lemma_edge_replacement_preserves_connectivity
    (n: nat) (t: list edge) (e_old e_new: edge)
  : Lemma (requires all_connected n t /\
                    mem_edge e_old t /\
                    e_new.w <= e_old.w /\
                    all_connected n (e_new :: t)) // assuming new edge maintains connectivity
          (ensures all_connected n ((e_new :: t) ))
  = () // Trivial from assumption

(*** Weight Lemmas for Edge Exchange ***)

// Filtering out an edge: weight decomposition
let rec filter_weight_decomp (e_rem: edge) (t: list edge)
  : Lemma (ensures total_weight t = 
                   total_weight (filter (fun e -> not (edge_eq e e_rem)) t) +
                   total_weight (filter (fun e -> edge_eq e e_rem) t))
          (decreases t)
  = match t with
    | [] -> ()
    | hd :: tl ->
      filter_weight_decomp e_rem tl

// All edges matching edge_eq have the same weight
let rec filter_matching_weight (e_rem: edge) (t: list edge)
  : Lemma (ensures (let c = length (filter (fun e -> edge_eq e e_rem) t) in
                    total_weight (filter (fun e -> edge_eq e e_rem) t) = op_Multiply c e_rem.w))
          (decreases t)
  = match t with
    | [] -> ()
    | hd :: tl ->
      filter_matching_weight e_rem tl;
      if edge_eq hd e_rem then
        // edge_eq checks weight equality, so hd.w = e_rem.w
        assert (hd.w = e_rem.w)
      else ()

// If mem_edge e t, then filter keeps at least one match
let rec filter_match_nonempty (e_rem: edge) (t: list edge)
  : Lemma (requires mem_edge e_rem t)
          (ensures length (filter (fun e -> edge_eq e e_rem) t) >= 1)
          (decreases t)
  = match t with
    | [] -> ()
    | hd :: tl ->
      if edge_eq e_rem hd then ()
      else filter_match_nonempty e_rem tl

// Filter only removes: length decreases
let rec filter_length_le (f: edge -> bool) (t: list edge)
  : Lemma (ensures length (filter f t) <= length t)
          (decreases t)
  = match t with
    | [] -> ()
    | _ :: tl -> filter_length_le f tl

// Complementary filter lengths sum to original
let rec filter_complement_length (f: edge -> bool) (t: list edge)
  : Lemma (ensures length (filter f t) + length (filter (fun e -> not (f e)) t) = length t)
          (decreases t)
  = match t with
    | [] -> ()
    | _ :: tl -> filter_complement_length f tl

(*** Main Theorem: Cut Property (CLRS Theorem 23.1) ***)

// If we can show that exchanging edges preserves spanning tree property
// and doesn't increase weight, we prove the cut property
#push-options "--z3rlimit 20"
let lemma_exchange_preserves_mst 
    (g: graph)
    (t: list edge)      // Original MST
    (e_add: edge)       // Edge to add (light edge crossing cut)
    (e_rem: edge)       // Edge to remove (from cycle)
  : Lemma (requires is_mst g t /\
                    mem_edge e_add g.edges /\
                    mem_edge e_rem t /\
                    e_add.w <= e_rem.w /\
                    ~(mem_edge e_add t) /\
                    // After adding e_add and removing e_rem, we get a spanning tree
                    is_spanning_tree g (e_add :: (filter (fun e -> not (edge_eq e e_rem)) t)))
          (ensures is_mst g (e_add :: (filter (fun e -> not (edge_eq e e_rem)) t)) \/
                   total_weight (e_add :: (filter (fun e -> not (edge_eq e e_rem)) t)) = 
                   total_weight t)
  = let t' = e_add :: filter (fun e -> not (edge_eq e e_rem)) t in
    let filtered = filter (fun e -> not (edge_eq e e_rem)) t in
    let matched = filter (fun e -> edge_eq e e_rem) t in
    // Weight decomposition
    filter_weight_decomp e_rem t;
    // Matched edges all have weight e_rem.w
    filter_matching_weight e_rem t;
    filter_match_nonempty e_rem t;
    let count = length matched in
    assert (count >= 1);
    assert (total_weight matched = op_Multiply count e_rem.w);
    // Length constraint: filter complement lengths sum to original
    filter_complement_length (fun e -> not (edge_eq e e_rem)) t;
    // len(filter (not.not.eq)) + len(filter not.eq) = len t
    // i.e., len(matched') + len(filtered) = len t
    // But we need filter (fun e -> not (not (edge_eq e e_rem))) = filter (fun e -> edge_eq e e_rem)
    // This is syntactically different, so let's use the other direction:
    filter_complement_length (fun e -> edge_eq e e_rem) t;
    // len(matched) + len(filtered) = len(t) 
    assert (length matched + length filtered = length t);
    // len(t) = n-1 (MST), len(t') = n-1 (spanning tree), len(t') = 1 + len(filtered)
    assert (length t = g.n - 1);
    assert (length t' = g.n - 1);
    assert (length t' = 1 + length filtered);
    // So: count = length matched = length t - length filtered = (n-1) - (n-2) = 1
    assert (count = 1);
    // total_weight t' = e_add.w + total_weight filtered
    //                = e_add.w + total_weight t - 1 * e_rem.w
    //                = e_add.w + total_weight t - e_rem.w
    assert (total_weight t = total_weight filtered + e_rem.w);
    assert (total_weight t' = e_add.w + total_weight filtered);
    // So total_weight t' = e_add.w + total_weight t - e_rem.w <= total_weight t
    assert (total_weight t' <= total_weight t);
    // T is MST, T' is spanning tree, so total_weight t <= total_weight t'
    assert (total_weight t <= total_weight t');
    // Therefore equal
    assert (total_weight t' = total_weight t);
    // T' has same weight as MST and is a spanning tree
    // Need: forall t''. is_spanning_tree g t'' ==> total_weight t' <= total_weight t''
    // From: total_weight t' = total_weight t and is_mst g t
    // So: total_weight t' = total_weight t <= total_weight t''
    introduce forall (t'': list edge). is_spanning_tree g t'' ==> total_weight t' <= total_weight t''
    with introduce _ ==> _
    with _h. ()
#pop-options

//SNIPPET_START: cut_property
// Main theorem: Cut Property
// If A ⊆ MST T, and (u,v) is light edge crossing cut respecting A,
// then A ∪ {(u,v)} ⊆ some MST
val cut_property:
  g: graph ->
  a: list edge ->  // Edge set A (subset of some MST)
  e: edge ->       // Light edge crossing cut
  s: cut ->        // The cut
  Lemma (requires 
          // Graph has at least one MST
          (exists (t: list edge). is_mst g t /\ subset_edges a t) /\
          // e is a light edge crossing the cut
          is_light_edge e s g /\
          // The cut respects A
          respects a s)
        (ensures 
          // A ∪ {e} is contained in some MST
          (exists (t: list edge). is_mst g t /\ subset_edges (e :: a) t))
//SNIPPET_END: cut_property

let cut_property g a e s =
  // Proof sketch:
  // 1. Let T be an MST containing A
  // 2. If e ∈ T, done (A ∪ {e} ⊆ T)
  // 3. If e ∉ T:
  //    a. Adding e to T creates a cycle C (T is maximal acyclic)
  //    b. C must cross cut S at another edge e' (besides e)
  //    c. e' ∉ A (cut respects A)
  //    d. w(e) ≤ w(e') (e is light)
  //    e. T' = T - {e'} + {e} is spanning tree with w(T') ≤ w(T)
  //    f. Thus T' is MST with A ∪ {e} ⊆ T'
  
  // Get MST T containing A
  assert (exists (t: list edge). is_mst g t /\ subset_edges a t);
  
  // The detailed proof requires reasoning about cycles and edge exchange
  // This is the complex part that would need the admitted lemmas above
  admit()

(*** Corollary: Generic MST Algorithm Correctness ***)

// If we start with empty set and repeatedly add safe edges,
// we eventually build an MST
let generic_mst_correctness_sketch
    (g: graph)
    (a: list edge)  // Current safe edge set
    (steps: nat)    // Remaining steps
  : Lemma (requires (exists (t: list edge). is_mst g t /\ subset_edges a t) /\
                    length a < g.n - 1)
          (ensures  True) // Would ensure: can extend A to MST
  = if steps = 0 then ()
    else begin
      // Find a cut respecting A and a light edge e crossing it
      // By cut_property, A ∪ {e} ⊆ some MST
      // Recurse with A ∪ {e}
      admit() // Sketch only
    end

// Final note: This formalization captures the essence of CLRS Theorem 23.1
// A complete proof would require substantial graph theory infrastructure
// particularly for reasoning about paths, cycles, and connectivity
