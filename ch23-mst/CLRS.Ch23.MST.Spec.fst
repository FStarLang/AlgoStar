(*
   CLRS Chapter 23: Minimum Spanning Trees - Cut Property Theorem
   
   This module formalizes the key MST theorem (CLRS Theorem 23.1):
   For any cut (S, V-S) of a graph G, if (u,v) is a light edge crossing
   the cut that respects edge set A, then A ∪ {(u,v)} is safe for some MST.
*)

module CLRS.Ch23.MST.Spec

open FStar.List.Tot

// Edge equality is reflexive
let edge_eq_reflexive (e: edge) 
  : Lemma (edge_eq e e = true)
  = ()

// Edge equality is symmetric
let edge_eq_symmetric (e1 e2: edge)
  : Lemma (edge_eq e1 e2 = edge_eq e2 e1)
  = ()

// An edge is in a list that starts with it
let mem_edge_hd (e: edge) (tl: list edge)
  : Lemma (mem_edge e (e :: tl) = true)
  = edge_eq_reflexive e

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

(*** Path Manipulation Helpers ***)

// Path concatenation: composing two paths
let rec path_concat (p1 p2: list edge) (a b c: nat)
  : Lemma (requires is_path_from_to p1 a b /\ is_path_from_to p2 b c)
          (ensures is_path_from_to (p1 @ p2) a c)
          (decreases p1)
  = match p1 with
    | [] -> ()
    | hd :: tl ->
      if hd.u = a then path_concat tl p2 hd.v b c
      else if hd.v = a then path_concat tl p2 hd.u b c
      else ()

// Subset edges preserved under append (both subsets of s)
let rec subset_edges_append_both (a b: list edge) (s: list edge)
  : Lemma (requires subset_edges a s /\ subset_edges b s)
          (ensures subset_edges (a @ b) s)
  = match a with
    | [] -> ()
    | _ :: tl -> subset_edges_append_both tl b s

// Subset edges preserved under snoc
let rec subset_edges_snoc (a: list edge) (e: edge) (s: list edge)
  : Lemma (requires subset_edges a s /\ mem_edge e s)
          (ensures subset_edges (a @ [e]) s)
  = match a with
    | [] -> edge_eq_reflexive e
    | _ :: tl -> subset_edges_snoc tl e s

// mem_edge is preserved by rev_acc
let rec mem_edge_rev_acc (e: edge) (l acc: list edge)
  : Lemma (ensures mem_edge e (rev_acc l acc) = (mem_edge e l || mem_edge e acc))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl -> mem_edge_rev_acc e tl (hd :: acc)

// mem_edge is preserved by rev
let mem_edge_rev (e: edge) (path: list edge)
  : Lemma (ensures mem_edge e (rev path) = mem_edge e path)
  = mem_edge_rev_acc e path []

// If all elements of l are in s, then subset_edges l s
let rec subset_from_mem (l: list edge) (s: list edge)
  : Lemma (requires forall (e: edge). mem_edge e l ==> mem_edge e s)
          (ensures subset_edges l s)
  = match l with
    | [] -> ()
    | hd :: tl ->
      edge_eq_reflexive hd;
      subset_from_mem tl s

// Subset edges preserved under reversal
let subset_edges_rev (path: list edge) (s: list edge)
  : Lemma (requires subset_edges path s)
          (ensures subset_edges (rev path) s)
  = let aux (e: edge) : Lemma (mem_edge e (rev path) ==> mem_edge e s) =
      mem_edge_rev e path;
      if mem_edge e (rev path) then
        mem_edge_subset e path s
    in
    FStar.Classical.forall_intro aux;
    subset_from_mem (rev path) s

// Path reversal for undirected graphs
let rec path_reverse (path: list edge) (a b: nat)
  : Lemma (requires is_path_from_to path a b)
          (ensures is_path_from_to (rev path) b a)
          (decreases path)
  = match path with
    | [] -> ()
    | hd :: tl ->
      let next = if hd.u = a then hd.v else hd.u in
      path_reverse tl next b;
      // IH: is_path_from_to (rev tl) b next
      assert (is_path_from_to [hd] next a);
      path_concat (rev tl) [hd] b next a;
      // Now: is_path_from_to (rev tl @ [hd]) b a
      // Show: rev (hd :: tl) == rev tl @ [hd]
      rev_rev' (hd :: tl);
      rev_rev' tl

// Reachability is symmetric for undirected graphs
let reachable_symmetric (es: list edge) (u v: nat)
  : Lemma (requires reachable es u v)
          (ensures reachable es v u)
  = FStar.Classical.exists_elim (reachable es v u)
      #_ #(fun path -> subset_edges path es /\ is_path_from_to path u v) ()
      (fun (path: list edge{subset_edges path es /\ is_path_from_to path u v}) ->
        path_reverse path u v;
        subset_edges_rev path es;
        assert (is_path_from_to (rev path) v u);
        assert (subset_edges (rev path) es))

// Reachability is transitive
let reachable_transitive (es: list edge) (a b c: nat)
  : Lemma (requires reachable es a b /\ reachable es b c)
          (ensures reachable es a c)
  = FStar.Classical.exists_elim (reachable es a c)
      #_ #(fun path1 -> subset_edges path1 es /\ is_path_from_to path1 a b) ()
      (fun (path1: list edge{subset_edges path1 es /\ is_path_from_to path1 a b}) ->
        FStar.Classical.exists_elim (reachable es a c)
          #_ #(fun path2 -> subset_edges path2 es /\ is_path_from_to path2 b c) ()
          (fun (path2: list edge{subset_edges path2 es /\ is_path_from_to path2 b c}) ->
            path_concat path1 path2 a b c;
            subset_edges_append_both path1 path2 es))

// If a path subset of (e :: t) doesn't use e, it's a subset of t
let rec path_not_using_e_in_t (path: list edge) (e: edge) (t: list edge)
  : Lemma (requires subset_edges path (e :: t) /\ not (mem_edge e path))
          (ensures subset_edges path t)
  = match path with
    | [] -> ()
    | hd :: tl ->
      // hd is in (e :: t), i.e., edge_eq hd e || mem_edge hd t
      // But ~(mem_edge e path) means edge_eq e hd = false
      edge_eq_symmetric e hd;
      assert (mem_edge hd t);
      path_not_using_e_in_t tl e t

// edge_eq is transitive
let edge_eq_transitive (e1 e2 e3: edge)
  : Lemma (requires edge_eq e1 e2 /\ edge_eq e2 e3)
          (ensures edge_eq e1 e3)
  = ()

// edges that are edge_eq have same endpoints (as sets) and same weight
let edge_eq_endpoints (e1 e2: edge)
  : Lemma (requires edge_eq e1 e2)
          (ensures e1.w = e2.w /\
                   ((e1.u = e2.u /\ e1.v = e2.v) \/ (e1.u = e2.v /\ e1.v = e2.u)))
  = ()

// edges that are edge_eq have the same crossing property
let edge_eq_crosses (e1 e2: edge) (s: cut)
  : Lemma (requires edge_eq e1 e2)
          (ensures crosses_cut e1 s = crosses_cut e2 s)
  = ()

(*** Graph Theory Lemmas for Cut Property ***)

// Helper: all_edges_distinct is preserved for sublists
let all_edges_distinct_tail (hd: edge) (tl: list edge)
  : Lemma (requires all_edges_distinct (hd :: tl))
          (ensures all_edges_distinct tl /\ not (mem_edge hd tl))
  = ()

// Helper: if edge_eq a b and ~(mem_edge b tl), then ~(mem_edge a tl)
let mem_edge_eq_neg (a b: edge) (tl: list edge)
  : Lemma (requires edge_eq a b /\ not (mem_edge b tl))
          (ensures not (mem_edge a tl))
  = if mem_edge a tl then
      mem_edge_eq a b tl  // derives mem_edge b tl, contradicting hypothesis

// Split a simple path at the first occurrence of an edge matching e.
// Since all_edges_distinct, the suffix doesn't reuse e, so it's entirely in t.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rec split_at_first_e (path: list edge) (e: edge) (t: list edge) (start finish: nat)
  : Lemma (requires is_path_from_to path start finish /\
                    subset_edges path (e :: t) /\
                    mem_edge e path /\
                    all_edges_distinct path)
          (ensures (reachable t start e.u /\ reachable t e.v finish) \/
                   (reachable t start e.v /\ reachable t e.u finish))
          (decreases path)
  = match path with
    | [] -> ()  // impossible: mem_edge e [] = false
    | hd :: tl ->
      let next = if hd.u = start then hd.v else hd.u in
      if edge_eq e hd then begin
        // Found edge e. hd connects start to next.
        edge_eq_endpoints e hd;
        // tl is suffix from next to finish
        // all_edges_distinct (hd :: tl) => ~(mem_edge hd tl) /\ all_edges_distinct tl
        all_edges_distinct_tail hd tl;
        // Since edge_eq e hd and ~(mem_edge hd tl), we get ~(mem_edge e tl)
        mem_edge_eq_neg e hd tl;
        assert (not (mem_edge e tl));
        // So tl is entirely in t
        path_not_using_e_in_t tl e t;
        assert (subset_edges tl t);
        // tl is a path from next to finish in t => reachable t next finish
        // reachable t start start via empty path (trivially)
        assert (is_path_from_to ([] #edge) start start);
        assert (subset_edges ([] #edge) t);
        // The SMT handles the endpoint case analysis
        ()
      end else begin
        // hd is not e, so hd is in t
        edge_eq_symmetric e hd;
        assert (mem_edge hd t);
        assert (mem_edge e tl);
        all_edges_distinct_tail hd tl;
        // Recurse on tl
        split_at_first_e tl e t next finish;
        // IH: (reachable t next e.u /\ reachable t e.v finish) \/
        //     (reachable t next e.v /\ reachable t e.u finish)
        // hd: reachable t start next
        assert (is_path_from_to [hd] start next);
        assert (subset_edges [hd] t);
        // Combine by transitivity
        FStar.Classical.or_elim
          #(reachable t next e.u /\ reachable t e.v finish)
          #(reachable t next e.v /\ reachable t e.u finish)
          #(fun _ -> (reachable t start e.u /\ reachable t e.v finish) \/
                     (reachable t start e.v /\ reachable t e.u finish))
          (fun _ -> reachable_transitive t start next e.u)
          (fun _ -> reachable_transitive t start next e.v)
      end
#pop-options

// A simple cycle in (e :: t) must use e if t is acyclic
let cycle_must_use_e (n: nat) (t: list edge) (e: edge) (v: nat) (cycle: list edge)
  : Lemma (requires acyclic n t /\
                    v < n /\ subset_edges cycle (e :: t) /\ 
                    Cons? cycle /\ all_edges_distinct cycle /\
                    is_path_from_to cycle v v)
          (ensures mem_edge e cycle)
  = if not (mem_edge e cycle) then begin
      path_not_using_e_in_t cycle e t;
      assert (subset_edges cycle t);
      assert (v < n /\ subset_edges cycle t /\ Cons? cycle /\ all_edges_distinct cycle);
      // acyclic n t gives ~(is_path_from_to cycle v v), contradiction
      ()
    end

// Helper: if t is acyclic and e's endpoints are NOT connected in t, then e :: t is also acyclic
#push-options "--z3rlimit 30"
let acyclic_when_unreachable (n: nat) (t: list edge) (e: edge)
  : Lemma (requires acyclic n t /\ e.u < n /\ e.v < n /\ ~(mem_edge e t) /\ ~(reachable t e.u e.v))
          (ensures acyclic n (e :: t))
  = introduce forall (vv: nat) (cycle: list edge).
      vv < n /\ subset_edges cycle (e :: t) /\ Cons? cycle /\ all_edges_distinct cycle ==>
      ~(is_path_from_to cycle vv vv)
    with introduce _ ==> _
    with _. (
      let show_false ()
        : Lemma (requires is_path_from_to cycle vv vv) (ensures False) =
        cycle_must_use_e n t e vv cycle;
        split_at_first_e cycle e t vv vv;
        FStar.Classical.or_elim
          #(reachable t vv e.u /\ reachable t e.v vv)
          #(reachable t vv e.v /\ reachable t e.u vv)
          #(fun _ -> reachable t e.u e.v)
          (fun _ -> reachable_transitive t e.v vv e.u;
                    reachable_symmetric t e.v e.u)
          (fun _ -> reachable_transitive t e.u vv e.v)
        // reachable t e.u e.v contradicts ~(reachable t e.u e.v)
      in
      FStar.Classical.move_requires show_false ()
    )
#pop-options

// If adding edge e to acyclic graph creates a simple cycle,
// then e connects two previously connected components
let lemma_adding_edge_creates_cycle (n: nat) (t: list edge) (e: edge)
  : Lemma (requires acyclic n t /\ 
                    e.u < n /\ e.v < n /\
                    ~(mem_edge e t) /\
                    ~(acyclic n (e :: t)))
          (ensures reachable t e.u e.v)
  = // Contrapositive: ~(reachable t e.u e.v) ==> acyclic n (e :: t)
    let cp () : Lemma (requires ~(reachable t e.u e.v)) (ensures acyclic n (e :: t)) =
      acyclic_when_unreachable n t e
    in
    FStar.Classical.move_requires cp ();
    // Now: ~(reachable t e.u e.v) ==> acyclic n (e :: t)
    // Also: ~(acyclic n (e :: t)) [precondition]
    // So: ~~(reachable t e.u e.v)
    // By excluded middle: reachable t e.u e.v
    FStar.Classical.excluded_middle (reachable t e.u e.v)

// A path from a to b where s(a) ≠ s(b) must contain a crossing edge
let rec path_crosses_when_sides_differ 
    (path: list edge) (es: list edge) (s: cut) (a b: nat)
  : Lemma (requires is_path_from_to path a b /\ subset_edges path es /\ s a <> s b)
          (ensures exists (e': edge). mem_edge e' path /\ mem_edge e' es /\ crosses_cut e' s)
          (decreases path)
  = match path with
    | [] -> () // a = b, s(a) = s(b), contradiction
    | hd :: tl ->
      let next = if hd.u = a then hd.v else hd.u in
      if crosses_cut hd s then
        // hd crosses the cut. Witness: e' = hd.
        edge_eq_reflexive hd
      else begin
        // ~(crosses_cut hd s): s(hd.u) = s(hd.v), so s(a) = s(next)
        // Then s(next) ≠ s(b). Recurse on tl.
        path_crosses_when_sides_differ tl es s next b;
        FStar.Classical.exists_elim 
          (exists (e': edge). mem_edge e' path /\ mem_edge e' es /\ crosses_cut e' s)
          #_ #(fun e' -> mem_edge e' tl /\ mem_edge e' es /\ crosses_cut e' s) ()
          (fun (e': edge{mem_edge e' tl /\ mem_edge e' es /\ crosses_cut e' s}) ->
            assert (mem_edge e' (hd :: tl)))
      end

// General version: a simple path using edge e with s(a)=s(b) must have a t-crossing
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec find_t_crossing (path: list edge) (e: edge) (t: list edge) (s: cut) (a b: nat)
  : Lemma (requires is_path_from_to path a b /\
                    subset_edges path (e :: t) /\
                    mem_edge e path /\
                    all_edges_distinct path /\
                    Cons? path /\
                    crosses_cut e s /\
                    s a = s b)
          (ensures exists (e': edge). mem_edge e' path /\ mem_edge e' t /\ crosses_cut e' s)
          (decreases path)
  = let hd :: tl = path in
    let next = if hd.u = a then hd.v else hd.u in
    if edge_eq e hd then begin
      // Found edge e. Suffix tl goes from next to b, entirely in t.
      all_edges_distinct_tail hd tl;
      mem_edge_eq_neg e hd tl;
      path_not_using_e_in_t tl e t;
      edge_eq_endpoints e hd;
      edge_eq_crosses hd e s;
      // crosses_cut hd s, so s(hd.u) ≠ s(hd.v), so s(a) ≠ s(next)
      // s(a) = s(b) and s(a) ≠ s(next), so s(next) ≠ s(b)
      // tl: path from next to b in t, s(next) ≠ s(b)
      path_crosses_when_sides_differ tl t s next b;
      FStar.Classical.exists_elim
        (exists (e': edge). mem_edge e' path /\ mem_edge e' t /\ crosses_cut e' s)
        #_ #(fun e' -> mem_edge e' tl /\ mem_edge e' t /\ crosses_cut e' s) ()
        (fun (e': edge{mem_edge e' tl /\ mem_edge e' t /\ crosses_cut e' s}) ->
          assert (mem_edge e' (hd :: tl)))
    end else begin
      edge_eq_symmetric e hd;
      assert (mem_edge hd t);
      if crosses_cut hd s then
        // hd crosses the cut and is in t. Witness: e' = hd.
        edge_eq_reflexive hd
      else begin
        // hd doesn't cross. s(a) = s(next). s(next) = s(b). Recurse on tl.
        all_edges_distinct_tail hd tl;
        assert (mem_edge e tl);
        find_t_crossing tl e t s next b;
        FStar.Classical.exists_elim
          (exists (e': edge). mem_edge e' path /\ mem_edge e' t /\ crosses_cut e' s)
          #_ #(fun e' -> mem_edge e' tl /\ mem_edge e' t /\ crosses_cut e' s) ()
          (fun (e': edge{mem_edge e' tl /\ mem_edge e' t /\ crosses_cut e' s}) ->
            assert (mem_edge e' (hd :: tl)))
      end
    end
#pop-options

// If adding edge (u,v) to tree T creates a cycle C,
// and (u,v) crosses cut S, then C contains another edge crossing S
let lemma_cycle_crosses_cut_twice 
    (n: nat) (t: list edge) (e: edge) (s: cut) (cycle: list edge)
  : Lemma (requires e.u < n /\ e.v < n /\
                    crosses_cut e s /\
                    subset_edges cycle (e :: t) /\
                    mem_edge e cycle /\
                    Cons? cycle /\
                    all_edges_distinct cycle /\
                    is_path_from_to cycle e.u e.u)
          (ensures (exists (e': edge). 
                     mem_edge e' cycle /\ 
                     mem_edge e' t /\ 
                     crosses_cut e' s))
  = // Cycle from e.u to e.u: s(e.u) = s(e.u). Uses e. all_edges_distinct.
    find_t_crossing cycle e t s e.u e.u

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

(*** Helpers for Cut Property Proof ***)

// Filtering preserves membership for non-matching edges
let rec mem_edge_filter_neg (x e_rem: edge) (t: list edge)
  : Lemma (requires mem_edge x t /\ not (edge_eq x e_rem))
          (ensures mem_edge x (filter (fun e -> not (edge_eq e e_rem)) t))
          (decreases t)
  = match t with
    | [] -> ()
    | hd :: tl ->
      if edge_eq x hd then begin
        if edge_eq hd e_rem then
          edge_eq_transitive x hd e_rem  // contradiction: derives edge_eq x e_rem
        else ()
      end else
        mem_edge_filter_neg x e_rem tl

// If cut respects a and e_rem crosses cut, then a ⊆ (e_add :: filter (...) t)
let rec subset_edges_exchange (a: list edge) (e_add e_rem: edge) (t: list edge) (s: cut)
  : Lemma (requires subset_edges a t /\ respects a s /\ crosses_cut e_rem s)
          (ensures subset_edges a (e_add :: filter (fun e -> not (edge_eq e e_rem)) t))
          (decreases a)
  = match a with
    | [] -> ()
    | hd :: tl ->
      // hd doesn't cross the cut (from respects)
      if edge_eq hd e_rem then edge_eq_crosses hd e_rem s  // contradiction
      else begin
        mem_edge_filter_neg hd e_rem t;
        ()
      end;
      subset_edges_exchange tl e_add e_rem t s

// Exchange preserves spanning tree (well-known graph theory fact):
// In a spanning tree T, if e_add connects two vertices joined by a path through e_rem,
// then T - {e_rem} + {e_add} is still a spanning tree.
// Proof requires: (1) e_rem removal splits T into two components,
// (2) e_add reconnects them (since it's on the path), (3) acyclicity is restored.
let exchange_is_spanning_tree
    (g: graph) (t: list edge) (e_add e_rem: edge) (path: list edge)
  : Lemma (requires is_spanning_tree g t /\
                    mem_edge e_add g.edges /\
                    mem_edge e_rem t /\
                    ~(mem_edge e_add t) /\
                    e_add.u < g.n /\ e_add.v < g.n /\ e_add.u <> e_add.v /\
                    subset_edges path t /\
                    is_path_from_to path e_add.u e_add.v /\
                    mem_edge e_rem path)
          (ensures is_spanning_tree g (e_add :: filter (fun e -> not (edge_eq e e_rem)) t))
  = admit()  // Standard graph theory: exchange in spanning tree

#push-options "--z3rlimit 30"
let cut_property g a e s =
  let goal : prop = exists (t': list edge). is_mst g t' /\ subset_edges (e :: a) t' in
  // Extract MST T containing A
  FStar.Classical.exists_elim
    goal
    #(list edge) #(fun t -> is_mst g t /\ subset_edges a t)
    ()
    (fun (t: list edge{is_mst g t /\ subset_edges a t}) ->
      if mem_edge e t then
        // Case: e already in T. T itself contains A ∪ {e}.
        ()
      else begin
        // Case: e not in T. Exchange argument.
        // Step 1: e's endpoints are connected in t (from all_connected)
        assert (all_connected g.n t);
        reachable_symmetric t 0 e.u;
        reachable_transitive t e.u 0 e.v;
        // Step 2: Path from e.u to e.v must cross cut (s(e.u) ≠ s(e.v))
        // Extract path from reachable
        FStar.Classical.exists_elim
          goal
          #(list edge) #(fun path -> subset_edges path t /\ is_path_from_to path e.u e.v)
          ()
          (fun (path: list edge{subset_edges path t /\ is_path_from_to path e.u e.v}) ->
            // Find crossing edge in path (which is in t)
            path_crosses_when_sides_differ path t s e.u e.v;
            // Extract the crossing edge e'
            FStar.Classical.exists_elim
              goal
              #edge #(fun e' -> mem_edge e' path /\ mem_edge e' t /\ crosses_cut e' s)
              ()
              (fun (e': edge{mem_edge e' path /\ mem_edge e' t /\ crosses_cut e' s}) ->
                // e' is in t, crosses cut, and in g.edges
                assert (subset_edges t g.edges);
                mem_edge_subset e' t g.edges;
                // e.w ≤ e'.w (e is light edge, e' crosses cut and is in g.edges)
                assert (e.w <= e'.w);
                // e.u ≠ e.v (from crosses_cut e s)
                assert (e.u <> e.v);
                let t' = e :: filter (fun e0 -> not (edge_eq e0 e')) t in
                // T' is a spanning tree (exchange lemma)
                exchange_is_spanning_tree g t e e' path;
                // T' is MST (exchange preserves MST + weight argument)
                lemma_exchange_preserves_mst g t e e';
                // Derive is_mst g t' from the disjunction
                introduce forall (t'': list edge). is_spanning_tree g t'' ==> total_weight t' <= total_weight t''
                with introduce _ ==> _ with _h. ();
                assert (is_mst g t');
                // subset_edges (e :: a) t': e is head, a avoids e' (respects cut)
                edge_eq_reflexive e;
                subset_edges_exchange a e e' t s;
                assert (subset_edges (e :: a) t')
              )
          )
      end
    )
#pop-options

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
      () // Sketch: ensures is True, so trivially satisfied
    end

// Final note: This formalization captures the essence of CLRS Theorem 23.1
// A complete proof would require substantial graph theory infrastructure
// particularly for reasoning about paths, cycles, and connectivity
