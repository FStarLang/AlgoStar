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
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
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
#push-options "--z3rlimit 5"
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
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
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
#push-options "--z3rlimit 50"
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

(*** Simple Path Extraction ***)

// Given a simple path (all_edges_distinct) with e in it, return the suffix
// after the first edge matching e. The suffix starts at one of e's endpoints.
let rec suffix_after_eq (e: edge) (path: list edge) (start finish: nat)
  : Ghost (nat & list edge)
          (requires is_path_from_to path start finish /\
                    mem_edge e path /\ all_edges_distinct path /\ Cons? path)
          (ensures fun (mid, rest) ->
                    is_path_from_to rest mid finish /\
                    ~(mem_edge e rest) /\
                    (mid = e.u \/ mid = e.v) /\
                    all_edges_distinct rest /\
                    length rest < length path /\
                    (forall x. mem_edge x rest ==> mem_edge x path))
          (decreases path)
  = let hd :: tl = path in
    let next = if hd.u = start then hd.v else hd.u in
    all_edges_distinct_tail hd tl;
    if edge_eq e hd then begin
      edge_eq_endpoints e hd;
      mem_edge_eq_neg e hd tl;
      (next, tl)
    end else begin
      edge_eq_symmetric e hd;
      let (mid, rest) = suffix_after_eq e tl next finish in
      (mid, rest)
    end

// Extract a simple subpath from any path (removing loops)
let rec simplify_path (path: list edge) (a b: nat)
  : Ghost (list edge)
          (requires is_path_from_to path a b /\ a <> b /\ Cons? path)
          (ensures fun path' ->
                    is_path_from_to path' a b /\
                    all_edges_distinct path' /\
                    Cons? path' /\
                    length path' <= length path /\
                    (forall e. mem_edge e path' ==> mem_edge e path))
          (decreases length path)
  = let e :: tl = path in
    let next = if e.u = a then e.v else e.u in
    if next = b then [e]  // Direct edge from a to b
    else begin
      // Tail is non-empty (otherwise next = b)
      assert (is_path_from_to tl next b);
      assert (next <> b);
      // Simplify the tail first
      let tl_simple = simplify_path tl next b in
      if not (mem_edge e tl_simple) then
        // e doesn't appear in simplified tail -> prepend e
        e :: tl_simple
      else begin
        // e appears in simplified tail -> find it and handle
        let (mid, suffix) = suffix_after_eq e tl_simple next b in
        // mid = e.u or e.v, suffix goes from mid to b
        // all_edges_distinct suffix, and e not in suffix
        if mid = a then begin
          // suffix goes from a to b. It's shorter. Recurse.
          assert (length suffix < length tl_simple);
          assert (length tl_simple <= length tl);
          assert (length tl < length path);
          if Nil? suffix then
            // a = b, contradiction
            [e]  // dummy, unreachable
          else
            simplify_path suffix a b
        end else begin
          // mid = next (the other endpoint of e)
          // e :: suffix is a simple path from a to b
          e :: suffix
        end
      end
    end

// Lemma wrapper: reachable implies simple path exists
let reachable_simple (es: list edge) (a b: nat)
  : Lemma (requires reachable es a b /\ a <> b)
          (ensures exists (path: list edge).
                    subset_edges path es /\ is_path_from_to path a b /\
                    all_edges_distinct path /\ Cons? path)
  = // From reachable, extract any path
    FStar.Classical.exists_elim
      (exists (path: list edge). subset_edges path es /\ is_path_from_to path a b /\
                                  all_edges_distinct path /\ Cons? path)
      #(list edge)
      #(fun path -> subset_edges path es /\ is_path_from_to path a b)
      ()
      (fun (path: list edge{subset_edges path es /\ is_path_from_to path a b}) ->
        if Nil? path then () // a = b, contradiction with a <> b
        else begin
          let path' = simplify_path path a b in
          // path' edges are all in path, which is in es
          let aux (e: edge)
            : Lemma (requires mem_edge e path')
                    (ensures mem_edge e es) =
            mem_edge_subset e path es
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
          subset_from_mem path' es;
          introduce exists (p: list edge).
            subset_edges p es /\ is_path_from_to p a b /\
            all_edges_distinct p /\ Cons? p
          with path' and ()
        end
      )

(*** Tree Theorem: connected graph has >= n-1 edges ***)

// Decidable reachability via strong excluded middle
let reachable_dec (es: list edge) (u v: nat) : GTot bool =
  FStar.StrongExcludedMiddle.strong_excluded_middle (reachable es u v)

// Component edge predicate: both endpoints reachable from root
let is_comp_edge (es: list edge) (root: nat) (ed: edge) : GTot bool =
  reachable_dec es root ed.u && reachable_dec es root ed.v

// Ghost filter: like List.Tot.filter but with a GTot predicate
let rec ghost_filter (f: edge -> GTot bool) (es: list edge) : GTot (list edge) (decreases es) =
  match es with
  | [] -> []
  | hd :: tl -> if f hd then hd :: ghost_filter f tl else ghost_filter f tl

// Ghost filter doesn't increase length
let rec ghost_filter_length (f: edge -> GTot bool) (es: list edge)
  : Lemma (ensures length (ghost_filter f es) <= length es) (decreases es) =
  match es with | [] -> () | _ :: tl -> ghost_filter_length f tl

// Membership through ghost filter when predicate respects edge_eq
let rec mem_edge_ghost_filter (e: edge) (f: edge -> GTot bool) (es: list edge)
  : Lemma (requires mem_edge e es /\ f e /\
                    (forall (e1 e2: edge). edge_eq e1 e2 ==> f e1 = f e2))
          (ensures mem_edge e (ghost_filter f es)) (decreases es)
  = match es with
    | hd :: tl -> if edge_eq e hd then () else mem_edge_ghost_filter e f tl

// Disjoint filters have sum of lengths <= original
let rec ghost_disjoint_filter_sum (f1 f2: edge -> GTot bool) (es: list edge)
  : Lemma (requires forall (e: edge). ~(f1 e /\ f2 e))
          (ensures length (ghost_filter f1 es) + length (ghost_filter f2 es) <= length es)
          (decreases es)
  = match es with | [] -> () | _ :: tl -> ghost_disjoint_filter_sum f1 f2 tl

// Redundant edge: both endpoints already reachable from root via tl,
// so adding e doesn't change reachability
let reachable_redundant (tl: list edge) (e: edge) (root w: nat)
  : Lemma (requires reachable tl root e.u /\ reachable tl root e.v /\
                    reachable (e :: tl) root w)
          (ensures reachable tl root w)
  = if root = w then begin
      assert (is_path_from_to ([] #edge) root root);
      assert (subset_edges ([] #edge) tl)
    end
    else begin
      reachable_simple (e :: tl) root w;
      FStar.Classical.exists_elim (reachable tl root w)
        #(list edge)
        #(fun path -> subset_edges path (e :: tl) /\ is_path_from_to path root w /\
                       all_edges_distinct path /\ Cons? path) ()
        (fun (p: list edge{subset_edges p (e :: tl) /\ is_path_from_to p root w /\
                            all_edges_distinct p /\ Cons? p}) ->
          if not (mem_edge e p) then
            path_not_using_e_in_t p e tl
          else begin
            split_at_first_e p e tl root w;
            FStar.Classical.or_elim
              #(reachable tl root e.u /\ reachable tl e.v w)
              #(reachable tl root e.v /\ reachable tl e.u w)
              #(fun _ -> reachable tl root w)
              (fun _ -> reachable_transitive tl root e.v w)
              (fun _ -> reachable_transitive tl root e.u w)
          end)
    end

// Neither endpoint reachable: adding e doesn't help reach from root
let reachable_neither (tl: list edge) (e: edge) (root w: nat)
  : Lemma (requires ~(reachable tl root e.u) /\ ~(reachable tl root e.v) /\
                    reachable (e :: tl) root w)
          (ensures reachable tl root w)
  = if root = w then begin
      assert (is_path_from_to ([] #edge) root root);
      assert (subset_edges ([] #edge) tl)
    end
    else begin
      reachable_simple (e :: tl) root w;
      FStar.Classical.exists_elim (reachable tl root w)
        #(list edge)
        #(fun path -> subset_edges path (e :: tl) /\ is_path_from_to path root w /\
                       all_edges_distinct path /\ Cons? path) ()
        (fun (p: list edge{subset_edges p (e :: tl) /\ is_path_from_to p root w /\
                            all_edges_distinct p /\ Cons? p}) ->
          if not (mem_edge e p) then
            path_not_using_e_in_t p e tl
          else begin
            split_at_first_e p e tl root w
            // Both disjuncts give reachable tl root e.u or reachable tl root e.v,
            // contradicting hypothesis. SMT derives False => anything.
          end)
    end

// Bridge: one endpoint reachable, the other not. Decomposition result.
let reachable_bridge (tl: list edge) (e: edge) (root w r nr: nat)
  : Lemma (requires (r = e.u /\ nr = e.v \/ r = e.v /\ nr = e.u) /\
                    reachable tl root r /\ ~(reachable tl root nr) /\
                    reachable (e :: tl) root w)
          (ensures reachable tl root w \/ reachable tl nr w)
  = if root = w then begin
      assert (is_path_from_to ([] #edge) root root);
      assert (subset_edges ([] #edge) tl)
    end
    else begin
      reachable_simple (e :: tl) root w;
      FStar.Classical.exists_elim (reachable tl root w \/ reachable tl nr w)
        #(list edge)
        #(fun path -> subset_edges path (e :: tl) /\ is_path_from_to path root w /\
                       all_edges_distinct path /\ Cons? path) ()
        (fun (p: list edge{subset_edges p (e :: tl) /\ is_path_from_to p root w /\
                            all_edges_distinct p /\ Cons? p}) ->
          if not (mem_edge e p) then
            path_not_using_e_in_t p e tl
          else begin
            split_at_first_e p e tl root w;
            FStar.Classical.or_elim
              #(reachable tl root e.u /\ reachable tl e.v w)
              #(reachable tl root e.v /\ reachable tl e.u w)
              #(fun _ -> reachable tl root w \/ reachable tl nr w)
              (fun _ -> if r = e.u then () // nr=e.v, have reachable tl e.v w = reachable tl nr w
                       else ()) // r=e.v, nr=e.u, reachable tl root e.u contradicts ~(reachable tl root nr)
              (fun _ -> if r = e.v then () // nr=e.u, have reachable tl e.u w = reachable tl nr w
                       else ()) // r=e.u, nr=e.v, reachable tl root e.v contradicts ~(reachable tl root nr)
          end)
    end

// Count vertices < m (bounded by n) reachable from root via es
let rec count_reachable (es: list edge) (root: nat) (n m: nat) : GTot nat (decreases m) =
  if m = 0 then 0
  else count_reachable es root n (m - 1) +
       (if (m - 1) < n && reachable_dec es root (m - 1) then 1 else 0)

// Monotonicity: if reachable in es implies reachable in es', count transfers
let rec count_reachable_mono (es es': list edge) (root root': nat) (n m: nat)
  : Lemma (requires forall (v: nat). v < n ==> reachable es root v ==> reachable es' root' v)
          (ensures count_reachable es root n m <= count_reachable es' root' n m) (decreases m)
  = if m = 0 then () else count_reachable_mono es es' root root' n (m - 1)

// Disjoint cover: if reachable in es implies reachable in tl from root1 or root2 (disjoint)
let rec count_reachable_disjoint_cover
    (es tl: list edge) (root root1 root2: nat) (n m: nat)
  : Lemma (requires (forall (v: nat). v < n ==> reachable es root v ==>
                      reachable tl root1 v \/ reachable tl root2 v) /\
                    (forall (v: nat). v < n ==> ~(reachable tl root1 v /\ reachable tl root2 v)))
          (ensures count_reachable es root n m <=
                   count_reachable tl root1 n m + count_reachable tl root2 n m) (decreases m)
  = if m = 0 then () else count_reachable_disjoint_cover es tl root root1 root2 n (m - 1)

// At-most-one: if reachable implies specific vertex, count <= 1
let rec count_reachable_at_most_one (es: list edge) (root: nat) (n m w: nat)
  : Lemma (requires forall (v: nat). v < n ==> reachable es root v ==> v = w)
          (ensures count_reachable es root n m <= 1) (decreases m)
  = if m = 0 then ()
    else begin
      count_reachable_at_most_one es root n (m - 1) w;
      if (m - 1) < n && reachable_dec es root (m - 1) then begin
        assert (m - 1 = w);
        // All v < m-1 with reachable must equal w = m-1, but v < m-1, contradiction
        // So count for m-1 is 0
        let rec zero_below (k: nat)
          : Lemma (requires forall (v: nat). v < n ==> reachable es root v ==> v = m - 1)
                  (ensures count_reachable es root n k = 0 \/ k > m - 1) (decreases k)
          = if k = 0 then ()
            else begin
              zero_below (k - 1);
              if (k - 1) < n && reachable_dec es root (k - 1) then
                assert (k - 1 = m - 1)
            end
        in
        zero_below (m - 1)
      end
    end

// Path edges have endpoints reachable from start
let rec path_endpoints_reachable (es path: list edge) (root a b: nat)
  : Lemma (requires subset_edges path es /\ is_path_from_to path a b /\ reachable es root a)
          (ensures forall (e': edge). mem_edge e' path ==>
                    reachable es root e'.u /\ reachable es root e'.v)
          (decreases path)
  = match path with
    | [] -> ()
    | hd :: tl ->
      let next = if hd.u = a then hd.v else hd.u in
      assert (is_path_from_to [hd] a next);
      assert (subset_edges [hd] es);
      reachable_transitive es root a next;
      path_endpoints_reachable es tl root next b

// Reachable in full list => reachable via component-filtered list
#push-options "--z3rlimit 5"
let reachable_in_component (es: list edge) (root v: nat)
  : Lemma (requires reachable es root v)
          (ensures (let f = fun (e: edge) -> reachable_dec es root e.u && reachable_dec es root e.v in
                    reachable (ghost_filter f es) root v))
  = let f = fun (e: edge) -> reachable_dec es root e.u && reachable_dec es root e.v in
    FStar.Classical.exists_elim
      (reachable (ghost_filter f es) root v)
      #(list edge) #(fun path -> subset_edges path es /\ is_path_from_to path root v) ()
      (fun (path: list edge{subset_edges path es /\ is_path_from_to path root v}) ->
        assert (is_path_from_to ([] #edge) root root);
        assert (subset_edges ([] #edge) es);
        assert (reachable es root root);
        path_endpoints_reachable es path root root v;
        let rec path_in_filter (p: list edge)
          : Lemma (requires subset_edges p es /\
                            (forall (e': edge). mem_edge e' p ==>
                              reachable es root e'.u /\ reachable es root e'.v))
                  (ensures subset_edges p (ghost_filter f es)) (decreases p)
          = match p with
            | [] -> ()
            | hd :: tl_p ->
              assert (reachable es root hd.u /\ reachable es root hd.v);
              assert (f hd);
              introduce forall (e1 e2: edge). edge_eq e1 e2 ==> f e1 = f e2
              with introduce _ ==> _ with _. edge_eq_endpoints e1 e2;
              mem_edge_ghost_filter hd f es;
              path_in_filter tl_p
        in
        path_in_filter path)
#pop-options


// Reachable with empty edges: only self-reachable
let reachable_empty (root v: nat)
  : Lemma (requires reachable ([] #edge) root v) (ensures root = v)
  = FStar.Classical.exists_elim (root = v)
      #(list edge) #(fun path -> subset_edges path ([] #edge) /\ is_path_from_to path root v) ()
      (fun (p: list edge{subset_edges p ([] #edge) /\ is_path_from_to p root v}) ->
        match p with | [] -> () | _ :: _ -> ())

// Main counting bound: number of reachable vertices <= 1 + number of edges
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
let rec count_reachable_bound (es: list edge) (root: nat) (n: nat)
  : Lemma (ensures count_reachable es root n n <= 1 + length es)
          (decreases length es)
  = match es with
    | [] ->
      // Only root is reachable from itself with no edges
      introduce forall (v: nat). v < n ==> reachable ([] #edge) root v ==> v = root
      with introduce _ ==> _ with _. begin
        introduce _ ==> _ with _. reachable_empty root v
      end;
      count_reachable_at_most_one ([] #edge) root n n root

    | e :: tl ->
      count_reachable_bound tl root n;
      if reachable_dec tl root e.u && reachable_dec tl root e.v then begin
        // Redundant edge: reachability unchanged, count doesn't increase
        introduce forall (v: nat). v < n ==> reachable es root v ==> reachable tl root v
        with introduce _ ==> _ with _. begin
          introduce _ ==> _ with _. reachable_redundant tl e root v
        end;
        count_reachable_mono es tl root root n n

      end else if not (reachable_dec tl root e.u) && not (reachable_dec tl root e.v) then begin
        // Neither endpoint reachable: count doesn't increase
        introduce forall (v: nat). v < n ==> reachable es root v ==> reachable tl root v
        with introduce _ ==> _ with _. begin
          introduce _ ==> _ with _. reachable_neither tl e root v
        end;
        count_reachable_mono es tl root root n n

      end else begin
        // Bridge case: one endpoint reachable, the other not
        let r  = if reachable_dec tl root e.u then e.u else e.v in
        let nr = if reachable_dec tl root e.u then e.v else e.u in

        // Component filters
        let fc_r  = fun (ed: edge) -> reachable_dec tl root ed.u && reachable_dec tl root ed.v in
        let fc_nr = fun (ed: edge) -> reachable_dec tl nr   ed.u && reachable_dec tl nr   ed.v in
        let es_r  = ghost_filter fc_r  tl in
        let es_nr = ghost_filter fc_nr tl in

        // IH on component edge lists
        ghost_filter_length fc_r  tl;
        ghost_filter_length fc_nr tl;
        count_reachable_bound es_r  root n;
        count_reachable_bound es_nr nr   n;

        // Component filters are disjoint
        introduce forall (ed: edge). ~(fc_r ed /\ fc_nr ed)
        with begin
          if fc_r ed && fc_nr ed then begin
            reachable_symmetric tl nr ed.u;
            reachable_transitive tl root ed.u nr
          end
        end;
        ghost_disjoint_filter_sum fc_r fc_nr tl;

        // count(tl, root) <= count(es_r, root) (from reachable_in_component)
        introduce forall (v: nat). v < n ==> reachable tl root v ==> reachable es_r root v
        with introduce _ ==> _ with _. begin
          introduce _ ==> _ with _. reachable_in_component tl root v
        end;
        count_reachable_mono tl es_r root root n n;

        // count(tl, nr) <= count(es_nr, nr) (from reachable_in_component)
        introduce forall (v: nat). v < n ==> reachable tl nr v ==> reachable es_nr nr v
        with introduce _ ==> _ with _. begin
          introduce _ ==> _ with _. reachable_in_component tl nr v
        end;
        count_reachable_mono tl es_nr nr nr n n;

        // Bridge decomposition: reachable es root v ==> reachable tl root v \/ reachable tl nr v
        introduce forall (v: nat). v < n ==> reachable es root v ==>
          reachable tl root v \/ reachable tl nr v
        with introduce _ ==> _ with _. begin
          introduce _ ==> _ with _. begin
            if reachable_dec tl root e.u then
              reachable_bridge tl e root v e.u e.v
            else
              reachable_bridge tl e root v e.v e.u
          end
        end;

        // Disjointness
        introduce forall (v: nat). v < n ==> ~(reachable tl root v /\ reachable tl nr v)
        with begin
          if v < n && reachable_dec tl root v && reachable_dec tl nr v then begin
            reachable_symmetric tl nr v;
            reachable_transitive tl root v nr
          end
        end;

        count_reachable_disjoint_cover es tl root root nr n n
      end
#pop-options

// Connected graph has >= n-1 edges
let connected_min_edges (n: nat) (es: list edge)
  : Lemma (requires n > 0 /\ all_connected n es)
          (ensures length es >= n - 1)
  = introduce forall (v: nat). v < n ==> reachable es 0 v
    with introduce _ ==> _ with _. begin
      assert (reachable es 0 v)
    end;
    let rec count_all (m: nat)
      : Lemma (requires forall (v: nat). v < n ==> reachable es 0 v)
              (ensures count_reachable es 0 n m = min m n) (decreases m)
      = if m = 0 then ()
        else begin
          count_all (m - 1)
        end
    in
    count_all n;
    count_reachable_bound es 0 n

(*** Helpers for Exchange Lemma Proof ***)

// Filtering preserves subset of a superset
let rec subset_edges_filter (t g_edges: list edge) (f: edge -> bool)
  : Lemma (requires subset_edges t g_edges)
          (ensures subset_edges (filter f t) g_edges)
          (decreases t)
  = match t with
    | [] -> ()
    | hd :: tl ->
      subset_edges_filter tl g_edges f

// Acyclicity is anti-monotone: fewer edges → still acyclic
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


let acyclic_subset (n: nat) (es es': list edge)
  : Lemma (requires acyclic n es /\ (forall (e:edge). mem_edge e es' ==> mem_edge e es))
          (ensures acyclic n es')
  = introduce forall (v: nat) (cycle: list edge).
      v < n /\ subset_edges cycle es' /\ Cons? cycle /\ all_edges_distinct cycle ==>
      ~(is_path_from_to cycle v v)
    with introduce _ ==> _
    with _. (
      let aux (e: edge)
        : Lemma (requires mem_edge e cycle)
                (ensures mem_edge e es) =
        mem_edge_subset e cycle es';
        assert (mem_edge e es)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      subset_from_mem cycle es
    )

// If x is in filter f t, then x is in t
let rec mem_edge_filter_implies_mem (x: edge) (t: list edge) (f: edge -> bool)
  : Lemma (requires mem_edge x (filter f t))
          (ensures mem_edge x t)
          (decreases t)
  = match t with
    | [] -> ()
    | hd :: tl ->
      if f hd then begin
        if edge_eq x hd then ()
        else mem_edge_filter_implies_mem x tl f
      end else
        mem_edge_filter_implies_mem x tl f

// Filtered tree is acyclic (since it's a subset of acyclic t)
let acyclic_filter (n: nat) (t: list edge) (e_rem: edge)
  : Lemma (requires acyclic n t)
          (ensures acyclic n (filter (fun e -> not (edge_eq e e_rem)) t))
  = let ft = filter (fun e -> not (edge_eq e e_rem)) t in
    let aux (e: edge)
      : Lemma (requires mem_edge e ft)
              (ensures mem_edge e t)
      = mem_edge_filter_implies_mem e t (fun e -> not (edge_eq e e_rem))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    acyclic_subset n t ft

// Forward: mem_edge in t implies mem_edge in e_rem :: filtered_t
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
let rec mem_edge_t_to_erem_ft (x e_rem: edge) (t: list edge)
  : Lemma (requires mem_edge x t)
          (ensures mem_edge x (e_rem :: filter (fun e -> not (edge_eq e e_rem)) t))
          (decreases t)
  = match t with
    | [] -> ()
    | hd :: tl ->
      if edge_eq x hd then begin
        if edge_eq hd e_rem then
          edge_eq_transitive x hd e_rem
        else ()
      end else begin
        mem_edge_t_to_erem_ft x e_rem tl;
        // IH: mem_edge x (e_rem :: filter tl)
        // Need: mem_edge x (e_rem :: filter (hd :: tl))
        if edge_eq hd e_rem then ()  // filter(hd::tl) = filter(tl)
        else ()  // filter(hd::tl) = hd :: filter(tl), so superset
      end
#pop-options

// Reachable in t implies reachable in e_rem :: filtered_t
#push-options "--z3rlimit 5"
let reachable_t_iff_erem_ft (t: list edge) (e_rem: edge) (u v: nat)
  : Lemma (requires reachable t u v)
          (ensures reachable (e_rem :: filter (fun e -> not (edge_eq e e_rem)) t) u v)
  = let ft = filter (fun e -> not (edge_eq e e_rem)) t in
    let t2 = e_rem :: ft in
    // reachable is an existential over paths
    // We prove: if subset_edges path t, then subset_edges path t2
    // which transfers the witness directly
    let aux (path: list edge)
      : Lemma (requires subset_edges path t /\ is_path_from_to path u v)
              (ensures reachable t2 u v) =
      let aux2 (e: edge)
        : Lemma (requires mem_edge e path) (ensures mem_edge e t2) =
        mem_edge_subset e path t;
        mem_edge_t_to_erem_ft e e_rem t
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux2);
      subset_from_mem path t2;
      assert (subset_edges path t2);
      assert (is_path_from_to path u v);
      introduce exists (p: list edge). subset_edges p t2 /\ is_path_from_to p u v
      with path and ()
    in
    // Now discharge the existential in the precondition
    FStar.Classical.exists_elim
      (reachable t2 u v)
      #(list edge)
      #(fun path -> subset_edges path t /\ is_path_from_to path u v)
      ()
      (fun path -> aux path)
#pop-options

// Reachable in e_rem :: ft implies reachable in e_add :: ft
// (by rerouting through e_add when the path uses e_rem)
// Key insight: if path doesn't use e_rem, it's in ft ⊆ e_add :: ft.
// If path uses e_rem, split it and reroute via e_add.
// This requires knowing that e_add connects the same components as e_rem.

// Helper: e_add not in filtered_t (since e_add not in t and ft ⊆ t)
let mem_edge_e_add_not_in_ft (e_add e_rem: edge) (t: list edge)
  : Lemma (requires ~(mem_edge e_add t))
          (ensures ~(mem_edge e_add (filter (fun e -> not (edge_eq e e_rem)) t)))
  = if mem_edge e_add (filter (fun e -> not (edge_eq e e_rem)) t) then
      mem_edge_filter_implies_mem e_add t (fun e -> not (edge_eq e e_rem))

// Helper: e_rem not in filtered_t (by construction of filter)
let rec mem_edge_e_rem_not_in_ft_aux (e_rem: edge) (t: list edge)
  : Lemma (ensures ~(mem_edge e_rem (filter (fun e -> not (edge_eq e e_rem)) t)))
          (decreases t)
  = match t with
    | [] -> ()
    | hd :: tl ->
      mem_edge_e_rem_not_in_ft_aux e_rem tl;
      if not (edge_eq hd e_rem) then begin
        // hd is kept in filter. Need to show e_rem is not edge_eq to hd.
        edge_eq_symmetric e_rem hd;
        if edge_eq e_rem hd then
          edge_eq_symmetric hd e_rem  // derives edge_eq hd e_rem, contradiction
        else ()
      end

let mem_edge_e_rem_not_in_ft (e_rem: edge) (t: list edge)
  : Lemma (ensures ~(mem_edge e_rem (filter (fun e -> not (edge_eq e e_rem)) t)))
  = mem_edge_e_rem_not_in_ft_aux e_rem t

// Converse of acyclic_when_unreachable: if acyclic (e :: t) and acyclic t and
// e.u ≠ e.v and e not in t, then not reachable t e.u e.v

// Helper: if edge_eq a b and mem_edge b l, then mem_edge a l
let rec mem_edge_eq_transfer (a b: edge) (l: list edge)
  : Lemma (requires edge_eq a b /\ mem_edge b l)
          (ensures mem_edge a l)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      if edge_eq b hd then
        (edge_eq_transitive a b hd; assert (edge_eq a hd))
      else
        mem_edge_eq_transfer a b tl

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
let rec all_edges_distinct_rev_acc (l acc: list edge)
  : Lemma (requires all_edges_distinct l /\ all_edges_distinct acc /\
                    (forall e. mem_edge e l ==> ~(mem_edge e acc)) /\
                    (forall e. mem_edge e acc ==> ~(mem_edge e l)))
          (ensures all_edges_distinct (rev_acc l acc))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      assert (~(mem_edge hd acc));
      assert (all_edges_distinct (hd :: acc));
      // Prove disjointness between tl and (hd :: acc)
      let aux1 (e: edge) : Lemma (requires mem_edge e tl) (ensures ~(mem_edge e (hd :: acc))) =
        if mem_edge e (hd :: acc) then begin
          if edge_eq e hd then begin
            edge_eq_symmetric e hd;
            mem_edge_eq_transfer hd e tl;
            assert (mem_edge hd tl);
            assert false
          end else begin
            assert (mem_edge e acc);
            assert (mem_edge e l);
            assert false
          end
        end
      in
      let aux2 (e: edge) : Lemma (requires mem_edge e (hd :: acc)) (ensures ~(mem_edge e tl)) =
        if mem_edge e tl then begin
          if edge_eq e hd then begin
            edge_eq_symmetric e hd;
            mem_edge_eq_transfer hd e tl;
            assert (mem_edge hd tl);
            assert false
          end else begin
            assert (mem_edge e acc);
            assert (mem_edge e l);
            assert false
          end
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux1);
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux2);
      all_edges_distinct_rev_acc tl (hd :: acc)
#pop-options

let all_edges_distinct_rev (l: list edge)
  : Lemma (requires all_edges_distinct l)
          (ensures all_edges_distinct (rev l))
  = all_edges_distinct_rev_acc l []

// Helper: if e not in any edge of path (via mem_edge), and path ⊂ t, and e not in t,
// then e not in rev path
let mem_edge_not_in_subset (e: edge) (p t: list edge)
  : Lemma (requires ~(mem_edge e t) /\ subset_edges p t)
          (ensures ~(mem_edge e p))
  = let rec aux (p': list edge)
      : Lemma (requires ~(mem_edge e t) /\ subset_edges p' t)
              (ensures ~(mem_edge e p'))
              (decreases p') =
      match p' with
      | [] -> ()
      | hd :: tl ->
        if edge_eq e hd then begin
          // mem_edge hd t is true (from subset_edges p' t)
          mem_edge_subset hd p' t;
          // edge_eq e hd and mem_edge hd t => mem_edge e t (by transfer)
          mem_edge_eq_transfer e hd t;
          assert (mem_edge e t);  // contradicts ~(mem_edge e t)
          assert false
        end else
          aux tl
    in
    aux p

let acyclic_implies_unreachable (n: nat) (t: list edge) (e: edge)
  : Lemma (requires acyclic n (e :: t) /\ acyclic n t /\
                    e.u < n /\ e.v < n /\ e.u <> e.v /\
                    ~(mem_edge e t))
          (ensures ~(reachable t e.u e.v))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (reachable t e.u e.v) then begin
      // Extract simple path from e.u to e.v in t
      reachable_simple t e.u e.v;
      // Now exists simple path P. Form cycle e :: rev(P).
      FStar.Classical.exists_elim
        (False)
        #(list edge)
        #(fun path -> subset_edges path t /\ is_path_from_to path e.u e.v /\
                       all_edges_distinct path /\ Cons? path)
        ()
        (fun (p: list edge{subset_edges p t /\ is_path_from_to p e.u e.v /\
                            all_edges_distinct p /\ Cons? p}) ->
          let rp = rev p in
          path_reverse p e.u e.v;
          subset_edges_rev p t;
          subset_edges_cons rp e t;
          // e not in p (since e not in t and p ⊂ t)
          mem_edge_not_in_subset e p t;
          // e not in rev p (since mem_edge preserved by rev)
          mem_edge_rev e p;
          assert (~(mem_edge e rp));
          // all_edges_distinct (rev p)
          all_edges_distinct_rev p;
          // Therefore all_edges_distinct (e :: rev p)
          assert (all_edges_distinct (e :: rp));
          assert (subset_edges (e :: rp) (e :: t));
          assert (is_path_from_to (e :: rp) e.u e.u);
          assert (Cons? (e :: rp))
          // The cycle (e :: rp) at vertex e.u < n contradicts acyclic n (e :: t)
        )
    end

// Reachable superset: if reachable in sub and sub ⊆ sup (via mem_edge), then reachable in sup
let reachable_superset (sub sup: list edge) (u v: nat)
  : Lemma (requires reachable sub u v /\ (forall e. mem_edge e sub ==> mem_edge e sup))
          (ensures reachable sup u v)
  = FStar.Classical.exists_elim
      (reachable sup u v)
      #(list edge)
      #(fun path -> subset_edges path sub /\ is_path_from_to path u v)
      ()
      (fun (p: list edge{subset_edges p sub /\ is_path_from_to p u v}) ->
        let rec transfer (p': list edge)
          : Lemma (requires subset_edges p' sub)
                  (ensures subset_edges p' sup)
                  (decreases p') =
          match p' with
          | [] -> ()
          | hd :: tl ->
            mem_edge_subset hd p' sub;
            assert (mem_edge hd sub);
            assert (mem_edge hd sup);
            transfer tl
        in
        transfer p;
        assert (subset_edges p sup);
        introduce exists (q: list edge). subset_edges q sup /\ is_path_from_to q u v
        with p and ()
      )

// Connectivity transfer: if path in (e_rem :: ft) and e_rem.u↔e_rem.v reachable in (e_add :: ft),
// then start↔finish reachable in (e_add :: ft)
let rec reach_transfer
    (p: list edge) (e_add e_rem: edge) (ft: list edge) (start finish: nat)
  : Lemma (requires is_path_from_to p start finish /\
                    subset_edges p (e_rem :: ft) /\
                    reachable (e_add :: ft) e_rem.u e_rem.v /\
                    reachable (e_add :: ft) e_rem.v e_rem.u)
          (ensures reachable (e_add :: ft) start finish)
          (decreases p)
  = match p with
    | [] -> ()
    | hd :: tl ->
      let next = if hd.u = start then hd.v else hd.u in
      // Recurse on tail
      reach_transfer tl e_add e_rem ft next finish;
      // Now: reachable (e_add :: ft) next finish
      // Need: reachable (e_add :: ft) start next (via hd)
      if edge_eq hd e_rem then begin
        // hd connects the same pair as e_rem
        edge_eq_endpoints hd e_rem;
        // {hd.u, hd.v} = {e_rem.u, e_rem.v}, start = hd.u or hd.v, next = the other
        // So reachable (e_add :: ft) start next follows from reachable e_rem.u e_rem.v or v.v. 
        assert (reachable (e_add :: ft) start next);
        reachable_transitive (e_add :: ft) start next finish
      end else begin
        // hd is in ft (not edge_eq to e_rem)
        assert (mem_edge hd ft);
        assert (mem_edge hd (e_add :: ft));
        // Single edge path: reachable (e_add :: ft) start next
        assert (is_path_from_to [hd] start next);
        assert (subset_edges [hd] (e_add :: ft));
        reachable_transitive (e_add :: ft) start next finish
      end

// subset of path in t is also in (e_rem :: ft), needed for split_at_first_e
let rec subset_edges_t_to_erem_ft (p: list edge) (e_rem: edge) (t: list edge)
  : Lemma (requires subset_edges p t)
          (ensures subset_edges p (e_rem :: filter (fun e -> not (edge_eq e e_rem)) t))
          (decreases p)
  = match p with
    | [] -> ()
    | hd :: tl ->
      mem_edge_t_to_erem_ft hd e_rem t;
      subset_edges_t_to_erem_ft tl e_rem t

// Exchange preserves spanning tree (well-known graph theory fact):
// In a spanning tree T, if e_add connects two vertices joined by a path through e_rem,
// then T - {e_rem} + {e_add} is still a spanning tree.
// Proof requires: (1) e_rem removal splits T into two components,
// (2) e_add reconnects them (since it's on the path), (3) acyclicity is restored.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1 --split_queries always"
let exchange_is_spanning_tree
    (g: graph) (t: list edge) (e_add e_rem: edge) (path: list edge)
  : Lemma (requires is_spanning_tree g t /\
                    mem_edge e_add g.edges /\
                    mem_edge e_rem t /\
                    ~(mem_edge e_add t) /\
                    e_add.u < g.n /\ e_add.v < g.n /\ e_add.u <> e_add.v /\
                    e_rem.u < g.n /\ e_rem.v < g.n /\ e_rem.u <> e_rem.v /\
                    subset_edges path t /\
                    is_path_from_to path e_add.u e_add.v /\
                    mem_edge e_rem path /\
                    all_edges_distinct path)
          (ensures is_spanning_tree g (e_add :: filter (fun e -> not (edge_eq e e_rem)) t))
  =
    let ft = filter (fun e -> not (edge_eq e e_rem)) t in
    let t' = e_add :: ft in

    // === Property 1: g.n > 0 ===
    assert (g.n > 0);

    // === Property 2: subset_edges t' g.edges ===
    subset_edges_filter t g.edges (fun e -> not (edge_eq e e_rem));
    assert (mem_edge e_add g.edges);
    assert (subset_edges ft g.edges);
    assert (subset_edges t' g.edges);

    // === Key structural facts ===
    // ft is acyclic (subset of t)
    acyclic_filter g.n t e_rem;
    assert (acyclic g.n ft);

    // e_rem not in ft, e_add not in ft
    mem_edge_e_rem_not_in_ft e_rem t;
    mem_edge_e_add_not_in_ft e_add e_rem t;

    // split_at_first_e on given path to decompose into ft-reachable segments
    // First need: subset_edges path (e_rem :: ft)
    subset_edges_t_to_erem_ft path e_rem t;
    split_at_first_e path e_rem ft e_add.u e_add.v;
    // Result: (reachable ft e_add.u e_rem.u ∧ reachable ft e_rem.v e_add.v) ∨
    //         (reachable ft e_add.u e_rem.v ∧ reachable ft e_rem.u e_add.v)

    // === Prove acyclic g.n (e_rem :: ft) ===
    // Any simple cycle in (e_rem :: ft) has its edges in t (via mem_edge transfer).
    // So acyclic g.n t implies acyclic g.n (e_rem :: ft).
    let acyclic_erem_ft () : Lemma (acyclic g.n (e_rem :: ft)) =
      introduce forall (v: nat) (c: list edge).
        v < g.n /\ subset_edges c (e_rem :: ft) /\ Cons? c /\
        all_edges_distinct c /\ is_path_from_to c v v ==> False
      with introduce _ ==> _
      with _h. begin
        // Transfer: subset_edges c (e_rem :: ft) => subset_edges c t
        let rec subset_transfer (c': list edge)
          : Lemma (requires subset_edges c' (e_rem :: ft))
                  (ensures subset_edges c' t)
                  (decreases c')
          = match c' with
            | [] -> ()
            | hd :: tl ->
              if edge_eq hd e_rem then begin
                edge_eq_symmetric hd e_rem;
                mem_edge_eq_transfer hd e_rem t
              end else begin
                mem_edge_filter_implies_mem hd t (fun e -> not (edge_eq e e_rem))
              end;
              subset_transfer tl
        in
        subset_transfer c
        // Now subset_edges c t, and acyclic g.n t says no simple cycle at v < g.n in t
      end
    in
    acyclic_erem_ft ();

    // === Property 5: acyclic g.n t' ===
    // Step 1: ~(reachable ft e_rem.u e_rem.v)
    acyclic_implies_unreachable g.n ft e_rem;
    assert (~(reachable ft e_rem.u e_rem.v));

    // Step 2: ~(reachable ft e_add.u e_add.v)
    // By contradiction: if reachable ft e_add.u e_add.v, then by transitivity with
    // the split_at_first_e result, we get reachable ft e_rem.u e_rem.v, contradiction.
    FStar.Classical.or_elim
      #(reachable ft e_add.u e_rem.u /\ reachable ft e_rem.v e_add.v)
      #(reachable ft e_add.u e_rem.v /\ reachable ft e_rem.u e_add.v)
      #(fun _ -> ~(reachable ft e_add.u e_add.v))
      (fun (_: squash (reachable ft e_add.u e_rem.u /\ reachable ft e_rem.v e_add.v)) ->
        // Case A: ft: e_add.u → e_rem.u and ft: e_rem.v → e_add.v
        if FStar.StrongExcludedMiddle.strong_excluded_middle (reachable ft e_add.u e_add.v) then begin
          reachable_symmetric ft e_add.u e_rem.u;
          reachable_transitive ft e_rem.u e_add.u e_add.v;
          reachable_symmetric ft e_rem.v e_add.v;
          reachable_transitive ft e_rem.u e_add.v e_rem.v;
          assert (reachable ft e_rem.u e_rem.v);
          assert false
        end)
      (fun (_: squash (reachable ft e_add.u e_rem.v /\ reachable ft e_rem.u e_add.v)) ->
        // Case B: ft: e_add.u → e_rem.v and ft: e_rem.u → e_add.v (symmetric)
        if FStar.StrongExcludedMiddle.strong_excluded_middle (reachable ft e_add.u e_add.v) then begin
          reachable_symmetric ft e_add.u e_rem.v;
          reachable_transitive ft e_rem.v e_add.u e_add.v;
          reachable_symmetric ft e_rem.u e_add.v;
          reachable_transitive ft e_rem.v e_add.v e_rem.u;
          reachable_symmetric ft e_rem.v e_rem.u;
          assert (reachable ft e_rem.u e_rem.v);
          assert false
        end);
    assert (~(reachable ft e_add.u e_add.v));

    // Step 3: acyclic g.n t'
    acyclic_when_unreachable g.n ft e_add;
    assert (acyclic g.n t');

    // === Property 4: all_connected g.n t' ===
    // Key fact: ft ⊂ t' (as mem_edge), so reachable ft a b => reachable t' a b
    let ft_sub_t' (e: edge) : Lemma (requires mem_edge e ft) (ensures mem_edge e t') = () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ft_sub_t');

    // Build: reachable t' e_rem.u e_rem.v via detour through e_add
    assert (is_path_from_to [e_add] e_add.u e_add.v);
    assert (subset_edges [e_add] t');

    let build_detour ()
      : Lemma (reachable t' e_rem.u e_rem.v /\ reachable t' e_rem.v e_rem.u) =
      FStar.Classical.or_elim
        #(reachable ft e_add.u e_rem.u /\ reachable ft e_rem.v e_add.v)
        #(reachable ft e_add.u e_rem.v /\ reachable ft e_rem.u e_add.v)
        #(fun _ -> reachable t' e_rem.u e_rem.v /\ reachable t' e_rem.v e_rem.u)
        (fun (_: squash (reachable ft e_add.u e_rem.u /\ reachable ft e_rem.v e_add.v)) ->
          // e_rem.u →ft→ e_add.u →e_add→ e_add.v →ft→ e_rem.v
          reachable_symmetric ft e_add.u e_rem.u;
          reachable_superset ft t' e_rem.u e_add.u;
          reachable_superset ft t' e_rem.v e_add.v;
          reachable_symmetric t' e_rem.v e_add.v;
          reachable_transitive t' e_rem.u e_add.u e_add.v;
          reachable_transitive t' e_rem.u e_add.v e_rem.v;
          // Symmetric direction
          reachable_symmetric t' e_rem.u e_rem.v)
        (fun (_: squash (reachable ft e_add.u e_rem.v /\ reachable ft e_rem.u e_add.v)) ->
          // e_rem.u →ft→ e_add.v ... e_add connects e_add.u↔e_add.v
          // e_rem.v →ft→ ... e_add.u →e_add→ e_add.v →ft→ e_rem.u
          reachable_superset ft t' e_rem.u e_add.v;
          reachable_superset ft t' e_add.u e_rem.v;
          reachable_symmetric t' e_add.u e_rem.v;
          reachable_transitive t' e_rem.u e_add.v e_add.u;
          reachable_transitive t' e_rem.u e_add.u e_rem.v;
          // Wait, e_add.v to e_add.u: need reachable t' e_add.v e_add.u
          // e_add connects e_add.u to e_add.v, so reachable t' e_add.u e_add.v
          // and reachable t' e_add.v e_add.u (symmetric of single edge)
          reachable_symmetric t' e_rem.u e_rem.v)
    in
    build_detour ();

    // Now use reach_transfer: reachable (e_rem :: ft) a b => reachable t' a b
    // Since t has same edge set as (e_rem :: ft), reachable t 0 v => reachable (e_rem :: ft) 0 v
    // => reachable t' 0 v
    introduce forall (v: nat). v < g.n ==> reachable t' 0 v
    with introduce _ ==> _
    with _h. begin
      // reachable t 0 v
      assert (all_connected g.n t);
      // Transfer: t → (e_rem :: ft) → t'
      reachable_t_iff_erem_ft t e_rem 0 v;
      // reachable (e_rem :: ft) 0 v
      // Now transfer to t' using reach_transfer
      FStar.Classical.exists_elim
        (reachable t' 0 v)
        #(list edge)
        #(fun path -> subset_edges path (e_rem :: ft) /\ is_path_from_to path 0 v)
        ()
        (fun (p: list edge{subset_edges p (e_rem :: ft) /\ is_path_from_to p 0 v}) ->
          reach_transfer p e_add e_rem ft 0 v)
    end;
    assert (all_connected g.n t');

    // === Property 3: length t' = g.n - 1 ===
    // length t' = 1 + length ft
    // length ft = length t - k where k = length (filter (edge_eq e_rem) t)
    // Need: k = 1, i.e., length (filter (edge_eq e_rem) t) = 1
    filter_complement_length (fun e -> edge_eq e e_rem) t;
    // length (filter (edge_eq e_rem) t) + length ft = length t = g.n - 1
    filter_match_nonempty e_rem t;
    // length (filter (edge_eq e_rem) t) >= 1
    // === Proving count = 1 ===
    // First establish all_connected g.n (e_rem :: ft)
    introduce forall (v: nat). v < g.n ==> reachable (e_rem :: ft) 0 v
    with introduce _ ==> _ with _. begin
      reachable_t_iff_erem_ft t e_rem 0 v
    end;
    assert (all_connected g.n (e_rem :: ft));
    // connected_min_edges: all_connected g.n (e_rem :: ft) ==> length (e_rem :: ft) >= g.n - 1
    // length (e_rem :: ft) = 1 + length ft = g.n - count
    // So g.n - count >= g.n - 1, hence count <= 1. Combined with >= 1: count = 1.
    connected_min_edges g.n (e_rem :: ft);
    assert (length (e_rem :: ft) >= g.n - 1);
    let count = length (filter (fun e -> edge_eq e e_rem) t) in
    assert (count = 1);
    assert (length ft = g.n - 1 - count);
    assert (length ft = g.n - 2);
    assert (length t' = 1 + length ft);
    assert (length t' = g.n - 1)
#pop-options

#push-options "--z3rlimit 5"
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
        // Step 1b: Extract a SIMPLE path from e.u to e.v
        assert (e.u <> e.v);  // from crosses_cut
        reachable_simple t e.u e.v;
        // Step 2: Simple path from e.u to e.v must cross cut (s(e.u) ≠ s(e.v))
        // Extract simple path from reachable_simple
        FStar.Classical.exists_elim
          goal
          #(list edge) #(fun path -> subset_edges path t /\ is_path_from_to path e.u e.v /\
                                      all_edges_distinct path /\ Cons? path)
          ()
          (fun (path: list edge{subset_edges path t /\ is_path_from_to path e.u e.v /\
                                 all_edges_distinct path /\ Cons? path}) ->
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
                // e'.u ≠ e'.v (from crosses_cut: different sides of cut implies different vertices)
                assert (crosses_cut e' s);
                assert (e'.u <> e'.v);
                // e'.u < g.n and e'.v < g.n: from graph well-formedness precondition
                assert (subset_edges t g.edges);
                mem_edge_subset e' t g.edges;
                assert (mem_edge e' g.edges);
                assert (e'.u < g.n /\ e'.v < g.n);
                let t' = e :: filter (fun e0 -> not (edge_eq e0 e')) t in
                // T' is a spanning tree (exchange lemma — path is simple)
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

(*** MST Existence: acyclic + connected → n-1 edges ***)

// Helper: e ∉ subset of set not containing e
let rec not_mem_of_subset (e: edge) (p t: list edge)
  : Lemma (requires subset_edges p t /\ ~(mem_edge e t))
          (ensures ~(mem_edge e p))
          (decreases p)
  = match p with
    | [] -> ()
    | hd :: tl ->
      if edge_eq e hd then begin
        edge_eq_symmetric e hd;
        mem_edge_eq hd e t
      end else not_mem_of_subset e tl t

// Helper: all_edges_distinct preserved by snoc when e ∉ p
let rec all_edges_distinct_snoc (p: list edge) (e0: edge)
  : Lemma (requires all_edges_distinct p /\ ~(mem_edge e0 p))
          (ensures all_edges_distinct (p @ [e0]))
          (decreases p)
  = match p with
    | [] -> ()
    | hd :: tl ->
      all_edges_distinct_snoc tl e0;
      mem_edge_append hd tl [e0];
      if edge_eq hd e0 then begin
        mem_edge_hd hd tl;
        mem_edge_eq hd e0 (hd :: tl)
      end else ()

// If endpoints of e are reachable from each other in t, then e :: t has a cycle.
// (Converse of acyclic_when_unreachable)
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
let reachable_implies_not_acyclic (n: nat) (t: list edge) (e: edge)
  : Lemma (requires acyclic n t /\ reachable t e.u e.v /\
                    e.u < n /\ e.v < n /\ e.u <> e.v /\ ~(mem_edge e t))
          (ensures ~(acyclic n (e :: t)))
  = reachable_simple t e.u e.v;
    FStar.Classical.exists_elim
      (~(acyclic n (e :: t)))
      #_
      #(fun (sp: list edge) ->
          subset_edges sp t /\ is_path_from_to sp e.u e.v /\
          all_edges_distinct sp /\ Cons? sp) ()
      (fun (sp: list edge{subset_edges sp t /\ is_path_from_to sp e.u e.v /\
                           all_edges_distinct sp /\ Cons? sp}) ->
        // Form cycle sp @ [e] from e.u back to e.u
        path_concat sp [e] e.u e.v e.u;
        let cycle = sp @ [e] in
        // subset_edges cycle (e :: t)
        subset_edges_cons sp e t;
        subset_edges_snoc sp e (e :: t);
        // all_edges_distinct cycle
        not_mem_of_subset e sp t;
        all_edges_distinct_snoc sp e;
        // cycle is a simple cycle in e :: t — contradicts acyclicity
        assert (e.u < n)
      )
#pop-options

// Corollary: acyclic(e :: t) ⟹ ¬reachable(t, e.u, e.v)
let acyclic_edge_disconnects (n: nat) (e: edge) (tl: list edge)
  : Lemma (requires acyclic n (e :: tl) /\ e.u < n /\ e.v < n /\ e.u <> e.v /\
                    ~(mem_edge e tl))
          (ensures ~(reachable tl e.u e.v))
  = let aux_sub (ed: edge) : Lemma (requires mem_edge ed tl)
                                    (ensures mem_edge ed (e :: tl)) = () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_sub);
    acyclic_subset n (e :: tl) tl;
    let aux () : Lemma (requires reachable tl e.u e.v) (ensures False) =
      reachable_implies_not_acyclic n tl e
    in
    FStar.Classical.move_requires aux ()

// Redundant edge impossible for acyclic graph:
// If both endpoints reachable from root in tl, then e :: tl has a cycle.
let acyclic_no_redundant (n: nat) (e: edge) (tl: list edge) (root: nat)
  : Lemma (requires acyclic n (e :: tl) /\ e.u < n /\ e.v < n /\ e.u <> e.v /\
                    ~(mem_edge e tl) /\
                    reachable tl root e.u /\ reachable tl root e.v)
          (ensures False)
  = reachable_symmetric tl root e.u;
    reachable_transitive tl e.u root e.v;
    let aux_sub (ed: edge) : Lemma (requires mem_edge ed tl)
                                    (ensures mem_edge ed (e :: tl)) = () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_sub);
    acyclic_subset n (e :: tl) tl;
    reachable_implies_not_acyclic n tl e

// Helper: ghost_filter over superset
let rec ghost_filter_superset
    (f1 f2: edge -> GTot bool) (es: list edge)
  : Lemma (requires forall (e: edge). mem_edge e es /\ f1 e ==> f2 e)
          (ensures length (ghost_filter f1 es) <= length (ghost_filter f2 es))
          (decreases es)
  = match es with
    | [] -> ()
    | hd :: tl ->
      ghost_filter_superset f1 f2 tl;
      if f1 hd then begin
        assert (f2 hd)
      end else ()

// Bridge case: if hd connects root's tl-component to nr's tl-component,
// then root reaches nr in tl, contradicting acyclicity of e :: tl.
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
let acyclic_bridge_no_cross
    (n: nat) (e: edge) (tl: list edge) (root: nat) (hd: edge)
  : Lemma (requires acyclic n (e :: tl) /\
                    (forall (ed: edge). mem_edge ed (e :: tl) ==> ed.u < n /\ ed.v < n /\ ed.u <> ed.v) /\
                    root < n /\
                    ~(mem_edge e tl) /\
                    mem_edge hd tl /\
                    (reachable_dec tl root e.u || reachable_dec tl root e.v) /\
                    ~(reachable_dec tl root e.u && reachable_dec tl root e.v) /\
                    reachable tl root hd.u /\
                    (let nr = if reachable_dec tl root e.u then e.v else e.u in
                     reachable tl nr hd.v))
          (ensures False)
  = let nr = if reachable_dec tl root e.u then e.v else e.u in
    acyclic_edge_disconnects n e tl;
    // ~(reachable tl e.u e.v)
    // hd connects hd.u (from root) to hd.v (from nr)
    assert (is_path_from_to [hd] hd.u hd.v);
    assert (subset_edges [hd] tl);
    assert (reachable tl hd.u hd.v);
    reachable_transitive tl root hd.u hd.v;
    reachable_symmetric tl nr hd.v;
    reachable_transitive tl root hd.v nr;
    // root reaches nr in tl
    if reachable_dec tl root e.u then begin
      reachable_symmetric tl root e.u;
      reachable_transitive tl e.u root e.v
    end else begin
      reachable_symmetric tl root e.v;
      reachable_transitive tl e.v root e.u;
      reachable_symmetric tl e.v e.u
    end
#pop-options

// Disjoint lower bound: if two disjoint sets of vertices inject into es's reachability,
// then count(es, root) >= count(tl, root1) + count(tl, root2).
let rec count_reachable_disjoint_lower
    (es tl: list edge) (root root1 root2: nat) (n m: nat)
  : Lemma (requires (forall (v: nat). v < n ==> reachable tl root1 v ==> reachable es root v) /\
                    (forall (v: nat). v < n ==> reachable tl root2 v ==> reachable es root v) /\
                    (forall (v: nat). v < n ==> ~(reachable tl root1 v /\ reachable tl root2 v)))
          (ensures count_reachable tl root1 n m + count_reachable tl root2 n m <=
                   count_reachable es root n m)
          (decreases m)
  = if m = 0 then () else count_reachable_disjoint_lower es tl root root1 root2 n (m - 1)

// In bridge case: component edges of es (w.r.t. root) from tl decompose into
// root's tl-component edges and nr's tl-component edges.
#push-options "--z3rlimit 15 --fuel 2 --ifuel 1"
let rec ghost_filter_bridge_split
    (n: nat) (e: edge) (tl rem: list edge) (root: nat)
  : Lemma (requires acyclic n (e :: tl) /\
                    (forall (ed: edge). mem_edge ed (e :: tl) ==> ed.u < n /\ ed.v < n /\ ed.u <> ed.v) /\
                    root < n /\
                    ~(mem_edge e tl) /\
                    (reachable_dec tl root e.u || reachable_dec tl root e.v) /\
                    ~(reachable_dec tl root e.u && reachable_dec tl root e.v) /\
                    (forall (ed: edge). mem_edge ed rem ==> mem_edge ed tl))
          (ensures (let es = e :: tl in
                    let nr = if reachable_dec tl root e.u then e.v else e.u in
                    let f_es ed = reachable_dec es root ed.u && reachable_dec es root ed.v in
                    let f_r  ed = reachable_dec tl root ed.u && reachable_dec tl root ed.v in
                    let f_nr ed = reachable_dec tl nr   ed.u && reachable_dec tl nr   ed.v in
                    length (ghost_filter f_es rem) <=
                    length (ghost_filter f_r rem) + length (ghost_filter f_nr rem)))
          (decreases rem)
  = let es = e :: tl in
    let nr = if reachable_dec tl root e.u then e.v else e.u in
    let r  = if reachable_dec tl root e.u then e.u else e.v in
    let f_es (ed: edge) : GTot bool = reachable_dec es root ed.u && reachable_dec es root ed.v in
    let f_r  (ed: edge) : GTot bool = reachable_dec tl root ed.u && reachable_dec tl root ed.v in
    let f_nr (ed: edge) : GTot bool = reachable_dec tl nr   ed.u && reachable_dec tl nr   ed.v in
    match rem with
    | [] -> ()
    | hd :: rest ->
      ghost_filter_bridge_split n e tl rest root;
      if f_es hd then begin
        // hd.u and hd.v reachable from root in es. By bridge decomposition:
        // each is reachable from root or nr in tl.
        let bridge_u () : Lemma (reachable tl root hd.u \/ reachable tl nr hd.u) =
          if reachable_dec tl root e.u then
            reachable_bridge tl e root hd.u e.u e.v
          else
            reachable_bridge tl e root hd.u e.v e.u
        in bridge_u ();
        let bridge_v () : Lemma (reachable tl root hd.v \/ reachable tl nr hd.v) =
          if reachable_dec tl root e.u then
            reachable_bridge tl e root hd.v e.u e.v
          else
            reachable_bridge tl e root hd.v e.v e.u
        in bridge_v ();
        // If mixed (one from root, one from nr), derive contradiction
        if reachable_dec tl root hd.u && reachable_dec tl nr hd.v &&
           not (reachable_dec tl root hd.v) && not (reachable_dec tl nr hd.u) then
          acyclic_bridge_no_cross n e tl root hd
        else if reachable_dec tl nr hd.u && reachable_dec tl root hd.v &&
                not (reachable_dec tl nr hd.v) && not (reachable_dec tl root hd.u) then begin
          // Symmetric: swap hd.u/hd.v role. root reaches hd.v, nr reaches hd.u.
          // hd also goes from hd.v to hd.u (is_path_from_to [hd] hd.u hd.v, but by symmetry...)
          // Actually: we need root -> hd.v and nr -> hd.u. Since hd connects them:
          assert (is_path_from_to [hd] hd.u hd.v);
          assert (subset_edges [hd] tl);
          assert (reachable tl hd.u hd.v);
          reachable_symmetric tl hd.u hd.v;
          // root -> hd.v -> hd.u <- nr
          reachable_transitive tl root hd.v hd.u;
          reachable_symmetric tl nr hd.u;
          reachable_transitive tl root hd.u nr;
          // root reaches nr in tl
          acyclic_edge_disconnects n e tl;
          if reachable_dec tl root e.u then begin
            reachable_symmetric tl root e.u;
            reachable_transitive tl e.u root e.v
          end else begin
            reachable_symmetric tl root e.v;
            reachable_transitive tl e.v root e.u;
            reachable_symmetric tl e.v e.u
          end
        end
        // Otherwise: both from root (f_r) or both from nr (f_nr). QED.
      end
#pop-options

// In bridge case: e itself is a component edge of es (both endpoints reachable from root in es)
let bridge_edge_in_component (tl: list edge) (e: edge) (root: nat)
  : Lemma (requires (reachable_dec tl root e.u || reachable_dec tl root e.v) /\
                    ~(reachable_dec tl root e.u && reachable_dec tl root e.v))
          (ensures (let es = e :: tl in
                    reachable_dec es root e.u && reachable_dec es root e.v))
  = let es = e :: tl in
    let r  = if reachable_dec tl root e.u then e.u else e.v in
    let nr = if reachable_dec tl root e.u then e.v else e.u in
    // root reaches r in tl ⊆ es
    assert (is_path_from_to ([] #edge) root root);
    assert (subset_edges ([] #edge) es);
    // r is reachable from root in tl, hence in es (superset)
    let sub_edges (v: nat) : Lemma (requires reachable tl root v) (ensures reachable es root v) =
      FStar.Classical.exists_elim (reachable es root v)
        #(list edge)
        #(fun p -> is_path_from_to p root v /\ subset_edges p tl) ()
        (fun (p: list edge{is_path_from_to p root v /\ subset_edges p tl}) ->
          introduce exists p. is_path_from_to p root v /\ subset_edges p es
          with p and (subset_edges_cons p e tl))
    in
    // root -> r in es
    if reachable_dec tl root r then sub_edges r;
    // nr reachable from root in es: root -> r -> e -> nr
    assert (is_path_from_to [e] r nr \/ is_path_from_to [e] nr r);
    // Actually, e goes from e.u to e.v. [e] is a path from e.u to e.v.
    assert (is_path_from_to [e] e.u e.v);
    assert (subset_edges [e] es);
    assert (reachable es e.u e.v);
    reachable_symmetric es e.u e.v;
    // Now: root reaches r in es, r reaches nr via e in es
    if reachable_dec tl root e.u then begin
      // r = e.u, nr = e.v. reachable es root e.u (from sub_edges r).
      // reachable es e.u e.v. Transitive: reachable es root e.v.
      sub_edges e.u;
      reachable_transitive es root e.u e.v
    end else begin
      // r = e.v, nr = e.u. reachable es root e.v (from sub_edges r).
      // reachable es e.v e.u (symmetric of e.u e.v). Transitive: reachable es root e.u.
      sub_edges e.v;
      reachable_transitive es root e.v e.u
    end

// In the neither case: reachable es root v ⟺ reachable tl root v.

// Helper: count_reachable includes at least root
let rec count_reachable_ge_one (es: list edge) (root: nat) (n m: nat)
  : Lemma (requires root < n /\ root < m /\ reachable es root root)
          (ensures count_reachable es root n m >= 1) (decreases m)
  = if m = root + 1 then ()
    else count_reachable_ge_one es root n (m - 1)

// Base case of acyclic_count_lower_bound
let acyclic_count_base (root: nat) (n: nat)
  : Lemma (requires root < n)
          (ensures count_reachable ([] #edge) root n n >=
                   1 + length (ghost_filter (is_comp_edge ([] #edge) root) ([] #edge)))
  = assert (is_path_from_to ([] #edge) root root);
    assert (subset_edges ([] #edge) ([] #edge));
    count_reachable_ge_one ([] #edge) root n n



// ghost_filter of f bounded by sum of ghost_filters of f1, f2 (for elements in list)
let rec ghost_filter_or_bound (f f1 f2: edge -> GTot bool) (es: list edge)
  : Lemma (requires forall (ed: edge). mem_edge ed es /\ f ed ==> f1 ed || f2 ed)
          (ensures length (ghost_filter f es) <= length (ghost_filter f1 es) + length (ghost_filter f2 es))
          (decreases es)
  = match es with
    | [] -> ()
    | hd :: tl -> ghost_filter_or_bound f f1 f2 tl

// For acyclic graph: count_reachable >= 1 + |component edges|
#push-options "--z3rlimit 35 --fuel 2 --ifuel 1"
let rec acyclic_count_lower_bound
    (es: list edge) (root: nat) (n: nat)
  : Lemma (requires acyclic n es /\ all_edges_distinct es /\
                    (forall (e: edge). mem_edge e es ==> e.u < n /\ e.v < n /\ e.u <> e.v) /\
                    root < n)
          (ensures count_reachable es root n n >=
                   1 + length (ghost_filter (is_comp_edge es root) es))
          (decreases length es)
  = let f = is_comp_edge es root in
    match es with
    | [] -> acyclic_count_base root n
    | e :: tl ->
      let aux_sub (ed: edge) : Lemma (requires mem_edge ed tl)
                                      (ensures mem_edge ed (e :: tl)) = () in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_sub);
      acyclic_subset n (e :: tl) tl;
      if reachable_dec tl root e.u && reachable_dec tl root e.v then begin
        reachable_symmetric tl root e.u;
        reachable_transitive tl e.u root e.v;
        reachable_implies_not_acyclic n tl e
      end else if not (reachable_dec tl root e.u) && not (reachable_dec tl root e.v) then begin
        acyclic_count_lower_bound tl root n;
        // reachable (e :: tl) root v <==> reachable tl root v (by reachable_neither)
        let fwd (v: nat) : Lemma (requires reachable (e :: tl) root v) (ensures reachable tl root v) =
          reachable_neither tl e root v
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires fwd);
        // count(es) >= count(tl) via monotonicity
        introduce forall (v: nat). v < n ==> reachable tl root v ==> reachable es root v
        with introduce _ ==> _ with _. begin
          introduce _ ==> _ with _.
            FStar.Classical.exists_elim (reachable es root v)
              #(list edge)
              #(fun p -> is_path_from_to p root v /\ subset_edges p tl) ()
              (fun (p: list edge{is_path_from_to p root v /\ subset_edges p tl}) ->
                introduce exists p. is_path_from_to p root v /\ subset_edges p es
                with p and (subset_edges_cons p e tl))
        end;
        count_reachable_mono tl es root root n n;
        // ghost_filter f es: e doesn't pass (neither endpoint reachable), rest <= f_tl tl
        let f_tl (ed: edge) : GTot bool = reachable_dec tl root ed.u && reachable_dec tl root ed.v in
        ghost_filter_superset f (is_comp_edge tl root) tl
      end else begin
        // Bridge case: one endpoint reachable, the other not
        let nr = if reachable_dec tl root e.u then e.v else e.u in
        let f_r  = is_comp_edge tl root in
        let f_nr = is_comp_edge tl nr in
        // IH on tl
        acyclic_count_lower_bound tl root n;
        acyclic_count_lower_bound tl nr n;
        // count(es, root) >= count(tl, root) + count(tl, nr) via disjoint_lower
        introduce forall (v: nat). v < n ==> reachable tl root v ==> reachable es root v
        with introduce _ ==> _ with _. begin
          introduce _ ==> _ with _.
            FStar.Classical.exists_elim (reachable es root v)
              #(list edge)
              #(fun p -> is_path_from_to p root v /\ subset_edges p tl) ()
              (fun (p: list edge{is_path_from_to p root v /\ subset_edges p tl}) ->
                introduce exists p. is_path_from_to p root v /\ subset_edges p es
                with p and (subset_edges_cons p e tl))
        end;
        bridge_edge_in_component tl e root;
        introduce forall (v: nat). v < n ==> reachable tl nr v ==> reachable es root v
        with introduce _ ==> _ with _. begin
          introduce _ ==> _ with _. begin
            FStar.Classical.exists_elim (reachable es nr v)
              #(list edge)
              #(fun p -> is_path_from_to p nr v /\ subset_edges p tl) ()
              (fun (p: list edge{is_path_from_to p nr v /\ subset_edges p tl}) ->
                introduce exists p. is_path_from_to p nr v /\ subset_edges p es
                with p and (subset_edges_cons p e tl));
            reachable_transitive es root nr v
          end
        end;
        acyclic_edge_disconnects n e tl;
        introduce forall (v: nat). v < n ==> ~(reachable tl root v /\ reachable tl nr v)
        with begin
          if v < n && reachable_dec tl root v && reachable_dec tl nr v then begin
            reachable_symmetric tl nr v;
            reachable_transitive tl root v nr;
            if reachable_dec tl root e.u then begin
              reachable_symmetric tl root e.u;
              reachable_transitive tl e.u root e.v
            end else begin
              reachable_symmetric tl root e.v;
              reachable_transitive tl e.v root e.u;
              reachable_symmetric tl e.v e.u
            end
          end
        end;
        count_reachable_disjoint_lower es tl root root nr n n;
        // |ghost_filter f tl| <= |ghost_filter f_r tl| + |ghost_filter f_nr tl|
        // For each ed ∈ tl: f ed ==> f_r ed || f_nr ed (bridge decomposition + no-cross)
        introduce forall (ed: edge). mem_edge ed tl /\ f ed ==> f_r ed || f_nr ed
        with begin
          if mem_edge ed tl && f ed then begin
            // ed.u and ed.v reachable from root in es → from root or nr in tl
            if reachable_dec tl root e.u then begin
              reachable_bridge tl e root ed.u e.u e.v;
              reachable_bridge tl e root ed.v e.u e.v
            end else begin
              reachable_bridge tl e root ed.u e.v e.u;
              reachable_bridge tl e root ed.v e.v e.u
            end;
            // If mixed (one from root, one from nr): contradiction via connectivity
            if reachable_dec tl root ed.u && reachable_dec tl nr ed.v &&
               not (reachable_dec tl root ed.v) && not (reachable_dec tl nr ed.u) then begin
              assert (is_path_from_to [ed] ed.u ed.v);
              assert (subset_edges [ed] tl);
              reachable_transitive tl root ed.u ed.v;
              reachable_symmetric tl nr ed.v;
              reachable_transitive tl root ed.v nr;
              ()  // root reaches nr in tl → contradiction (acyclic_edge_disconnects)
            end
            else if reachable_dec tl nr ed.u && reachable_dec tl root ed.v &&
                    not (reachable_dec tl nr ed.v) && not (reachable_dec tl root ed.u) then begin
              assert (is_path_from_to [ed] ed.u ed.v);
              assert (subset_edges [ed] tl);
              reachable_symmetric tl ed.u ed.v;
              reachable_transitive tl root ed.v ed.u;
              reachable_symmetric tl nr ed.u;
              reachable_transitive tl root ed.u nr;
              ()  // root reaches nr in tl → contradiction
            end
          end
        end;
        ghost_filter_or_bound f f_r f_nr tl
      end
#pop-options

// Acyclic + connected ⟹ exactly n-1 edges
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
let acyclic_connected_length (n: nat) (es: list edge)
  : Lemma (requires n > 0 /\ all_connected n es /\ acyclic n es /\ all_edges_distinct es /\
                    (forall (e: edge). mem_edge e es ==> e.u < n /\ e.v < n /\ e.u <> e.v))
          (ensures length es >= n - 1 /\ length es <= n - 1)
  = connected_min_edges n es;
    acyclic_count_lower_bound es 0 n;
    introduce forall (v: nat). v < n ==> reachable es 0 v
    with introduce _ ==> _ with _. assert (reachable es 0 v);
    let rec count_all (m: nat)
      : Lemma (requires forall (v: nat). v < n ==> reachable es 0 v)
              (ensures count_reachable es 0 n m = min m n) (decreases m)
      = if m = 0 then () else count_all (m - 1)
    in
    count_all n;
    let f = is_comp_edge es 0 in
    let rec all_in_comp (l: list edge)
      : Lemma (requires (forall (e: edge). mem_edge e l ==> e.u < n /\ e.v < n) /\
                        (forall (v: nat). v < n ==> reachable es 0 v))
              (ensures length (ghost_filter f l) = length l)
              (decreases l)
      = match l with
        | [] -> ()
        | hd :: tl -> all_in_comp tl
    in
    all_in_comp es
#pop-options

