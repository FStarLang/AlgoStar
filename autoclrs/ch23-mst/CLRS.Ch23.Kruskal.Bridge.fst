(*
   Kruskal's Algorithm — Greedy MST Bridge (Proofs)

   Uses the cut property (CLRS Theorem 23.1) to prove that greedy selection
   of minimum cross-component edges produces a safe edge set (⊆ some MST).
*)

module CLRS.Ch23.Kruskal.Bridge

open FStar.List.Tot
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Kruskal.Components
open CLRS.Ch23.Kruskal.Spec

module MSTSpec = CLRS.Ch23.MST.Spec
module Comp = CLRS.Ch23.Kruskal.Components
module KSpec = CLRS.Ch23.Kruskal.Spec

(*** Helper: reachable vertices are on the same side of the component cut ***)

/// If u and v are reachable in the forest, then same_component_dec agrees on them
/// relative to any root.
let reachable_same_side (forest: list edge) (root u v: nat)
  : Lemma
    (requires reachable forest u v)
    (ensures same_component_dec forest root u = same_component_dec forest root v)
  = // Case analysis on same_component_dec forest root u
    if same_component_dec forest root u then begin
      // root reachable from u (by soundness)
      same_component_dec_sound forest root u;
      // root ~ u and u ~ v, so root ~ v (transitivity)
      reachable_transitive forest root u v;
      // By completeness: same_component_dec forest root v = true
      same_component_dec_complete forest root v
    end else begin
      // root NOT reachable from u
      // Suppose same_component_dec forest root v = true
      if same_component_dec forest root v then begin
        same_component_dec_sound forest root v;
        // root ~ v and v ~ u (symmetry of u ~ v)
        reachable_symmetric forest u v;
        reachable_transitive forest root v u;
        // root ~ u, so by completeness, dec = true. Contradiction.
        same_component_dec_complete forest root u
      end else ()
    end

(*** Helper: forest edges don't cross the component cut ***)

/// Each edge in the forest connects reachable vertices
let edge_mem_reachable (e: edge) (forest: list edge)
  : Lemma
    (requires mem_edge e forest)
    (ensures reachable forest e.u e.v)
  = // The path [e] witnesses reachability
    edge_eq_reflexive e;
    assert (is_path_from_to [e] e.u e.v);
    assert (subset_edges [e] forest)

/// The forest respects the component cut (no forest edge crosses it)
let rec forest_respects_component_cut
  (forest sub: list edge) (root: nat)
  (s: cut)
  : Lemma
    (requires
      (forall (v: nat). s v = same_component_dec forest root v) /\
      (forall (e: edge). mem_edge e sub ==> mem_edge e forest))
    (ensures respects sub s)
    (decreases sub)
  = match sub with
    | [] -> ()
    | hd :: tl ->
      // hd ∈ sub ⟹ hd ∈ forest ⟹ reachable hd.u hd.v
      assert (mem_edge hd (hd :: tl));
      edge_mem_reachable hd forest;
      // reachable ⟹ same side of cut
      reachable_same_side forest root hd.u hd.v;
      assert (s hd.u = s hd.v);
      assert (not (crosses_cut hd s));
      // Recursive: tl also respects
      assert (forall (e: edge). mem_edge e tl ==> mem_edge e (hd :: tl));
      forest_respects_component_cut forest tl root s

(*** Helper: crossing the cut implies different components ***)

/// If an edge crosses the component cut, its endpoints are not reachable in the forest
let crossing_means_unreachable
  (forest: list edge) (root: nat) (e': edge) (s: cut)
  : Lemma
    (requires
      (forall (v: nat). s v = same_component_dec forest root v) /\
      crosses_cut e' s)
    (ensures ~(reachable forest e'.u e'.v))
  = // crosses_cut means s(e'.u) ≠ s(e'.v)
    // So one is in root's component and the other isn't.
    // If reachable(forest, e'.u, e'.v), then same_component_dec agrees, contradiction.
    FStar.Classical.move_requires (reachable_same_side forest root e'.u) e'.v

(*** Main theorem: greedy_step_safe ***)

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let greedy_step_safe (g: graph) (forest: list edge) (e: edge)
  : Lemma
    (requires
      g.n > 0 /\
      (forall (e': edge). mem_edge e' g.edges ==> e'.u < g.n /\ e'.v < g.n) /\
      (exists (t: list edge). is_mst g t /\ subset_edges forest t) /\
      mem_edge e g.edges /\
      e.u < g.n /\ e.v < g.n /\
      ~(reachable forest e.u e.v) /\
      (forall (e': edge). mem_edge e' g.edges ==>
        e'.u < g.n /\ e'.v < g.n ==>
        ~(reachable forest e'.u e'.v) ==>
        e.w <= e'.w))
    (ensures
      (exists (t: list edge). is_mst g t /\ subset_edges (e :: forest) t))
  = // Define the component cut: S(v) = true iff v is reachable from e.u in forest
    let s : cut = fun v -> same_component_dec forest e.u v in

    // (1) e crosses the cut
    // s(e.u) = true (reflexivity)
    same_component_reflexive forest e.u;
    same_component_dec_complete forest e.u e.u;
    assert (s e.u = true);
    // s(e.v) = false (by contradiction with ¬reachable)
    (if same_component_dec forest e.u e.v then begin
       same_component_dec_sound forest e.u e.v;
       assert (reachable forest e.u e.v) // contradicts hypothesis
     end else ());
    assert (s e.v = false);
    assert (crosses_cut e s);

    // (2) forest respects the cut
    // Every forest edge (a,b) has a ∈ forest, so mem_edge (a,b) forest.
    // Passing sub = forest with forest_edges ⊆ forest (trivially).
    forest_respects_component_cut forest forest e.u s;
    assert (respects forest s);

    // (3) e is a light edge crossing the cut
    // For any e' crossing s: ¬reachable(forest, e'.u, e'.v) (by crossing_means_unreachable)
    // So e.w ≤ e'.w (by precondition)
    introduce forall (e': edge).
      mem_edge e' g.edges /\ crosses_cut e' s ==> e.w <= e'.w
    with introduce _ ==> _ with _. begin
      crossing_means_unreachable forest e.u e' s
    end;
    assert (is_light_edge e s g);

    // (4) Apply cut_property
    cut_property g forest e s
#pop-options

(*** safe_spanning_tree_is_mst ***)

/// Helper: acyclicity is preserved for subsets
let acyclic_subset (a b: list edge) (n: nat)
  : Lemma (requires acyclic n b /\ subset_edges a b)
          (ensures acyclic n a)
  = introduce forall (v: nat) (cycle: list edge).
      v < n /\ subset_edges cycle a /\ Cons? cycle /\ all_edges_distinct cycle ==>
      ~(is_path_from_to cycle v v)
    with introduce _ ==> _ with _. subset_edges_transitive cycle a b

/// Helper: remove first matching edge from a list
let rec remove_edge_first (e: edge) (l: list edge) : list edge =
  match l with
  | [] -> []
  | hd :: tl -> if edge_eq e hd then tl else hd :: remove_edge_first e tl

let rec remove_edge_first_length (e: edge) (l: list edge)
  : Lemma (requires mem_edge e l)
          (ensures length (remove_edge_first e l) = length l - 1)
          (decreases l)
  = match l with
    | hd :: tl -> if edge_eq e hd then () else remove_edge_first_length e tl

let rec remove_edge_first_weight (e: edge) (l: list edge)
  : Lemma (requires mem_edge e l)
          (ensures total_weight l = e.w + total_weight (remove_edge_first e l))
          (decreases l)
  = match l with
    | hd :: tl ->
      if edge_eq e hd then
        edge_eq_endpoints e hd
      else
        remove_edge_first_weight e tl

let rec remove_edge_first_mem (x e: edge) (l: list edge)
  : Lemma (requires mem_edge x l /\ ~(edge_eq x e))
          (ensures mem_edge x (remove_edge_first e l))
          (decreases l)
  = match l with
    | hd :: tl ->
      if edge_eq e hd then begin
        // removed hd. x ≠ e (by hypothesis). If edge_eq x hd, then edge_eq x e by transitivity? No!
        // Actually, x might be edge_eq to hd but not to e. That can't happen because
        // edge_eq e hd and edge_eq x hd would give edge_eq x e (not directly from transitivity of edge_eq).
        // But we have ~(edge_eq x e), and we just need x ∈ tl.
        // edge_eq x hd || mem_edge x tl = mem_edge x (hd :: tl) = true
        // Case: edge_eq x hd = true. Then we need edge_eq x e.
        //   From edge_eq e hd: (e.u=hd.u ∧ e.v=hd.v ∧ e.w=hd.w) ∨ (e.u=hd.v ∧ e.v=hd.u ∧ e.w=hd.w)
        //   From edge_eq x hd: (x.u=hd.u ∧ x.v=hd.v ∧ x.w=hd.w) ∨ (x.u=hd.v ∧ x.v=hd.u ∧ x.w=hd.w)
        //   In all 4 combinations: x.w = hd.w = e.w and endpoints match, giving edge_eq x e.
        //   But ~(edge_eq x e). Contradiction. So edge_eq x hd = false.
        if edge_eq x hd then
          edge_eq_transitive x hd e
        else ()
      end else begin
        if edge_eq x hd then ()
        else remove_edge_first_mem x e tl
      end

let rec remove_edge_first_still_in (x e: edge) (l: list edge)
  : Lemma (ensures mem_edge x (remove_edge_first e l) ==> mem_edge x l)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      if edge_eq e hd then ()
      else remove_edge_first_still_in x e tl

/// Subset + noRepeats ⟹ length ≤
let rec subset_noRepeats_length_le (a b: list edge)
  : Lemma (requires noRepeats_edge a /\ subset_edges a b)
          (ensures length a <= length b)
          (decreases a)
  = match a with
    | [] -> ()
    | hd :: tl ->
      assert (mem_edge hd b);
      let b' = remove_edge_first hd b in
      remove_edge_first_length hd b;
      // tl ⊆ b': each element of tl is in b and ≠ hd, so it's in b'
      let rec prove_tl_subset (p: list edge)
        : Lemma (requires (forall (e: edge). mem_edge e p ==> mem_edge e tl) /\
                          noRepeats_edge (hd :: tl) /\
                          subset_edges (hd :: tl) b)
                (ensures subset_edges p b')
                (decreases p)
        = match p with
          | [] -> ()
          | e :: rest ->
            assert (mem_edge e tl);
            assert (not (mem_edge hd tl));
            // e ∈ tl and hd ∉ tl. If edge_eq e hd, then hd ∈ tl via mem_edge_eq. Contradiction.
            (if edge_eq e hd then begin
              edge_eq_symmetric e hd;
              mem_edge_eq hd e tl
            end else ());
            // e ∈ (hd :: tl) ⟹ e ∈ b
            mem_edge_subset e (hd :: tl) b;
            // e ∈ b and ~(edge_eq e hd) ⟹ e ∈ remove_edge_first hd b = b'
            remove_edge_first_mem e hd b;
            prove_tl_subset rest
      in
      prove_tl_subset tl;
      subset_noRepeats_length_le tl b'

/// Weight equality for mutually-containing edge lists
let rec total_weight_mutual_eq (a b: list edge)
  : Lemma (requires noRepeats_edge a /\ subset_edges a b /\
                    (forall (e: edge). mem_edge e b ==> mem_edge e a) /\
                    length a = length b)
          (ensures total_weight a = total_weight b)
          (decreases a)
  = match a with
    | [] -> (match b with | [] -> ())
    | hd :: tl ->
      assert (mem_edge hd b);
      let b' = remove_edge_first hd b in
      remove_edge_first_length hd b;
      remove_edge_first_weight hd b;
      // tl ⊆ b'
      let rec prove_tl_subset_b' (p: list edge)
        : Lemma (requires (forall (e: edge). mem_edge e p ==> mem_edge e tl) /\
                          noRepeats_edge (hd :: tl) /\
                          subset_edges (hd :: tl) b)
                (ensures subset_edges p b')
                (decreases p)
        = match p with
          | [] -> ()
          | e :: rest ->
            assert (mem_edge e tl);
            (if edge_eq e hd then begin
              edge_eq_symmetric e hd;
              mem_edge_eq hd e tl
            end else ());
            mem_edge_subset e (hd :: tl) b;
            remove_edge_first_mem e hd b;
            prove_tl_subset_b' rest
      in
      prove_tl_subset_b' tl;
      // b' ⊆ tl: each e ∈ b' is in b, hence in (hd :: tl) = a.
      // If edge_eq e hd, derive contradiction via counting.
      introduce forall (e: edge). mem_edge e b' ==> mem_edge e tl
      with introduce _ ==> _ with _. begin
        remove_edge_first_still_in e hd b;
        assert (mem_edge e b);
        assert (mem_edge e (hd :: tl));
        if mem_edge e tl then ()
        else begin
          // e is edge_eq to hd. All of tl maps into b' without using hd-equivalents.
          // But e (hd-equivalent) takes a slot in b', leaving only |b'|-1 slots for tl.
          // tl has |b'| elements (noRepeats). Contradiction via pigeonhole.
          assert (edge_eq e hd);
          let b'' = remove_edge_first e b' in
          remove_edge_first_length e b';
          // tl ⊆ b'': tl elements are not edge_eq to hd, hence not to e
          let rec tl_subset_b'' (p: list edge)
            : Lemma (requires (forall (x: edge). mem_edge x p ==> mem_edge x tl) /\
                              noRepeats_edge (hd :: tl) /\
                              mem_edge e b' /\ edge_eq e hd)
                    (ensures subset_edges p b'')
                    (decreases p)
            = match p with
              | [] -> ()
              | x :: rest ->
                assert (mem_edge x tl);
                (if edge_eq x hd then begin
                  edge_eq_symmetric x hd;
                  mem_edge_eq hd x tl
                end else ());
                assert (~(edge_eq x hd));
                // ~(edge_eq x e) because edge_eq e hd and ~(edge_eq x hd)
                (if edge_eq x e then edge_eq_transitive x e hd else ());
                assert (~(edge_eq x e));
                // x ∈ b' (from prove_tl_subset_b')
                mem_edge_subset x tl b';
                // x ∈ b' and ~(edge_eq x e) ⟹ x ∈ b''
                remove_edge_first_mem x e b';
                tl_subset_b'' rest
          in
          tl_subset_b'' tl;
          subset_noRepeats_length_le tl b'';
          // length tl ≤ length b'' = length b' - 1 = length tl - 1. Contradiction!
          assert false
        end
      end;
      total_weight_mutual_eq tl b'

/// Connected subset of tree implies reverse containment
let connected_subset_of_tree (g: graph) (result mst: list edge)
  : Lemma (requires is_spanning_tree g mst /\
                    subset_edges result mst /\
                    all_connected g.n result /\
                    acyclic g.n result /\
                    (forall (e: edge). mem_edge e mst ==> e.u < g.n /\ e.v < g.n) /\
                    (forall (e: edge). mem_edge e mst ==> e.u <> e.v))
          (ensures forall (e: edge). mem_edge e mst ==> mem_edge e result)
  = introduce forall (e: edge). mem_edge e mst ==> mem_edge e result
    with introduce _ ==> _ with _. begin
      if not (mem_edge e result) then begin
        // e.u and e.v are valid vertices, both connected in result
        assert (e.u < g.n /\ e.v < g.n /\ e.u <> e.v);
        // All vertices < g.n are reachable from 0 in result
        assert (reachable result 0 e.u);
        reachable_symmetric result 0 e.u;
        assert (reachable result e.u 0);
        assert (reachable result 0 e.v);
        reachable_transitive result e.u 0 e.v;
        assert (reachable result e.u e.v);
        // result is acyclic, e has valid endpoints, e ∉ result, e.u ≠ e.v
        // So adding e would create a cycle
        reachable_implies_not_acyclic g.n result e;
        assert (~(acyclic g.n (e :: result)));
        // But e :: result ⊆ mst, and mst is acyclic (spanning tree)
        assert (subset_edges (e :: result) mst);
        acyclic_subset (e :: result) mst g.n;
        assert (acyclic g.n (e :: result));
        // Contradiction
        ()
      end else ()
    end

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let safe_spanning_tree_is_mst (g: graph) (forest: list edge)
  : Lemma
    (requires
      is_spanning_tree g forest /\
      (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v) /\
      noRepeats_edge forest /\
      (exists (t: list edge). is_mst g t /\ subset_edges forest t))
    (ensures is_mst g forest)
  = FStar.Classical.exists_elim (is_mst g forest)
      #_
      #(fun (t: list edge) -> is_mst g t /\ subset_edges forest t)
      ()
      (fun (t: list edge{is_mst g t /\ subset_edges forest t}) ->
        assert (is_spanning_tree g t);

        // MST edges have valid endpoints
        introduce forall (e: edge). mem_edge e t ==> e.u < g.n /\ e.v < g.n
        with introduce _ ==> _ with _. mem_edge_subset e t g.edges;
        introduce forall (e: edge). mem_edge e t ==> e.u <> e.v
        with introduce _ ==> _ with _. mem_edge_subset e t g.edges;

        // Every edge of t is in forest (connected-subset-of-tree argument)
        connected_subset_of_tree g forest t;

        // Build subset_edges t forest
        let rec build_subset (l: list edge)
          : Lemma (requires forall (e: edge). mem_edge e l ==> mem_edge e forest)
                  (ensures subset_edges l forest)
                  (decreases l)
          = match l with | [] -> () | _ :: tl -> build_subset tl
        in
        build_subset t;

        assert (length forest = g.n - 1);
        assert (length t = g.n - 1);

        // Weight equality from mutual containment + noRepeats
        total_weight_mutual_eq forest t;
        assert (total_weight forest = total_weight t);

        introduce forall (t': list edge).
          is_spanning_tree g t' ==> total_weight forest <= total_weight t'
        with introduce _ ==> _ with _. ()
      )
#pop-options
