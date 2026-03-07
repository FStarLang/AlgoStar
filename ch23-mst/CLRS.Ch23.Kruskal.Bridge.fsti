(*
   Kruskal's Algorithm — Greedy MST Bridge

   Proves the key lemmas connecting any greedy MST algorithm to MST correctness:

   1. greedy_step_safe: Adding the minimum-weight cross-component edge to a safe
      forest (⊆ some MST) preserves the safe-edge property.  Uses the cut property
      (CLRS Theorem 23.1) with the cut defined by the adding vertex's component.

   2. safe_spanning_tree_is_mst: A spanning tree that is safe (⊆ some MST) is
      itself an MST.  Uses the connected-subset-of-tree argument from Kruskal.Spec.

   These lemmas bridge the gap between the imperative Kruskal implementation
   (which greedily selects minimum cross-component edges) and the MST spec.
*)

module CLRS.Ch23.Kruskal.Bridge

open FStar.List.Tot
open CLRS.Ch23.MST.Spec

/// No duplicate edges in a list (using edge_eq)
let rec noRepeats_edge (l: list edge) : bool =
  match l with
  | [] -> true
  | hd :: tl -> not (mem_edge hd tl) && noRepeats_edge tl

/// Greedy step: If the current forest is safe (⊆ some MST) and we add the
/// minimum-weight edge whose endpoints are in different components,
/// the new forest is still safe.
///
/// Proof strategy: define cut S = {v | reachable from e.u in forest}.
///   - S respects forest (forest edges stay within components)
///   - e crosses S (e.u reachable from itself, e.v not reachable)
///   - e is light for S (any S-crossing edge is cross-component, hence ≥ e.w)
///   - By cut_property (Thm 23.1): (e :: forest) ⊆ some MST.
val greedy_step_safe (g: graph) (forest: list edge) (e: edge)
  : Lemma
    (requires
      g.n > 0 /\
      (forall (e': edge). mem_edge e' g.edges ==> e'.u < g.n /\ e'.v < g.n) /\
      // forest is safe: subset of some MST
      (exists (t: list edge). is_mst g t /\ subset_edges forest t) /\
      // e is a valid graph edge
      mem_edge e g.edges /\
      e.u < g.n /\ e.v < g.n /\
      // e connects different components
      ~(reachable forest e.u e.v) /\
      // e has minimum weight among all cross-component graph edges
      (forall (e': edge). mem_edge e' g.edges ==>
        e'.u < g.n /\ e'.v < g.n ==>
        ~(reachable forest e'.u e'.v) ==>
        e.w <= e'.w))
    (ensures
      (exists (t: list edge). is_mst g t /\ subset_edges (e :: forest) t))

/// If a spanning tree is safe (⊆ some MST), then it IS an MST.
val safe_spanning_tree_is_mst (g: graph) (forest: list edge)
  : Lemma
    (requires
      is_spanning_tree g forest /\
      (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v) /\
      // noRepeats is needed for the weight equality argument
      noRepeats_edge forest /\
      (exists (t: list edge). is_mst g t /\ subset_edges forest t))
    (ensures is_mst g forest)
