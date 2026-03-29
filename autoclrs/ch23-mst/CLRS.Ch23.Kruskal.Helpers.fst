module CLRS.Ch23.Kruskal.Helpers

/// Helper lemmas for maintaining the forest invariant in Kruskal's algorithm.
/// These are separated from the main Pulse file to avoid polluting Z3's context.

open FStar.List.Tot

module Seq = FStar.Seq
module MSTSpec = CLRS.Ch23.MST.Spec
module KSpec = CLRS.Ch23.Kruskal.Spec
module UF = CLRS.Ch23.Kruskal.UF

// Redefine edges_from_arrays locally (same as in Kruskal.fst)
let rec edges_from_arrays (seu sev: Seq.seq int) (ec: nat) (i: nat{i <= ec})
  : Pure (list MSTSpec.edge)
    (requires ec <= Seq.length seu /\ ec <= Seq.length sev /\
             (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0))
    (ensures fun _ -> True)
    (decreases (ec - i))
  = if i >= ec then []
    else
      let u = Seq.index seu i in
      let v = Seq.index sev i in
      { MSTSpec.u = u; v = v; w = 1 } :: edges_from_arrays seu sev ec (i + 1)

(*** Helper lemmas for forest invariant maintenance ***)

// Empty edge set is acyclic
let empty_is_forest (n: nat) : Lemma (KSpec.is_forest ([] #MSTSpec.edge) n)
  = ()

// edges_from_arrays with same underlying arrays at positions < ec gives same result
#push-options "--fuel 2 --ifuel 0 --z3rlimit 5"
let rec edges_from_arrays_stable
    (seu sev seu' sev': Seq.seq int) (ec: nat) (i: nat{i <= ec})
  : Lemma 
    (requires
      ec <= Seq.length seu /\ ec <= Seq.length sev /\
      ec <= Seq.length seu' /\ ec <= Seq.length sev' /\
      (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
      (forall (k:nat). k < ec ==> Seq.index seu' k >= 0 /\ Seq.index sev' k >= 0) /\
      (forall (k:nat). i <= k /\ k < ec ==> Seq.index seu' k = Seq.index seu k) /\
      (forall (k:nat). i <= k /\ k < ec ==> Seq.index sev' k = Seq.index sev k))
    (ensures edges_from_arrays seu' sev' ec i == edges_from_arrays seu sev ec i)
    (decreases (ec - i))
  = if i >= ec then ()
    else edges_from_arrays_stable seu sev seu' sev' ec (i + 1)
#pop-options

// edges_from_arrays with ec+1 = old list ++ [new_edge]
#push-options "--fuel 2 --ifuel 0 --z3rlimit 5"
let rec edges_from_arrays_snoc
    (seu sev: Seq.seq int) (ec: nat) (i: nat{i <= ec})
    (u_val v_val: nat)
  : Lemma
    (requires
      ec < Seq.length seu /\ ec < Seq.length sev /\
      (forall (k:nat). k < ec + 1 ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
      Seq.index seu ec = u_val /\ Seq.index sev ec = v_val)
    (ensures
      edges_from_arrays seu sev (ec + 1) i ==
      edges_from_arrays seu sev ec i @
        (if i <= ec then [{MSTSpec.u = u_val; v = v_val; w = 1}] else []))
    (decreases (ec + 1 - i))
  = if i > ec then ()
    else if i = ec then ()
    else edges_from_arrays_snoc seu sev ec (i + 1) u_val v_val
#pop-options

// mem_edge equivalence between (e :: t) and (t @ [e])
let rec mem_edge_append_last (x e: MSTSpec.edge) (t: list MSTSpec.edge)
  : Lemma (ensures MSTSpec.mem_edge x (t @ [e]) = (MSTSpec.mem_edge x t || MSTSpec.edge_eq x e))
          (decreases t)
  = match t with
    | [] -> ()
    | _ :: tl -> mem_edge_append_last x e tl

let mem_edge_cons_vs_append (x e: MSTSpec.edge) (t: list MSTSpec.edge)
  : Lemma (ensures MSTSpec.mem_edge x (e :: t) = MSTSpec.mem_edge x (t @ [e]))
  = mem_edge_append_last x e t

// subset_edges equivalence between (e :: t) and (t @ [e])
let rec subset_edges_cons_vs_append (cycle: list MSTSpec.edge) (e: MSTSpec.edge) (t: list MSTSpec.edge)
  : Lemma (ensures MSTSpec.subset_edges cycle (e :: t) = MSTSpec.subset_edges cycle (t @ [e]))
          (decreases cycle)
  = match cycle with
    | [] -> ()
    | hd :: tl ->
      mem_edge_cons_vs_append hd e t;
      subset_edges_cons_vs_append tl e t

// acyclic equivalence: (e :: t) <==> (t @ [e])
let acyclic_cons_vs_append (n: nat) (e: MSTSpec.edge) (t: list MSTSpec.edge)
  : Lemma (ensures MSTSpec.acyclic n (e :: t) <==> MSTSpec.acyclic n (t @ [e]))
  = let aux_fwd (v: nat) (cycle: list MSTSpec.edge)
      : Lemma (requires v < n /\ MSTSpec.subset_edges cycle (t @ [e]) /\
                        Cons? cycle /\ MSTSpec.all_edges_distinct cycle /\
                        MSTSpec.acyclic n (e :: t))
              (ensures ~(MSTSpec.is_path_from_to cycle v v))
      = subset_edges_cons_vs_append cycle e t
    in
    let aux_bwd (v: nat) (cycle: list MSTSpec.edge)
      : Lemma (requires v < n /\ MSTSpec.subset_edges cycle (e :: t) /\
                        Cons? cycle /\ MSTSpec.all_edges_distinct cycle /\
                        MSTSpec.acyclic n (t @ [e]))
              (ensures ~(MSTSpec.is_path_from_to cycle v v))
      = subset_edges_cons_vs_append cycle e t
    in
    FStar.Classical.forall_intro_2 (fun v -> FStar.Classical.move_requires (aux_fwd v));
    FStar.Classical.forall_intro_2 (fun v -> FStar.Classical.move_requires (aux_bwd v))

// Key lemma: appending an unreachable edge preserves acyclicity
let acyclic_snoc_unreachable (n: nat) (t: list MSTSpec.edge) (e: MSTSpec.edge)
  : Lemma (requires MSTSpec.acyclic n t /\ e.u < n /\ e.v < n /\
                    ~(MSTSpec.mem_edge e t) /\ ~(MSTSpec.reachable t e.u e.v))
          (ensures MSTSpec.acyclic n (t @ [e]))
  = MSTSpec.acyclic_when_unreachable n t e;
    acyclic_cons_vs_append n e t
