module CLRS.Ch24.BellmanFord.SpecBridge

(*
   Formal bridge between two shortest-path distance specifications:

   - CLRS.Ch24.ShortestPath.Spec:  flat weight seq, int with abstract sentinel (inf > 0)
   - CLRS.Ch24.BellmanFord.Spec:   adjacency matrix, option int

   Main result: sp_dist_k_equiv shows both sp_dist_k definitions compute
   corresponding values under appropriate boundedness conditions.
*)


module SP  = CLRS.Ch24.ShortestPath.Spec
module BFS = CLRS.Ch24.BellmanFord.Spec
module Seq = FStar.Seq

let inf : int = SP.inf

(* ================================================================
   1.  Flatten adjacency matrix to row-major flat weight sequence
   ================================================================ *)

(* Row-major layout: index u*n + v stores the weight of edge (u, v) *)
let flatten_adj (#n: nat) (adj: BFS.adj_matrix n)
  : Tot (s:Seq.seq int{Seq.length s == n * n})
  =
  if n = 0 then Seq.empty #int
  else
    Seq.init (n * n) (fun (idx: nat{idx < n * n}) ->
      BFS.edge_weight adj (idx / n) (idx % n))

let flatten_adj_length (#n: nat) (adj: BFS.adj_matrix n)
  : Lemma (Seq.length (flatten_adj adj) == n * n)
  = ()

(* Key indexing lemma: flat[u*n+v] = edge_weight adj u v *)
let flatten_adj_index (#n: nat) (adj: BFS.adj_matrix n) (u v: nat)
  : Lemma
    (requires u < n /\ v < n)
    (ensures (
      u * n + v < Seq.length (flatten_adj adj) /\
      Seq.index (flatten_adj adj) (u * n + v) == BFS.edge_weight adj u v))
  =
  assert (u * n + v < n * n);
  assert (u * n + v == v + u * n);
  FStar.Math.Lemmas.lemma_div_plus v u n;
  FStar.Math.Lemmas.small_div v n;
  FStar.Math.Lemmas.lemma_mod_plus v u n;
  FStar.Math.Lemmas.small_mod v n

(* ================================================================
   2.  Correspondence predicate
   ================================================================ *)

(* When an option int (BFS) and a sentinel int (SP) represent the same value *)
let option_int_correspond (o: option int) (i: int) : prop =
  match o with
  | None   -> i == inf
  | Some d -> i == d /\ d < inf

(* ================================================================
   3.  Boundedness precondition
   ================================================================ *)

(*
   The SP specification caps candidate distances at `inf` via the sentinel
   check (if via_u < inf && w < inf then via_u + w else inf).  The BFS
   specification tracks exact option-int values.  They agree only when no
   reachable shortest-path weight reaches or exceeds inf.

   well_bounded packages the conditions that guarantee this:
   (A) all finite sp_dist_k values are strictly below inf
   (B) every finite (sp_dist + edge_weight) sum stays below inf
*)
let well_bounded (#n: nat) (adj: BFS.adj_matrix n) (src: nat{src < n}) (k: nat) : prop =
  BFS.valid_graph adj /\
  (forall (v: nat) (k': nat). v < n /\ k' <= k ==>
    (match BFS.sp_dist_k adj src v k' with
     | None   -> True
     | Some d -> d < inf)) /\
  (forall (u v: nat) (k': nat). u < n /\ v < n /\ k' < k ==>
    (match BFS.sp_dist_k adj src u k' with
     | None   -> True
     | Some d -> BFS.edge_weight adj u v >= inf \/ d + BFS.edge_weight adj u v < inf))

let well_bounded_weaken (#n: nat) (adj: BFS.adj_matrix n) (src: nat{src < n}) (k: nat{k > 0})
  : Lemma (requires well_bounded adj src k)
          (ensures  well_bounded adj src (k - 1))
  = ()

(* ================================================================
   4.  Main equivalence theorem — mutually recursive proof
   ================================================================ *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 1 --split_queries no"

let rec sp_dist_k_equiv
  (#n: nat) (adj: BFS.adj_matrix n) (src dst: nat{src < n /\ dst < n}) (k: nat)
  : Lemma
    (requires well_bounded adj src k)
    (ensures  option_int_correspond
                (BFS.sp_dist_k adj src dst k)
                (SP.sp_dist_k (flatten_adj adj) n src dst k))
    (decreases %[k; 1])
  =
  if k = 0 then ()
  else begin
    well_bounded_weaken adj src k;
    sp_dist_k_equiv adj src dst (k - 1);
    min_over_preds_equiv adj src dst k
      (BFS.sp_dist_k adj src dst (k - 1))
      (SP.sp_dist_k (flatten_adj adj) n src dst (k - 1))
      0
  end

and min_over_preds_equiv
  (#n: nat) (adj: BFS.adj_matrix n) (src dst: nat{src < n /\ dst < n})
  (k: nat{k > 0}) (best_opt: option int) (best_int: int) (u: nat)
  : Lemma
    (requires
      well_bounded adj src k /\
      option_int_correspond best_opt best_int)
    (ensures
      option_int_correspond
        (BFS.min_over_preds adj src dst k best_opt u n)
        (SP.min_over_predecessors (flatten_adj adj) n src dst k best_int u))
    (decreases %[k; 0; n - u])
  =
  if u >= n then ()
  else begin
    let flat = flatten_adj adj in

    (* IH: sp_dist_k at (u, k−1) *)
    well_bounded_weaken adj src k;
    sp_dist_k_equiv adj src u (k - 1);

    (* Weight correspondence *)
    flatten_adj_index adj u dst;

    let dist_to_u = BFS.sp_dist_k adj src u (k - 1) in
    let via_u     = SP.sp_dist_k flat n src u (k - 1) in
    let w_edge    = BFS.edge_weight adj u dst in

    (* Candidate-sum bound from well_bounded (B) *)
    (match dist_to_u with
     | Some d_u ->
       if w_edge < inf then
         assert (d_u + w_edge < inf)   (* from well_bounded (B) *)
       else ()
     | None -> ());

    (* Compute new accumulators — mirrors the bodies of both functions *)
    let w_sp = if u * n + dst < Seq.length flat
               then Seq.index flat (u * n + dst) else inf in

    let candidate_opt : option int =
      match dist_to_u with
      | None     -> None
      | Some d_u -> if w_edge < inf then Some (d_u + w_edge) else None in
    let candidate_int : int =
      if via_u < inf && w_sp < inf then via_u + w_sp else inf in

    let new_best_opt : option int =
      match candidate_opt, best_opt with
      | None,   _      -> best_opt
      | Some c, None   -> Some c
      | Some c, Some b -> if c < b then Some c else Some b in
    let new_best_int : int =
      if candidate_int < best_int then candidate_int else best_int in

    (* Show new accumulators correspond, by case analysis *)
    begin match candidate_opt with
    | None ->
      assert (candidate_int == inf);
      (match best_opt with
       | None   -> assert (best_int == inf);
                   assert (new_best_int == inf)
       | Some b -> assert (best_int == b /\ b < inf);
                   assert (new_best_int == b));
      assert (option_int_correspond new_best_opt new_best_int)

    | Some c ->
      assert (c < inf /\ candidate_int == c);
      (match best_opt with
       | None ->
         assert (best_int == inf);
         assert (new_best_int == c);
         assert (option_int_correspond new_best_opt new_best_int)
       | Some b ->
         assert (best_int == b /\ b < inf);
         if c < b then
           assert (option_int_correspond new_best_opt new_best_int)
         else
           assert (option_int_correspond new_best_opt new_best_int))
    end;

    (* Recurse *)
    min_over_preds_equiv adj src dst k new_best_opt new_best_int (u + 1)
  end

#pop-options

(* ================================================================
   5.  Wrapper for sp_dist
   ================================================================ *)

let sp_dist_equiv
  (#n: nat) (adj: BFS.adj_matrix n) (src dst: nat{src < n /\ dst < n})
  : Lemma
    (requires n > 0 /\ well_bounded adj src (n - 1))
    (ensures (
      let flat = flatten_adj adj in
      match BFS.sp_dist adj src dst with
      | None   -> SP.sp_dist flat n src dst == inf
      | Some d -> SP.sp_dist flat n src dst == d /\ d < inf))
  =
  sp_dist_k_equiv adj src dst (n - 1)
