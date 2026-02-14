module CLRS.Ch35.VertexCover.Spec

(**
 * 2-approximation ratio proof for APPROX-VERTEX-COVER (CLRS Theorem 35.1)
 *
 * NO admits. NO assumes.
 *)

open FStar.Mul
open FStar.List.Tot
open FStar.Seq

(*** Type definitions ***)

type edge = nat & nat
type cover_fn = nat -> bool

let edge_uses_vertex (e: edge) (v: nat) : bool =
  let (u1, v1) = e in u1 = v || v1 = v

let edges_share_vertex (e1 e2: edge) : bool =
  let (u1, v1) = e1 in
  let (u2, v2) = e2 in
  u1 = u2 || u1 = v2 || v1 = u2 || v1 = v2

let rec pairwise_disjoint (m: list edge) : Type0 =
  match m with
  | [] -> True
  | e :: rest ->
      (forall (e': edge). memP e' rest ==> ~(edges_share_vertex e e')) /\
      pairwise_disjoint rest

let is_valid_cover_for_edges (c: cover_fn) (edges: list edge) : Type0 =
  forall (e: edge). memP e edges ==> (let (u, v) = e in c u \/ c v)

let rec count_cover (c: cover_fn) (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0
  else (if c (n - 1) then 1 else 0) + count_cover c (n - 1)

(*** Minimum vertex cover specification (P2.7.1) ***)

// Extract edges from adjacency matrix representation
// adj is a sequence of length n*n where adj[i*n+j] != 0 means edge (i,j) exists
// We only consider edges (u,v) where u < v to avoid counting each edge twice
let rec extract_edges (adj: seq int) (n: nat) (u v: nat) 
  : Tot (list edge) (decreases ((if u >= n then 0 else n - u) * (n + 1) + (if v > n then 0 else n + 1 - v))) =
  if u >= n then []
  else if v >= n then extract_edges adj n (u + 1) (u + 2)
  else if v > u && Seq.length adj = n * n && Seq.index adj (u * n + v) <> 0
       then (u, v) :: extract_edges adj n u (v + 1)
       else extract_edges adj n u (v + 1)

// A cover is valid for a graph if it covers all edges
let is_valid_graph_cover (adj: seq int) (n: nat) (c: cover_fn) : Type0 =
  let edges = extract_edges adj n 0 1 in
  is_valid_cover_for_edges c edges

// Minimum vertex cover: a cover with the smallest possible cardinality
// This is the optimization problem that the approximation algorithm targets
let is_minimum_vertex_cover (adj: seq int) (n: nat) (c_min: cover_fn) : Type0 =
  is_valid_graph_cover adj n c_min /\
  (forall (c': cover_fn). is_valid_graph_cover adj n c' ==>
    count_cover c_min n <= count_cover c' n)

// OPT(adj, n) = the size of the minimum vertex cover
// (as a logical proposition - existence is guaranteed for finite graphs)
let min_vertex_cover_size (adj: seq int) (n: nat) (opt: nat) : Type0 =
  exists (c_min: cover_fn). 
    is_minimum_vertex_cover adj n c_min /\ 
    count_cover c_min n = opt

(*** Counting lemmas (non-mutually-recursive) ***)

let rec count_cover_ext (c1 c2: cover_fn) (n: nat)
  : Lemma (requires forall (x: nat). x < n ==> (c1 x == c2 x))
          (ensures count_cover c1 n == count_cover c2 n)
          (decreases n)
  = if n = 0 then () else count_cover_ext c1 c2 (n - 1)

let rec count_zero (n: nat) 
  : Lemma (ensures count_cover (fun (_ : nat) -> false) n == 0) (decreases n)
  = if n = 0 then () else count_zero (n - 1)

let rec count_single (v: nat) (n: nat)
  : Lemma (requires v < n)
          (ensures count_cover (fun (x:nat) -> x = v) n == 1)
          (decreases n)
  = if n = 0 then ()
    else if v = n - 1 then (
      let c : cover_fn = fun (x:nat) -> x = v in
      let c0 : cover_fn = fun (_ : nat) -> false in
      count_cover_ext c c0 (n - 1);
      count_zero (n - 1)
    ) else
      count_single v (n - 1)

let rec count_cover_mono (c1 c2: cover_fn) (n: nat)
  : Lemma (requires forall (v: nat). v < n /\ c2 v ==> c1 v)
          (ensures count_cover c1 n >= count_cover c2 n)
          (decreases n)
  = if n = 0 then () else count_cover_mono c1 c2 (n - 1)

// count_split: removing two distinct vertices from a cover
// count c n >= (c u ? 1 : 0) + (c v ? 1 : 0) + count c_without n
// where c_without x = c x && x <> u && x <> v
let rec count_split_one (c: cover_fn) (w: nat) (n: nat)
  : Lemma (requires w < n)
          (ensures (let c' : cover_fn = fun (x:nat) -> c x && x <> w in
                   count_cover c n >= (if c w then 1 else 0) + count_cover c' n))
          (decreases n)
  = let c' : cover_fn = fun (x:nat) -> c x && x <> w in
    if n = 0 then ()
    else if w = n - 1 then
      count_cover_ext c c' (n - 1)
    else (
      assert (c' (n - 1) == c (n - 1));
      count_split_one c w (n - 1)
    )

let count_split (c: cover_fn) (u v: nat) (n: nat)
  : Lemma (requires u < n /\ v < n /\ u <> v)
          (ensures (let c' : cover_fn = fun (x:nat) -> c x && not (x = u || x = v) in
                   count_cover c n >= 
                   (if c u then 1 else 0) + (if c v then 1 else 0) + count_cover c' n))
  = let c_no_u : cover_fn = fun (x:nat) -> c x && x <> u in
    let c' : cover_fn = fun (x:nat) -> c x && not (x = u || x = v) in
    count_split_one c u n;
    // count c n >= (c u ? 1 : 0) + count c_no_u n
    // Now split v from c_no_u
    assert (c_no_u v == c v); // since u <> v
    count_split_one c_no_u v n;
    // count c_no_u n >= (c_no_u v ? 1 : 0) + count (c_no_u && _ <> v) n
    // c_no_u && _ <> v = c && _ <> u && _ <> v = c'
    let c'' : cover_fn = fun (x:nat) -> c_no_u x && x <> v in
    count_cover_ext c' c'' n

(*** Edge contribution and matching arguments ***)

let edge_contribution (c: cover_fn) (e: edge) : nat =
  let (u, v) = e in
  (if c u then 1 else 0) + (if c v then 1 else 0)

let rec sum_contributions (c: cover_fn) (m: list edge) : Tot nat (decreases m) =
  match m with
  | [] -> 0
  | e :: rest -> edge_contribution c e + sum_contributions c rest

let rec sum_ge_length (c: cover_fn) (m: list edge)
  : Lemma (requires is_valid_cover_for_edges c m)
          (ensures sum_contributions c m >= List.Tot.length m)
          (decreases m)
  = match m with
    | [] -> ()
    | _ :: rest -> sum_ge_length c rest

// If edges in m don't use vertices u or v, then removing u,v from c doesn't change contributions
let rec sum_restricted (c: cover_fn) (m: list edge) (u v: nat)
  : Lemma (requires forall (e: edge). memP e m ==> 
              (let (a, b) = e in a <> u /\ b <> u /\ a <> v /\ b <> v))
          (ensures sum_contributions c m == 
                   sum_contributions (fun (x:nat) -> c x && not (x = u || x = v)) m)
          (decreases m)
  = match m with
    | [] -> ()
    | (eu, ev) :: rest ->
        sum_restricted c rest u v

// Helper: disjointness from edges_share_vertex to vertex-level facts  
let disjoint_implies_no_shared_vertices (e1 e2: edge)
  : Lemma (requires ~(edges_share_vertex e1 e2))
          (ensures (let (u1, v1) = e1 in let (u2, v2) = e2 in
                   u2 <> u1 /\ v2 <> u1 /\ u2 <> v1 /\ v2 <> v1))
  = ()

// Helper: if f returns false for all elements, existsb returns false
let rec existsb_false_forall (#a: Type) (f: a -> bool) (l: list a)
  : Lemma (requires forall (x: a). memP x l ==> f x == false)
          (ensures existsb f l == false)
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: rest -> existsb_false_forall f rest

// Key lemma: for a disjoint matching, sum of contributions <= count of cover
let rec sum_le_count (c: cover_fn) (m: list edge) (n: nat)
  : Lemma (requires pairwise_disjoint m /\
                    (forall (e: edge). memP e m ==> (let (u, v) = e in u < n /\ v < n /\ u <> v)))
          (ensures sum_contributions c m <= count_cover c n)
          (decreases m)
  = match m with
    | [] -> ()
    | e :: rest ->
        let (u, v) = e in
        let c' : cover_fn = fun (x:nat) -> c x && not (x = u || x = v) in
        // Prove rest doesn't use u or v
        let aux (e': edge) : Lemma (requires memP e' rest)
          (ensures (let (a, b) = e' in a <> u /\ b <> u /\ a <> v /\ b <> v)) =
          disjoint_implies_no_shared_vertices e e'
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        sum_restricted c rest u v;
        sum_le_count c' rest n;
        count_split c u v n

(*** Matching lower bound ***)

let matching_lower_bound (c: cover_fn) (m: list edge) (n: nat)
  : Lemma (requires
              pairwise_disjoint m /\
              is_valid_cover_for_edges c m /\
              (forall (e: edge). memP e m ==> (let (u, v) = e in u < n /\ v < n /\ u <> v)))
          (ensures count_cover c n >= List.Tot.length m)
  = sum_ge_length c m;
    sum_le_count c m n

(*** Cover size lemmas (recursive on n) ***)

let rec matching_cover_add_one (c c_rest: cover_fn) (w: nat) (n: nat)
  : Lemma (requires
              w < n /\ ~(c_rest w) /\
              (forall (x: nat). x < n ==> (c x == (x = w || c_rest x))))
          (ensures count_cover c n == 1 + count_cover c_rest n)
          (decreases n)
  = if n = 0 then ()
    else if w = n - 1 then (
      assert (c (n - 1) == true);
      assert (c_rest (n - 1) == false);
      count_cover_ext c c_rest (n - 1)
    ) else (
      assert (c (n - 1) == c_rest (n - 1));
      matching_cover_add_one c c_rest w (n - 1)
    )

let rec matching_cover_add_two (c c_rest: cover_fn) (u v: nat) (n: nat)
  : Lemma (requires
              u < n /\ v < n /\ u <> v /\
              ~(c_rest u) /\ ~(c_rest v) /\
              (forall (x: nat). x < n ==> (c x == (x = u || x = v || c_rest x))))
          (ensures count_cover c n == 2 + count_cover c_rest n)
          (decreases n)
  = if n = 0 then ()
    else if u = n - 1 then (
      assert (c (n - 1) == true);
      assert (c_rest (n - 1) == false);
      let c_mid : cover_fn = fun (x:nat) -> x = v || c_rest x in
      count_cover_ext c c_mid (n - 1);
      matching_cover_add_one c_mid c_rest v (n - 1)
    ) else if v = n - 1 then (
      assert (c (n - 1) == true);
      assert (c_rest (n - 1) == false);
      let c_mid : cover_fn = fun (x:nat) -> x = u || c_rest x in
      count_cover_ext c c_mid (n - 1);
      matching_cover_add_one c_mid c_rest u (n - 1)
    ) else (
      assert (c (n - 1) == c_rest (n - 1));
      matching_cover_add_two c c_rest u v (n - 1)
    )

(*** Algorithm cover size = 2 * matching size ***)

let rec matching_cover_size (m: list edge) (n: nat)
  : Lemma (requires
              pairwise_disjoint m /\
              (forall (e: edge). memP e m ==> (let (u, v) = e in u < n /\ v < n /\ u <> v)))
          (ensures 
              count_cover (fun (x:nat) -> existsb (fun e -> edge_uses_vertex e x) m) n ==
              2 * List.Tot.length m)
          (decreases m)
  = let c : cover_fn = fun (x:nat) -> existsb (fun e -> edge_uses_vertex e x) m in
    match m with
    | [] ->
        count_cover_ext c (fun (_:nat) -> false) n;
        count_zero n
    | e :: rest ->
        let (u, v) = e in
        let c_rest : cover_fn = fun (x:nat) -> existsb (fun e -> edge_uses_vertex e x) rest in
        matching_cover_size rest n;
        // Prove u and v are not in c_rest
        let aux_u (e': edge) : Lemma (requires memP e' rest) (ensures edge_uses_vertex e' u == false) =
          disjoint_implies_no_shared_vertices e e'
        in
        let aux_v (e': edge) : Lemma (requires memP e' rest) (ensures edge_uses_vertex e' v == false) =
          disjoint_implies_no_shared_vertices e e'
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_u);
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_v);
        existsb_false_forall (fun e -> edge_uses_vertex e u) rest;
        existsb_false_forall (fun e -> edge_uses_vertex e v) rest;
        assert (c_rest u == false);
        assert (c_rest v == false);
        matching_cover_add_two c c_rest u v n

(*** CLRS Theorem 35.1: 2-approximation ***)

let theorem_35_1 
  (m: list edge) (c_opt: cover_fn) (n: nat)
  : Lemma (requires
              pairwise_disjoint m /\
              (forall (e: edge). memP e m ==> (let (u, v) = e in u < n /\ v < n /\ u <> v)) /\
              is_valid_cover_for_edges c_opt m)
          (ensures (
              let c_alg : cover_fn = fun (x:nat) -> existsb (fun e -> edge_uses_vertex e x) m in
              count_cover c_alg n == 2 * List.Tot.length m /\
              count_cover c_opt n >= List.Tot.length m /\
              count_cover c_alg n <= 2 * count_cover c_opt n))
  = matching_cover_size m n;
    matching_lower_bound c_opt m n

(*** Connection to Pulse implementation (P2.7.2) ***)

// The is_cover predicate from the Pulse implementation
let is_cover_pulse (s_adj s_cover: seq int) (n: nat) (bound_u bound_v: nat) : prop =
  Seq.length s_adj == n * n /\
  Seq.length s_cover == n /\
  (forall (u v: nat). (u < bound_u \/ (u == bound_u /\ v < bound_v)) ==>
    u < n ==> v < n ==> u < v ==>
    Seq.index s_adj (u * n + v) <> 0 ==>
    (Seq.index s_cover u <> 0 \/ Seq.index s_cover v <> 0))

// Convert sequence to cover function (with bounds check)
let seq_to_cover_fn (s_cover: seq int) (n: nat{Seq.length s_cover = n}) : cover_fn =
  fun (i: nat) -> i < n && Seq.index s_cover i <> 0

// Lemma: extract_edges collects all edges progressively
let rec extract_edges_complete (adj: seq int) (n: nat) (u v u' v': nat)
  : Lemma (requires u <= u' /\ u' < n /\ v' > u' /\ v' < n /\
                    Seq.length adj = n * n /\
                    (u < u' \/ (u = u' /\ v <= v')))
          (ensures (let edges_now = extract_edges adj n u v in
                   let edges_later = extract_edges adj n u' v' in
                   Seq.index adj (u' * n + v') <> 0 ==>
                   memP (u', v') edges_now \/ memP (u', v') edges_later))
          (decreases ((if u >= n then 0 else n - u) * (n + 1) + (if v > n then 0 else n + 1 - v)))
  = if u >= n then ()
    else if v >= n then extract_edges_complete adj n (u + 1) (u + 2) u' v'
    else if v > u then
      if u = u' && v = v' then ()
      else extract_edges_complete adj n u (v + 1) u' v'
    else extract_edges_complete adj n u (v + 1) u' v'

// Lemma: every edge in extract_edges is valid
let rec extract_edges_valid (adj: seq int) (n: nat) (u v: nat)
  : Lemma (requires Seq.length adj = n * n)
          (ensures (forall (e: edge). memP e (extract_edges adj n u v) ==>
                    (let (u', v') = e in
                     u' < n /\ v' < n /\ u' < v' /\
                     Seq.index adj (u' * n + v') <> 0)))
          (decreases ((if u >= n then 0 else n - u) * (n + 1) + (if v > n then 0 else n + 1 - v)))
  = if u >= n then ()
    else if v >= n then extract_edges_valid adj n (u + 1) (u + 2)
    else if v > u && Seq.length adj = n * n && Seq.index adj (u * n + v) <> 0
         then extract_edges_valid adj n u (v + 1)
         else extract_edges_valid adj n u (v + 1)

// Main connection lemma: Pulse is_cover implies pure spec is_valid_graph_cover
let pulse_cover_is_valid (s_adj s_cover: seq int) (n: nat)
  : Lemma (requires is_cover_pulse s_adj s_cover n n 0 /\ Seq.length s_cover = n)
          (ensures is_valid_graph_cover s_adj n (seq_to_cover_fn s_cover n))
  = let edges = extract_edges s_adj n 0 1 in
    let c = seq_to_cover_fn s_cover n in
    extract_edges_valid s_adj n 0 1;
    let aux (e: edge) : Lemma (requires memP e edges)
                              (ensures (let (u, v) = e in c u \/ c v)) =
      let (u, v) = e in
      // From extract_edges_valid, we know u < n, v < n, u < v, and edge exists
      assert (u < n /\ v < n /\ u < v);
      assert (Seq.index s_adj (u * n + v) <> 0);
      // From is_cover_pulse with bound_u = n and bound_v = 0, 
      // all edges (u, v) with u < n and v < n and u < v are covered
      assert (Seq.index s_cover u <> 0 \/ Seq.index s_cover v <> 0);
      // Therefore c u \/ c v
      ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
