module CLRS.Ch35.VertexCover.Lemmas

(**
 * Proofs of lemmas about APPROX-VERTEX-COVER (CLRS Chapter 35).
 *
 * Includes counting lemmas, matching arguments, CLRS Theorem 35.1,
 * and the connection from Pulse's is_cover to the pure specification.
 *
 * 0 admits. Fully proven.
 *)

open FStar.Mul
open FStar.List.Tot
open FStar.Seq
open CLRS.Ch35.VertexCover.Spec

(*** Counting lemmas ***)

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
    assert (c_no_u v == c v);
    count_split_one c_no_u v n;
    let c'' : cover_fn = fun (x:nat) -> c_no_u x && x <> v in
    count_cover_ext c' c'' n

(*** Edge contribution and matching arguments ***)

let rec sum_ge_length (c: cover_fn) (m: list edge)
  : Lemma (requires is_valid_cover_for_edges c m)
          (ensures sum_contributions c m >= List.Tot.length m)
          (decreases m)
  = match m with
    | [] -> ()
    | _ :: rest -> sum_ge_length c rest

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

let disjoint_implies_no_shared_vertices (e1 e2: edge)
  : Lemma (requires ~(edges_share_vertex e1 e2))
          (ensures (let (u1, v1) = e1 in let (u2, v2) = e2 in
                   u2 <> u1 /\ v2 <> u1 /\ u2 <> v1 /\ v2 <> v1))
  = ()

let rec existsb_false_forall (#a: Type) (f: a -> bool) (l: list a)
  : Lemma (requires forall (x: a). memP x l ==> f x == false)
          (ensures existsb f l == false)
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: rest -> existsb_false_forall f rest

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
        let aux (e': edge) : Lemma (requires memP e' rest)
          (ensures (let (a, b) = e' in a <> u /\ b <> u /\ a <> v /\ b <> v)) =
          disjoint_implies_no_shared_vertices e e'
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        sum_restricted c rest u v;
        sum_le_count c' rest n;
        count_split c u v n

(*** Matching lower bound ***)

//SNIPPET_START: matching_lower_bound
let matching_lower_bound (c: cover_fn) (m: list edge) (n: nat)
  : Lemma (requires
              pairwise_disjoint m /\
              is_valid_cover_for_edges c m /\
              (forall (e: edge). memP e m ==> (let (u, v) = e in u < n /\ v < n /\ u <> v)))
          (ensures count_cover c n >= List.Tot.length m)
  = sum_ge_length c m;
    sum_le_count c m n
//SNIPPET_END: matching_lower_bound

(*** Cover size lemmas ***)

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

//SNIPPET_START: matching_cover_size
let rec matching_cover_size (m: list edge) (n: nat)
  : Lemma (requires
              pairwise_disjoint m /\
              (forall (e: edge). memP e m ==> (let (u, v) = e in u < n /\ v < n /\ u <> v)))
          (ensures 
              count_cover (fun (x:nat) -> existsb (fun e -> edge_uses_vertex e x) m) n ==
              2 * List.Tot.length m)
          (decreases m)
//SNIPPET_END: matching_cover_size
  = let c : cover_fn = fun (x:nat) -> existsb (fun e -> edge_uses_vertex e x) m in
    match m with
    | [] ->
        count_cover_ext c (fun (_:nat) -> false) n;
        count_zero n
    | e :: rest ->
        let (u, v) = e in
        let c_rest : cover_fn = fun (x:nat) -> existsb (fun e -> edge_uses_vertex e x) rest in
        matching_cover_size rest n;
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

//SNIPPET_START: theorem_35_1
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
//SNIPPET_END: theorem_35_1

(*** Connection to Pulse implementation ***)

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

let pulse_cover_is_valid (s_adj s_cover: seq int) (n: nat)
  : Lemma (requires is_cover s_adj s_cover n n 0 /\ Seq.length s_cover = n)
          (ensures is_valid_graph_cover s_adj n (seq_to_cover_fn s_cover n))
  = let edges = extract_edges s_adj n 0 1 in
    let c = seq_to_cover_fn s_cover n in
    extract_edges_valid s_adj n 0 1;
    let aux (e: edge) : Lemma (requires memP e edges)
                              (ensures (let (u, v) = e in c u \/ c v)) =
      let (u, v) = e in
      assert (u < n /\ v < n /\ u < v);
      assert (Seq.index s_adj (u * n + v) <> 0);
      assert (Seq.index s_cover u <> 0 \/ Seq.index s_cover v <> 0);
      ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(*** Completeness of extract_edges ***)

let rec extract_edges_contains (adj: seq int) (n: nat) (u v u' v': nat)
  : Lemma (requires Seq.length adj = n * n /\
                    u' < n /\ v' < n /\ u' < v' /\
                    Seq.index adj (u' * n + v') <> 0 /\
                    u <= u' /\ (u < u' \/ v <= v'))
          (ensures memP (u', v') (extract_edges adj n u v))
          (decreases ((if u >= n then 0 else n - u) * (n + 1) + (if v > n then 0 else n + 1 - v)))
  = if u >= n then ()
    else if v >= n then
      extract_edges_contains adj n (u + 1) (u + 2) u' v'
    else if v > u && Seq.length adj = n * n && Seq.index adj (u * n + v) <> 0
    then (
      if u = u' && v = v' then ()
      else extract_edges_contains adj n u (v + 1) u' v'
    )
    else extract_edges_contains adj n u (v + 1) u' v'

let valid_graph_cover_covers_edge (adj: seq int) (n: nat) (c: cover_fn) (u v: nat)
  : Lemma (requires is_valid_graph_cover adj n c /\
                    Seq.length adj = n * n /\
                    u < n /\ v < n /\ u < v /\ Seq.index adj (u * n + v) <> 0)
          (ensures c u \/ c v)
  = extract_edges_contains adj n 0 1 u v

let rec valid_cover_covers_matching (adj: seq int) (n: nat) (c: cover_fn) (m: list edge)
  : Lemma (requires is_valid_graph_cover adj n c /\
                    Seq.length adj = n * n /\
                    (forall (e: edge). memP e m ==>
                      (let (u, v) = e in u < n /\ v < n /\ u < v /\ Seq.index adj (u * n + v) <> 0)))
          (ensures is_valid_cover_for_edges c m)
          (decreases m)
  = match m with
    | [] -> ()
    | (u, v) :: rest ->
        valid_graph_cover_covers_edge adj n c u v;
        valid_cover_covers_matching adj n c rest

(*** Existence of minimum vertex cover ***)

// The trivial "all vertices" cover is valid for any edge list
let all_true_is_valid_for_edges (edges: list edge)
  : Lemma (ensures is_valid_cover_for_edges (fun (_ : nat) -> true) edges)
  = ()

let all_true_is_valid (adj: seq int) (n: nat)
  : Lemma (requires Seq.length adj = n * n)
          (ensures is_valid_graph_cover adj n (fun (_ : nat) -> true))
  = all_true_is_valid_for_edges (extract_edges adj n 0 1)

let rec count_all_true (n: nat)
  : Lemma (ensures count_cover (fun (_ : nat) -> true) n = n) (decreases n)
  = if n = 0 then () else count_all_true (n - 1)

// Well-ordering argument: if a valid cover exists with count ≤ bound,
// then a minimum vertex cover exists.
#push-options "--z3rlimit 5"
let rec min_cover_exists_aux (adj: seq int) (n: nat) (bound: nat)
  : Lemma 
    (requires Seq.length adj = n * n /\
              (exists (c: cover_fn). is_valid_graph_cover adj n c /\ count_cover c n <= bound))
    (ensures exists (opt: nat). min_vertex_cover_size adj n opt)
    (decreases bound)
  = if bound = 0 then ()
    else (
      FStar.Classical.excluded_middle 
        (exists (c: cover_fn). is_valid_graph_cover adj n c /\ count_cover c n <= bound - 1);
      FStar.Classical.move_requires (min_cover_exists_aux adj n) (bound - 1)
    )
#pop-options

// Every finite graph has a minimum vertex cover.
let min_cover_exists (adj: seq int) (n: nat)
  : Lemma (requires Seq.length adj = n * n)
          (ensures exists (opt: nat). min_vertex_cover_size adj n opt)
  = all_true_is_valid adj n;
    count_all_true n;
    min_cover_exists_aux adj n n

(*** 2-Approximation Ratio Theorem — connecting Pulse cover to CLRS Theorem 35.1 ***)
//SNIPPET_START: approximation_ratio_theorem
let approximation_ratio_theorem (s_adj s_cover: seq int) (n: nat) (m: list edge) (c_opt: cover_fn)
  : Lemma (requires
            Seq.length s_cover = n /\
            Seq.length s_adj = n * n /\
            (forall (i: nat). i < n ==> (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
            is_valid_graph_cover s_adj n c_opt /\
            pairwise_disjoint m /\
            (forall (e: edge). memP e m ==> (let (u, v) = e in u < n /\ v < n /\ u <> v)) /\
            (forall (e: edge). memP e m ==> (let (u, v) = e in u < v /\ Seq.index s_adj (u * n + v) <> 0)) /\
            (forall (x: nat). x < n ==> ((Seq.index s_cover x <> 0) == existsb (fun e -> edge_uses_vertex e x) m)))
          (ensures count_cover (seq_to_cover_fn s_cover n) n <= 2 * count_cover c_opt n)
  = let c_alg = seq_to_cover_fn s_cover n in
    let c_m : cover_fn = fun (x:nat) -> existsb (fun e -> edge_uses_vertex e x) m in
    count_cover_ext c_alg c_m n;
    valid_cover_covers_matching s_adj n c_opt m;
    theorem_35_1 m c_opt n
//SNIPPET_END: approximation_ratio_theorem
