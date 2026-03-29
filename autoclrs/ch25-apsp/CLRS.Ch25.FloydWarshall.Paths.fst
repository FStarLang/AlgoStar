module CLRS.Ch25.FloydWarshall.Paths

(**
 * Graph-theoretic shortest path formalism for Floyd-Warshall.
 *
 * Proves that fw_entry adj n i j k equals the minimum walk weight over
 * all valid walks from i to j with intermediate vertices in {0..k-1}.
 *
 * Proof structure:
 *   §1. Walk definitions
 *   §2. Basic walk properties + base case (k=0)
 *   §3. Walk splitting and weight additivity
 *   §4. Walk concatenation and restriction
 *   §5. Monotonicity: fw_entry(i,j,k) ≤ fw_entry(i,j,k-1)
 *   §6. Achievability: exists walk w with weight == fw_entry
 *   §7. Soundness: fw_entry ≤ walk_weight for all restricted walks
 *   §8. Final theorem: fw_entry adj n i j n == δ(i,j)
 *
 * NO admits. NO assumes.
 *)

open FStar.Mul
module Seq = FStar.Seq
open FStar.List.Tot
open CLRS.Ch25.FloydWarshall.Spec

(* ========================================================================
   § 1. Walk Definitions
   ======================================================================== *)

let is_walk (w: list nat) : bool = length w >= 2

let walk_src (w: list nat{is_walk w}) : nat = hd w
let walk_dst (w: list nat{is_walk w}) : nat = last w

let rec walk_weight (adj: Seq.seq int) (n: nat) (w: list nat) : Tot int (decreases w) =
  match w with
  | [] | [_] -> 0
  | u :: v :: rest ->
    if u * n + v >= Seq.length adj then inf
    else Seq.index adj (u * n + v) + walk_weight adj n (v :: rest)

let rec all_less_than (l: list nat) (k: nat) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | x :: rest -> x < k && all_less_than rest k

let walk_valid (w: list nat) (n: nat) : bool =
  all_less_than w n

let intermediates (w: list nat) : Tot (list nat) =
  match w with
  | [] | [_] -> []
  | _ :: rest -> if Nil? rest then [] else init #nat rest

let walk_restricted (w: list nat) (k: nat) : bool =
  all_less_than (intermediates w) k

let valid_restricted_walk (adj: Seq.seq int) (n: nat) (i j: nat) (k: nat) (w: list nat) : prop =
  is_walk w /\ walk_valid w n /\ walk_src w == i /\ walk_dst w == j /\
  walk_restricted w k /\ Seq.length adj == n * n

// If all vertices are < n, then intermediates are also < n
let rec lemma_all_lt_sublist (l: list nat) (k: nat)
  : Lemma (requires all_less_than l k = true)
          (ensures  all_less_than (intermediates l) k = true)
          (decreases l)
  = match l with
    | [] | [_] | [_; _] -> ()
    | a :: b :: c :: rest ->
      // intermediates (a :: b :: c :: rest) = init (b :: c :: rest) = b :: init (c :: rest)
      // all_less_than (a :: b :: c :: rest) k ==> a < k /\ b < k /\ all_less_than (c :: rest) k
      // Need: all_less_than (b :: init (c :: rest)) k
      // b < k is known. Need: all_less_than (init (c :: rest)) k
      // intermediates (b :: c :: rest) = init (c :: rest)
      // all_less_than (b :: c :: rest) k is known (sublist of input)
      lemma_all_lt_sublist (b :: c :: rest) k

let lemma_walk_valid_restricted (w: list nat) (n: nat)
  : Lemma (requires walk_valid w n)
          (ensures walk_restricted w n)
  = lemma_all_lt_sublist w n

(* ========================================================================
   § 2. Basic Walk Properties + Base Case
   ======================================================================== *)

let lemma_direct_walk_valid (adj: Seq.seq int) (n: nat) (i j: nat) (k: nat)
  : Lemma (requires i < n /\ j < n /\ Seq.length adj == n * n)
          (ensures valid_restricted_walk adj n i j k [i; j])
  = ()

let lemma_direct_walk_weight (adj: Seq.seq int) (n: nat) (i j: nat)
  : Lemma (requires i < n /\ j < n /\ Seq.length adj == n * n)
          (ensures walk_weight adj n [i; j] == Seq.index adj (i * n + j))
  = ()

let lemma_fw_entry_base (adj: Seq.seq int) (n: nat) (i j: nat)
  : Lemma (requires i < n /\ j < n /\ Seq.length adj == n * n)
          (ensures fw_entry adj n i j 0 == walk_weight adj n [i; j])
  = ()

let lemma_restricted_0_is_direct (w: list nat) (n: nat) (i j: nat)
  : Lemma (requires is_walk w /\ walk_valid w n /\ walk_src w == i /\ walk_dst w == j /\
                    walk_restricted w 0)
          (ensures w == [i; j])
  = match w with
    | [_; _] -> ()
    | _ :: b :: _ :: _ ->
      assert (mem b (intermediates w));
      assert (b < 0)

let lemma_fw_entry_k0_is_shortest (adj: Seq.seq int) (n: nat) (i j: nat) (w: list nat)
  : Lemma (requires i < n /\ j < n /\ Seq.length adj == n * n /\
                    valid_restricted_walk adj n i j 0 w)
          (ensures fw_entry adj n i j 0 == walk_weight adj n w)
  = lemma_restricted_0_is_direct w n i j;
    lemma_fw_entry_base adj n i j

(* ========================================================================
   § 3. Walk Splitting and Weight Additivity
   ======================================================================== *)

// Split a walk at the first occurrence of vertex v in its intermediates.
// Returns the prefix [src, ..., v].
let rec walk_split_prefix (w: list nat) (v: nat)
  : Tot (list nat) (decreases length w)
  = match w with
    | [] | [_] | [_; _] -> w
    | a :: b :: rest ->
      if b = v then [a; b]
      else a :: walk_split_prefix (b :: rest) v

// Returns the suffix [v, ..., dst].
let rec walk_split_suffix (w: list nat) (v: nat)
  : Tot (list nat) (decreases length w)
  = match w with
    | [] | [_] | [_; _] -> w
    | a :: b :: rest ->
      if b = v then b :: rest
      else walk_split_suffix (b :: rest) v

// The prefix is a walk when v appears in intermediates
let rec lemma_split_prefix_is_walk (w: list nat) (v: nat)
  : Lemma (requires is_walk w /\ mem v (intermediates w))
          (ensures is_walk (walk_split_prefix w v))
          (decreases length w)
  = match w with
    | _ :: b :: rest ->
      if b = v then ()
      else begin
        // v must be in intermediates of b :: rest
        // intermediates (a :: b :: rest) = init (b :: rest) when rest <> []
        // if rest = [x], intermediates = [b], so if b<>v, contradiction
        // if rest = x :: y :: more, intermediates = b :: init (rest) 
        //   since b<>v, v must be in init(rest) = intermediates of (b :: rest)
        match rest with
        | [] -> () // impossible since v in intermediates
        | [_] -> () // intermediates = [b], b<>v, contradiction
        | _ :: _ :: _ -> lemma_split_prefix_is_walk (b :: rest) v
      end

// The suffix is a walk when v appears in intermediates
let rec lemma_split_suffix_is_walk (w: list nat) (v: nat)
  : Lemma (requires is_walk w /\ mem v (intermediates w))
          (ensures is_walk (walk_split_suffix w v))
          (decreases length w)
  = match w with
    | _ :: b :: rest ->
      if b = v then ()
      else begin
        match rest with
        | [] -> ()
        | [_] -> ()
        | _ :: _ :: _ -> lemma_split_suffix_is_walk (b :: rest) v
      end

// The prefix starts at walk_src
let rec lemma_split_prefix_src (w: list nat) (v: nat)
  : Lemma (requires is_walk w /\ mem v (intermediates w))
          (ensures walk_src (walk_split_prefix w v) == walk_src w)
          (decreases length w)
  = match w with
    | _ :: b :: rest ->
      if b = v then ()
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ -> lemma_split_prefix_src (b :: rest) v

// The prefix ends at v
let rec lemma_split_prefix_dst (w: list nat) (v: nat)
  : Lemma (requires is_walk w /\ mem v (intermediates w))
          (ensures walk_dst (walk_split_prefix w v) == v)
          (decreases length w)
  = match w with
    | _ :: b :: rest ->
      if b = v then ()
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ ->
          lemma_split_prefix_is_walk (b :: rest) v;
          lemma_split_prefix_dst (b :: rest) v

// The suffix starts at v
let rec lemma_split_suffix_src (w: list nat) (v: nat)
  : Lemma (requires is_walk w /\ mem v (intermediates w))
          (ensures is_walk (walk_split_suffix w v) /\
                   walk_src (walk_split_suffix w v) == v)
          (decreases length w)
  = lemma_split_suffix_is_walk w v;
    match w with
    | _ :: b :: rest ->
      if b = v then ()
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ -> lemma_split_suffix_src (b :: rest) v

// The suffix ends at walk_dst
let rec lemma_split_suffix_dst (w: list nat) (v: nat)
  : Lemma (requires is_walk w /\ mem v (intermediates w))
          (ensures is_walk (walk_split_suffix w v) /\
                   walk_dst (walk_split_suffix w v) == walk_dst w)
          (decreases length w)
  = lemma_split_suffix_is_walk w v;
    match w with
    | _ :: b :: rest ->
      if b = v then ()
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ ->
          lemma_split_suffix_is_walk (b :: rest) v;
          lemma_split_suffix_dst (b :: rest) v

// The prefix starts with the same first two elements as the walk (when v is deeper)
let rec lemma_split_prefix_hd (w: list nat) (v: nat)
  : Lemma (requires is_walk w /\ mem v (intermediates w))
          (ensures Cons? (walk_split_prefix w v) /\ hd (walk_split_prefix w v) == hd w)
          (decreases length w)
  = match w with
    | _ :: b :: rest ->
      if b = v then ()
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ -> lemma_split_prefix_hd (b :: rest) v

// Weight additivity: weight(w) == weight(prefix) + weight(suffix)
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let rec lemma_split_weight (adj: Seq.seq int) (n: nat) (w: list nat) (v: nat)
  : Lemma (requires is_walk w /\ mem v (intermediates w) /\ Seq.length adj == n * n /\
                    walk_valid w n /\ n > 0)
          (ensures walk_weight adj n w ==
                   walk_weight adj n (walk_split_prefix w v) +
                   walk_weight adj n (walk_split_suffix w v))
          (decreases length w)
  = match w with
    | a :: b :: rest ->
      if b = v then ()
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ ->
          lemma_split_weight adj n (b :: rest) v;
          lemma_split_prefix_hd (b :: rest) v;
          lemma_split_prefix_is_walk (b :: rest) v;
          let pfx = walk_split_prefix (b :: rest) v in
          assert (hd pfx == b);
          assert (is_walk pfx);
          assert (length pfx >= 2);
          // walk_split_prefix(w, v) = a :: pfx
          assert (walk_split_prefix w v == a :: pfx);
          // Since pfx starts with b and has length >= 2, a :: pfx = a :: b :: tl pfx
          assert (a * n + b < n * n);
          // walk_weight (a :: pfx) = adj[a,b] + walk_weight pfx
          assert (walk_weight adj n (a :: pfx) ==
                  Seq.index adj (a * n + b) + walk_weight adj n pfx);
          // walk_weight w = adj[a,b] + walk_weight (b::rest)
          assert (walk_weight adj n w ==
                  Seq.index adj (a * n + b) + walk_weight adj n (b :: rest))
#pop-options

// The suffix is strictly shorter
let rec lemma_split_suffix_shorter (w: list nat) (v: nat)
  : Lemma (requires is_walk w /\ mem v (intermediates w))
          (ensures length (walk_split_suffix w v) < length w)
          (decreases length w)
  = match w with
    | _ :: b :: rest ->
      if b = v then ()
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ -> lemma_split_suffix_shorter (b :: rest) v

// walk_valid is preserved by splitting
let rec lemma_split_prefix_valid (w: list nat) (v: nat) (n: nat)
  : Lemma (requires is_walk w /\ walk_valid w n /\ mem v (intermediates w))
          (ensures walk_valid (walk_split_prefix w v) n)
          (decreases length w)
  = match w with
    | _ :: b :: rest ->
      if b = v then ()
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ -> lemma_split_prefix_valid (b :: rest) v n

let rec lemma_split_suffix_valid (w: list nat) (v: nat) (n: nat)
  : Lemma (requires is_walk w /\ walk_valid w n /\ mem v (intermediates w))
          (ensures walk_valid (walk_split_suffix w v) n)
          (decreases length w)
  = match w with
    | _ :: b :: rest ->
      if b = v then ()
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ -> lemma_split_suffix_valid (b :: rest) v n

(* ========================================================================
   § 4. Restriction Properties of Split Walks
   ======================================================================== *)

// The prefix (split at FIRST v in intermediates) has intermediates not containing v
let rec lemma_split_prefix_no_v (w: list nat) (v: nat)
  : Lemma (requires is_walk w /\ mem v (intermediates w))
          (ensures not (mem v (intermediates (walk_split_prefix w v))))
          (decreases length w)
  = match w with
    | _ :: b :: rest ->
      if b = v then ()  // prefix = [a; b], intermediates = []
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ -> lemma_split_prefix_no_v (b :: rest) v

// If walk is restricted to k and v = k-1, the prefix is restricted to k-1
let rec lemma_split_prefix_restricted (w: list nat) (k: nat)
  : Lemma (requires is_walk w /\ k > 0 /\ mem (k-1) (intermediates w) /\
                    walk_restricted w k)
          (ensures walk_restricted (walk_split_prefix w (k-1)) (k-1))
          (decreases length w)
  = match w with
    | _ :: b :: rest ->
      if b = k - 1 then ()  // prefix = [a; b], intermediates = [], restricted to anything
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ -> lemma_split_prefix_restricted (b :: rest) k

// The suffix is restricted to k (same level as original)
let rec lemma_split_suffix_restricted (w: list nat) (v: nat) (k: nat)
  : Lemma (requires is_walk w /\ mem v (intermediates w) /\ walk_restricted w k)
          (ensures walk_restricted (walk_split_suffix w v) k)
          (decreases length w)
  = match w with
    | _ :: b :: rest ->
      if b = v then ()  // suffix = v :: rest, intermediates ⊂ intermediates of w
      else match rest with
        | [] | [_] -> ()
        | _ :: _ :: _ -> lemma_split_suffix_restricted (b :: rest) v k

// Weakening: restricted to k-1 implies restricted to k
let rec lemma_all_less_than_weaken (l: list nat) (k: nat)
  : Lemma (requires k > 0 /\ all_less_than l (k - 1) = true) 
          (ensures all_less_than l k = true) 
          (decreases l) =
  match l with
  | [] -> ()
  | x :: rest -> lemma_all_less_than_weaken rest k

let lemma_restricted_weaken (w: list nat) (k: nat)
  : Lemma (requires k > 0 /\ walk_restricted w (k - 1))
          (ensures walk_restricted w k)
  = lemma_all_less_than_weaken (intermediates w) k

// Strengthening: all < k and k-1 not in list implies all < k-1
let rec lemma_all_less_than_strengthen (l: list nat) (k: nat)
  : Lemma (requires k > 0 /\ all_less_than l k = true /\ not (mem (k - 1) l))
          (ensures all_less_than l (k - 1) = true)
          (decreases l) =
  match l with
  | [] -> ()
  | x :: rest -> lemma_all_less_than_strengthen rest k

let lemma_restricted_strengthen (w: list nat) (k: nat)
  : Lemma (requires k > 0 /\ walk_restricted w k /\ not (mem (k - 1) (intermediates w)))
          (ensures walk_restricted w (k - 1))
  = lemma_all_less_than_strengthen (intermediates w) k

(* ========================================================================
   § 5. Walk Concatenation
   ======================================================================== *)

// Concatenate w1 = [a;...;v] and w2 = [v;...;b] into [a;...;v;...;b]
let walk_concat (w1: list nat) (w2: list nat{is_walk w2}) : list nat =
  w1 @ (tl w2)

let lemma_concat_is_walk (w1 w2: list nat)
  : Lemma (requires is_walk w1 /\ is_walk w2)
          (ensures is_walk (walk_concat w1 w2))
  = assert (length (walk_concat w1 w2) == length w1 + length w2 - 1);
    assert (length w1 >= 2 /\ length w2 >= 2)

let lemma_concat_src (w1 w2: list nat)
  : Lemma (requires is_walk w1 /\ is_walk w2)
          (ensures walk_src (walk_concat w1 w2) == walk_src w1)
  = // hd ((a :: rest) @ l) = a, trivial by reduction
    ()

// Weight of concatenation
#push-options "--z3rlimit 10 --fuel 4 --ifuel 2"
let rec lemma_concat_weight (adj: Seq.seq int) (n: nat) (w1 w2: list nat)
  : Lemma (requires is_walk w1 /\ is_walk w2 /\ walk_dst w1 == walk_src w2 /\
                    walk_valid w1 n /\ walk_valid w2 n /\
                    Seq.length adj == n * n)
          (ensures walk_weight adj n (walk_concat w1 w2) ==
                   walk_weight adj n w1 + walk_weight adj n w2)
          (decreases w1)
  = match w1 with
    | [a; b] ->
      assert (a < n /\ b < n);
      assert (a * n + b < n * n);
      assert (b :: tl w2 == w2)
    | a :: b :: c :: rest' ->
      let rest = b :: c :: rest' in
      assert (walk_valid rest n);
      assert (walk_dst rest == walk_dst w1);
      lemma_concat_weight adj n rest w2
#pop-options

// last of append with non-empty second list
let rec lemma_last_append (l1 l2: list nat)
  : Lemma (requires Cons? l1 /\ Cons? l2)
          (ensures last (l1 @ l2) == last l2)
          (decreases l1)
  = match l1 with
    | [_] -> ()
    | _ :: rest -> lemma_last_append rest l2

// Dst of concatenation
let lemma_concat_dst (w1 w2: list nat)
  : Lemma (requires is_walk w1 /\ is_walk w2)
          (ensures walk_dst (walk_concat w1 w2) == walk_dst w2)
  = assert (Cons? w1);
    assert (Cons? (tl w2));
    lemma_last_append w1 (tl w2)

// walk_valid preserved by concatenation
let rec lemma_concat_valid (w1 w2: list nat) (n: nat)
  : Lemma (requires is_walk w1 /\ is_walk w2 /\ walk_valid w1 n /\ walk_valid w2 n)
          (ensures walk_valid (walk_concat w1 w2) n)
          (decreases w1)
  = match w1 with
    | [a; b] -> ()
    | a :: b :: c :: rest' ->
      let rest = b :: c :: rest' in
      lemma_concat_valid rest w2 n

// Helper: all_less_than distributes over append
let rec lemma_all_lt_append (l1 l2: list nat) (k: nat)
  : Lemma (requires all_less_than l1 k /\ all_less_than l2 k)
          (ensures all_less_than (l1 @ l2) k)
          (decreases l1)
  = match l1 with
    | [] -> ()
    | _ :: rest -> lemma_all_lt_append rest l2 k

// Helper: all_less_than (init l) k /\ last l < k ==> all_less_than l k
let rec lemma_all_lt_init_last (l: list nat) (k: nat)
  : Lemma (requires Cons? l /\ all_less_than (init l) k /\ last l < k)
          (ensures all_less_than l k)
          (decreases l)
  = match l with
    | [_] -> ()
    | _ :: rest -> lemma_all_lt_init_last rest k

// Helper: init (l1 @ l2) = l1 @ init l2 when l2 is non-empty
#push-options "--fuel 2 --ifuel 1"
let rec lemma_init_append (l1: list nat) (l2: list nat{Cons? l2})
  : Lemma (ensures init (l1 @ l2) == l1 @ init l2)
          (decreases l1)
  = match l1 with
    | [] -> ()
    | [x] -> ()
    | x :: rest -> lemma_init_append rest l2
#pop-options

// walk_restricted for concatenation
let lemma_concat_restricted (w1 w2: list nat) (k: nat)
  : Lemma (requires is_walk w1 /\ is_walk w2 /\
                    walk_restricted w1 k /\ walk_restricted w2 k /\
                    walk_dst w1 < k)
          (ensures walk_restricted (walk_concat w1 w2) k)
  = // tl w1 has all elements < k: intermediates w1 are < k, and last (tl w1) = walk_dst w1 < k
    let t1 = tl w1 in
    let t2 = tl w2 in
    // tl w1 = intermediates w1 ++ [walk_dst w1], need all_less_than (tl w1) k
    lemma_all_lt_init_last t1 k;
    // init (tl w2) = intermediates w2, all < k
    assert (all_less_than (init t2) k);
    // intermediates(walk_concat w1 w2) = init (tl (w1 @ tl w2)) = init (tl w1 @ tl w2)
    //   = tl w1 @ init (tl w2) (by init_append, since Cons? (tl w2))
    assert (Cons? t2);
    lemma_init_append t1 t2;
    lemma_all_lt_append t1 (init t2) k

(* ========================================================================
   § 6. Monotonicity: fw_entry(i,j,k) ≤ fw_entry(i,j,k-1)
   ======================================================================== *)

let lemma_fw_entry_monotone (adj: Seq.seq int) (n: nat) (i j k: nat)
  : Lemma (requires k > 0 /\ i < n /\ j < n /\ Seq.length adj == n * n)
          (ensures fw_entry adj n i j k <= fw_entry adj n i j (k - 1))
  = ()  // Immediate: fw_entry(i,j,k) = min(fw_entry(i,j,k-1), ...) ≤ fw_entry(i,j,k-1)

let rec lemma_fw_entry_monotone_gen (adj: Seq.seq int) (n: nat) (i j k1 k2: nat)
  : Lemma (requires i < n /\ j < n /\ Seq.length adj == n * n /\ k1 <= k2)
          (ensures fw_entry adj n i j k2 <= fw_entry adj n i j k1)
          (decreases (k2 - k1))
  = if k1 = k2 then ()
    else begin
      lemma_fw_entry_monotone adj n i j k2;
      lemma_fw_entry_monotone_gen adj n i j k1 (k2 - 1)
    end

(* ========================================================================
   § 7. Achievability: for each fw_entry, there exists an achieving walk
   ======================================================================== *)

let rec achieving_walk (adj: Seq.seq int) (n: nat) (i j k: nat)
  : Pure (list nat)
    (requires i < n /\ j < n /\ k <= n /\ Seq.length adj == n * n)
    (ensures fun w ->
      valid_restricted_walk adj n i j k w /\
      walk_weight adj n w == fw_entry adj n i j k)
    (decreases k)
  = if k = 0 then begin
      lemma_direct_walk_valid adj n i j 0;
      lemma_direct_walk_weight adj n i j;
      [i; j]
    end
    else
      let without = fw_entry adj n i j (k - 1) in
      let d_ik = fw_entry adj n i (k - 1) (k - 1) in
      let d_kj = fw_entry adj n (k - 1) j (k - 1) in
      let via = d_ik + d_kj in
      if via < without then begin
        // Via k-1 is strictly better — concatenate achieving walks
        let w1 = achieving_walk adj n i (k - 1) (k - 1) in
        let w2 = achieving_walk adj n (k - 1) j (k - 1) in
        let w = walk_concat w1 w2 in
        lemma_concat_is_walk w1 w2;
        lemma_concat_src w1 w2;
        lemma_concat_dst w1 w2;
        lemma_concat_valid w1 w2 n;
        lemma_concat_weight adj n w1 w2;
        // w1 restricted to k-1, w2 restricted to k-1, walk_dst w1 = k-1 < k
        lemma_restricted_weaken w1 k;
        lemma_restricted_weaken w2 k;
        lemma_concat_restricted w1 w2 k;
        // weight = d_ik + d_kj = via = fw_entry(i,j,k) since via < without
        w
      end
      else begin
        // Without k-1 is at least as good — reuse walk from level k-1
        let w = achieving_walk adj n i j (k - 1) in
        // w is restricted to k-1, hence also to k
        lemma_restricted_weaken w k;
        w
      end

(* ========================================================================
   § 8. Soundness: fw_entry ≤ walk_weight for all restricted walks
   ======================================================================== *)

// Mutually recursive: strip_cycles needs soundness at k-1, 
// soundness needs strip_cycles at k.
// Combined decreases measure: %[k; length w]

let rec lemma_strip_cycles
  (adj: Seq.seq int) (n: nat) (j k: nat) (w: list nat)
  : Lemma
    (requires
      k > 0 /\ k <= n /\ j < n /\ Seq.length adj == n * n /\
      valid_restricted_walk adj n (k - 1) j k w /\
      (forall (k': nat) (v: nat). k' <= n /\ v < n ==> fw_entry adj n v v k' >= 0))
    (ensures fw_entry adj n (k - 1) j (k - 1) <= walk_weight adj n w)
    (decreases %[k; length w])
  = if not (mem (k - 1) (intermediates w)) then begin
      // w restricted to k but k-1 not in intermediates, so restricted to k-1
      lemma_restricted_strengthen w k;
      // Apply soundness at level k-1
      lemma_fw_entry_sound adj n (k - 1) j (k - 1) w
    end
    else begin
      // k-1 appears in intermediates — split at first k-1
      lemma_split_prefix_is_walk w (k - 1);
      lemma_split_suffix_is_walk w (k - 1);
      lemma_split_prefix_src w (k - 1);
      lemma_split_prefix_dst w (k - 1);
      lemma_split_suffix_src w (k - 1);
      lemma_split_suffix_dst w (k - 1);
      lemma_split_weight adj n w (k - 1);
      lemma_split_suffix_shorter w (k - 1);
      lemma_split_prefix_valid w (k - 1) n;
      lemma_split_suffix_valid w (k - 1) n;
      lemma_split_prefix_restricted w k;
      lemma_split_suffix_restricted w (k - 1) k;
      let w_a = walk_split_prefix w (k - 1) in  // k-1 → k-1, restricted to k-1
      let w_b = walk_split_suffix w (k - 1) in  // k-1 → j, restricted to k
      // w_a: k-1 → k-1, restricted to k-1 — use soundness at k-1
      lemma_fw_entry_sound adj n (k - 1) (k - 1) (k - 1) w_a;
      assert (fw_entry adj n (k - 1) (k - 1) (k - 1) <= walk_weight adj n w_a);
      // fw_entry(k-1,k-1,...) >= 0 implies weight(w_a) >= 0
      assert (walk_weight adj n w_a >= 0);
      // w_b: k-1 → j, restricted to k, |w_b| < |w| — recurse
      lemma_strip_cycles adj n j k w_b;
      assert (fw_entry adj n (k - 1) j (k - 1) <= walk_weight adj n w_b);
      // weight(w) = weight(w_a) + weight(w_b) >= weight(w_b)
      assert (walk_weight adj n w == walk_weight adj n w_a + walk_weight adj n w_b);
      assert (walk_weight adj n w_b <= walk_weight adj n w)
    end

and lemma_fw_entry_sound
  (adj: Seq.seq int) (n: nat) (i j k: nat) (w: list nat)
  : Lemma
    (requires
      i < n /\ j < n /\ k <= n /\ Seq.length adj == n * n /\
      valid_restricted_walk adj n i j k w /\
      (forall (k': nat) (v: nat). k' <= n /\ v < n ==> fw_entry adj n v v k' >= 0))
    (ensures fw_entry adj n i j k <= walk_weight adj n w)
    (decreases %[k; length w])
  = if k = 0 then begin
      lemma_restricted_0_is_direct w n i j;
      lemma_fw_entry_base adj n i j
    end
    else if not (mem (k - 1) (intermediates w)) then begin
      // w restricted to k but k-1 not in intermediates
      lemma_restricted_strengthen w k;
      lemma_fw_entry_sound adj n i j (k - 1) w;
      lemma_fw_entry_monotone adj n i j k
    end
    else begin
      // Split at first k-1
      lemma_split_prefix_is_walk w (k - 1);
      lemma_split_suffix_is_walk w (k - 1);
      lemma_split_prefix_src w (k - 1);
      lemma_split_prefix_dst w (k - 1);
      lemma_split_suffix_src w (k - 1);
      lemma_split_suffix_dst w (k - 1);
      lemma_split_weight adj n w (k - 1);
      lemma_split_prefix_valid w (k - 1) n;
      lemma_split_suffix_valid w (k - 1) n;
      lemma_split_prefix_restricted w k;
      lemma_split_suffix_restricted w (k - 1) k;
      let w_a = walk_split_prefix w (k - 1) in  // i → k-1, restricted to k-1
      let w_b = walk_split_suffix w (k - 1) in  // k-1 → j, restricted to k
      // w_a: i → k-1, restricted to k-1 — use soundness at k-1
      lemma_fw_entry_sound adj n i (k - 1) (k - 1) w_a;
      assert (fw_entry adj n i (k - 1) (k - 1) <= walk_weight adj n w_a);
      // w_b: k-1 → j, restricted to k — use cycle-stripping
      lemma_split_suffix_shorter w (k - 1);  // length w_b < length w
      lemma_strip_cycles adj n j k w_b;
      assert (fw_entry adj n (k - 1) j (k - 1) <= walk_weight adj n w_b);
      // Combine: fw_entry(i,j,k) ≤ fw_entry(i,k-1,k-1) + fw_entry(k-1,j,k-1) ≤ weight(w)
      assert (fw_entry adj n i j k <=
              fw_entry adj n i (k - 1) (k - 1) + fw_entry adj n (k - 1) j (k - 1));
      assert (walk_weight adj n w ==
              walk_weight adj n w_a + walk_weight adj n w_b)
    end

(* ========================================================================
   § 9. Top-level Shortest-Path Theorems
   ======================================================================== *)

// fw_entry is at most the weight of any valid walk (with all vertices < n)
let fw_entry_leq_any_walk
  (adj: Seq.seq int) (n: nat) (i j: nat) (w: list nat)
  : Lemma
    (requires
      i < n /\ j < n /\ n > 0 /\ Seq.length adj == n * n /\
      is_walk w /\ walk_valid w n /\ walk_src w == i /\ walk_dst w == j /\
      (forall (k': nat) (v: nat). k' <= n /\ v < n ==> fw_entry adj n v v k' >= 0))
    (ensures fw_entry adj n i j n <= walk_weight adj n w)
  = // Any walk with valid vertices is restricted to n (all intermediates < n)
    lemma_walk_valid_restricted w n;
    assert (valid_restricted_walk adj n i j n w);
    lemma_fw_entry_sound adj n i j n w

// fw_entry equals the weight of some valid walk
let fw_entry_eq_some_walk
  (adj: Seq.seq int) (n: nat) (i j: nat)
  : Lemma
    (requires i < n /\ j < n /\ n > 0 /\ Seq.length adj == n * n)
    (ensures exists (w: list nat).
      is_walk w /\ walk_valid w n /\ walk_src w == i /\ walk_dst w == j /\
      walk_weight adj n w == fw_entry adj n i j n)
  = let w = achieving_walk adj n i j n in
    ()

