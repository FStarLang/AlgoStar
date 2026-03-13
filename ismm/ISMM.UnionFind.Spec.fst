(**
 * ISMM: Extended Union-Find Pure Specification
 *
 * Paper: "Reference Counting Deeply Immutable Data Structures with Cycles"
 *        Parkinson, Clebsch, Wrigstad — ISMM '24
 *
 * Adapts CLRS.Ch21.UnionFind.Spec for the 4-state status encoding.
 * Nodes in RANK or REP state participate in the union-find forest;
 * UNMARKED and RC nodes are roots by convention (parent == self).
 *
 * Key properties:
 *   - pure_find is total (terminates) under rank_invariant
 *   - pure_union preserves uf_inv
 *   - Correctness: after union(x,y), pure_find x == pure_find y
 *   - Stability: union does not merge unrelated sets
 *)
module ISMM.UnionFind.Spec

open FStar.Seq
module Seq = FStar.Seq
open ISMM.Status

(*** 1. Forest Model ***)

/// UF state: three parallel arrays.
///   tag[i]:    status (UNMARKED=0, RANK=1, REP=2, RC=3)
///   parent[i]: UF parent (self for roots; parent index for non-roots)
///   rank[i]:   UF rank (meaningful for roots)
///
/// Separating parent and rank avoids the problem where converting a RANK
/// root to REP would destroy its rank information, breaking rank_invariant
/// for its children.
type uf_state = {
  n: nat;
  tag:    Seq.seq int;
  parent: Seq.seq nat;
  rank:   Seq.seq nat;
}

let is_root (s: uf_state) (i: nat) : prop =
  i < s.n /\ Seq.length s.parent == s.n /\
  Seq.index s.parent i == i

let is_valid (s: uf_state) : prop =
  s.n > 0 /\
  Seq.length s.tag == s.n /\
  Seq.length s.parent == s.n /\
  Seq.length s.rank == s.n /\
  (forall (i: nat). i < s.n ==> valid_tag (Seq.index s.tag i)) /\
  (forall (i: nat). i < s.n ==> Seq.index s.parent i < s.n)

/// CLRS Lemma 21.4: rank strictly increases along parent pointers.
let rank_invariant (s: uf_state) : prop =
  is_valid s /\
  (forall (x: nat). x < s.n /\ Seq.index s.parent x <> x ==>
    Seq.index s.rank x < Seq.index s.rank (Seq.index s.parent x))

/// Base invariant (structural): sufficient for pure_find termination.
let uf_inv_base (s: uf_state) : prop =
  is_valid s /\ rank_invariant s

(*** 2. Termination Measure ***)

let rec count_above (rank: Seq.seq nat) (r: nat) (k: nat) (n: nat{k <= n /\ n <= Seq.length rank})
  : Tot nat (decreases (n - k))
  = if k >= n then 0
    else (if Seq.index rank k > r then 1 else 0) + count_above rank r (k + 1) n

let rec count_above_mono (rank: Seq.seq nat) (r1 r2: nat) (k: nat) (n: nat{k <= n /\ n <= Seq.length rank})
  : Lemma (requires r1 <= r2)
          (ensures count_above rank r2 k n <= count_above rank r1 k n)
          (decreases (n - k))
  = if k >= n then () else count_above_mono rank r1 r2 (k + 1) n

let rec count_above_strict (rank: Seq.seq nat) (r: nat) (px: nat) (k: nat)
                           (n: nat{k <= n /\ n <= Seq.length rank})
  : Lemma (requires px < n /\ Seq.index rank px > r /\ k <= px)
          (ensures count_above rank r k n > count_above rank (Seq.index rank px) k n)
          (decreases (n - k))
  = if k = px then count_above_mono rank r (Seq.index rank px) (k + 1) n
    else count_above_strict rank r px (k + 1) n

(*** 3. Total Pure Find ***)

let rec pure_find (s: uf_state{uf_inv_base s}) (x: nat{x < s.n})
  : Tot nat (decreases (count_above s.rank (Seq.index s.rank x) 0 s.n))
  = if Seq.index s.parent x = x then x
    else begin
      count_above_strict s.rank (Seq.index s.rank x) (Seq.index s.parent x) 0 s.n;
      pure_find s (Seq.index s.parent x)
    end

let is_uf_root (s: uf_state{is_valid s}) (i: nat{i < s.n}) : prop =
  Seq.index s.parent i == i

let rec pure_find_is_root (s: uf_state{uf_inv_base s}) (x: nat{x < s.n})
  : Lemma (ensures is_root s (pure_find s x) /\ pure_find s x < s.n)
          (decreases (count_above s.rank (Seq.index s.rank x) 0 s.n))
  = if Seq.index s.parent x = x then ()
    else begin
      count_above_strict s.rank (Seq.index s.rank x) (Seq.index s.parent x) 0 s.n;
      pure_find_is_root s (Seq.index s.parent x)
    end

let pure_find_in_bounds (s: uf_state{uf_inv_base s}) (x: nat{x < s.n})
  : Lemma (ensures pure_find s x < s.n)
  = pure_find_is_root s x

let pure_find_root (s: uf_state{uf_inv_base s}) (root: nat{root < s.n})
  : Lemma (requires is_root s root)
          (ensures pure_find s root == root)
  = ()

let pure_find_idempotent (s: uf_state{uf_inv_base s}) (x: nat{x < s.n})
  : Lemma (ensures (pure_find_in_bounds s x;
                    pure_find s (pure_find s x) == pure_find s x))
  = pure_find_in_bounds s x;
    pure_find_is_root s x;
    pure_find_root s (pure_find s x)

let pure_find_step (s: uf_state{uf_inv_base s}) (x: nat{x < s.n})
  : Lemma (requires Seq.index s.parent x <> x)
          (ensures pure_find s x == pure_find s (Seq.index s.parent x))
  = count_above_strict s.rank (Seq.index s.rank x) (Seq.index s.parent x) 0 s.n

/// If two states agree on parent, rank, and n, pure_find gives the same result.
let rec pure_find_ext (s s': uf_state{uf_inv_base s /\ uf_inv_base s'}) (x: nat{x < s.n})
  : Lemma (requires s'.parent == s.parent /\ s'.rank == s.rank /\ s'.n == s.n)
          (ensures pure_find s' x == pure_find s x)
          (decreases (count_above s.rank (Seq.index s.rank x) 0 s.n))
  = if Seq.index s.parent x = x then ()
    else begin
      count_above_strict s.rank (Seq.index s.rank x) (Seq.index s.parent x) 0 s.n;
      pure_find_ext s s' (Seq.index s.parent x)
    end

(*** 1b. Component Size and Size-Rank Invariant ***)

/// 2^k, defined locally to avoid importing FStar.Math.Lib
let rec pow2 (k: nat) : Tot (r:nat{r >= 1}) (decreases k) =
  if k = 0 then 1 else op_Multiply 2 (pow2 (k - 1))

/// pow2 k > k for all k >= 0 (used to derive rank < n from 2^rank <= n)
let rec pow2_gt (k: nat) : Lemma (ensures pow2 k > k) (decreases k)
  = if k = 0 then ()
    else begin pow2_gt (k - 1); assert (pow2 (k-1) > k - 1) end

/// Count nodes whose pure_find root is `root`, scanning indices [0, k).
/// Requires uf_inv_base for pure_find termination.
let rec comp_count (s: uf_state{uf_inv_base s}) (root: nat{root < s.n}) (k: nat{k <= s.n})
  : Tot nat (decreases k)
  = if k = 0 then 0
    else (if pure_find s (k-1) = root then 1 else 0) + comp_count s root (k-1)

let rec comp_count_le (s: uf_state{uf_inv_base s}) (root: nat{root < s.n}) (k: nat{k <= s.n})
  : Lemma (ensures comp_count s root k <= k) (decreases k)
  = if k = 0 then () else comp_count_le s root (k-1)

/// comp_count is extensional: same parent/rank/n → same comp_count.
let rec comp_count_ext
  (s s': uf_state{uf_inv_base s /\ uf_inv_base s'})
  (root: nat{root < s.n}) (k: nat{k <= s.n})
  : Lemma (requires s'.parent == s.parent /\ s'.rank == s.rank /\ s'.n == s.n)
          (ensures comp_count s' root k == comp_count s root k)
          (decreases k)
  = if k = 0 then ()
    else begin pure_find_ext s s' (k-1); comp_count_ext s s' root (k-1) end

/// Size-rank invariant: for every root, its component has >= 2^rank nodes.
/// This is the key CLRS Lemma 21.4 property that bounds ranks.
let size_rank_inv (s: uf_state{uf_inv_base s}) : prop =
  forall (root: nat). root < s.n /\ Seq.index s.parent root = root ==>
    comp_count s root s.n >= pow2 (Seq.index s.rank root)

/// Tag-only changes preserve size_rank_inv (parent, rank unchanged).
let size_rank_inv_tag_ext
  (s s': uf_state{uf_inv_base s /\ uf_inv_base s'})
  : Lemma (requires s'.parent == s.parent /\ s'.rank == s.rank /\ s'.n == s.n /\ size_rank_inv s)
          (ensures size_rank_inv s')
  = let aux (root: nat{root < s'.n /\ Seq.index s'.parent root = root})
      : Lemma (comp_count s' root s'.n >= pow2 (Seq.index s'.rank root))
      = comp_count_ext s s' root s.n
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// If pure_find agrees on all nodes, comp_count agrees (even if parent differs).
let rec comp_count_find_ext
  (s s': uf_state{uf_inv_base s /\ uf_inv_base s'})
  (root: nat{root < s.n}) (k: nat{k <= s.n})
  : Lemma (requires s'.n == s.n /\ (forall (z:nat). z < s.n ==> pure_find s' z == pure_find s z))
          (ensures comp_count s' root k == comp_count s root k)
          (decreases k)
  = if k = 0 then ()
    else begin
      assert (pure_find s' (k-1) == pure_find s (k-1));
      comp_count_find_ext s s' root (k-1)
    end

/// If pure_find is preserved and roots/rank are compatible, size_rank_inv is preserved.
let size_rank_inv_find_ext
  (s s': uf_state{uf_inv_base s /\ uf_inv_base s'})
  : Lemma (requires s'.n == s.n /\ s'.rank == s.rank
                  /\ (forall (z:nat). z < s.n ==> pure_find s' z == pure_find s z)
                  /\ (forall (r:nat). r < s.n /\ Seq.index s'.parent r = r ==>
                        Seq.index s.parent r = r)
                  /\ size_rank_inv s)
          (ensures size_rank_inv s')
  = let aux (root: nat{root < s'.n /\ Seq.index s'.parent root = root})
      : Lemma (comp_count s' root s'.n >= pow2 (Seq.index s'.rank root))
      = comp_count_find_ext s s' root s.n
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let uf_inv (s: uf_state) : prop =
  uf_inv_base s /\ size_rank_inv s

(*** 4. Make Initial State ***)

/// In the initial state, every node is its own root, so comp_count = 1 for each.
let rec comp_count_self_parent
  (s: uf_state{uf_inv_base s})
  (root: nat{root < s.n}) (k: nat{k <= s.n})
  : Lemma
      (requires forall (i: nat). i < s.n ==> Seq.index s.parent i = i)
      (ensures comp_count s root k == (if root < k then 1 else 0))
      (decreases k)
  = if k = 0 then ()
    else comp_count_self_parent s root (k - 1)

/// All nodes start UNMARKED with parent == self, rank == 0.
let make_state (n: nat{n > 0}) : (s: uf_state{uf_inv s}) =
  let s = { n = n;
            tag = Seq.create n tag_unmarked;
            parent = Seq.init n (fun (i: nat{i < n}) -> (i <: nat));
            rank = Seq.create n 0 } in
  // Prove size_rank_inv: comp_count = 1 for each root, pow2(0) = 1
  assert (uf_inv_base s);
  let aux (root: nat{root < s.n})
    : Lemma (requires Seq.index s.parent root = root)
            (ensures comp_count s root s.n >= pow2 (Seq.index s.rank root))
    = comp_count_self_parent s root s.n
  in FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  s

let make_state_find (n: nat{n > 0}) (x: nat{x < n})
  : Lemma (pure_find (make_state n) x == x)
  = ()

(*** Rank bound: rank[i] < n for all i ***)

/// Follows from size_rank_inv: pow2(rank) <= comp_count <= n, and pow2(k) > k.
let rec rank_bounded (s: uf_state{uf_inv s}) (x: nat{x < s.n})
  : Lemma (ensures Seq.index s.rank x < s.n)
          (decreases (count_above s.rank (Seq.index s.rank x) 0 s.n))
  = let p = Seq.index s.parent x in
    if p = x then begin
      // Root case: from size_rank_inv, comp_count >= pow2(rank).
      // comp_count <= n and pow2(rank) > rank, so rank < pow2(rank) <= n.
      comp_count_le s x s.n;
      pow2_gt (Seq.index s.rank x)
    end
    else begin
      count_above_strict s.rank (Seq.index s.rank x) p 0 s.n;
      rank_bounded s p
    end

let rank_bounded_all (s: uf_state{uf_inv s})
  : Lemma (forall (i: nat). i < s.n ==> Seq.index s.rank i < s.n)
  = let aux (i: nat{i < s.n}) : Lemma (Seq.index s.rank i < s.n)
      = rank_bounded s i
    in FStar.Classical.forall_intro aux

(*** 5. Pure Union (defined here so SizeRank can import only Spec) ***)

/// Union two nodes by rank. Links one root to the other via parent array.
let pure_union (s: uf_state{uf_inv_base s}) (x y: nat{x < s.n /\ y < s.n}) : uf_state =
  pure_find_in_bounds s x; pure_find_in_bounds s y;
  let root_x = pure_find s x in
  let root_y = pure_find s y in
  if root_x = root_y then s
  else
    let rx = Seq.index s.rank root_x in
    let ry = Seq.index s.rank root_y in
    if rx < ry then
      { s with parent = Seq.upd s.parent root_x root_y }
    else if rx > ry then
      { s with parent = Seq.upd s.parent root_y root_x }
    else
      { s with parent = Seq.upd s.parent root_y root_x;
               rank = Seq.upd s.rank root_x (rx + 1) }

#push-options "--z3rlimit 20"
/// pure_union preserves the base invariant (is_valid + rank_invariant).
let pure_union_preserves_inv_base (s: uf_state{uf_inv_base s}) (x y: nat{x < s.n /\ y < s.n})
  : Lemma (ensures uf_inv_base (pure_union s x y))
  = pure_find_in_bounds s x; pure_find_in_bounds s y;
    pure_find_is_root s x; pure_find_is_root s y;
    let root_x = pure_find s x in
    let root_y = pure_find s y in
    if root_x = root_y then ()
    else
      let s' = pure_union s x y in
      let valid_aux (i: nat{i < s'.n}) : Lemma (Seq.index s'.parent i < s'.n) = () in
      FStar.Classical.forall_intro valid_aux;
      let ri_aux (z: nat{z < s'.n /\ Seq.index s'.parent z <> z})
        : Lemma (Seq.index s'.rank z < Seq.index s'.rank (Seq.index s'.parent z))
        = () in FStar.Classical.forall_intro ri_aux
#pop-options

(*** 6. How pure_find changes after linking root_a → root_b ***)

#restart-solver
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let rec pure_find_after_link
  (s s': uf_state{uf_inv_base s /\ uf_inv_base s'})
  (root_a root_b: nat)
  (z: nat{z < s.n})
  : Lemma
      (requires
        root_a < s.n /\ root_b < s.n /\ root_a <> root_b /\
        is_root s root_a /\ is_root s root_b /\
        s'.n == s.n /\ Seq.length s'.rank == s.n /\
        s'.parent == Seq.upd s.parent root_a root_b /\
        (forall (i: nat). i < s.n ==> Seq.index s'.rank i >= Seq.index s.rank i))
      (ensures
        (if pure_find s z = root_a then pure_find s' z = root_b
         else if pure_find s z = root_b then pure_find s' z = root_b
         else pure_find s' z = pure_find s z))
      (decreases (count_above s.rank (Seq.index s.rank z) 0 s.n))
  = let pz = Seq.index s.parent z in
    if pz = z then begin
      if z = root_a then begin
        assert (Seq.index s'.parent root_a == root_b);
        assert (Seq.index s'.parent root_b == root_b);
        assert (pure_find s' root_b == root_b);
        count_above_strict s'.rank (Seq.index s'.rank root_a) root_b 0 s'.n;
        assert (pure_find s' root_a == pure_find s' root_b)
      end else ()
    end
    else begin
      assert (z <> root_a);
      assert (Seq.index s'.parent z == pz);
      count_above_strict s.rank (Seq.index s.rank z) pz 0 s.n;
      pure_find_after_link s s' root_a root_b pz;
      count_above_strict s'.rank (Seq.index s'.rank z) pz 0 s'.n
    end
#pop-options
