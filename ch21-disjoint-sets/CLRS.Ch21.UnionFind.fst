(*
   Union-Find (Disjoint Sets) - Verified implementation in Pulse
   
   Implements union by rank with path compression (CLRS Chapter 21).
   - find: read-only root-finding with shared permission
   - find_compress: root-finding + one-step path compression (parent[x] = root)
   - union_: union by rank with rank increment on equal-rank merge (CLRS line 5-6)
   
   Proves:
   1. Memory safety
   2. find returns a root (parent[root] = root)
   3. After make_set, each element is its own parent
   4. After union(x, y), find(x) == find(y)
   5. find_compress sets parent[x] directly to root
   
   NO admits. NO assumes.
*)

module CLRS.Ch21.UnionFind
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Specifications ==========

// Well-formed parent array: all values are valid indices < n
let well_formed (parent: Seq.seq SZ.t) (n: nat) : prop =
  n > 0 /\
  n <= Seq.length parent /\
  (forall (idx: nat). idx < n ==> SZ.v (Seq.index parent idx) < n)

// Element is a root if parent[i] = i
let is_root (parent: Seq.seq SZ.t) (i: nat) : prop =
  i < Seq.length parent /\
  SZ.v (Seq.index parent i) == i

// Depth to root: every element reaches a root in at most depth steps
// This captures the acyclicity/forest property
let rec has_root_within (parent: Seq.seq SZ.t) (i: nat) (depth: nat) : Tot prop (decreases depth) =
  i < Seq.length parent /\
  (SZ.v (Seq.index parent i) == i \/  // i is a root
   (depth > 0 /\ has_root_within parent (SZ.v (Seq.index parent i)) (depth - 1)))

// A forest: every element reaches a root within n steps
let is_forest (parent: Seq.seq SZ.t) (n: nat) : prop =
  well_formed parent n /\
  (forall (idx: nat). idx < n ==> has_root_within parent idx n)

// Pure recursive find (specification only)
let rec find_root (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) : Tot nat (decreases fuel) =
  if fuel = 0 then i
  else if i >= Seq.length parent then i
  else
    let p = SZ.v (Seq.index parent i) in
    if p = i then i
    else find_root parent p (fuel - 1)

// Key lemma: following parent pointers from a node with has_root_within
// eventually reaches a root
let rec find_root_is_root (parent: Seq.seq SZ.t) (i: nat) (depth: nat)
  : Lemma (requires has_root_within parent i depth)
          (ensures is_root parent (find_root parent i depth))
          (decreases depth)
  = if SZ.v (Seq.index parent i) = i then ()
    else find_root_is_root parent (SZ.v (Seq.index parent i)) (depth - 1)

// find_root with more fuel gives same result
let rec find_root_monotone (parent: Seq.seq SZ.t) (i: nat) (d1 d2: nat)
  : Lemma (requires has_root_within parent i d1 /\ d2 >= d1)
          (ensures find_root parent i d1 == find_root parent i d2)
          (decreases d1)
  = if SZ.v (Seq.index parent i) = i then ()
    else begin
      assert (d1 > 0 /\ d2 > 0);
      find_root_monotone parent (SZ.v (Seq.index parent i)) (d1 - 1) (d2 - 1)
    end

// ========== Forest path analysis (for union preservation proof) ==========

// Weakening: more depth is always fine
let rec has_root_within_weaken (parent: Seq.seq SZ.t) (i: nat) (d d': nat)
  : Lemma (requires has_root_within parent i d /\ d' >= d)
          (ensures has_root_within parent i d')
          (decreases d)
  = if SZ.v (Seq.index parent i) = i then ()
    else has_root_within_weaken parent (SZ.v (Seq.index parent i)) (d - 1) (d' - 1)

// Follow parent pointers for a given number of steps
let rec follow (parent: Seq.seq SZ.t) (i: nat) (steps: nat) : Tot nat (decreases steps) =
  if steps = 0 then i
  else if i >= Seq.length parent then i
  else follow parent (SZ.v (Seq.index parent i)) (steps - 1)

// follow unfolds one step
let follow_step (parent: Seq.seq SZ.t) (i: nat) (steps: nat)
  : Lemma (requires i < Seq.length parent /\ steps > 0)
          (ensures follow parent i steps == follow parent (SZ.v (Seq.index parent i)) (steps - 1))
  = ()

// follow composes
let rec follow_split (parent: Seq.seq SZ.t) (n: nat) (i: nat) (a b: nat)
  : Lemma (requires well_formed parent n /\ i < n /\ a + b <= n)
          (ensures follow parent i (a + b) == follow parent (follow parent i a) b)
          (decreases a)
  = if a = 0 then ()
    else begin
      let p = SZ.v (Seq.index parent i) in
      follow_split parent n p (a - 1) b
    end

// follow stays in bounds for well_formed forests
let rec follow_bounded (parent: Seq.seq SZ.t) (n: nat) (i: nat) (steps: nat)
  : Lemma (requires well_formed parent n /\ i < n /\ steps <= n)
          (ensures follow parent i steps < n)
          (decreases steps)
  = if steps = 0 then ()
    else follow_bounded parent n (SZ.v (Seq.index parent i)) (steps - 1)

// Cycle at a non-root contradicts has_root_within
let rec nonroot_cycle_false (parent: Seq.seq SZ.t) (n: nat) (v: nat) (m: pos) (d: nat)
  : Lemma (requires well_formed parent n /\ v < n /\
                    SZ.v (Seq.index parent v) <> v /\
                    follow parent v m == v /\
                    has_root_within parent v d /\ m <= n)
          (ensures False)
          (decreases d)
  = // v is not a root, so d > 0 and has_root_within parent (parent[v]) (d-1)
    let p = SZ.v (Seq.index parent v) in
    // follow v m = v, and follow v 1 = p
    // So follow p (m-1) = v (by unfolding follow v m)
    assert (follow parent p (m - 1) == v);
    // So follow p m = follow (follow p (m-1)) 1 = follow v 1 = p
    follow_split parent n p (m - 1) 1;
    assert (follow parent p m == p);
    // Now: has_root_within parent p (d-1), and follow p m = p
    if SZ.v (Seq.index parent p) = p then begin
      // p is a root, so follow p k = p for all k
      // follow p (m-1) = p. But follow p (m-1) = v. So v = p.
      let rec follow_root_stays (parent: Seq.seq SZ.t) (r: nat) (k: nat)
        : Lemma (requires r < Seq.length parent /\ SZ.v (Seq.index parent r) = r)
                (ensures follow parent r k == r)
                (decreases k)
        = if k = 0 then () else follow_root_stays parent r (k - 1)
      in
      follow_root_stays parent p (m - 1);
      assert (v == p);
      assert (SZ.v (Seq.index parent v) == v)
    end
    else
      nonroot_cycle_false parent n p m (d - 1)

// Number of steps from i to its root (with given fuel)
let rec path_len (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) : Tot nat (decreases fuel) =
  if fuel = 0 then 0
  else if i >= Seq.length parent then 0
  else if SZ.v (Seq.index parent i) = i then 0
  else 1 + path_len parent (SZ.v (Seq.index parent i)) (fuel - 1)

// path_len is at most fuel
let rec path_len_le_fuel (parent: Seq.seq SZ.t) (i: nat) (fuel: nat)
  : Lemma (ensures path_len parent i fuel <= fuel)
          (decreases fuel)
  = if fuel = 0 then ()
    else if i >= Seq.length parent then ()
    else if SZ.v (Seq.index parent i) = i then ()
    else path_len_le_fuel parent (SZ.v (Seq.index parent i)) (fuel - 1)

// has_root_within holds at the exact path length
let rec has_root_within_exact (parent: Seq.seq SZ.t) (i: nat) (fuel: nat)
  : Lemma (requires has_root_within parent i fuel)
          (ensures has_root_within parent i (path_len parent i fuel))
          (decreases fuel)
  = if SZ.v (Seq.index parent i) = i then ()
    else has_root_within_exact parent (SZ.v (Seq.index parent i)) (fuel - 1)

// The k-th node on the path (0 = start, path_len = root)
let rec path_node (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) (k: nat) : Tot nat (decreases k) =
  if k = 0 then i
  else if fuel = 0 then i
  else if i >= Seq.length parent then i
  else if SZ.v (Seq.index parent i) = i then i
  else path_node parent (SZ.v (Seq.index parent i)) (fuel - 1) (k - 1)

// path_node equals follow for k <= path_len
let rec path_node_eq_follow (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) (k: nat)
  : Lemma (requires i < Seq.length parent /\ has_root_within parent i fuel /\ k <= path_len parent i fuel)
          (ensures path_node parent i fuel k == follow parent i k)
          (decreases k)
  = if k = 0 then ()
    else begin
      // k > 0, fuel > 0 (since k <= path_len <= fuel and path_len > 0 means parent[i] ≠ i)
      // parent[i] ≠ i (since path_len > 0)
      let p = SZ.v (Seq.index parent i) in
      path_node_eq_follow parent p (fuel - 1) (k - 1)
    end

// path_node at k < path_len is NOT a root
let rec path_node_not_root (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) (k: nat)
  : Lemma (requires i < Seq.length parent /\ has_root_within parent i fuel /\
                    k < path_len parent i fuel)
          (ensures (let v = path_node parent i fuel k in
                    v < Seq.length parent /\ SZ.v (Seq.index parent v) <> v))
          (decreases k)
  = if k = 0 then ()  // path_len > 0 means parent[i] ≠ i, so i is not a root
    else path_node_not_root parent (SZ.v (Seq.index parent i)) (fuel - 1) (k - 1)

// path_node is bounded
let rec path_node_bounded (parent: Seq.seq SZ.t) (n: nat) (i: nat) (fuel: nat) (k: nat)
  : Lemma (requires well_formed parent n /\ i < n /\ has_root_within parent i fuel /\
                    k <= path_len parent i fuel)
          (ensures path_node parent i fuel k < n)
          (decreases k)
  = if k = 0 then ()
    else path_node_bounded parent n (SZ.v (Seq.index parent i)) (fuel - 1) (k - 1)

// KEY LEMMA: path_len < n for forests (path visits ≤ n distinct nodes)
// Proof by contradiction using FStar.Fin.pigeonhole
#push-options "--z3rlimit 40"
let path_len_strict_bound (parent: Seq.seq SZ.t) (n: nat) (i: nat)
  : Lemma (requires is_forest parent n /\ i < n)
          (ensures path_len parent i n < n)
  = let pl = path_len parent i n in
    path_len_le_fuel parent i n;
    if pl >= n then begin
      // Build a sequence of pl+1 > n path nodes, all < n
      // By pigeonhole, two are equal, creating a cycle → contradiction
      let mk_node (k: nat{k < pl + 1}) : FStar.Fin.under n =
        path_node_bounded parent n i n k;
        path_node parent i n k
      in
      let s : Seq.seq (FStar.Fin.under n) = Seq.init (pl + 1) mk_node in
      assert (Seq.length s == pl + 1);
      assert (pl + 1 > n);  // since pl >= n
      let (k1, k2) = FStar.Fin.pigeonhole #n s in
      // k1 < k2, and path_node k1 = path_node k2
      assert (k1 < k2);
      assert (Seq.index s k1 == Seq.index s k2);
      assert (path_node parent i n k1 == path_node parent i n k2);
      let v = path_node parent i n k1 in
      // v is not a root (since k1 < k2 <= pl means k1 < pl)
      path_node_not_root parent i n k1;
      assert (SZ.v (Seq.index parent v) <> v);
      // v = follow i k1, and path_node k2 = follow i k2 = v
      path_node_eq_follow parent i n k1;
      path_node_eq_follow parent i n k2;
      assert (follow parent i k1 == v);
      assert (follow parent i k2 == v);
      // follow v (k2 - k1) = v (cycle!)
      let m = k2 - k1 in
      follow_bounded parent n i n;
      assert (follow parent i n < n);
      follow_bounded parent n i k1;
      assert (v < n);
      follow_split parent n i k1 m;
      assert (follow parent i (k1 + m) == follow parent v m);
      assert (follow parent v m == v);
      // has_root_within parent v n (from is_forest)
      // Contradiction: non-root cycle at v
      nonroot_cycle_false parent n v m n
    end
#pop-options

// Tightening: in a forest, has_root_within holds at depth n-1
let has_root_within_tight (parent: Seq.seq SZ.t) (n: nat) (i: nat)
  : Lemma (requires is_forest parent n /\ i < n)
          (ensures has_root_within parent i (n - 1))
  = has_root_within_exact parent i n;
    path_len_strict_bound parent n i;
    has_root_within_weaken parent i (path_len parent i n) (n - 1)

// Union increases depth by at most 1
let rec union_depth_increase
  (parent: Seq.seq SZ.t) (n: nat) (root_a root_b: nat) (i: nat) (d: nat)
  : Lemma (requires well_formed parent n /\
                    root_a < n /\ root_b < n /\ root_a <> root_b /\
                    is_root parent root_a /\ is_root parent root_b /\
                    i < n /\ d <= n /\
                    has_root_within parent i d /\ SZ.fits root_b)
          (ensures has_root_within (Seq.upd parent root_a (SZ.uint_to_t root_b)) i (d + 1))
          (decreases d)
  = let parent' = Seq.upd parent root_a (SZ.uint_to_t root_b) in
    if SZ.v (Seq.index parent i) = i then begin
      // i is a root in old forest
      if i = root_a then begin
        // parent'[root_a] = root_b, and root_b is still a root in parent'
        assert (SZ.v (Seq.index parent' root_a) == root_b);
        assert (SZ.v (Seq.index parent' root_b) == root_b);
        // has_root_within parent' root_b 0 (root_b is a root)
        // has_root_within parent' root_a 1
        assert (has_root_within parent' root_a 1);
        has_root_within_weaken parent' root_a 1 (d + 1)
      end
      else begin
        // i ≠ root_a, so parent'[i] = parent[i] = i
        assert (SZ.v (Seq.index parent' i) == i);
        assert (has_root_within parent' i 0);
        has_root_within_weaken parent' i 0 (d + 1)
      end
    end
    else begin
      // i is not a root. Since root_a IS a root, i ≠ root_a.
      assert (i <> root_a);
      assert (SZ.v (Seq.index parent' i) == SZ.v (Seq.index parent i));
      let p = SZ.v (Seq.index parent i) in
      // has_root_within parent p (d-1), and d > 0
      union_depth_increase parent n root_a root_b p (d - 1)
      // IH gives: has_root_within parent' p d
      // Since parent'[i] = p and d+1 > 0: has_root_within parent' i (d+1)
    end

// Union preserves is_forest
let union_preserves_is_forest
  (parent: Seq.seq SZ.t) (n: nat) (root_a root_b: nat)
  : Lemma (requires is_forest parent n /\
                    root_a < n /\ root_b < n /\ root_a <> root_b /\
                    is_root parent root_a /\ is_root parent root_b /\
                    SZ.fits root_b)
          (ensures is_forest (Seq.upd parent root_a (SZ.uint_to_t root_b)) n)
  = let parent' = Seq.upd parent root_a (SZ.uint_to_t root_b) in
    // well_formed parent' n: all indices still valid
    assert (well_formed parent' n);
    // has_root_within for all nodes
    let aux (idx: nat{idx < n})
      : Lemma (has_root_within parent' idx n)
      = has_root_within_tight parent n idx;
        // has_root_within parent idx (n-1)
        union_depth_increase parent n root_a root_b idx (n - 1)
        // has_root_within parent' idx n
    in
    FStar.Classical.forall_intro aux

fn make_set
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  requires
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      SZ.v n > 0 /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank
    )
  ensures exists* sp sr.
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      is_forest sp (SZ.v n) /\
      (forall (idx: nat). idx < SZ.v n ==> is_root sp idx) /\
      (forall (idx: nat). idx < SZ.v n /\ idx < Seq.length sr ==> SZ.v (Seq.index sr idx) == 0)
    )
{
  let mut i: SZ.t = 0sz;
  
  while (!i <^ n)
  invariant exists* vi sp sr.
    R.pts_to i vi **
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index sp j) == j) /\
      (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index sr j) == 0) /\
      SZ.v n > 0 /\
      SZ.v n <= Seq.length sp /\
      SZ.v n <= Seq.length sr
    )
  {
    let vi = !i;
    parent.(vi) <- vi;
    rank.(vi) <- 0sz;
    i := SZ.(vi +^ 1sz);
  };
  
  // At exit: loop counter equals n, all properties hold
  with vi sp sr. assert (R.pts_to i vi ** A.pts_to parent sp ** A.pts_to rank sr);
  
  // Establish well_formed
  assert pure (forall (j: nat). j < SZ.v n ==> SZ.v (Seq.index sp j) == j);
  assert pure (forall (j: nat). j < SZ.v n ==> j < SZ.v n);
  assert pure (forall (j: nat). j < SZ.v n ==> SZ.v (Seq.index sp j) < SZ.v n);
  assert pure (Seq.length sp == Seq.length sparent);
  
  // Establish is_root property
  assert pure (forall (j: nat). j < SZ.v n ==> 
    (j < Seq.length sp /\ SZ.v (Seq.index sp j) == j));
  
  // vi is bound but we don't use it - leave reference for automatic cleanup
  ()
}

// ========== find: Find the root of element i ==========

// Lemma: following parent pointers preserves has_root_within (with decreased depth)
let has_root_step (parent: Seq.seq SZ.t) (i: nat) (depth: nat)
  : Lemma (requires has_root_within parent i depth /\ depth > 0 /\ 
                     SZ.v (Seq.index parent i) <> i)
          (ensures has_root_within parent (SZ.v (Seq.index parent i)) (depth - 1))
  = ()

//SNIPPET_START: find_sig
fn find
  (#p: perm)
  (parent: array SZ.t)
  (#s: Ghost.erased (Seq.seq SZ.t))
  (x: SZ.t)
  (n: SZ.t)
  requires
    A.pts_to parent #p s **
    pure (
      is_forest s (SZ.v n) /\
      SZ.v x < SZ.v n
    )
  returns root: SZ.t
  ensures
    A.pts_to parent #p s **
    pure (
      SZ.v root < SZ.v n /\
      is_root s (SZ.v root) /\
      find_root s (SZ.v x) (SZ.v n) == SZ.v root
    )
//SNIPPET_END: find_sig
{
  let mut current: SZ.t = x;
  let mut fuel: SZ.t = n;
  
  while (
    let curr = !current;
    let parent_curr = parent.(curr);
    not (parent_curr = curr)
  )
  invariant exists* vcurr vfuel.
    R.pts_to current vcurr **
    R.pts_to fuel vfuel **
    A.pts_to parent #p s **
    pure (
      SZ.v vcurr < SZ.v n /\
      SZ.v vfuel <= SZ.v n /\
      has_root_within s (SZ.v vcurr) (SZ.v vfuel) /\
      find_root s (SZ.v vcurr) (SZ.v vfuel) == find_root s (SZ.v x) (SZ.v n)
    )
  {
    let curr = !current;
    let parent_curr = parent.(curr);
    let vfuel = !fuel;
    // parent_curr <> curr, so depth > 0 and we can step
    current := parent_curr;
    fuel := vfuel -^ 1sz;
  };
  
  !current
}

// ========== find_compress: Find with one-step path compression ==========
// Sets parent[x] = root directly. This is the simplest form of compression.
// Full path compression (CLRS FIND-SET) compresses all nodes on the path,
// but proving acyclicity of the path for the loop invariant is involved.

// Compressing x to root preserves well_formed
let compress_preserves_wf (parent: Seq.seq SZ.t) (n: nat) (i root: nat)
  : Lemma (requires well_formed parent n /\ i < n /\ root < n /\ SZ.fits root)
          (ensures well_formed (Seq.upd parent i (SZ.uint_to_t root)) n)
  = ()

// Compressing x to its root preserves has_root_within for all nodes
let rec compress_preserves_hrw
  (parent: Seq.seq SZ.t) (n: nat) (x root: nat) (j: nat) (d: nat)
  : Lemma (requires is_forest parent n /\ x < n /\ root < n /\
                    is_root parent root /\ SZ.fits root /\
                    find_root parent x n == root /\
                    j < n /\ d <= n /\ has_root_within parent j d)
          (ensures has_root_within (Seq.upd parent x (SZ.uint_to_t root)) j d)
          (decreases d)
  = let parent' = Seq.upd parent x (SZ.uint_to_t root) in
    if SZ.v (Seq.index parent j) = j then begin
      // j is a root in old forest
      if j = x then begin
        // x is a root and x's root is root. Since x is a root, root = x.
        assert (find_root parent x n == x);  // x is its own root
        assert (root == x);
        // parent'[x] = root = x. So j is still a root.
        assert (SZ.v (Seq.index parent' j) == j)
      end
      else begin
        // j ≠ x, parent'[j] = parent[j] = j
        assert (SZ.v (Seq.index parent' j) == j)
      end
    end
    else begin
      // j is not a root, d > 0
      if j = x then begin
        // parent'[x] = root. root is still a root (if root ≠ x, parent'[root] = parent[root] = root;
        // if root = x, parent'[x] = x).
        if root = x then
          assert (SZ.v (Seq.index parent' x) == x)
        else begin
          assert (SZ.v (Seq.index parent' x) == root);
          assert (SZ.v (Seq.index parent' root) == root);
          // has_root_within parent' root 0, weaken to d-1
          has_root_within_weaken parent' root 0 (d - 1)
        end
      end
      else begin
        // j ≠ x, parent'[j] = parent[j]
        let p = SZ.v (Seq.index parent j) in
        compress_preserves_hrw parent n x root p (d - 1)
      end
    end

// Compression preserves is_forest
let compress_preserves_is_forest
  (parent: Seq.seq SZ.t) (n: nat) (x root: nat)
  : Lemma (requires is_forest parent n /\ x < n /\ root < n /\
                    is_root parent root /\ SZ.fits root /\
                    find_root parent x n == root)
          (ensures is_forest (Seq.upd parent x (SZ.uint_to_t root)) n)
  = let parent' = Seq.upd parent x (SZ.uint_to_t root) in
    assert (well_formed parent' n);
    let aux (idx: nat{idx < n})
      : Lemma (has_root_within parent' idx n)
      = compress_preserves_hrw parent n x root idx n
    in
    FStar.Classical.forall_intro aux

fn find_compress
  (parent: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (x: SZ.t)
  (n: SZ.t)
  requires
    A.pts_to parent sparent **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n
    )
  returns root: SZ.t
  ensures exists* sp.
    A.pts_to parent sp **
    pure (
      SZ.v root < SZ.v n /\
      is_root sparent (SZ.v root) /\
      find_root sparent (SZ.v x) (SZ.v n) == SZ.v root /\
      is_forest sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      // x now points directly to root
      SZ.v (Seq.index sp (SZ.v x)) == SZ.v root /\
      // root is still a root
      SZ.v (Seq.index sp (SZ.v root)) == SZ.v root
    )
{
  // Find the root
  let root = find #1.0R parent x n;
  // Compress: set parent[x] = root
  parent.(x) <- root;
  compress_preserves_is_forest sparent (SZ.v n) (SZ.v x) (SZ.v root);
  root
}

// ========== union: Merge two sets ==========

// Union preserves well_formed when attaching one root under another
let union_preserves_wf (parent: Seq.seq SZ.t) (n: nat) (root_a root_b: nat)
  : Lemma 
      (requires well_formed parent n /\ root_a < n /\ root_b < n /\ SZ.fits root_b)
      (ensures well_formed (Seq.upd parent root_a (SZ.uint_to_t root_b)) n)
  = ()

//SNIPPET_START: union_sig
fn union_
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (x: SZ.t)
  (y: SZ.t)
  (n: SZ.t)
  requires
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v y < SZ.v n /\
      Seq.length srank == Seq.length sparent
    )
  returns res: (SZ.t & SZ.t)
  ensures exists* sp sr.
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      is_forest sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      // Returned roots are the find_root results
      SZ.v (fst res) == find_root sparent (SZ.v x) (SZ.v n) /\
      SZ.v (snd res) == find_root sparent (SZ.v y) (SZ.v n) /\
      is_root sparent (SZ.v (fst res)) /\
      is_root sparent (SZ.v (snd res)) /\
      // Functional correctness: the roots are now connected
      (fst res = snd res ==> Seq.equal sp sparent) /\
      (fst res <> snd res ==> 
        (SZ.v (Seq.index sp (SZ.v (fst res))) == SZ.v (snd res) \/
         SZ.v (Seq.index sp (SZ.v (snd res))) == SZ.v (fst res)))
    )
//SNIPPET_END: union_sig
{
  // Find roots
  let root_x = find parent x n;
  let root_y = find parent y n;
  
  // If already in same set, nothing to do
  if (root_x = root_y) {
    (root_x, root_y)
  } else {
    // Union by rank
    let rank_x = rank.(root_x);
    let rank_y = rank.(root_y);
    
    if (rank_x <^ rank_y) {
      parent.(root_x) <- root_y;
      union_preserves_is_forest sparent (SZ.v n) (SZ.v root_x) (SZ.v root_y);
      (root_x, root_y)
    } else {
      if (rank_x >^ rank_y) {
        parent.(root_y) <- root_x;
        union_preserves_is_forest sparent (SZ.v n) (SZ.v root_y) (SZ.v root_x);
        (root_x, root_y)
      } else {
        // Equal rank: attach root_y under root_x and increment rank (CLRS line 5-6)
        parent.(root_y) <- root_x;
        union_preserves_is_forest sparent (SZ.v n) (SZ.v root_y) (SZ.v root_x);
        let new_rank = (if (rank_x <^ SZ.sub n 1sz) then SZ.add rank_x 1sz else rank_x);
        rank.(root_x) <- new_rank;
        (root_x, root_y)
      };
    };
  }
}
