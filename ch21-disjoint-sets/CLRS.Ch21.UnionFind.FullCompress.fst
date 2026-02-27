(*
   Full Path Compression for Union-Find — CLRS §21.3

   FIND-SET(x)
     if x ≠ x.p
       x.p = FIND-SET(x.p)
     return x.p

   Iterative equivalent (two-pass):
     Pass 1: Walk to root
     Pass 2: Walk again, setting all parents to root

   This implements the CLRS full path compression, where ALL nodes
   on the path from x to root get their parent set to root.
   The existing find_compress only compresses one node (x.p = root).
*)

module CLRS.Ch21.UnionFind.FullCompress
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Specifications (same as UnionFind.fst) ==========

let is_root_at (parent: Seq.seq SZ.t) (i: nat) : prop =
  i < Seq.length parent /\ SZ.v (Seq.index parent i) == i

let well_formed (parent: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length parent >= n /\
  (forall (i: nat). i < n ==> SZ.v (Seq.index parent i) < n)

// Depth to root: element reaches a root in at most depth steps
let rec has_root_within (parent: Seq.seq SZ.t) (i: nat) (depth: nat) : Tot prop (decreases depth) =
  i < Seq.length parent /\
  (SZ.v (Seq.index parent i) == i \/  // i is a root
   (depth > 0 /\ has_root_within parent (SZ.v (Seq.index parent i)) (depth - 1)))

// A forest: every element reaches a root within n steps
let is_forest (parent: Seq.seq SZ.t) (n: nat) : prop =
  well_formed parent n /\
  (forall (idx: nat). idx < n ==> has_root_within parent idx n)

// Helper lemma: has_root_within with depth 0 means i is a root
let has_root_within_zero (parent: Seq.seq SZ.t) (i: nat)
  : Lemma (requires i < Seq.length parent /\ has_root_within parent i 0)
          (ensures SZ.v (Seq.index parent i) == i)
  = ()

// ========== Forest path analysis (for is_forest preservation) ==========

// Weaken: more depth is always fine
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

let follow_step (parent: Seq.seq SZ.t) (i: nat) (steps: nat)
  : Lemma (requires i < Seq.length parent /\ steps > 0)
          (ensures follow parent i steps == follow parent (SZ.v (Seq.index parent i)) (steps - 1))
  = ()

let rec follow_split (parent: Seq.seq SZ.t) (n: nat) (i: nat) (a b: nat)
  : Lemma (requires well_formed parent n /\ n > 0 /\ i < n /\ a + b <= n)
          (ensures follow parent i (a + b) == follow parent (follow parent i a) b)
          (decreases a)
  = if a = 0 then ()
    else follow_split parent n (SZ.v (Seq.index parent i)) (a - 1) b

let rec follow_bounded (parent: Seq.seq SZ.t) (n: nat) (i: nat) (steps: nat)
  : Lemma (requires well_formed parent n /\ n > 0 /\ i < n /\ steps <= n)
          (ensures follow parent i steps < n)
          (decreases steps)
  = if steps = 0 then ()
    else follow_bounded parent n (SZ.v (Seq.index parent i)) (steps - 1)

// Cycle at a non-root contradicts has_root_within
let rec nonroot_cycle_false (parent: Seq.seq SZ.t) (n: nat) (v: nat) (m: pos) (d: nat)
  : Lemma (requires well_formed parent n /\ n > 0 /\ v < n /\
                    SZ.v (Seq.index parent v) <> v /\
                    follow parent v m == v /\
                    has_root_within parent v d /\ m <= n)
          (ensures False)
          (decreases d)
  = let p = SZ.v (Seq.index parent v) in
    assert (follow parent p (m - 1) == v);
    follow_split parent n p (m - 1) 1;
    assert (follow parent p m == p);
    if SZ.v (Seq.index parent p) = p then begin
      let rec follow_root_stays (parent: Seq.seq SZ.t) (r: nat) (k: nat)
        : Lemma (requires r < Seq.length parent /\ SZ.v (Seq.index parent r) = r)
                (ensures follow parent r k == r)
                (decreases k)
        = if k = 0 then () else follow_root_stays parent r (k - 1)
      in
      follow_root_stays parent p (m - 1);
      assert (v == p)
    end
    else nonroot_cycle_false parent n p m (d - 1)

// Number of steps from i to its root (with given fuel)
let rec path_len (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) : Tot nat (decreases fuel) =
  if fuel = 0 then 0
  else if i >= Seq.length parent then 0
  else if SZ.v (Seq.index parent i) = i then 0
  else 1 + path_len parent (SZ.v (Seq.index parent i)) (fuel - 1)

let rec path_len_le_fuel (parent: Seq.seq SZ.t) (i: nat) (fuel: nat)
  : Lemma (ensures path_len parent i fuel <= fuel)
          (decreases fuel)
  = if fuel = 0 then ()
    else if i >= Seq.length parent then ()
    else if SZ.v (Seq.index parent i) = i then ()
    else path_len_le_fuel parent (SZ.v (Seq.index parent i)) (fuel - 1)

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

let rec path_node_eq_follow (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) (k: nat)
  : Lemma (requires i < Seq.length parent /\ has_root_within parent i fuel /\ k <= path_len parent i fuel)
          (ensures path_node parent i fuel k == follow parent i k)
          (decreases k)
  = if k = 0 then ()
    else path_node_eq_follow parent (SZ.v (Seq.index parent i)) (fuel - 1) (k - 1)

let rec path_node_not_root (parent: Seq.seq SZ.t) (i: nat) (fuel: nat) (k: nat)
  : Lemma (requires i < Seq.length parent /\ has_root_within parent i fuel /\
                    k < path_len parent i fuel)
          (ensures (let v = path_node parent i fuel k in
                    v < Seq.length parent /\ SZ.v (Seq.index parent v) <> v))
          (decreases k)
  = if k = 0 then ()
    else path_node_not_root parent (SZ.v (Seq.index parent i)) (fuel - 1) (k - 1)

let rec path_node_bounded (parent: Seq.seq SZ.t) (n: nat) (i: nat) (fuel: nat) (k: nat)
  : Lemma (requires well_formed parent n /\ n > 0 /\ i < n /\ has_root_within parent i fuel /\
                    k <= path_len parent i fuel)
          (ensures path_node parent i fuel k < n)
          (decreases k)
  = if k = 0 then ()
    else path_node_bounded parent n (SZ.v (Seq.index parent i)) (fuel - 1) (k - 1)

// KEY: path_len < n for forests (pigeonhole: path visits ≤ n distinct nodes)
#push-options "--z3rlimit 40"
let path_len_strict_bound (parent: Seq.seq SZ.t) (n: nat) (i: nat)
  : Lemma (requires is_forest parent n /\ n > 0 /\ i < n)
          (ensures path_len parent i n < n)
  = let pl = path_len parent i n in
    path_len_le_fuel parent i n;
    if pl >= n then begin
      let mk_node (k: nat{k < pl + 1}) : FStar.Fin.under n =
        path_node_bounded parent n i n k;
        path_node parent i n k
      in
      let s : Seq.seq (FStar.Fin.under n) = Seq.init (pl + 1) mk_node in
      assert (Seq.length s == pl + 1);
      assert (pl + 1 > n);
      let (k1, k2) = FStar.Fin.pigeonhole #n s in
      assert (k1 < k2);
      let v = path_node parent i n k1 in
      path_node_not_root parent i n k1;
      path_node_eq_follow parent i n k1;
      path_node_eq_follow parent i n k2;
      let m = k2 - k1 in
      follow_bounded parent n i k1;
      follow_split parent n i k1 m;
      nonroot_cycle_false parent n v m n
    end
#pop-options

// Tightening: in a forest, has_root_within holds at depth n-1
let has_root_within_tight (parent: Seq.seq SZ.t) (n: nat) (i: nat)
  : Lemma (requires is_forest parent n /\ n > 0 /\ i < n)
          (ensures has_root_within parent i (n - 1))
  = has_root_within_exact parent i n;
    path_len_strict_bound parent n i;
    has_root_within_weaken parent i (path_len parent i n) (n - 1)

// Setting parent[v] = root_sz increases depth by at most 1
let rec upd_depth_increase
  (parent: Seq.seq SZ.t) (n: nat) (v: nat) (root_sz: SZ.t) (j: nat) (d: nat)
  : Lemma (requires well_formed parent n /\ n > 0 /\
                    v < n /\ SZ.v root_sz < n /\
                    is_root_at parent (SZ.v root_sz) /\
                    j < n /\ d <= n /\
                    has_root_within parent j d)
          (ensures has_root_within (Seq.upd parent v root_sz) j (d + 1))
          (decreases d)
  = let root = SZ.v root_sz in
    let parent' = Seq.upd parent v root_sz in
    if SZ.v (Seq.index parent j) = j then begin
      if j = v then begin
        if root = v then
          has_root_within_weaken parent' v 0 (d + 1)
        else begin
          assert (SZ.v (Seq.index parent' root) == root);
          has_root_within_weaken parent' v 1 (d + 1)
        end
      end
      else has_root_within_weaken parent' j 0 (d + 1)
    end
    else begin
      if j = v then begin
        if root = v then
          has_root_within_weaken parent' v 0 (d + 1)
        else begin
          assert (SZ.v (Seq.index parent' root) == root);
          has_root_within_weaken parent' v 1 (d + 1)
        end
      end
      else begin
        assert (SZ.v (Seq.index parent' j) == SZ.v (Seq.index parent j));
        upd_depth_increase parent n v root_sz (SZ.v (Seq.index parent j)) (d - 1)
      end
    end

// Setting parent[v] = root_sz preserves is_forest (for ANY v, root or not)
let upd_preserves_is_forest
  (parent: Seq.seq SZ.t) (n: nat) (v: nat) (root_sz: SZ.t)
  : Lemma (requires is_forest parent n /\ n > 0 /\ v < n /\ SZ.v root_sz < n /\
                    is_root_at parent (SZ.v root_sz))
          (ensures is_forest (Seq.upd parent v root_sz) n)
  = let parent' = Seq.upd parent v root_sz in
    assert (well_formed parent' n);
    let aux (idx: nat{idx < n})
      : Lemma (has_root_within parent' idx n)
      = has_root_within_tight parent n idx;
        upd_depth_increase parent n v root_sz idx (n - 1)
    in
    FStar.Classical.forall_intro aux

// ========== Two-pass full path compression ==========

// Pass 2 helper: walk from x towards root, setting parent[x] = root for each node
// Terminates because each step moves closer to root (parent chain is finite)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
fn compress_path
  (parent: A.array SZ.t)
  (x: SZ.t) (root: SZ.t) (n: SZ.t)
  (#sparent: erased (Seq.seq SZ.t))
  requires
    A.pts_to parent sparent **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v root < SZ.v n /\
      SZ.v n > 0 /\
      is_root_at sparent (SZ.v root)
    )
  ensures exists* sp.
    A.pts_to parent sp **
    pure (
      is_forest sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      SZ.v x < SZ.v n /\
      SZ.v root < SZ.v n /\
      // x now points to root
      SZ.v (Seq.index sp (SZ.v x)) == SZ.v root /\
      // root still points to itself
      SZ.v (Seq.index sp (SZ.v root)) == SZ.v root
    )
{
  // Walk from x, compressing each node to point directly to root
  let mut curr = x;
  // Use a bounded loop (max n iterations — each node visited at most once)
  let mut count: SZ.t = 0sz;
  while (
    let vc = !curr;
    not (vc = root) && SZ.lt !count n
  )
  invariant exists* vc vcount sp.
    R.pts_to curr vc **
    R.pts_to count vcount **
    A.pts_to parent sp **
    pure (
      SZ.v vc < SZ.v n /\
      SZ.v vcount <= SZ.v n /\
      is_forest sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      is_root_at sp (SZ.v root)
    )
  {
    let vc = !curr;
    // Capture ghost state before modification
    with sp_pre. assert (A.pts_to parent sp_pre);
    // Read current parent before overwriting
    let par = parent.(vc);
    // Set parent[curr] = root
    parent.(vc) <- root;
    // Prove is_forest is preserved
    upd_preserves_is_forest sp_pre (SZ.v n) (SZ.v vc) root;
    // Move to the old parent
    curr := par;
    // Increment bound counter
    let c = !count;
    count := SZ.add c 1sz
  };

  // After loop: either curr == root or count hit n
  // Read concrete values to bind invariant existentials
  let _vc_f = !curr;
  let _cnt_f = !count;
  // Capture ghost state before final write
  with sp_pre2. assert (A.pts_to parent sp_pre2);
  // Check what pure facts are available
  assert (pure (is_forest sp_pre2 (SZ.v n)));
  assert (pure (is_root_at sp_pre2 (SZ.v root)));
  assert (pure (Seq.length sp_pre2 == Seq.length sparent));
  assert (pure (SZ.v n > 0));
  assert (pure (SZ.v x < SZ.v n));
  assert (pure (SZ.v root < SZ.v n));
  // Set parent[x] = root one more time to be safe
  parent.(x) <- root;
  // Prove is_forest is preserved
  upd_preserves_is_forest sp_pre2 (SZ.v n) (SZ.v x) root;
  // Bind final state for postcondition
  with sp_final. assert (A.pts_to parent sp_final)
}
#pop-options

// CLRS §21.3 FIND-SET with full path compression (two-pass iterative)
// Pass 1: find root (walk to self-referencing node)
// Pass 2: compress all nodes on path to point directly to root
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
//SNIPPET_START: find_set_sig
fn find_set
  (parent: A.array SZ.t)
  (x: SZ.t) (n: SZ.t)
  (#sparent: erased (Seq.seq SZ.t))
  requires
    A.pts_to parent sparent **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v n > 0
    )
  returns root: SZ.t
  ensures exists* sp.
    A.pts_to parent sp **
    pure (
      SZ.v root < SZ.v n /\
      SZ.v x < SZ.v n /\
      is_forest sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      // x now points directly to root
      SZ.v (Seq.index sp (SZ.v x)) == SZ.v root /\
      // root still points to itself
      SZ.v (Seq.index sp (SZ.v root)) == SZ.v root
    )
//SNIPPET_END: find_set_sig
{
  // Pass 1: Find root — walk parent chain until self-loop
  let mut curr = x;
  let mut bound: SZ.t = 0sz;
  while (
    let vc = !curr;
    let p = parent.(vc);
    not (p = vc) && SZ.lt !bound n
  )
  invariant exists* vc vb.
    R.pts_to curr vc **
    R.pts_to bound vb **
    A.pts_to parent sparent **
    pure (
      SZ.v vc < SZ.v n /\
      SZ.v vb <= SZ.v n /\
      is_forest sparent (SZ.v n) /\
      has_root_within sparent (SZ.v vc) (SZ.v n - SZ.v vb)
    )
  {
    let vc = !curr;
    let p = parent.(vc);
    curr := p;
    let b = !bound;
    bound := SZ.add b 1sz
  };

  let root = !curr;
  let b = !bound;
  // After loop exit: either (parent[root] == root) or (bound >= n)
  // From the invariant, we have has_root_within sparent root (n - bound)
  // If parent[root] == root, then root is_root_at
  // If bound >= n, then (n - bound) <= 0, but has_root_within with depth 0 is impossible
  // unless root is a root. Actually, let's check explicitly:
  let p_root = parent.(root);
  if (p_root = root) {
    // Direct case: root is a root
    ()
  } else {
    // parent[root] != root, so loop exited due to bound >= n
    // From invariant: has_root_within sparent root (n - bound)
    // If bound >= n, then n - bound <= 0
    // has_root_within with depth <= 0 requires root to be a root (parent[root] == root)
    // But we have parent[root] != root, contradiction
    // This means SMT should derive False
    assert (pure (SZ.v b >= SZ.v n));  // loop exited due to bound
    assert (pure (has_root_within sparent (SZ.v root) (SZ.v n - SZ.v b)));
    assert (pure (SZ.v n - SZ.v b <= 0));
    // has_root_within with depth 0 requires parent[root] == root
    has_root_within_zero sparent (SZ.v root);
    // Now SMT knows SZ.v (Seq.index sparent (SZ.v root)) == SZ.v root
    // but we have p_root != root, which contradicts
    assert (pure (SZ.v p_root == SZ.v (Seq.index sparent (SZ.v root))));
    assert (pure (SZ.v p_root == SZ.v root));
    assert (pure (p_root == root));
    // But the else branch assumes p_root != root, so False
    assert (pure False);
    unreachable ()
  };
  // Now we know p_root == root
  assert (pure (SZ.v (Seq.index sparent (SZ.v root)) == SZ.v root));
  assert (pure (is_root_at sparent (SZ.v root)));

  // Pass 2: Compress path — set all nodes from x to root to point to root
  compress_path parent x root n;

  root
}
#pop-options
