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
      is_root_at sparent (SZ.v root)
    )
  ensures exists* sp.
    A.pts_to parent sp **
    pure (
      well_formed sp (SZ.v n) /\
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
      well_formed sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      is_root_at sp (SZ.v root)
    )
  {
    let vc = !curr;
    // Read current parent before overwriting
    let par = parent.(vc);
    // Set parent[curr] = root
    parent.(vc) <- root;
    // Move to the old parent
    curr := par;
    // Increment bound counter
    let c = !count;
    count := SZ.add c 1sz
  };

  // After loop: either curr == root or count hit n
  // In either case, set parent[x] = root one more time to be safe
  parent.(x) <- root;
  with sp_final. assert (A.pts_to parent sp_final);
  
  // Prove the postcondition properties
  // 1. Length is preserved by writes
  assert (pure (Seq.length sp_final == Seq.length sparent));
  
  // 2. The write sets parent[x] = root
  assert (pure (SZ.v (Seq.index sp_final (SZ.v x)) == SZ.v root));
  
  // 3. x and root bounds follow from precondition
  assert (pure (SZ.v x < SZ.v n));
  assert (pure (SZ.v root < SZ.v n));
  
  // 4. Root is still a root - the loop invariant maintained is_root_at,
  //    and we only wrote to parent[x], not parent[root]
  assert (pure (SZ.v (Seq.index sp_final (SZ.v root)) == SZ.v root));
  
  // 5. Well-formedness: all indices point within bounds
  //    The loop invariant maintained well_formed, and writing root (which is < n) 
  //    at position x preserves this
  assert (pure (well_formed sp_final (SZ.v n)))
}
#pop-options

// CLRS §21.3 FIND-SET with full path compression (two-pass iterative)
// Pass 1: find root (walk to self-referencing node)
// Pass 2: compress all nodes on path to point directly to root
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
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
      well_formed sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      // x now points directly to root
      SZ.v (Seq.index sp (SZ.v x)) == SZ.v root /\
      // root still points to itself
      SZ.v (Seq.index sp (SZ.v root)) == SZ.v root
    )
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
