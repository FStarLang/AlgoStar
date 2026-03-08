(*
   Pure Specification: Union-Find (CLRS Chapter 21)

   Defines the union-find data structure and proves:
   1. pure_find is total (terminates) under rank_invariant — no fuel
   2. pure_union preserves all invariants
   3. Correctness: after union(x,y), pure_find x == pure_find y
   4. Stability: union(x,y) does not merge unrelated sets
*)

module CLRS.Ch21.UnionFind.Spec

open FStar.Seq
module Seq = FStar.Seq

(*** 1. Forest Model ***)

type uf_forest = {
  parent: Seq.seq nat;
  rank: Seq.seq nat;
  n: nat;
}

let is_root (f: uf_forest) (i: nat) : prop =
  i < f.n /\ Seq.length f.parent == f.n /\
  Seq.index f.parent i == i

let is_valid_uf (f: uf_forest) : prop =
  f.n > 0 /\
  Seq.length f.parent == f.n /\
  Seq.length f.rank == f.n /\
  (forall (i: nat). i < f.n ==> Seq.index f.parent i < f.n)

// CLRS Lemma 21.4: rank strictly increases along parent pointers
let rank_invariant (f: uf_forest) : prop =
  is_valid_uf f /\
  (forall (x: nat). x < f.n /\ Seq.index f.parent x <> x ==>
    Seq.index f.rank x < Seq.index f.rank (Seq.index f.parent x))

let uf_inv (f: uf_forest) : prop =
  is_valid_uf f /\ rank_invariant f

(*** 2. Termination Measure ***)

// Count nodes with rank strictly above threshold r, in [k, n)
let rec count_above (rank: Seq.seq nat) (r: nat) (k: nat) (n: nat{k <= n /\ n <= Seq.length rank})
  : Tot nat (decreases (n - k))
  = if k >= n then 0
    else (if Seq.index rank k > r then 1 else 0) + count_above rank r (k + 1) n

let rec count_above_mono (rank: Seq.seq nat) (r1 r2: nat) (k: nat) (n: nat{k <= n /\ n <= Seq.length rank})
  : Lemma (requires r1 <= r2)
          (ensures count_above rank r2 k n <= count_above rank r1 k n)
          (decreases (n - k))
  = if k >= n then () else count_above_mono rank r1 r2 (k + 1) n

// px has rank > r, so it is counted at threshold r but not at threshold rank[px]
let rec count_above_strict (rank: Seq.seq nat) (r: nat) (px: nat) (k: nat) (n: nat{k <= n /\ n <= Seq.length rank})
  : Lemma (requires px < n /\ Seq.index rank px > r /\ k <= px)
          (ensures count_above rank r k n > count_above rank (Seq.index rank px) k n)
          (decreases (n - k))
  = if k = px then count_above_mono rank r (Seq.index rank px) (k + 1) n
    else count_above_strict rank r px (k + 1) n

(*** 3. Total Pure Find — no fuel ***)

let rec pure_find (f: uf_forest{uf_inv f}) (x: nat{x < f.n})
  : Tot nat (decreases (count_above f.rank (Seq.index f.rank x) 0 f.n))
  = if Seq.index f.parent x = x then x
    else begin
      count_above_strict f.rank (Seq.index f.rank x) (Seq.index f.parent x) 0 f.n;
      pure_find f (Seq.index f.parent x)
    end

let rec pure_find_is_root (f: uf_forest{uf_inv f}) (x: nat{x < f.n})
  : Lemma (ensures is_root f (pure_find f x))
          (decreases (count_above f.rank (Seq.index f.rank x) 0 f.n))
  = if Seq.index f.parent x = x then ()
    else begin
      count_above_strict f.rank (Seq.index f.rank x) (Seq.index f.parent x) 0 f.n;
      pure_find_is_root f (Seq.index f.parent x)
    end

let pure_find_in_bounds (f: uf_forest{uf_inv f}) (x: nat{x < f.n})
  : Lemma (ensures pure_find f x < f.n)
  = pure_find_is_root f x

let pure_find_root (f: uf_forest{uf_inv f}) (root: nat{root < f.n})
  : Lemma (requires is_root f root)
          (ensures pure_find f root == root)
  = ()

let pure_find_idempotent (f: uf_forest{uf_inv f}) (x: nat{x < f.n})
  : Lemma (ensures (pure_find_in_bounds f x; pure_find f (pure_find f x) == pure_find f x))
  = pure_find_in_bounds f x;
    pure_find_is_root f x;
    pure_find_root f (pure_find f x)

// Stepping through parent preserves pure_find for non-roots
let pure_find_step (f: uf_forest{uf_inv f}) (x: nat{x < f.n})
  : Lemma (requires Seq.index f.parent x <> x)
          (ensures (pure_find f x == pure_find f (Seq.index f.parent x)))
  = count_above_strict f.rank (Seq.index f.rank x) (Seq.index f.parent x) 0 f.n

(*** 4. Make Forest ***)

let make_forest (n: nat{n > 0}) : (f: uf_forest{uf_inv f}) =
  { parent = Seq.init n (fun (i: nat{i < n}) -> (i <: nat));
    rank = Seq.init n (fun (_: nat{_ < n}) -> (0 <: nat));
    n = n }

// Every element is its own representative in a fresh forest
let make_forest_find (n: nat{n > 0}) (x: nat{x < n})
  : Lemma (pure_find (make_forest n) x == x)
  = ()

(*** 4b. Compression Lemmas ***)

// Rank monotonicity along path to root
let rec rank_mono (f: uf_forest{uf_inv f}) (x: nat{x < f.n})
  : Lemma (ensures (pure_find_in_bounds f x;
                    Seq.index f.rank x <= Seq.index f.rank (pure_find f x)))
          (decreases (count_above f.rank (Seq.index f.rank x) 0 f.n))
  = let p = Seq.index f.parent x in
    if p = x then pure_find_root f x
    else begin count_above_strict f.rank (Seq.index f.rank x) p 0 f.n;
               rank_mono f p; pure_find_in_bounds f p end

// Strict version for non-roots
let rank_strict_mono (f: uf_forest{uf_inv f}) (x: nat{x < f.n})
  : Lemma (requires Seq.index f.parent x <> x)
          (ensures (pure_find_in_bounds f x;
                    Seq.index f.rank x < Seq.index f.rank (pure_find f x)))
  = count_above_strict f.rank (Seq.index f.rank x) (Seq.index f.parent x) 0 f.n;
    rank_mono f (Seq.index f.parent x); pure_find_in_bounds f (Seq.index f.parent x)

// Compression of v to its root preserves uf_inv
#push-options "--z3rlimit 20"
let compress_preserves_uf_inv (f: uf_forest{uf_inv f}) (v: nat{v < f.n})
  : Lemma (ensures (pure_find_in_bounds f v;
                    uf_inv { f with parent = Seq.upd f.parent v (pure_find f v) }))
  = pure_find_in_bounds f v; pure_find_is_root f v;
    let f' = { f with parent = Seq.upd f.parent v (pure_find f v) } in
    let valid_aux (i: nat{i < f'.n}) : Lemma (Seq.index f'.parent i < f'.n) = () in
    FStar.Classical.forall_intro valid_aux;
    if Seq.index f.parent v = v then ()
    else begin
      rank_strict_mono f v;
      let ri_aux (z: nat{z < f'.n /\ Seq.index f'.parent z <> z})
        : Lemma (Seq.index f'.rank z < Seq.index f'.rank (Seq.index f'.parent z))
        = () in FStar.Classical.forall_intro ri_aux
    end
#pop-options

// pure_find of a non-root differs from the node itself
let pure_find_nonroot (f: uf_forest{uf_inv f}) (v: nat{v < f.n})
  : Lemma (requires Seq.index f.parent v <> v)
          (ensures pure_find f v <> v)
  = pure_find_is_root f v

// Compression of v to its root preserves pure_find for ALL nodes
#push-options "--fuel 1 --ifuel 0 --z3rlimit 80"
let rec compress_preserves_find
  (f: uf_forest{uf_inv f}) (v: nat{v < f.n}) (z: nat{z < f.n})
  : Lemma (requires (pure_find_in_bounds f v;
                     pure_find_is_root f v;
                     True))
          (ensures (let root = pure_find f v in
                    let f' = { f with parent = Seq.upd f.parent v root } in
                    compress_preserves_uf_inv f v;
                    pure_find f' z == pure_find f z))
          (decreases (count_above f.rank (Seq.index f.rank z) 0 f.n))
  = pure_find_in_bounds f v; pure_find_is_root f v;
    compress_preserves_uf_inv f v;
    let root = pure_find f v in
    let f' = { f with parent = Seq.upd f.parent v root } in
    let pz = Seq.index f.parent z in
    if pz = z then begin
      if z = v then (pure_find_root f v; assert (root == v))
      else ()
    end
    else begin
      if z = v then begin
        pure_find_nonroot f v;
        rank_strict_mono f v;
        // f'[v] = root, root != v, f'[root] = f[root] = root
        // pure_find f' root = root (1 unfolding, root is a root in f')
        assert (Seq.index f'.parent root == root);
        pure_find_root f' root;
        // pure_find f' v steps to pure_find f' root (another unfolding)
        count_above_strict f'.rank (Seq.index f'.rank v) root 0 f'.n;
        assert (pure_find f' v == root)
      end
      else begin
        count_above_strict f.rank (Seq.index f.rank z) pz 0 f.n;
        compress_preserves_find f v pz;
        count_above_strict f'.rank (Seq.index f'.rank z) pz 0 f'.n
      end
    end
#pop-options

// Forall wrapper: compression preserves pure_find for ALL nodes at once
let compress_preserves_find_all (f: uf_forest{uf_inv f}) (v: nat{v < f.n})
  : Lemma (ensures (pure_find_in_bounds f v;
                    let root = pure_find f v in
                    let f' = { f with parent = Seq.upd f.parent v root } in
                    uf_inv f' /\
                    (forall (z: nat). z < f.n ==> pure_find f' z == pure_find f z)))
  = compress_preserves_uf_inv f v;
    pure_find_in_bounds f v;
    let root = pure_find f v in
    let f' = { f with parent = Seq.upd f.parent v root } in
    let aux (z: nat{z < f.n})
      : Lemma (pure_find f' z == pure_find f z)
      = compress_preserves_find f v z
    in
    FStar.Classical.forall_intro aux

(*** 5. Pure Union ***)

let pure_union (f: uf_forest{uf_inv f}) (x y: nat{x < f.n /\ y < f.n}) : uf_forest =
  pure_find_in_bounds f x; pure_find_in_bounds f y;
  let root_x = pure_find f x in
  let root_y = pure_find f y in
  if root_x = root_y then f
  else
    let rx = Seq.index f.rank root_x in
    let ry = Seq.index f.rank root_y in
    if rx < ry then
      { f with parent = Seq.upd f.parent root_x root_y }
    else if rx > ry then
      { f with parent = Seq.upd f.parent root_y root_x }
    else
      { f with parent = Seq.upd f.parent root_y root_x;
               rank = Seq.upd f.rank root_x (rx + 1) }

#push-options "--z3rlimit 20"
let pure_union_preserves_inv (f: uf_forest{uf_inv f}) (x y: nat{x < f.n /\ y < f.n})
  : Lemma (ensures uf_inv (pure_union f x y))
  = pure_find_in_bounds f x; pure_find_in_bounds f y;
    pure_find_is_root f x; pure_find_is_root f y;
    let root_x = pure_find f x in
    let root_y = pure_find f y in
    if root_x = root_y then ()
    else
      let f' = pure_union f x y in
      let valid_aux (i: nat{i < f'.n}) : Lemma (Seq.index f'.parent i < f'.n) = () in
      FStar.Classical.forall_intro valid_aux;
      let ri_aux (z: nat{z < f'.n /\ Seq.index f'.parent z <> z})
        : Lemma (Seq.index f'.rank z < Seq.index f'.rank (Seq.index f'.parent z)) = ()
      in FStar.Classical.forall_intro ri_aux
#pop-options

(*** 6. Correctness: pure_find changes after link ***)

// How pure_find changes when we link root_a -> root_b:
// - Nodes in root_a's tree now find root_b
// - Nodes in root_b's tree still find root_b
// - Nodes in other trees are unchanged
#restart-solver
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let rec pure_find_after_link
  (f f': uf_forest{uf_inv f /\ uf_inv f'})
  (root_a root_b: nat)
  (z: nat{z < f.n})
  : Lemma
      (requires
        root_a < f.n /\ root_b < f.n /\ root_a <> root_b /\
        is_root f root_a /\ is_root f root_b /\
        f'.n == f.n /\ Seq.length f'.rank == f.n /\
        f'.parent == Seq.upd f.parent root_a root_b /\
        (forall (i: nat). i < f.n ==> Seq.index f'.rank i >= Seq.index f.rank i))
      (ensures
        (if pure_find f z = root_a then pure_find f' z = root_b
         else if pure_find f z = root_b then pure_find f' z = root_b
         else pure_find f' z = pure_find f z))
      (decreases (count_above f.rank (Seq.index f.rank z) 0 f.n))
  = let pz = Seq.index f.parent z in
    if pz = z then begin
      if z = root_a then begin
        assert (Seq.index f'.parent root_a == root_b);
        assert (Seq.index f'.parent root_b == root_b);
        assert (pure_find f' root_b == root_b);
        count_above_strict f'.rank (Seq.index f'.rank root_a) root_b 0 f'.n;
        assert (pure_find f' root_a == pure_find f' root_b)
      end else ()
    end
    else begin
      assert (z <> root_a);
      assert (Seq.index f'.parent z == pz);
      count_above_strict f.rank (Seq.index f.rank z) pz 0 f.n;
      pure_find_after_link f f' root_a root_b pz;
      count_above_strict f'.rank (Seq.index f'.rank z) pz 0 f'.n
    end
#pop-options

(*** 7. Main Theorems ***)

// Correctness: union merges the two sets
#restart-solver
#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let pure_union_same_set (f: uf_forest{uf_inv f}) (x y: nat{x < f.n /\ y < f.n})
  : Lemma (ensures (pure_union_preserves_inv f x y;
                    let f' = pure_union f x y in
                    pure_find f' x == pure_find f' y))
  = pure_union_preserves_inv f x y;
    pure_find_in_bounds f x; pure_find_in_bounds f y;
    pure_find_is_root f x; pure_find_is_root f y;
    let root_x = pure_find f x in
    let root_y = pure_find f y in
    if root_x = root_y then ()
    else begin
      let f' = pure_union f x y in
      let rx = Seq.index f.rank root_x in
      let ry = Seq.index f.rank root_y in
      if rx < ry then begin
        pure_find_after_link f f' root_x root_y x;
        pure_find_after_link f f' root_x root_y y
      end
      else if rx > ry then begin
        pure_find_after_link f f' root_y root_x x;
        pure_find_after_link f f' root_y root_x y
      end
      else begin
        pure_find_after_link f f' root_y root_x x;
        pure_find_after_link f f' root_y root_x y
      end
    end
#pop-options

// Stability: union does not merge unrelated sets
#restart-solver
#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let pure_union_other_set (f: uf_forest{uf_inv f}) (x y z: nat{x < f.n /\ y < f.n /\ z < f.n})
  : Lemma (requires pure_find f z <> pure_find f x /\ pure_find f z <> pure_find f y)
          (ensures (pure_union_preserves_inv f x y;
                    pure_find (pure_union f x y) z == pure_find f z))
  = pure_union_preserves_inv f x y;
    pure_find_in_bounds f x; pure_find_in_bounds f y;
    pure_find_is_root f x; pure_find_is_root f y;
    let root_x = pure_find f x in
    let root_y = pure_find f y in
    if root_x = root_y then ()
    else begin
      let f' = pure_union f x y in
      let rx = Seq.index f.rank root_x in
      let ry = Seq.index f.rank root_y in
      if rx < ry then
        pure_find_after_link f f' root_x root_y z
      else if rx > ry then
        pure_find_after_link f f' root_y root_x z
      else
        pure_find_after_link f f' root_y root_x z
    end
#pop-options

// Stability (universal): union does not merge any unrelated set
#restart-solver
#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let pure_union_stability (f: uf_forest{uf_inv f}) (x y: nat{x < f.n /\ y < f.n})
  : Lemma (ensures (pure_union_preserves_inv f x y;
                    let f' = pure_union f x y in
                    forall (z: nat). z < f.n ==>
                      pure_find f z <> pure_find f x ==>
                      pure_find f z <> pure_find f y ==>
                      pure_find f' z == pure_find f z))
  = pure_union_preserves_inv f x y;
    let aux (z: nat{z < f.n})
      : Lemma (requires pure_find f z <> pure_find f x /\
                        pure_find f z <> pure_find f y)
              (ensures pure_find (pure_union f x y) z == pure_find f z)
      = pure_union_other_set f x y z
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options
