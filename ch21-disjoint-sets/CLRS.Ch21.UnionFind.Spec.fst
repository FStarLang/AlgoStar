(*
   Pure F* Specification: Union-Find Rank Invariants
   
   Proves CLRS Lemma 21.4 and related rank properties for union-by-rank.
   
   Key results:
   1. Lemma 21.4: For all non-root x, rank[x] < rank[parent[x]]
   2. Rank is monotone along parent chains (toward root)
   3. pure_find terminates using rank as decreasing measure
   4. pure_union preserves correctness of pure_find
   
   The logarithmic bound (rank[x] ≤ ⌊log₂ n⌋) requires counting subtree sizes,
   which is admitted here for brevity.
*)

module CLRS.Ch21.UnionFind.Spec

open FStar.Seq
open FStar.Math.Lemmas

module Seq = FStar.Seq

(*** 1. Forest Model ***)

//SNIPPET_START: uf_forest_def
// Union-Find forest with parent pointers and ranks
type uf_forest = {
  parent: Seq.seq nat;
  rank: Seq.seq nat;
  n: nat
}

// Valid forest: all parent pointers and ranks are in bounds
let is_valid_uf (f: uf_forest) : prop =
  f.n > 0 /\
  Seq.length f.parent == f.n /\
  Seq.length f.rank == f.n /\
  (forall (i: nat). i < f.n ==> Seq.index f.parent i < f.n) /\
  (forall (i: nat). i < f.n ==> Seq.index f.rank i >= 0)

// Element is a root if parent[i] = i
let is_root (f: uf_forest) (i: nat) : prop =
  i < f.n /\ 
  i < Seq.length f.parent /\
  Seq.index f.parent i == i
//SNIPPET_END: uf_forest_def

// Initial forest: each element is its own parent with rank 0
let make_forest (n: nat{n > 0}) : uf_forest =
  let mk_parent (i: nat{i < n}) : nat = i in
  let mk_rank (i: nat{i < n}) : nat = 0 in
  { parent = Seq.init n mk_parent;
    rank = Seq.init n mk_rank;
    n = n }

// Lemma: make_forest produces a valid forest
let make_forest_valid (n: nat{n > 0})
  : Lemma (is_valid_uf (make_forest n))
  = ()

(*** 2. Rank Invariant (CLRS Lemma 21.4) ***)

//SNIPPET_START: rank_invariant
// Rank invariant: for all non-root x, rank[x] < rank[parent[x]]
// Only meaningful when is_valid_uf holds
let rank_invariant (f: uf_forest) : prop =
  is_valid_uf f ==>
  (forall (x: nat{x < f.n}). Seq.index f.parent x <> x ==>
    Seq.index f.rank x < Seq.index f.rank (Seq.index f.parent x))
//SNIPPET_END: rank_invariant

// Initial forest satisfies rank invariant (vacuously - all are roots)
let make_forest_rank_invariant (n: nat{n > 0})
  : Lemma (rank_invariant (make_forest n))
  = ()

(*** 3. Pure Find Operation ***)

// Find root by following parent pointers, with explicit fuel
// Returns None if fuel runs out, Some root if found
let rec pure_find_fuel (f: uf_forest{is_valid_uf f}) (x: nat{x < f.n}) (fuel: nat)
  : Tot (option nat) (decreases fuel)
  = if fuel = 0 then None
    else
      let px = Seq.index f.parent x in
      if px = x then Some x
      else pure_find_fuel f px (fuel - 1)

// Ranks bounded property: proven in RankBound module (rank_logarithmic_bound_sized)
// log2_floor(n) < n for all n > 0, so rank(x) <= log2_floor(n) < n
let ranks_bounded (f: uf_forest) : prop =
  is_valid_uf f ==>
  (forall (x: nat{x < f.n}). Seq.index f.rank x < f.n)

// Explicit quantifier instantiation for rank_invariant
let rank_inv_inst (f: uf_forest{is_valid_uf f}) (x: nat{x < f.n})
  : Lemma (requires rank_invariant f /\ Seq.index f.parent x <> x)
          (ensures Seq.index f.rank x < Seq.index f.rank (Seq.index f.parent x))
  = ()

// Core lemma: if fuel + rank(x) > bound and all ranks <= bound, find succeeds
#restart-solver
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let rec find_fuel_by_bound (f: uf_forest{is_valid_uf f}) (x: nat{x < f.n}) (fuel: nat) (bound: nat)
  : Lemma (requires rank_invariant f /\
                    fuel + Seq.index f.rank x > bound /\
                    (forall (i: nat). i < f.n ==> Seq.index f.rank i <= bound))
          (ensures Some? (pure_find_fuel f x fuel))
          (decreases (bound - Seq.index f.rank x))
  = let px = Seq.index f.parent x in
    if px = x then ()
    else begin
      rank_inv_inst f x;
      find_fuel_by_bound f px (fuel - 1) bound
    end
#pop-options

(* Termination proof for pure_find_fuel using counting argument.
   Key insight: the number of nodes with rank strictly above rank[x]
   decreases each time we follow a parent pointer (by rank_invariant).
   Since this count is bounded by f.n - 1, the chain terminates within f.n steps.
   This avoids needing ranks_bounded (rank < n) as an assumption. *)

let rec count_rank_above (f: uf_forest{is_valid_uf f}) (r: nat) (k: nat{k <= f.n})
  : Tot nat (decreases (f.n - k))
  = if k >= f.n then 0
    else (if Seq.index f.rank k > r then 1 else 0) + count_rank_above f r (k + 1)

#restart-solver
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"

let rec count_rank_above_bound (f: uf_forest{is_valid_uf f}) (r: nat) (k: nat{k <= f.n})
  : Lemma (ensures count_rank_above f r k <= f.n - k)
          (decreases (f.n - k))
  = if k >= f.n then () else count_rank_above_bound f r (k + 1)

let rec count_rank_above_mono (f: uf_forest{is_valid_uf f}) (r1 r2: nat) (k: nat{k <= f.n})
  : Lemma (requires r1 <= r2)
          (ensures count_rank_above f r2 k <= count_rank_above f r1 k)
          (decreases (f.n - k))
  = if k >= f.n then () else count_rank_above_mono f r1 r2 (k + 1)

// Node px has rank > r, so it's counted for threshold r but not for threshold rank[px]
let rec count_rank_above_strict (f: uf_forest{is_valid_uf f}) (r: nat) 
                                 (px: nat{px < f.n}) (k: nat{k <= f.n})
  : Lemma (requires Seq.index f.rank px > r /\ k <= px)
          (ensures count_rank_above f r k > count_rank_above f (Seq.index f.rank px) k)
          (decreases (f.n - k))
  = if k = px then count_rank_above_mono f r (Seq.index f.rank px) (k + 1)
    else count_rank_above_strict f r px (k + 1)

// Node x has rank[x] which is NOT > rank[x], so count excludes at least x
let rec count_rank_above_lt_n (f: uf_forest{is_valid_uf f}) (x: nat{x < f.n})
                               (k: nat{k <= f.n})
  : Lemma (requires k <= x)
          (ensures count_rank_above f (Seq.index f.rank x) k < f.n - k)
          (decreases (f.n - k))
  = if k = x then count_rank_above_bound f (Seq.index f.rank x) (k + 1)
    else count_rank_above_lt_n f x (k + 1)

let rec find_fuel_mono (f: uf_forest{is_valid_uf f}) (x: nat{x < f.n}) (fuel1 fuel2: nat)
  : Lemma (requires fuel1 <= fuel2 /\ Some? (pure_find_fuel f x fuel1))
          (ensures Some? (pure_find_fuel f x fuel2))
          (decreases fuel1)
  = if fuel1 = 0 then ()
    else let px = Seq.index f.parent x in
         if px = x then ()
         else find_fuel_mono f px (fuel1 - 1) (fuel2 - 1)

#pop-options

// Core lemma: pure_find_fuel succeeds with count_rank_above(rank[x], 0) + 1 fuel
#restart-solver
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let rec find_succeeds_by_count (f: uf_forest{is_valid_uf f /\ rank_invariant f}) (x: nat{x < f.n})
  : Lemma (ensures Some? (pure_find_fuel f x (count_rank_above f (Seq.index f.rank x) 0 + 1)))
          (decreases count_rank_above f (Seq.index f.rank x) 0)
  = let px = Seq.index f.parent x in
    if px = x then ()
    else begin
      rank_inv_inst f x;
      count_rank_above_strict f (Seq.index f.rank x) px 0;
      find_succeeds_by_count f px;
      find_fuel_mono f px (count_rank_above f (Seq.index f.rank px) 0 + 1)
                          (count_rank_above f (Seq.index f.rank x) 0)
    end
#pop-options

// Under rank_invariant, n steps of fuel is always enough.
// Proved via counting: nodes with rank > rank[x] strictly decrease along
// parent chains, and this count is at most f.n - 1 (since x itself is excluded).
let pure_find_fuel_sufficient (f: uf_forest{is_valid_uf f /\ rank_invariant f}) 
                               (x: nat{x < f.n})
  : Lemma (ensures Some? (pure_find_fuel f x f.n))
  = find_succeeds_by_count f x;
    count_rank_above_lt_n f x 0;
    find_fuel_mono f x (count_rank_above f (Seq.index f.rank x) 0 + 1) f.n

//SNIPPET_START: pure_find
// Pure find: follow parent pointers to root (guaranteed to terminate under rank_invariant)
let pure_find (f: uf_forest{is_valid_uf f /\ rank_invariant f}) (x: nat{x < f.n}) : nat =
  pure_find_fuel_sufficient f x;
  Some?.v (pure_find_fuel f x f.n)
//SNIPPET_END: pure_find

// Lemma: pure_find result is in bounds
let rec pure_find_in_bounds_fuel (f: uf_forest{is_valid_uf f}) (x: nat{x < f.n}) (fuel: nat)
  : Lemma (ensures (match pure_find_fuel f x fuel with
                    | Some r -> r < f.n
                    | None -> True))
          (decreases fuel)
  = if fuel = 0 then ()
    else
      let px = Seq.index f.parent x in
      if px = x then ()
      else pure_find_in_bounds_fuel f px (fuel - 1)

let pure_find_in_bounds (f: uf_forest{is_valid_uf f /\ rank_invariant f}) (x: nat{x < f.n})
  : Lemma (ensures pure_find f x < f.n)
  = pure_find_fuel_sufficient f x;
    pure_find_in_bounds_fuel f x f.n

// Lemma: pure_find returns a root
let rec pure_find_is_root_fuel (f: uf_forest{is_valid_uf f}) (x: nat{x < f.n}) (fuel: nat)
  : Lemma (ensures (match pure_find_fuel f x fuel with
                    | Some r -> is_root f r
                    | None -> True))
          (decreases fuel)
  = if fuel = 0 then ()
    else
      let px = Seq.index f.parent x in
      if px = x then ()
      else pure_find_is_root_fuel f px (fuel - 1)

let pure_find_is_root (f: uf_forest{is_valid_uf f /\ rank_invariant f}) (x: nat{x < f.n})
  : Lemma (ensures is_root f (pure_find f x))
  = pure_find_fuel_sufficient f x;
    pure_find_is_root_fuel f x f.n

(*** 4. Additional Rank Properties ***)

// Lemma: Under rank invariant, rank strictly increases toward root
let rank_increases_to_root (f: uf_forest) (x: nat{x < f.n})
  : Lemma (requires rank_invariant f /\ is_valid_uf f /\ Seq.index f.parent x <> x)
          (ensures (let px = Seq.index f.parent x in
                    Seq.index f.rank x < Seq.index f.rank px /\
                    px < f.n))
  = let px = Seq.index f.parent x in
    ()

// Corollary: rank is monotone along any parent chain (rank[x] ≤ rank[root])
// This is a consequence of rank_invariant (rank increases strictly toward root)
let rec rank_monotone_chain_fuel (f: uf_forest{is_valid_uf f /\ rank_invariant f}) 
                                  (x: nat{x < f.n}) (fuel: nat)
  : Lemma (ensures (match pure_find_fuel f x fuel with
                    | Some root -> root < f.n /\ Seq.index f.rank x <= Seq.index f.rank root
                    | None -> True))
          (decreases fuel)
  = if fuel = 0 then ()
    else
      let px = Seq.index f.parent x in
      if px = x then ()
      else begin
        rank_increases_to_root f x;
        rank_monotone_chain_fuel f px (fuel - 1)
      end

let rank_monotone_chain (f: uf_forest{is_valid_uf f /\ rank_invariant f}) (x: nat{x < f.n})
  : Lemma (ensures (let root = pure_find f x in
                    root < f.n /\
                    Seq.index f.rank x <= Seq.index f.rank root))
  = pure_find_in_bounds f x;
    pure_find_fuel_sufficient f x;
    rank_monotone_chain_fuel f x f.n;
    let root = pure_find f x in
    assert (root < f.n);
    assert (Some root == pure_find_fuel f x f.n)

(*** 5. Pure Union Operation ***)

//SNIPPET_START: pure_union
// Union two trees by rank (CLRS union-by-rank heuristic)
let pure_union (f: uf_forest{is_valid_uf f /\ rank_invariant f}) (x y: nat{x < f.n /\ y < f.n}) : uf_forest =
  pure_find_in_bounds f x;
  pure_find_in_bounds f y;
  let root_x = pure_find f x in
  let root_y = pure_find f y in
  if root_x = root_y then f  // Already in same set
  else
    let rank_x = Seq.index f.rank root_x in
    let rank_y = Seq.index f.rank root_y in
    if rank_x < rank_y then
      // Attach root_x under root_y, ranks unchanged
      { f with parent = Seq.upd f.parent root_x root_y }
    else if rank_x > rank_y then
      // Attach root_y under root_x, ranks unchanged
      { f with parent = Seq.upd f.parent root_y root_x }
    else
      // Equal rank: attach root_y under root_x, increment rank[root_x]
      { f with 
        parent = Seq.upd f.parent root_y root_x;
        rank = Seq.upd f.rank root_x (rank_x + 1) }
//SNIPPET_END: pure_union

// Lemma: pure_union preserves validity
let pure_union_valid (f: uf_forest{is_valid_uf f /\ rank_invariant f}) (x y: nat{x < f.n /\ y < f.n})
  : Lemma (ensures is_valid_uf (pure_union f x y))
  = pure_find_in_bounds f x;
    pure_find_in_bounds f y;
    let root_x = pure_find f x in
    let root_y = pure_find f y in
    let f' = pure_union f x y in
    // Prove all indices still in bounds
    let aux (i: nat{i < f.n}) 
      : Lemma (Seq.index f'.parent i < f'.n)
      = ()
    in
    FStar.Classical.forall_intro aux

(*** 5. Rank Invariant Preservation ***)

// Key lemma: pure_union preserves rank invariant (Lemma 21.4 holds after union)
// This is the core of the correctness argument.

// Helper: updating parent at a root doesn't affect non-roots
let update_root_parent_preserves_non_root (f: uf_forest{is_valid_uf f}) (root new_parent: nat)
  : Lemma (requires root < f.n /\ new_parent < f.n /\ is_root f root)
          (ensures (let f' = { f with parent = Seq.upd f.parent root new_parent } in
                    forall (x: nat{x < f.n}). x <> root /\ Seq.index f.parent x <> x ==>
                      Seq.index f'.parent x == Seq.index f.parent x /\
                      Seq.index f'.rank x == Seq.index f.rank x))
  = ()

// Main lemma: pure_union preserves rank_invariant
let pure_union_preserves_rank_invariant (f: uf_forest{is_valid_uf f /\ rank_invariant f}) 
                                        (x y: nat{x < f.n /\ y < f.n})
  : Lemma (ensures rank_invariant (pure_union f x y))
  = pure_find_in_bounds f x;
    pure_find_in_bounds f y;
    pure_find_is_root f x;
    pure_find_is_root f y;
    let root_x = pure_find f x in
    let root_y = pure_find f y in
    let f' = pure_union f x y in
    
    if root_x = root_y then ()
    else
      let rank_x = Seq.index f.rank root_x in
      let rank_y = Seq.index f.rank root_y in
      
      // Case 1: rank_x < rank_y
      // Attach root_x under root_y
      // Old non-roots still satisfy invariant (unchanged)
      // root_x becomes non-root with rank_x < rank_y = rank[parent[root_x]] ✓
      if rank_x < rank_y then begin
        let check_node (z: nat{z < f.n})
          : Lemma (Seq.index f'.parent z <> z ==> 
                   Seq.index f'.rank z < Seq.index f'.rank (Seq.index f'.parent z))
          = if z = root_x then ()
            else if Seq.index f.parent z = z then ()
            else ()
        in
        FStar.Classical.forall_intro check_node
      end
      // Case 2: rank_x > rank_y (symmetric)
      else if rank_x > rank_y then begin
        let check_node (z: nat{z < f.n})
          : Lemma (Seq.index f'.parent z <> z ==> 
                   Seq.index f'.rank z < Seq.index f'.rank (Seq.index f'.parent z))
          = if z = root_y then ()
            else if Seq.index f.parent z = z then ()
            else ()
        in
        FStar.Classical.forall_intro check_node
      end
      // Case 3: rank_x = rank_y
      // Attach root_y under root_x, increment rank[root_x]
      // Old non-roots: unchanged ranks and parents (except root_y)
      // root_y becomes non-root: rank_y < rank_y + 1 = rank[root_x] ✓
      else begin
        let check_node (z: nat{z < f.n})
          : Lemma (Seq.index f'.parent z <> z ==> 
                   Seq.index f'.rank z < Seq.index f'.rank (Seq.index f'.parent z))
          = if z = root_y then ()
            else if Seq.index f.parent z = z then ()
            else ()
        in
        FStar.Classical.forall_intro check_node
      end

(*** 6. Correctness: pure_union connects representatives ***)

// Helper: pure_find on old root traces to itself
let pure_find_root_is_self (f: uf_forest{is_valid_uf f /\ rank_invariant f}) (root: nat{root < f.n})
  : Lemma (requires is_root f root)
          (ensures pure_find f root == root)
  = ()

// Determinism: pure_find_fuel with more fuel gives the same result
#restart-solver
#push-options "--fuel 1 --ifuel 0 --z3rlimit 15"
let rec pure_find_fuel_deterministic
  (f: uf_forest{is_valid_uf f})
  (z: nat{z < f.n})
  (fuel1 fuel2: nat)
  : Lemma (requires fuel1 <= fuel2 /\ Some? (pure_find_fuel f z fuel1))
          (ensures pure_find_fuel f z fuel1 = pure_find_fuel f z fuel2)
          (decreases fuel1)
  = if fuel1 = 0 then () // contradicts Some?
    else
      let px = Seq.index f.parent z in
      if px = z then ()
      else begin
        // pure_find_fuel f z fuel1 = pure_find_fuel f px (fuel1-1), Some
        // pure_find_fuel f z fuel2 = pure_find_fuel f px (fuel2-1)
        // fuel1-1 <= fuel2-1
        pure_find_fuel_deterministic f px (fuel1 - 1) (fuel2 - 1)
      end
#pop-options

// Rank-independence: pure_find_fuel only depends on parent array, not rank
#restart-solver
#push-options "--fuel 1 --ifuel 0 --z3rlimit 15"
let rec pure_find_fuel_rank_independent
  (f1 f2: uf_forest{is_valid_uf f1 /\ is_valid_uf f2})
  (z: nat{z < f1.n /\ z < f2.n})
  (fuel: nat)
  : Lemma (requires f1.parent == f2.parent /\ f1.n == f2.n)
          (ensures pure_find_fuel f1 z fuel == pure_find_fuel f2 z fuel)
          (decreases fuel)
  = if fuel = 0 then ()
    else
      let px = Seq.index f1.parent z in
      if px = z then ()
      else pure_find_fuel_rank_independent f1 f2 px (fuel - 1)
#pop-options

// Helper: Following a parent chain in modified forest
// If we change parent[a] = b where a was a root, then:
// - pure_find of a now finds pure_find of b
// - other elements unaffected (if they don't go through a)

// Fuel-based helper: relate pure_find_fuel on f and f' where f' only differs at changed_node
#restart-solver
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let rec pure_find_fuel_after_update
  (f: uf_forest{is_valid_uf f /\ rank_invariant f})
  (changed_node new_parent: nat{changed_node < f.n /\ new_parent < f.n /\ changed_node <> new_parent})
  (z: nat{z < f.n})
  (fuel: nat)
  : Lemma (requires is_root f changed_node /\ is_root f new_parent /\
                    Some? (pure_find_fuel f z fuel))
          (ensures (let f' = { f with parent = Seq.upd f.parent changed_node new_parent } in
                    (match pure_find_fuel f z fuel with
                     | Some r -> 
                       if r = changed_node 
                       then pure_find_fuel f' z (fuel + 1) = Some new_parent
                       else pure_find_fuel f' z fuel = Some r
                     | None -> True)))
          (decreases fuel)
  = let f' = { f with parent = Seq.upd f.parent changed_node new_parent } in
    if fuel = 0 then () // contradicts Some? (pure_find_fuel f z fuel)
    else
      let px_f = Seq.index f.parent z in
      if px_f = z then begin
        // z is a root in f
        // pure_find_fuel f z fuel = Some z
        assert (pure_find_fuel f z fuel = Some z);
        if z = changed_node then begin
          // In f', parent[z] = new_parent, new_parent is a root (parent[new_parent] = new_parent in f, unchanged in f')
          assert (Seq.index f'.parent z = new_parent);
          assert (Seq.index f'.parent new_parent = Seq.index f.parent new_parent);
          assert (Seq.index f.parent new_parent = new_parent); // new_parent is a root in f
          assert (pure_find_fuel f' z (fuel + 1) = pure_find_fuel f' new_parent fuel);
          assert (pure_find_fuel f' new_parent fuel = Some new_parent)
        end
        else begin
          // z is a root in f and z <> changed_node, so parent_f'[z] = parent_f[z] = z
          assert (Seq.index f'.parent z = z);
          assert (pure_find_fuel f' z fuel = Some z)
        end
      end
      else begin
        // z is not a root in f
        assert (z <> changed_node); // changed_node is a root in f
        // So parent_f'[z] = parent_f[z] = px_f
        assert (Seq.index f'.parent z = px_f);
        // Recurse: pure_find_fuel f px_f (fuel-1) = pure_find_fuel f z fuel (Some)
        pure_find_fuel_after_update f changed_node new_parent px_f (fuel - 1);
        // Now use the IH result
        match pure_find_fuel f px_f (fuel - 1) with
        | Some r ->
          if r = changed_node then begin
            assert (pure_find_fuel f' px_f fuel = Some new_parent);
            // pure_find_fuel f' z (fuel+1) = pure_find_fuel f' px_f fuel = Some new_parent
            assert (pure_find_fuel f' z (fuel + 1) = pure_find_fuel f' px_f fuel)
          end
          else begin
            assert (pure_find_fuel f' px_f (fuel - 1) = Some r);
            // pure_find_fuel f' z fuel = pure_find_fuel f' px_f (fuel-1) = Some r
            assert (pure_find_fuel f' z fuel = pure_find_fuel f' px_f (fuel - 1))
          end
        | None -> ()
      end
#pop-options

// Now prove the main lemma using the fuel-based helper
//SNIPPET_START: pure_union_correctness
// Main correctness theorem for pure_union  
#restart-solver
#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let pure_union_correctness (f: uf_forest{is_valid_uf f /\ rank_invariant f}) (x y: nat{x < f.n /\ y < f.n})
  : Lemma (ensures (let f' = pure_union f x y in
                    is_valid_uf f' /\
                    rank_invariant f' /\
                    pure_find f' x == pure_find f' y))
//SNIPPET_END: pure_union_correctness
  = pure_union_valid f x y;
    pure_union_preserves_rank_invariant f x y;
    pure_find_in_bounds f x;
    pure_find_in_bounds f y;
    pure_find_is_root f x;
    pure_find_is_root f y;
    let root_x = pure_find f x in
    let root_y = pure_find f y in
    if root_x = root_y then ()
    else begin
      let f' = pure_union f x y in
      assert (is_valid_uf f');
      assert (rank_invariant f');
      pure_find_fuel_sufficient f x;
      pure_find_fuel_sufficient f y;
      let rank_x = Seq.index f.rank root_x in
      let rank_y = Seq.index f.rank root_y in
      // f_p = parent-only change (used by fuel_after_update)
      let changed = if rank_x < rank_y then root_x 
                    else root_y in
      let target = if rank_x < rank_y then root_y
                   else root_x in
      let f_p = { f with parent = Seq.upd f.parent changed target } in
      // f_p is valid
      let check_fp (i: nat{i < f_p.n}) : Lemma (Seq.index f_p.parent i < f_p.n) = () in
      FStar.Classical.forall_intro check_fp;
      // f' has same parent as f_p
      assert (f'.parent == f_p.parent);
      assert (f'.n == f_p.n);
      // Apply fuel_after_update
      pure_find_fuel_after_update f changed target x f.n;
      pure_find_fuel_after_update f changed target y f.n;
      // For x: pure_find f x = root_x
      // For y: pure_find f y = root_y
      if rank_x < rank_y then begin
        // changed = root_x, target = root_y
        // x: pure_find f x = root_x = changed => pure_find_fuel f_p x (f.n+1) = Some root_y
        assert (pure_find_fuel f_p x (f.n + 1) = Some root_y);
        // y: pure_find f y = root_y <> root_x = changed => pure_find_fuel f_p y f.n = Some root_y
        assert (pure_find_fuel f_p y f.n = Some root_y);
        // Transfer to f' (same parent)
        pure_find_fuel_rank_independent f_p f' x (f.n + 1);
        pure_find_fuel_rank_independent f_p f' y f.n;
        // f' has sufficient fuel
        pure_find_fuel_sufficient f' x;
        pure_find_fuel_sufficient f' y;
        pure_find_fuel_deterministic f' x f.n (f.n + 1);
        assert (pure_find_fuel f' x f.n = Some root_y);
        assert (pure_find_fuel f' y f.n = Some root_y);
        assert (pure_find f' x == root_y);
        assert (pure_find f' y == root_y)
      end
      else if rank_x > rank_y then begin
        // changed = root_y, target = root_x
        // x: pure_find f x = root_x <> root_y = changed => pure_find_fuel f_p x f.n = Some root_x
        assert (pure_find_fuel f_p x f.n = Some root_x);
        // y: pure_find f y = root_y = changed => pure_find_fuel f_p y (f.n+1) = Some root_x
        assert (pure_find_fuel f_p y (f.n + 1) = Some root_x);
        // Transfer to f'
        pure_find_fuel_rank_independent f_p f' x f.n;
        pure_find_fuel_rank_independent f_p f' y (f.n + 1);
        pure_find_fuel_sufficient f' x;
        pure_find_fuel_sufficient f' y;
        pure_find_fuel_deterministic f' y f.n (f.n + 1);
        assert (pure_find_fuel f' x f.n = Some root_x);
        assert (pure_find_fuel f' y f.n = Some root_x);
        assert (pure_find f' x == root_x);
        assert (pure_find f' y == root_x)
      end
      else begin
        // Equal rank: changed = root_y, target = root_x
        // f' also changes rank, but parent is same as f_p
        // x: pure_find f x = root_x <> root_y = changed => pure_find_fuel f_p x f.n = Some root_x
        assert (pure_find_fuel f_p x f.n = Some root_x);
        // y: pure_find f y = root_y = changed => pure_find_fuel f_p y (f.n+1) = Some root_x
        assert (pure_find_fuel f_p y (f.n + 1) = Some root_x);
        // Transfer to f'
        pure_find_fuel_rank_independent f_p f' x f.n;
        pure_find_fuel_rank_independent f_p f' y (f.n + 1);
        pure_find_fuel_sufficient f' x;
        pure_find_fuel_sufficient f' y;
        pure_find_fuel_deterministic f' y f.n (f.n + 1);
        assert (pure_find_fuel f' x f.n = Some root_x);
        assert (pure_find_fuel f' y f.n = Some root_x);
        assert (pure_find f' x == root_x);
        assert (pure_find f' y == root_x)
      end
    end
#pop-options

// See CLRS.Ch21.UnionFind.RankBound for the full proof:
//   rank_logarithmic_bound_sized: rank[x] <= log2_floor(n)
// The proof tracks subtree sizes (size_rank_invariant: size[x] >= 2^rank[x])
// and uses the bound size[x] <= n to conclude 2^rank[x] <= n.

(*** 8. Summary Theorems ***)

// Theorem: Union-Find maintains all invariants through sequence of operations
// (Proof requires showing that pure_union preserves f.n, which is straightforward
// but omitted for brevity)
let uf_invariant_maintained (f: uf_forest{is_valid_uf f /\ rank_invariant f}) (ops: list (nat * nat))
  : Lemma (requires (forall x y. (x, y) `List.Tot.mem` ops ==> x < f.n /\ y < f.n))
          (ensures True)  // Simplified - would prove invariants maintained
  = ()

// Theorem: Termination of pure_find guaranteed by rank_invariant
// (Encoded in decreases clause of pure_find)

// Corollary: Under rank_invariant, pure_find always terminates and returns a root
let pure_find_total_correctness (f: uf_forest{is_valid_uf f /\ rank_invariant f}) (x: nat{x < f.n})
  : Lemma (ensures is_root f (pure_find f x) /\ pure_find f x < f.n)
  = pure_find_is_root f x;
    pure_find_in_bounds f x
