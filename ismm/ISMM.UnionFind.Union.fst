(**
 * ISMM: Union-Find Union Operation and Correctness Lemmas
 *
 * Separated from ISMM.UnionFind.Spec for faster incremental checking.
 * Provides:
 *   - pure_union: merge two RANK-state representatives
 *   - Invariant preservation
 *   - Correctness (merged sets find the same root)
 *   - Stability (unrelated sets unchanged)
 *)
module ISMM.UnionFind.Union

open FStar.Seq
module Seq = FStar.Seq
open ISMM.Status
open ISMM.UnionFind.Spec

(*** 1. Rank Monotonicity Along Paths ***)

let rec rank_mono (s: uf_state{uf_inv s}) (x: nat{x < s.n})
  : Lemma (ensures (pure_find_in_bounds s x;
                    Seq.index s.rank x <= Seq.index s.rank (pure_find s x)))
          (decreases (count_above s.rank (Seq.index s.rank x) 0 s.n))
  = let p = Seq.index s.parent x in
    if p = x then pure_find_root s x
    else begin
      count_above_strict s.rank (Seq.index s.rank x) p 0 s.n;
      rank_mono s p;
      pure_find_in_bounds s p
    end

let rank_strict_mono (s: uf_state{uf_inv s}) (x: nat{x < s.n})
  : Lemma (requires Seq.index s.parent x <> x)
          (ensures (pure_find_in_bounds s x;
                    Seq.index s.rank x < Seq.index s.rank (pure_find s x)))
  = count_above_strict s.rank (Seq.index s.rank x) (Seq.index s.parent x) 0 s.n;
    rank_mono s (Seq.index s.parent x);
    pure_find_in_bounds s (Seq.index s.parent x)

(*** 2. Pure Union ***)

/// Union two nodes by rank. Links one root to the other via parent array.
/// Tag array is NOT modified — tags change during freeze, not during union.
let pure_union (s: uf_state{uf_inv s}) (x y: nat{x < s.n /\ y < s.n}) : uf_state =
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

(*** 3. Invariant Preservation ***)

#push-options "--z3rlimit 20"
let pure_union_preserves_inv (s: uf_state{uf_inv s}) (x y: nat{x < s.n /\ y < s.n})
  : Lemma (ensures uf_inv (pure_union s x y))
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

(*** 4. How pure_find changes after linking root_a → root_b ***)

#restart-solver
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let rec pure_find_after_link
  (s s': uf_state{uf_inv s /\ uf_inv s'})
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

(*** 5. Correctness: union merges the two sets ***)

#restart-solver
#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let pure_union_same_set (s: uf_state{uf_inv s}) (x y: nat{x < s.n /\ y < s.n})
  : Lemma (ensures (pure_union_preserves_inv s x y;
                    let s' = pure_union s x y in
                    pure_find s' x == pure_find s' y))
  = pure_union_preserves_inv s x y;
    pure_find_in_bounds s x; pure_find_in_bounds s y;
    pure_find_is_root s x; pure_find_is_root s y;
    let root_x = pure_find s x in
    let root_y = pure_find s y in
    if root_x = root_y then ()
    else begin
      let s' = pure_union s x y in
      let rx = Seq.index s.rank root_x in
      let ry = Seq.index s.rank root_y in
      if rx < ry then begin
        pure_find_after_link s s' root_x root_y x;
        pure_find_after_link s s' root_x root_y y
      end
      else if rx > ry then begin
        pure_find_after_link s s' root_y root_x x;
        pure_find_after_link s s' root_y root_x y
      end
      else begin
        pure_find_after_link s s' root_y root_x x;
        pure_find_after_link s s' root_y root_x y
      end
    end
#pop-options

(*** 6. Stability: union does not merge unrelated sets ***)

#restart-solver
#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let pure_union_other_set (s: uf_state{uf_inv s}) (x y z: nat{x < s.n /\ y < s.n /\ z < s.n})
  : Lemma (requires pure_find s z <> pure_find s x /\ pure_find s z <> pure_find s y)
          (ensures (pure_union_preserves_inv s x y;
                    pure_find (pure_union s x y) z == pure_find s z))
  = pure_union_preserves_inv s x y;
    pure_find_in_bounds s x; pure_find_in_bounds s y;
    pure_find_is_root s x; pure_find_is_root s y;
    let root_x = pure_find s x in
    let root_y = pure_find s y in
    if root_x = root_y then ()
    else begin
      let s' = pure_union s x y in
      let rx = Seq.index s.rank root_x in
      let ry = Seq.index s.rank root_y in
      if rx < ry then
        pure_find_after_link s s' root_x root_y z
      else if rx > ry then
        pure_find_after_link s s' root_y root_x z
      else
        pure_find_after_link s s' root_y root_x z
    end
#pop-options

#restart-solver
#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let pure_union_stability (s: uf_state{uf_inv s}) (x y: nat{x < s.n /\ y < s.n})
  : Lemma (ensures (pure_union_preserves_inv s x y;
                    let s' = pure_union s x y in
                    forall (z: nat). z < s.n ==>
                      pure_find s z <> pure_find s x ==>
                      pure_find s z <> pure_find s y ==>
                      pure_find s' z == pure_find s z))
  = pure_union_preserves_inv s x y;
    let aux (z: nat{z < s.n})
      : Lemma (requires pure_find s z <> pure_find s x /\
                        pure_find s z <> pure_find s y)
              (ensures pure_find (pure_union s x y) z == pure_find s z)
      = pure_union_other_set s x y z
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options
