(**
 * ISMM: Union-Find Union Operation and Correctness Lemmas
 *
 * Provides:
 *   - pure_union_preserves_inv: full invariant preservation (uses SizeRank)
 *   - Correctness (merged sets find the same root)
 *   - Stability (unrelated sets unchanged)
 *)
module ISMM.UnionFind.Union

open FStar.Seq
module Seq = FStar.Seq
open ISMM.Status
open ISMM.UnionFind.Spec

(*** 1. Rank Monotonicity Along Paths ***)

let rec rank_mono (s: uf_state{uf_inv_base s}) (x: nat{x < s.n})
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

let rank_strict_mono (s: uf_state{uf_inv_base s}) (x: nat{x < s.n})
  : Lemma (requires Seq.index s.parent x <> x)
          (ensures (pure_find_in_bounds s x;
                    Seq.index s.rank x < Seq.index s.rank (pure_find s x)))
  = count_above_strict s.rank (Seq.index s.rank x) (Seq.index s.parent x) 0 s.n;
    rank_mono s (Seq.index s.parent x);
    pure_find_in_bounds s (Seq.index s.parent x)

(*** 2. Full Invariant Preservation ***)

/// pure_union preserves the full uf_inv (base + size_rank_inv).
let pure_union_preserves_inv (s: uf_state{uf_inv s}) (x y: nat{x < s.n /\ y < s.n})
  : Lemma (ensures uf_inv (pure_union s x y))
  = pure_union_preserves_inv_base s x y;
    ISMM.UF.SizeRank.pure_union_preserves_size_rank s x y

(*** 3. Correctness: union merges the two sets ***)

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

(*** 4. Stability: union does not merge unrelated sets ***)

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
