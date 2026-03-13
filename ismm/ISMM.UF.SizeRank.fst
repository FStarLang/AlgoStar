(**
 * ISMM: Size-Rank Invariant Preservation under Union
 *
 * Proves that pure_union preserves size_rank_inv.
 * Uses pure_find_after_link from Spec to reason about
 * how comp_count changes after linking two roots.
 *)
module ISMM.UF.SizeRank

open FStar.Seq
module Seq = FStar.Seq
open ISMM.UnionFind.Spec

(*** 1. comp_count after linking root_a → root_b ***)

/// After linking root_a → root_b, comp_count for root_b gains root_a's component.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let rec comp_count_after_link_merged
  (s s': uf_state{uf_inv_base s /\ uf_inv_base s'})
  (root_a root_b: nat)
  (k: nat)
  : Lemma
      (requires
        root_a < s.n /\ root_b < s.n /\ root_a <> root_b /\
        k <= s.n /\
        is_root s root_a /\ is_root s root_b /\
        s'.n == s.n /\
        (forall (z: nat). z < s.n ==>
          (if pure_find s z = root_a then pure_find s' z = root_b
           else if pure_find s z = root_b then pure_find s' z = root_b
           else pure_find s' z = pure_find s z)))
      (ensures comp_count s' root_b k == comp_count s root_a k + comp_count s root_b k)
      (decreases k)
  = if k = 0 then ()
    else comp_count_after_link_merged s s' root_a root_b (k - 1)
#pop-options

/// After linking root_a → root_b, comp_count for other roots is unchanged.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let rec comp_count_after_link_other
  (s s': uf_state{uf_inv_base s /\ uf_inv_base s'})
  (root_a root_b: nat)
  (r: nat)
  (k: nat)
  : Lemma
      (requires
        root_a < s.n /\ root_b < s.n /\ root_a <> root_b /\
        r < s.n /\ r <> root_a /\ r <> root_b /\
        k <= s.n /\
        is_root s root_a /\ is_root s root_b /\
        s'.n == s.n /\
        (forall (z: nat). z < s.n ==>
          (if pure_find s z = root_a then pure_find s' z = root_b
           else if pure_find s z = root_b then pure_find s' z = root_b
           else pure_find s' z = pure_find s z)))
      (ensures comp_count s' r k == comp_count s r k)
      (decreases k)
  = if k = 0 then ()
    else comp_count_after_link_other s s' root_a root_b r (k - 1)
#pop-options

(*** 2. pure_union preserves size_rank_inv ***)

/// Main theorem: pure_union preserves the size-rank invariant.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let pure_union_preserves_size_rank
  (s: uf_state{uf_inv s}) (x y: nat{x < s.n /\ y < s.n})
  : Lemma (ensures (pure_union_preserves_inv_base s x y;
                    size_rank_inv (pure_union s x y)))
  = pure_union_preserves_inv_base s x y;
    pure_find_in_bounds s x; pure_find_in_bounds s y;
    pure_find_is_root s x; pure_find_is_root s y;
    let root_x = pure_find s x in
    let root_y = pure_find s y in
    if root_x = root_y then ()
    else begin
      let s' = pure_union s x y in
      let rx = Seq.index s.rank root_x in
      let ry = Seq.index s.rank root_y in
      // Apply pure_find_after_link for all nodes
      let link_facts (z: nat{z < s.n})
        : Lemma (if pure_find s z = root_x then
                   (if rx < ry then pure_find s' z = root_y
                    else pure_find s' z = root_x)
                 else if pure_find s z = root_y then
                   (if rx < ry then pure_find s' z = root_y
                    else pure_find s' z = root_x)
                 else pure_find s' z = pure_find s z)
        = if rx < ry then
            pure_find_after_link s s' root_x root_y z
          else
            pure_find_after_link s s' root_y root_x z
      in FStar.Classical.forall_intro link_facts;
      if rx < ry then begin
        // root_x → root_y: root_y stays, gets root_x's component, rank unchanged
        comp_count_after_link_merged s s' root_x root_y s.n;
        // For other roots
        let other_ok (r: nat{r < s'.n /\ Seq.index s'.parent r = r /\ r <> root_y})
          : Lemma (comp_count s' r s'.n >= pow2 (Seq.index s'.rank r))
          = assert (r <> root_x); // root_x is no longer a root
            comp_count_after_link_other s s' root_x root_y r s.n
        in FStar.Classical.forall_intro (FStar.Classical.move_requires other_ok)
      end
      else if rx > ry then begin
        // root_y → root_x: symmetric
        comp_count_after_link_merged s s' root_y root_x s.n;
        let other_ok (r: nat{r < s'.n /\ Seq.index s'.parent r = r /\ r <> root_x})
          : Lemma (comp_count s' r s'.n >= pow2 (Seq.index s'.rank r))
          = assert (r <> root_y);
            comp_count_after_link_other s s' root_y root_x r s.n
        in FStar.Classical.forall_intro (FStar.Classical.move_requires other_ok)
      end
      else begin
        // Equal rank: root_y → root_x, rank[root_x] += 1
        assert (not (rx < ry) /\ not (rx > ry));
        assert (rx >= ry /\ ry >= rx);
        comp_count_after_link_merged s s' root_y root_x s.n;
        assert (comp_count s' root_x s'.n == comp_count s root_y s.n + comp_count s root_x s.n);
        // pow2(rx + 1) = 2 * pow2(rx), and both components have >= pow2(rx) nodes
        assert (pow2 (rx + 1) == op_Multiply 2 (pow2 rx));
        let other_ok (r: nat{r < s'.n /\ Seq.index s'.parent r = r /\ r <> root_x})
          : Lemma (comp_count s' r s'.n >= pow2 (Seq.index s'.rank r))
          = assert (r <> root_y);
            comp_count_after_link_other s s' root_y root_x r s.n
        in FStar.Classical.forall_intro (FStar.Classical.move_requires other_ok)
      end
    end
#pop-options

