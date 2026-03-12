(**
 * ISMM: Union-Find — Path Compression Lemmas
 *
 * Adapts compression proofs from CLRS.Ch21.UnionFind.Spec (§4b).
 * Proves that compressing a node v to its root preserves uf_inv
 * and pure_find for all nodes.
 *)
module ISMM.UnionFind.Compress

open FStar.Mul
module Seq = FStar.Seq
open ISMM.Status
open ISMM.UnionFind.Spec
open ISMM.UnionFind.Union   // for rank_mono, rank_strict_mono

(*** Compression: pointing v directly to its root ***)

/// pure_find of a non-root differs from the node itself
let pure_find_nonroot (s: uf_state{uf_inv s}) (v: nat{v < s.n})
  : Lemma (requires Seq.index s.parent v <> v)
          (ensures pure_find s v <> v)
  = pure_find_is_root s v

/// Compressing v preserves uf_inv.
#push-options "--z3rlimit 20"
let compress_preserves_uf_inv (s: uf_state{uf_inv s}) (v: nat{v < s.n})
  : Lemma (ensures (pure_find_in_bounds s v;
                    uf_inv { s with parent = Seq.upd s.parent v (pure_find s v) }))
  = pure_find_in_bounds s v; pure_find_is_root s v;
    let s' = { s with parent = Seq.upd s.parent v (pure_find s v) } in
    let valid_aux (i: nat{i < s'.n}) : Lemma (Seq.index s'.parent i < s'.n) = () in
    FStar.Classical.forall_intro valid_aux;
    if Seq.index s.parent v = v then ()
    else begin
      rank_strict_mono s v;
      let ri_aux (z: nat{z < s'.n /\ Seq.index s'.parent z <> z})
        : Lemma (Seq.index s'.rank z < Seq.index s'.rank (Seq.index s'.parent z))
        = () in FStar.Classical.forall_intro ri_aux
    end
#pop-options

/// Compressing v to its root preserves pure_find for ALL nodes z.
#push-options "--fuel 1 --ifuel 0 --z3rlimit 80"
let rec compress_preserves_find
  (s: uf_state{uf_inv s}) (v: nat{v < s.n}) (z: nat{z < s.n})
  : Lemma (requires (pure_find_in_bounds s v;
                     pure_find_is_root s v;
                     True))
          (ensures (let root = pure_find s v in
                    let s' = { s with parent = Seq.upd s.parent v root } in
                    compress_preserves_uf_inv s v;
                    pure_find s' z == pure_find s z))
          (decreases (count_above s.rank (Seq.index s.rank z) 0 s.n))
  = pure_find_in_bounds s v; pure_find_is_root s v;
    compress_preserves_uf_inv s v;
    let root = pure_find s v in
    let s' = { s with parent = Seq.upd s.parent v root } in
    let pz = Seq.index s.parent z in
    if pz = z then begin
      if z = v then (pure_find_root s v; assert (root == v))
      else ()
    end
    else begin
      if z = v then begin
        pure_find_nonroot s v;
        rank_strict_mono s v;
        assert (Seq.index s'.parent root == root);
        pure_find_root s' root;
        count_above_strict s'.rank (Seq.index s'.rank v) root 0 s'.n;
        assert (pure_find s' v == root)
      end
      else begin
        count_above_strict s.rank (Seq.index s.rank z) pz 0 s.n;
        compress_preserves_find s v pz;
        count_above_strict s'.rank (Seq.index s'.rank z) pz 0 s'.n
      end
    end
#pop-options

/// Universal wrapper: compression preserves uf_inv and pure_find for all nodes.
let compress_preserves_find_all (s: uf_state{uf_inv s}) (v: nat{v < s.n})
  : Lemma (ensures (pure_find_in_bounds s v;
                    let root = pure_find s v in
                    let s' = { s with parent = Seq.upd s.parent v root } in
                    uf_inv s' /\
                    (forall (z: nat). z < s.n ==> pure_find s' z == pure_find s z)))
  = compress_preserves_uf_inv s v;
    pure_find_in_bounds s v;
    let root = pure_find s v in
    let s' = { s with parent = Seq.upd s.parent v root } in
    let aux (z: nat{z < s.n})
      : Lemma (pure_find s' z == pure_find s z)
      = compress_preserves_find s v z
    in
    FStar.Classical.forall_intro aux
