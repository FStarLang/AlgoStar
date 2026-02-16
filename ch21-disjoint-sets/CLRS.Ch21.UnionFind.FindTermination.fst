(*
   Proof that pure_find_fuel terminates under rank_invariant.
   
   Key insight: rank strictly increases along parent pointers.
   Decreasing measure: bound - rank(x), where bound >= all ranks.
   
   We need ranks_bounded (rank < n for all nodes), which is proven
   in UnionFind.RankBound. We add it as a precondition here to keep
   this module self-contained.
*)
module CLRS.Ch21.UnionFind.FindTermination

open FStar.Seq
module Seq = FStar.Seq

type uf_forest = {
  parent: Seq.seq nat;
  rank: Seq.seq nat;
  n: nat
}

let is_valid_uf (f: uf_forest) : prop =
  f.n > 0 /\
  Seq.length f.parent == f.n /\
  Seq.length f.rank == f.n /\
  (forall (i: nat). i < f.n ==> Seq.index f.parent i < f.n) /\
  (forall (i: nat). i < f.n ==> Seq.index f.rank i >= 0)

let rank_invariant (f: uf_forest) : prop =
  is_valid_uf f ==>
  (forall (x: nat{x < f.n}). Seq.index f.parent x <> x ==>
    Seq.index f.rank x < Seq.index f.rank (Seq.index f.parent x))

let ranks_bounded (f: uf_forest) : prop =
  is_valid_uf f ==>
  (forall (x: nat{x < f.n}). Seq.index f.rank x < f.n)

let rec pure_find_fuel (f: uf_forest{is_valid_uf f}) (x: nat{x < f.n}) (fuel: nat)
  : Tot (option nat) (decreases fuel)
  = if fuel = 0 then None
    else
      let px = Seq.index f.parent x in
      if px = x then Some x
      else pure_find_fuel f px (fuel - 1)

(* Explicit quantifier instantiation for rank_invariant *)
let rank_inv_inst (f: uf_forest{is_valid_uf f}) (x: nat{x < f.n})
  : Lemma (requires rank_invariant f /\ Seq.index f.parent x <> x)
          (ensures Seq.index f.rank x < Seq.index f.rank (Seq.index f.parent x))
  = ()

(* Core lemma: if fuel + rank(x) > bound and all ranks <= bound, find succeeds.
   Decreasing: bound - rank(x). *)
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

(* Main theorem: with rank_invariant + ranks_bounded, fuel=n always suffices.
   Proof: all ranks < n, so all ranks <= n-1.
   fuel = n, rank(x) >= 0, so fuel + rank(x) >= n > n-1. *)
let pure_find_fuel_sufficient 
  (f: uf_forest{is_valid_uf f /\ rank_invariant f /\ ranks_bounded f}) 
  (x: nat{x < f.n})
  : Lemma (ensures Some? (pure_find_fuel f x f.n))
  = find_fuel_by_bound f x f.n (f.n - 1)
