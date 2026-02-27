(*
   Proof that pure_find_fuel terminates under rank_invariant.
   
   Key insight: rank strictly increases along parent pointers.
   Decreasing measure: bound - rank(x), where bound >= all ranks.
   
   Types and definitions imported from CLRS.Ch21.UnionFind.Spec.
*)
module CLRS.Ch21.UnionFind.FindTermination

open FStar.Seq
open CLRS.Ch21.UnionFind.Spec

module Seq = FStar.Seq

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
